/* An ILP extractor that returns the optimal DAG-extraction.

This extractor is simple so that it's easy to see that it's correct.

If the timeout is reached, it will return the result of the faster-greedy-dag extractor.
*/

use std::time::SystemTime;

use super::*;
use coin_cbc::{Col, Model, Sense};
use indexmap::IndexSet;

struct ClassVars {
    active: Col,
    nodes: Vec<Col>,
}

pub struct CbcExtractorWithTimeout<const TIMEOUT_IN_SECONDS: u32>;

impl<const TIMEOUT_IN_SECONDS: u32> Extractor for CbcExtractorWithTimeout<TIMEOUT_IN_SECONDS> {
    fn extract(&self, egraph: &EGraph, roots: &[ClassId]) -> ExtractionResult {
        return extract(egraph, roots, TIMEOUT_IN_SECONDS);
    }
}

pub struct CbcExtractor;

impl Extractor for CbcExtractor {
    fn extract(&self, egraph: &EGraph, roots: &[ClassId]) -> ExtractionResult {
        return extract(egraph, roots, std::u32::MAX);
    }
}

fn extract(egraph: &EGraph, roots: &[ClassId], timeout_seconds: u32) -> ExtractionResult {
    let mut model = Model::default();

    model.set_parameter("seconds", &timeout_seconds.to_string());
    model.set_parameter("loglevel", "0");

    let vars: IndexMap<ClassId, ClassVars> = egraph
        .classes()
        .values()
        .map(|class| {
            let cvars = ClassVars {
                active: model.add_binary(),
                nodes: class.nodes.iter().map(|_| model.add_binary()).collect(),
            };
            (class.id.clone(), cvars)
        })
        .collect();

    for (class_id, class) in &vars {
        // class active == some node active
        // sum(for node_active in class) == class_active
        let row = model.add_row();
        model.set_row_equal(row, 0.0);
        model.set_weight(row, class.active, -1.0);
        for &node_active in &class.nodes {
            model.set_weight(row, node_active, 1.0);
        }

        let childrens_classes_var = |nid: NodeId| {
            egraph[&nid]
                .children
                .iter()
                .map(|n| egraph[n].eclass.clone())
                .map(|n| vars[&n].active)
                .collect::<IndexSet<_>>()
        };

        for (node_id, &node_active) in egraph[class_id].nodes.iter().zip(&class.nodes) {
            for child_active in childrens_classes_var(node_id.clone()) {
                // node active implies child active, encoded as:
                //   node_active <= child_active
                //   node_active - child_active <= 0
                let row = model.add_row();
                model.set_row_upper(row, 0.0);
                model.set_weight(row, node_active, 1.0);
                model.set_weight(row, child_active, -1.0);
            }
        }

        // block cycles when the node contains it's own class.
        for (node_id, &node_active) in egraph[class_id].nodes.iter().zip(&class.nodes) {
            let childrens_classes_var = |nid: NodeId| {
                egraph[&nid]
                    .children
                    .iter()
                    .map(|n| egraph[n].eclass.clone())
                    .collect::<IndexSet<_>>()
            };

            if childrens_classes_var(node_id.clone()).contains(class_id) {
                let row = model.add_row();
                model.set_row_upper(row, 0.0);
                model.set_weight(row, node_active, 1.0);
            }
        }
    }

    model.set_obj_sense(Sense::Minimize);
    for class in egraph.classes().values() {
        for (node_id, &node_active) in class.nodes.iter().zip(&vars[&class.id].nodes) {
            let node = &egraph[node_id];
            let node_cost = node.cost.into_inner();
            assert!(node_cost >= 0.0);

            if node_cost != 0.0 {
                model.set_obj_coeff(node_active, node_cost);
            }
        }
    }

    for root in roots {
        model.set_col_lower(vars[root].active, 1.0);
    }

    let mut solver_vars = Vars::new();

    let start_time = SystemTime::now();

    loop {
        // Set the solver limit based on how long has passed already.
        if let Ok(difference) = SystemTime::now().duration_since(start_time) {
            let seconds = timeout_seconds.saturating_sub(difference.as_secs().try_into().unwrap());
            model.set_parameter("seconds", &seconds.to_string());
        } else {
            model.set_parameter("seconds", "0");
        }

        let solution = model.solve();
        log::info!(
            "CBC status {:?}, {:?}, obj = {}",
            solution.raw().status(),
            solution.raw().secondary_status(),
            solution.raw().obj_value(),
        );

        if solution.raw().status() != coin_cbc::raw::Status::Finished {
            assert!(timeout_seconds != std::u32::MAX);

            let initial_result =
                super::faster_greedy_dag::FasterGreedyDagExtractor.extract(egraph, roots);
            log::info!("Unfinished CBC solution");
            return initial_result;
        }

        let mut result = ExtractionResult::default();

        for (id, var) in &vars {
            let active = solution.col(var.active) > 0.0;
            if active {
                let node_idx = var
                    .nodes
                    .iter()
                    .position(|&n| solution.col(n) > 0.0)
                    .unwrap();
                let node_id = egraph[id].nodes[node_idx].clone();
                result.choose(id.clone(), node_id);
            }
        }

        let cycles = find_cycles_in_result(&result, egraph, roots);
        if cycles.is_empty() {
            return result;
        }

        println!("found {} cycles", cycles.len());
        for cycle in cycles {
            println!("Blocking: {:?} ", cycle);
            block_cycles(&mut model, &vars, &egraph, &mut solver_vars, &cycle);
        }
    }
}

struct Vars {
    levels: IndexMap<ClassId, Col>,
    opposite: IndexMap<NodeId, Col>,
}

impl Vars {
    fn new() -> Self {
        Vars {
            levels: IndexMap::new(),
            opposite: IndexMap::new(),
        }
    }

    fn get_level(&mut self, model: &mut Model, class_id: &ClassId) -> Col {
        if self.levels.contains_key(class_id) {
            return *self.levels.get(class_id).unwrap();
        } else {
            let var = model.add_col();
            self.levels.insert(class_id.clone(), var);
            return var;
        }
    }

    fn get_opposite(&mut self, model: &mut Model, node_col: &Col, node_id: &NodeId) -> Col {
        if self.opposite.contains_key(node_id) {
            return *self.opposite.get(node_id).unwrap();
        } else {
            let opposite_col = model.add_binary();
            self.opposite.insert(node_id.clone(), opposite_col);
            let row = model.add_row();
            model.set_row_equal(row, 1.0);
            model.set_weight(row, opposite_col, 1.0);
            model.set_weight(row, *node_col, 1.0);

            return opposite_col;
        }
    }
}

/*

 To block cycles, we enforce that a topological ordering exists on the extraction.
 Each class is mapped to a variable (called its level).  Then for each node,
 we add a constraint that if a node is active, then the level of the class the node
 belongs to must be less than than the level of each of the node's children.

 To create a cycle, the levels would need to decrease, so they're blocked. For example,
 given a two class cycle: if class A, has level 'l', and class B has level 'm', then
 'l' must be less than 'm', but because there is also an active node in class B that
 has class A as a child, 'm' must be less than 'l', which is a contradiction.
*/

fn block_cycles(
    model: &mut Model,
    vars: &IndexMap<ClassId, ClassVars>,
    egraph: &EGraph,
    solver_vars: &mut Vars,
    cycle: &Vec<ClassId>,
) {
    if cycle.is_empty() {
        return;
    }
    for i in 0..cycle.len() {
        let current_class_id = &cycle[i];
        let next_class_id = &cycle[(i + 1) % cycle.len()];

        let childrens_classes_var = |nid: NodeId| {
            egraph[&nid]
                .children
                .iter()
                .map(|n| egraph[n].eclass.clone())
                .collect::<IndexSet<_>>()
        };

        let mut found = 0;
        for child in egraph[current_class_id].nodes.iter() {
            if childrens_classes_var(child.clone()).contains(next_class_id) {
                let node_idx = egraph[current_class_id]
                    .nodes
                    .iter()
                    .position(|n| child == n)
                    .unwrap();

                found += 1;
                let node_col = vars[current_class_id].nodes[node_idx];

                assert!(current_class_id != next_class_id);

                let row = model.add_row();
                model.set_row_lower(row, 1.0);
                let current_var = solver_vars.get_level(model, current_class_id);
                model.set_weight(row, current_var, -1.0);
                let next_var = solver_vars.get_level(model, next_class_id);
                model.set_weight(row, next_var, 1.0);

                // If n.variable is 0, then disable the contraint.
                let var = solver_vars.get_opposite(model, &node_col, child);
                model.set_weight(row, var, (vars.len() + 1) as f64);
            }
        }
        println!("number found {found}");
    }
}

#[derive(Clone)]
enum TraverseStatus {
    Doing,
    Done,
}

const CYCLE_LIMIT: usize = 1000;

fn find_cycles_in_result(
    extraction_result: &ExtractionResult,
    egraph: &EGraph,
    roots: &[ClassId],
) -> Vec<Vec<ClassId>> {
    let mut status = IndexMap::<ClassId, TraverseStatus>::default();
    let mut cycles = vec![];
    for root in roots {
        let mut stack = vec![];
        cycle_dfs(
            extraction_result,
            egraph,
            root,
            &mut status,
            &mut cycles,
            &mut stack,
        )
    }
    cycles
}

fn cycle_dfs(
    extraction_result: &ExtractionResult,
    egraph: &EGraph,
    class_id: &ClassId,
    status: &mut IndexMap<ClassId, TraverseStatus>,
    cycles: &mut Vec<Vec<ClassId>>,
    stack: &mut Vec<ClassId>,
) {
    match status.get(class_id).cloned() {
        Some(TraverseStatus::Done) => (),
        Some(TraverseStatus::Doing) => {
            // Get the part of the stack between the first visit to the class and now.
            let mut cycle = vec![];
            if let Some(pos) = stack.iter().position(|id| id == class_id) {
                cycle.extend_from_slice(&stack[pos..]);
            }
            cycles.push(cycle);
        }
        None => {
            if cycles.len() > CYCLE_LIMIT {
                return;
            }
            status.insert(class_id.clone(), TraverseStatus::Doing);
            stack.push(class_id.clone());
            let node_id = &extraction_result.choices[class_id];

            let childrens_classes_var = |nid: NodeId| {
                egraph[&nid]
                    .children
                    .iter()
                    .map(|n| egraph[n].eclass.clone())
                    .collect::<IndexSet<_>>()
            };

            for child_cid in childrens_classes_var(node_id.clone()) {
                cycle_dfs(extraction_result, egraph, &child_cid, status, cycles, stack)
            }
            let last = stack.pop();
            assert_eq!(*class_id, last.unwrap());
            status.insert(class_id.clone(), TraverseStatus::Done);
        }
    }
}
