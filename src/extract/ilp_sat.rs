use super::*;

struct ClassVars {
    active: i32,
    nodes: Vec<i32>,
}

pub struct CbcExtractor;

impl Extractor for CbcExtractor {
    fn extract(&self, egraph: &EGraph, roots: &[ClassId]) -> ExtractionResult {
        let mut next_var: i32 = 1;
        let mut get_next = || {
            let current = next_var;
            next_var += 1;
            current
        };

        let vars: IndexMap<ClassId, ClassVars> = egraph
            .classes()
            .values()
            .map(|class| {
                let cvars = ClassVars {
                    active: get_next(),
                    nodes: class.nodes.iter().map(|_| get_next()).collect(),
                };
                (class.id.clone(), cvars)
            })
            .collect();

        let mut sat: cadical::Solver = Default::default();
        let false_literal = get_next();
        sat.add_clause(vec![-false_literal]);

        let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);

        // Disable the node if it points to itself.
        for class in egraph.classes().values() {
            for (node_idx, node_id) in class.nodes.iter().enumerate() {
                let node = &egraph[node_id];
                if node
                    .children
                    .iter()
                    .map(|n| n2c(n))
                    .any(|cid| *cid == class.id)
                {
                    //    vars.get_mut(&class.id).unwrap().nodes[node_idx] = false_literal;
                }
            }
        }

        for class in egraph.classes().values() {
            for (node_id, &node_active) in class.nodes.iter().zip(&vars[&class.id].nodes) {
                let node = &egraph[node_id];
                //model.set_obj_coeff(node_active, node.cost.into_inner());
                /*
                print!(
                    " {} x{}",
                    (1000.0 * node.cost.into_inner()) as i64,
                    node_active
                );
                */
            }
        }

        for (id, class) in &vars {
            // class active == some node active
            // sum(for node_active in class) == class_active

            //let row = model.add_row();
            //model.set_row_equal(row, 0.0);
            //model.set_weight(row, class.active, -1.0);
            let mut clause: Vec<i32> = Vec::new();
            clause.push(-class.active);

            for &node_active in &class.nodes {
                //model.set_weight(row, node_active, 1.0);
                clause.push(node_active);
            }
            sat.add_clause(clause);

            for (node_id, &node_active) in egraph[id].nodes.iter().zip(&class.nodes) {
                let node = &egraph[node_id];
                for child in &node.children {
                    let eclass_id = &egraph[child].eclass;
                    let child_active = vars[eclass_id].active;
                    // node active implies child active, encoded as:
                    //   node_active <= child_active
                    //   node_active - child_active <= 0
                    //let row = model.add_row();
                    //model.set_row_upper(row, 0.0);
                    //model.set_weight(row, node_active, 1.0);
                    //model.set_weight(row, child_active, -1.0);
                    sat.add_clause(vec![-node_active, child_active]);
                }
            }
        }

        for root in roots {
            sat.add_clause(vec![vars[root].active]);
        }

        loop {
            let result = sat.solve();
            assert_eq!(result, Some(true));

            let mut result = ExtractionResult::default();

            for (id, var) in &vars {
                let active = sat.value(var.active) == Some(true);
                if active {
                    let node_idx = var
                        .nodes
                        .iter()
                        .position(|&n| sat.value(n) == Some(true))
                        .unwrap();
                    let node_id = egraph[id].nodes[node_idx].clone();
                    result.choose(id.clone(), node_id);
                }
            }

            let cycles = find_cycles(&result, egraph, roots);
            if cycles.is_empty() {
                return result;
            } else {
                for c in &cycles {
                    block_cycle(&mut sat, &egraph, c, &vars, &mut get_next);
                }
            }
        }
    }
}

fn block_cycle(
    sat: &mut cadical::Solver,
    egraph: &EGraph,
    cycle: &Vec<ClassId>,
    vars: &IndexMap<ClassId, ClassVars>,
    get_next: &mut impl FnMut() -> i32,
) {
    if cycle.len() == 0 {
        return;
    }
    let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);

    let node_to_var = |node_id: &NodeId| -> Option<i32> {
        let class_id = egraph.nid_to_cid(node_id);
        let class_nodes = &egraph[class_id].nodes;

        // Find the index of the node_id in the class's nodes list
        let node_index = class_nodes.iter().position(|nid| nid == node_id)?;

        // Fetch the corresponding variable from the ClassVars's nodes vector
        vars.get(class_id)
            .and_then(|class_vars| class_vars.nodes.get(node_index).cloned())
    };

    let mut blocking = Vec::new();
    for i in 0..cycle.len() {
        let current_class_id = &cycle[i];
        let next_class_id = &cycle[(i + 1) % cycle.len()];

        let blocking_var = get_next();
        blocking.push(-blocking_var.clone());
        for node_id in &egraph[current_class_id].nodes {
            let node = &egraph[node_id];
            if node
                .children
                .iter()
                .map(|n| n2c(n))
                .any(|cid| *cid == *next_class_id)
            {
                sat.add_clause(vec![-node_to_var(node_id).unwrap(), blocking_var]);
            }
        }
    }
    sat.add_clause(blocking);
}

#[derive(Clone)]
enum TraverseStatus {
    Doing,
    Done,
}

