use super::*;
use coin_cbc::{Col, Model, Sense};
use std::collections::HashSet;
use std::fmt;

struct CbcNode {
    node: NodeId,
    children: HashSet<ClassId>,
    active: Col,
    cost: Cost,
}

impl fmt::Debug for CbcNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CbcNode {{ node: {:?}, children: {:?},  cost: {:?} }}",
            self.node, self.children, self.cost
        )
    }
}

struct ClassVars {
    active: Col,
    members: Vec<CbcNode>,
    children_intersection: Vec<ClassId>, //not used yet.
}

pub struct CbcExtractor;

impl Extractor for CbcExtractor {
    fn extract(&self, egraph: &EGraph, roots: &[ClassId]) -> ExtractionResult {
        let mut vars: HashMap<ClassId, ClassVars> = HashMap::default();
        let mut model = Model::default();

        let nid_to_cid = |nid: &NodeId| egraph.nid_to_cid(nid);

        let true_literal = model.add_binary();
        model.set_col_lower(true_literal, 1.0);

        let false_literal = model.add_binary();
        model.set_col_upper(false_literal, 0.0);

        let initial_result = super::bottom_up::BottomUpExtractor.extract(egraph, roots);
        let initial_result_cost = initial_result.dag_cost(egraph, roots);
        println!("@Initial Cost: {}", initial_result_cost);

        for class in egraph.classes().values() {
            let nodes_in_class = &class.nodes;
            let mut cbc_nodes: Vec<CbcNode> = Vec::default();
            for n in nodes_in_class {
                let children: HashSet<ClassId> = egraph[n]
                    .children
                    .iter()
                    .map(|c| nid_to_cid(c).clone())
                    .collect();

                // Don't add if children loop, or if they contain the single root node.
                if !children.contains(&class.id) {
                    if roots.len() != 1 || !children.contains(&roots[0]) {
                        cbc_nodes.push(CbcNode {
                            node: n.clone(),
                            children: children,
                            active: model.add_binary(),
                            cost: egraph[n].cost,
                        });
                    }
                }
            }

            cbc_nodes.sort_by_key(|e| e.children.len());

            let mut to_remove = Vec::new();

            for i in 0..cbc_nodes.len() {
                for j in (i + 1)..cbc_nodes.len() {
                    let node_a = &cbc_nodes[i];
                    let node_b = &cbc_nodes[j];

                    if node_a.cost <= node_b.cost && node_a.children.is_subset(&node_b.children) {
                        to_remove.push(j);
                    }
                }
            }

            to_remove.sort_unstable();
            to_remove.dedup();

            for &index in to_remove.iter().rev() {
                cbc_nodes.remove(index);
            }

            // No single node's cost can exceed the previously best.
            cbc_nodes.retain(|node| node.cost <= initial_result_cost);

            vars.insert(
                class.id.clone(),
                ClassVars {
                    active: if cbc_nodes.len() == 1 {
                        // If there's only a single possible node, re-use its variable.
                        cbc_nodes[0].active
                    } else if cbc_nodes.len() == 0 {
                        // If there are no possible members, make it false.
                        false_literal
                    } else {
                        model.add_binary()
                    },
                    children_intersection: if cbc_nodes.len() > 1 {
                        intersection_of_children(&cbc_nodes)
                    } else {
                        Vec::default()
                    },
                    members: cbc_nodes,
                },
            );
        }

        // If there is a single parent class. Push the cost up to it.
        let child_to_parent = classes_with_single_parent(&vars);
        println!("@Classes with a single parent: {}", child_to_parent.len());

        for i in 0..3 {
            for (child, parent) in &child_to_parent {
                assert!(child != parent);

                let child_vars = vars.get_mut(&child).unwrap();
                let min_cost: Cost = child_vars
                    .members
                    .iter()
                    .map(|n| n.cost)
                    .min()
                    .unwrap_or(Cost::default());

                if min_cost.into_inner() == 0.0 {
                    continue;
                }

                for member in &mut child_vars.members {
                    member.cost -= min_cost;
                }

                if let Some(parent_vars) = vars.get_mut(&parent) {
                    for parent_member in &mut parent_vars.members {
                        if parent_member.children.contains(&child) {
                            parent_member.cost += min_cost;
                        }
                    }
                }

                if vars[&parent]
                    .members
                    .iter()
                    .filter(|m| m.children.contains(child))
                    .count()
                    == 1
                    && vars[&child].members.len() == 1
                {
                    let children = vars[&child].members[0].children.clone();

                    if let Some(parent_var) = vars.get_mut(&parent) {
                        parent_var.children_intersection.clear();
                        if let Some(m) = parent_var
                            .members
                            .iter_mut()
                            .find(|m| m.children.contains(child))
                        {
                            //m.children.extend(children);
                        }
                    }

                    let child_var = vars.get_mut(&child).unwrap();
                    //child_var.children_intersection.clear();
                    //child_var.members[0].children.clear();

                    //assert!(vars[&child].members[0].cost == Cost::default());
                }

                /*
                println!(
                    "@parent: {:?} child: {:?}",
                    vars[parent].members, vars[child].members
                );
                */
            }
        }

        let mut reachable_classes: HashSet<ClassId> = HashSet::default();
        reachable(&vars, &roots, &mut reachable_classes);
        let mut initial_size = vars.len();
        vars.retain(|class_id, _| reachable_classes.contains(class_id));
        println!("@Unreachable classes {}", initial_size - vars.len());

        let mut nodes = 0;
        for v in vars.values() {
            nodes += v.members.len();
        }

        println!("@classes: {} members: {}", vars.len(), nodes);

        for root in roots {
            model.set_col_lower(vars[root].active, 1.0);
        }

        for class_vars in vars.values() {
            //If the class is active, one of the members must be, too.
            if class_vars.members.len() > 1 {
                let row = model.add_row();
                model.set_row_equal(row, 0.0);
                model.set_weight(row, class_vars.active, -1.0);
                for node_active in &class_vars.members {
                    model.set_weight(row, node_active.active, 1.0);
                }
            }

            for class_id in &class_vars.children_intersection {
                let row = model.add_row();
                model.set_row_upper(row, 0.0);
                model.set_weight(row, class_vars.active, 1.0);
                model.set_weight(row, vars[&class_id].active, -1.0);
            }

            for cbc_node in &class_vars.members {
                let row = model.add_row();
                model.set_row_upper(row, 0.0);
                model.set_weight(
                    row,
                    cbc_node.active,
                    (cbc_node.children.len() - class_vars.children_intersection.len()) as f64,
                );

                for child_class_id in &cbc_node.children {
                    if !class_vars.children_intersection.contains(child_class_id) {
                        let child_active = vars[child_class_id].active;
                        model.set_weight(row, child_active, -1.0);
                    }
                }
            }
        }

        let mut count = 0;

        model.set_obj_sense(Sense::Minimize);
        for class_vars in vars.values() {
            let min_cost: Cost = class_vars
                .members
                .iter()
                .map(|n| n.cost)
                .min()
                .unwrap_or(Cost::default());

            if min_cost != 0.0 {
                //model.set_obj_coeff(class_vars.active, min_cost.into_inner());
                count += 1;
            }

            for node in &class_vars.members {
                // Add the nodes cost (if it's non-zero)
                if node.cost.into_inner() - min_cost.into_inner() != 0.0 {
                    //  model
                    //    .set_obj_coeff(node.active, node.cost.into_inner() - min_cost.into_inner());
                    count += 1;
                }
            }
        }
        println!("@objective fn {}", count);

        if false {
            let initial_result = super::bottom_up::BottomUpExtractor.extract(egraph, roots);
            return initial_result;
        }

        let mut loop_count = 0;
        loop {
            let solution = model.solve();
            log::info!(
                "CBC status {:?}, {:?}, obj = {}",
                solution.raw().status(),
                solution.raw().secondary_status(),
                solution.raw().obj_value(),
            );

            let mut result = ExtractionResult::default();

            for (class_id, var) in &vars {
                if solution.col(var.active) > 0.0 {
                    let node_id = var
                        .members
                        .iter()
                        .find(|n| solution.col(n.active) > 0.0)
                        .unwrap()
                        .node
                        .clone();
                    result.choose(class_id.clone(), node_id);
                }
            }

            let cycles = find_cycles_in_result(&result, egraph, roots);
            if cycles.is_empty() {
                return result;
            } else {
                loop_count += 1;
                println!("@Blocking {}", loop_count);
                for c in cycles {
                    block_cycle(&mut model, &egraph, &c, &vars);
                }
            }
        }
    }
}

#[derive(Clone)]
enum TraverseStatus {
    Doing,
    Done,
}

pub fn find_cycles_in_result(
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
            let mut cycle = vec![];
            if let Some(pos) = stack.iter().position(|id| id == class_id) {
                cycle.extend_from_slice(&stack[pos..]);
            }
            cycles.push(cycle);
        }
        None => {
            status.insert(class_id.clone(), TraverseStatus::Doing);
            stack.push(class_id.clone());
            let node_id = &extraction_result.choices[class_id];
            let node = &egraph[node_id];
            for child in &node.children {
                let child_cid = egraph.nid_to_cid(child);
                cycle_dfs(extraction_result, egraph, child_cid, status, cycles, stack);
            }
            let last = stack.pop();
            assert!(*class_id == last.unwrap());
            status.insert(class_id.clone(), TraverseStatus::Done);
        }
    }
}

fn block_cycle(
    model: &mut Model,
    egraph: &EGraph,
    cycle: &Vec<ClassId>,
    vars: &HashMap<ClassId, ClassVars>,
) {
    assert!(!cycle.is_empty());

    let nid_to_cid = |nid: &NodeId| egraph.nid_to_cid(nid);

    let node_to_var = |node_id: &NodeId| -> Col {
        let class_id = egraph.nid_to_cid(node_id);
        let class_members = &vars.get(class_id).unwrap().members;

        // Find the index of the node_id in the class's nodes list
        let node_index = class_members.iter().position(|nid| nid.node == *node_id);

        // Fetch the corresponding variable from the ClassVars's nodes vector
        return class_members[node_index.unwrap()].active;
    };

    let mut blocking = Vec::new();
    for i in 0..cycle.len() {
        let current_class_id = &cycle[i];
        let next_class_id = &cycle[(i + 1) % cycle.len()];

        let blocking_var = model.add_binary();
        blocking.push(blocking_var.clone());

        for node_id in &vars.get(current_class_id).unwrap().members {
            let node = &egraph[&node_id.node];
            if node
                .children
                .iter()
                .map(|n| nid_to_cid(n))
                .any(|cid| *cid == *next_class_id)
            {
                let row = model.add_row();
                model.set_row_upper(row, 0.0);
                model.set_weight(row, node_to_var(&node_id.node), 1.0);
                model.set_weight(row, blocking_var, -1.0);
            }
        }
    }
    let row = model.add_row();
    model.set_row_upper(row, blocking.len() as f64 - 1.0);
    for b in blocking {
        model.set_weight(row, b, 1.0);
    }
}

fn intersection_of_children(cbc_nodes: &[CbcNode]) -> Vec<ClassId> {
    if cbc_nodes.is_empty() {
        return Vec::new();
    }

    let mut iter = cbc_nodes.iter();

    // Start with the children of the first node.
    let mut intersection = iter.next().unwrap().children.clone();

    for node in iter {
        // Update the intersection with the children of the next node.
        intersection = intersection.intersection(&node.children).cloned().collect();
    }

    intersection.into_iter().collect()
}

fn classes_with_single_parent(vars: &HashMap<ClassId, ClassVars>) -> HashMap<ClassId, ClassId> {
    // Mapping from child class to parent classes
    let mut child_to_parents: HashMap<ClassId, HashSet<ClassId>> = HashMap::new();

    for (&ref class_id, class_vars) in vars.iter() {
        for cbc_node in &class_vars.members {
            for child_class in &cbc_node.children {
                child_to_parents
                    .entry(child_class.clone())
                    .or_insert_with(HashSet::new)
                    .insert(class_id.clone());
            }
        }
    }

    // return classes with only one parent
    child_to_parents
        .into_iter()
        .filter_map(|(child_class, parents)| {
            if parents.len() == 1 {
                Some((child_class, parents.into_iter().next().unwrap()))
            } else {
                None
            }
        })
        .collect()
}

fn reachable(
    vars: &HashMap<ClassId, ClassVars>,
    classes: &[ClassId],
    is_reachable: &mut HashSet<ClassId>,
) {
    for class in classes {
        if is_reachable.insert(class.clone()) {
            let class_vars = vars.get(&class).unwrap();
            for cbc_node in &class_vars.members {
                for child_class in &cbc_node.children {
                    reachable(vars, &[child_class.clone()], is_reachable);
                }
            }
        }
    }
}
