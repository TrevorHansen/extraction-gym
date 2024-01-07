use core::panic;

use super::*;
use coin_cbc::{Col, Model, Sense};
use indexmap::IndexSet;

struct ClassVars {
    active: Col,
    order: Col,
    nodes: Vec<Col>,
    shared_children: HashSet<ClassId>,
}

pub struct CBCUpdated;

//Classes with single nodes, the class's activate variables replaces the nodes.
const replace_singles: bool = false;
const dont_find_cycles: bool = false;
const add_redundant_sos1: bool = false;

impl Extractor for CBCUpdated {
    fn extract(&self, egraph: &EGraph, roots: &[ClassId]) -> ExtractionResult {
        let max_order = egraph.nodes.len() as f64 * 10.0;

        let mut model = Model::default();

        let mut is_reachable: IndexSet<ClassId> = IndexSet::default();
        reachable(&egraph, &roots, &mut is_reachable);
        println!(
            "@Reachable classes {} of total {}",
            is_reachable.len(),
            egraph.classes().len()
        );

        println!("@Self linked nodes: {}", count_self_link(egraph));
        println!(
            "@Links to the root node: {} ",
            countRootLinks(egraph, roots)
        );

        let initial_result = super::bottom_up::BottomUpExtractor.extract(egraph, roots);
        let lowest_cost = initial_result.dag_cost(egraph, roots);
        println!(
            "@Nodes exceeding {} the lowest cost: {}",
            costs_exceeding(egraph, lowest_cost),
            lowest_cost
        );

        println!("@Nodes have a cheaper option: {}", too_costly(egraph));
        println!(
            "@Nodes with a single parent: {}",
            classes_with_single_parent(egraph)
        );

        println!(
            "@Saved by doing on class instead: {}",
            children_intersection_per_class(egraph)
        );

        println!("@Subset and cheaper: {}", count_subset_and_cheaper(egraph));

        let min_cost_per_class = minCosts(egraph);

        let vars: IndexMap<ClassId, ClassVars> = egraph
            .classes()
            .values()
            .map(|class| {
                let active_var = model.add_binary();
                let mut node_var: Vec<_> = class.nodes.iter().map(|_| model.add_binary()).collect();

                if replace_singles && node_var.len() == 1 {
                    node_var = vec![active_var];
                }

                let cvars = ClassVars {
                    active: active_var,
                    order: model.add_col(),
                    nodes: node_var,
                    shared_children: get_children_intersection_per_class(egraph, class.id.clone()),
                };
                model.set_col_upper(cvars.order, max_order);
                (class.id.clone(), cvars)
            })
            .collect();

        for (id, class) in &vars {
            // class active == some node active
            // sum(for node_active in class) == class_active
            if !replace_singles || class.nodes.len() != 1 {
                let row = model.add_row();
                model.set_row_equal(row, 0.0);
                model.set_weight(row, class.active, -1.0);
                for &node_active in &class.nodes {
                    model.set_weight(row, node_active, 1.0);
                }
            }

            for (node_id, &node_active) in egraph[id].nodes.iter().zip(&class.nodes) {
                let node = &egraph[node_id];
                for c in &class.shared_children {
                    let row = model.add_row();
                    model.set_row_upper(row, 0.0);
                    model.set_weight(row, class.active, 1.0);
                    model.set_weight(row, vars.get(c).unwrap().active, -1.0);
                }

                for child in &node.children {
                    let eclass_id = &egraph[child].eclass;
                    if class.shared_children.contains(eclass_id) {
                        continue;
                    }
                    let child_active = vars[eclass_id].active;
                    // node active implies child active, encoded as:
                    //   node_active <= child_active
                    //   node_active - child_active <= 0
                    let row = model.add_row();
                    model.set_row_upper(row, 0.0);
                    model.set_weight(row, node_active, 1.0);
                    model.set_weight(row, child_active, -1.0);
                }
            }
        }

        if add_redundant_sos1 {
            for (_, class) in &vars {
                let pairs: Vec<(Col, f64)> = class
                    .nodes
                    .iter()
                    .enumerate()
                    .map(|(i, &item)| (item, i as f64 + 1.0))
                    .collect();

                model.add_sos1(pairs);
            }
        }

        model.set_obj_sense(Sense::Minimize);
        for class in egraph.classes().values() {
            // Add the base class cost ( if it's non-zero)
            let min: Cost = *min_cost_per_class.get(&class.id).unwrap();
            if min != 0.0 {
                //model.set_obj_coeff(vars.get(&class.id).unwrap().active, min.into_inner());
            }

            // Add the nodes cost (if it's non-zero)
            for (node_id, &node_active) in class.nodes.iter().zip(&vars[&class.id].nodes) {
                let node = &egraph[node_id];
                if node.cost.into_inner() - min.into_inner() != 0.0 {
                    // model.set_obj_coeff(node_active, node.cost.into_inner() - min.into_inner());
                }
            }
        }

        for root in roots {
            model.set_col_lower(vars[root].active, 1.0);
        }

        if false {
            // set initial solution based on bottom up extractor
            for (class, class_vars) in egraph.classes().values().zip(vars.values()) {
                if let Some(node_id) = initial_result.choices.get(&class.id) {
                    model.set_col_initial_solution(class_vars.active, 1.0);
                    for col in &class_vars.nodes {
                        model.set_col_initial_solution(*col, 0.0);
                    }
                    let node_idx = class.nodes.iter().position(|n| n == node_id).unwrap();
                    model.set_col_initial_solution(class_vars.nodes[node_idx], 1.0);
                } else {
                    model.set_col_initial_solution(class_vars.active, 0.0);
                }
            }
        }

        let mut banned_cycles: IndexSet<(ClassId, usize)> = Default::default();
        // find_cycles(egraph, |id, i| {
        //     banned_cycles.insert((id, i));
        // });

        //for iteration in 0..
        {
            let iteration = 0;
            if iteration == 0 {
                find_cycles(egraph, |id, i| {
                    banned_cycles.insert((id, i));
                });
            } else if iteration >= 2 {
                panic!("Too many iterations");
            }

            for (id, class) in &vars {
                for (i, (_node, &node_active)) in
                    egraph[id].nodes.iter().zip(&class.nodes).enumerate()
                {
                    if banned_cycles.contains(&(id.clone(), i)) {
                        model.set_col_upper(node_active, 0.0);
                        model.set_col_lower(node_active, 0.0);
                    }
                }
            }

            let solution = model.solve();
            log::info!(
                "CBC status {:?}, {:?}, obj = {}",
                solution.raw().status(),
                solution.raw().secondary_status(),
                solution.raw().obj_value(),
            );

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

            let cycles = result.find_cycles(egraph, roots);
            if cycles.is_empty() {
                return result;
            } else {
                return initial_result;
                log::info!("Found {} cycles", cycles.len());
                // for id in cycles {
                //     let class = &vars[&id];
                //     let node_idx = class
                //         .nodes
                //         .iter()
                //         .position(|&n| solution.col(n) > 0.0)
                //         .unwrap();
                //     banned_cycles.insert((id, node_idx));
                // }
            }
        }
        unreachable!()
    }
}

// from @khaki3
// fixes bug in egg 0.9.4's version
// https://github.com/egraphs-good/egg/issues/207#issuecomment-1264737441
fn find_cycles(egraph: &EGraph, mut f: impl FnMut(ClassId, usize)) {
    if dont_find_cycles {
        return;
    }

    let mut pending: IndexMap<ClassId, Vec<(ClassId, usize)>> = IndexMap::default();
    let mut order: IndexMap<ClassId, usize> = IndexMap::default();
    let mut memo: IndexMap<(ClassId, usize), bool> = IndexMap::default();
    let mut stack: Vec<(ClassId, usize)> = vec![];

    let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);

    for class in egraph.classes().values() {
        let id = &class.id;
        for (i, node_id) in egraph[id].nodes.iter().enumerate() {
            let node = &egraph[node_id];
            for child in &node.children {
                let child = n2c(child).clone();
                pending
                    .entry(child)
                    .or_insert_with(Vec::new)
                    .push((id.clone(), i));
            }

            if node.is_leaf() {
                stack.push((id.clone(), i));
            }
        }
    }

    let mut count = 0;

    while let Some((id, i)) = stack.pop() {
        if memo.get(&(id.clone(), i)).is_some() {
            continue;
        }

        let node_id = &egraph[&id].nodes[i];
        let node = &egraph[node_id];
        let mut update = false;

        if node.is_leaf() {
            update = true;
        } else if node.children.iter().all(|x| order.get(n2c(x)).is_some()) {
            if let Some(ord) = order.get(&id) {
                update = node.children.iter().all(|x| &order[n2c(x)] < ord);
                if !update {
                    memo.insert((id, i), false);
                    continue;
                }
            } else {
                update = true;
            }
        }

        if update {
            if order.get(&id).is_none() {
                order.insert(id.clone(), count);
                count += 1;
            }
            memo.insert((id.clone(), i), true);
            if let Some(mut v) = pending.remove(&id) {
                stack.append(&mut v);
                stack.sort();
                stack.dedup();
            };
        }
    }

    // Exclude if it's not memoed with true. Note the ID needs to match too.
    for class in egraph.classes().values() {
        let id = &class.id;
        for (i, _node) in class.nodes.iter().enumerate() {
            if let Some(true) = memo.get(&(id.clone(), i)) {
                continue;
            }
            f(id.clone(), i);
        }
    }
}

pub fn costs_exceeding(egraph: &EGraph, c: Cost) -> usize {
    let mut count = 0;

    for class in egraph.classes().values() {
        for n in &egraph[&class.id].nodes {
            if egraph[n].cost > c {
                count += 1
            }
        }
    }
    return count;
}

pub fn minCosts(egraph: &EGraph) -> IndexMap<ClassId, Cost> {
    let mut result: IndexMap<ClassId, Cost> = IndexMap::default();

    for class in egraph.classes().values() {
        let min: Cost = egraph[&class.id]
            .nodes
            .iter()
            .map(|n| egraph[n].cost)
            .min()
            .unwrap();

        result.insert(class.id.clone(), min);
    }
    return result;
}

// Nodes that have the same cost.
pub fn countSameCost(egraph: &EGraph) -> usize {
    let mut count = 0;

    for class in egraph.classes().values() {
        let costs: Vec<Cost> = egraph[&class.id]
            .nodes
            .iter()
            .map(|n| egraph[n].cost)
            .collect();
        let distinct = costs
            .iter()
            .collect::<IndexSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if distinct.len() == 1 && costs.len() > 1 {
            count += costs.len();
            println!("distinct {} {}", distinct[0], costs.len());
        }
    }
    return count;
}

// Number of nodes that exceed the cost of a zero-child node in the same class.
pub fn too_costly(egraph: &EGraph) -> usize {
    let mut count = 0;

    for class in egraph.classes().values() {
        let nodes = &egraph[&class.id].nodes;
        let min_cost = nodes
            .iter()
            .filter(|&n| egraph[n].children.is_empty())
            .map(|n| egraph[n].cost)
            .min();
        if min_cost.is_some() {
            count += nodes
                .iter()
                .filter(|n| egraph[*n].cost <= min_cost.unwrap())
                .collect::<Vec<_>>()
                .len()
                - 1;
        }
    }
    return count;
}

// Number of nodes that point to themselves.
pub fn count_self_link(egraph: &EGraph) -> i32 {
    let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);
    let mut count = 0;

    for class in egraph.classes().values() {
        for n in &egraph[&class.id].nodes {
            for c in &egraph[n].children {
                if class.id == *n2c(c) {
                    count += 1;
                }
            }
        }
    }
    return count;
}

// If there's a single root, the number of nodes that point to the root.
pub fn countRootLinks(egraph: &EGraph, root: &[ClassId]) -> i32 {
    let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);

    if root.len() == 0 {
        return 0;
    }
    let mut count = 0;
    let root_class = root[0].clone();

    for class in egraph.classes().values() {
        for n in &egraph[&class.id].nodes {
            for c in &egraph[n].children {
                if *n2c(c) == root_class {
                    count += 1;
                }
            }
        }
    }
    return count;
}

// Which classes are reachable from here.
pub fn reachable(egraph: &EGraph, classes: &[ClassId], is_reachable: &mut IndexSet<ClassId>) {
    let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);

    for class in classes {
        if !is_reachable.insert(class.clone()) {
            continue;
        }
        for n in &egraph[class].nodes {
            for c in &egraph[n].children {
                let childrens_classes: Vec<ClassId> = vec![n2c(c).clone()];
                reachable(egraph, &childrens_classes, is_reachable);
            }
        }
    }
}

pub fn classes_with_single_parent(egraph: &EGraph) -> usize {
    // Mapping from child class to parent classes
    let mut child_to_parents: HashMap<ClassId, HashSet<ClassId>> = HashMap::new();

    for class in egraph.classes().values() {
        for node in &egraph[&class.id].nodes {
            for child in &egraph[node].children {
                let child_class = egraph.nid_to_cid(child);
                child_to_parents
                    .entry(child_class.clone())
                    .or_insert_with(HashSet::new)
                    .insert(class.id.clone());
            }
        }
    }

    // Count classes with only one parent
    child_to_parents
        .iter()
        .filter(|(_, parents)| parents.len() == 1)
        .map(|(child_class, _)| egraph[child_class].nodes.len())
        .sum()
}

use std::collections::HashSet;

pub fn children_intersection_per_class(egraph: &EGraph) -> usize {
    let mut count = 0;

    for class in egraph.classes().values() {
        let mut intersection: Option<HashSet<NodeId>> = None;

        for node in &egraph[&class.id].nodes {
            let current_children: HashSet<NodeId> = egraph[node].children.iter().cloned().collect();

            intersection = match intersection {
                Some(prev_children) => Some(
                    prev_children
                        .intersection(&current_children)
                        .cloned()
                        .collect(),
                ),
                None => Some(current_children),
            };
        }

        if let Some(intersected_children) = intersection {
            count += intersected_children.len() * (egraph[&class.id].nodes.len() - 1);
        }
    }

    return count;
}

pub fn get_children_intersection_per_class(egraph: &EGraph, class_id: ClassId) -> HashSet<ClassId> {
    let n2c = |nid: &NodeId| egraph.nid_to_cid(nid);

    let mut intersection: Option<HashSet<ClassId>> = None;

    for node in &egraph[&class_id].nodes {
        let current_children: HashSet<ClassId> = egraph[node]
            .children
            .iter()
            .map(|n| n2c(n).clone())
            .collect();

        intersection = match intersection {
            Some(existing_intersection) => Some(
                existing_intersection
                    .intersection(&current_children)
                    .cloned()
                    .collect(),
            ),
            None => Some(current_children),
        };
    }

    intersection.unwrap_or_default()
}

pub fn count_subset_and_cheaper(egraph: &EGraph) -> usize {
    let mut count = 0;

    for class in egraph.classes().values() {
        let mut nodes_data: Vec<(_, _, _)> = class
            .nodes
            .iter()
            .map(|node| {
                (
                    node,
                    egraph[node].cost,
                    egraph[node]
                        .children
                        .iter()
                        .cloned()
                        .collect::<HashSet<_>>(),
                )
            })
            .collect();

        // Sort by number of children
        nodes_data.sort_by_key(|(_, _, children_set)| children_set.len());

        for i in 0..nodes_data.len() {
            let (node_a, cost_a, children_a) = &nodes_data[i];

            for j in (i + 1)..nodes_data.len() {
                let (node_b, cost_b, children_b) = &nodes_data[j];

                if cost_a < cost_b && children_a.is_subset(children_b) {
                    count += 1;
                }
            }
        }
    }

    count
}
