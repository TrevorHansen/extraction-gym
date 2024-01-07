use super::*;

struct ClassVars {
    active: i64,
    nodes: Vec<i64>,
}

pub struct CbcExtractor;

impl Extractor for CbcExtractor {
    fn extract(&self, egraph: &EGraph, roots: &[ClassId]) -> ExtractionResult {
        let mut next_var: i64 = 1;
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

        println!("* #variable= 12 #constraint= 7");
        println!("*");
        print!("min: ");
        for class in egraph.classes().values() {
            for (node_id, &node_active) in class.nodes.iter().zip(&vars[&class.id].nodes) {
                let node = &egraph[node_id];
                //model.set_obj_coeff(node_active, node.cost.into_inner());
                print!(
                    " {} x{}",
                    (1000.0 * node.cost.into_inner()) as i64,
                    node_active
                );
            }
        }
        println!(";");

        for (id, class) in &vars {
            // class active == some node active
            // sum(for node_active in class) == class_active

            //let row = model.add_row();
            //model.set_row_equal(row, 0.0);
            //model.set_weight(row, class.active, -1.0);
            print!("-1 x{} ", class.active);
            for &node_active in &class.nodes {
                //model.set_weight(row, node_active, 1.0);
                print!("+1 x{} ", node_active);
            }
            println!(" = 0;");

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
                    println!("-1 x{} +1 x{} >= 0;", node_active, child_active);
                }
            }
        }

        for root in roots {
            println!("1 x{} = 1;", vars[root].active);
        }
        ExtractionResult::default()
    }
}

// from @khaki3
// fixes bug in egg 0.9.4's version
// https://github.com/egraphs-good/egg/issues/207#issuecomment-1264737441
fn find_cycles(egraph: &EGraph, mut f: impl FnMut(ClassId, usize)) {
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
