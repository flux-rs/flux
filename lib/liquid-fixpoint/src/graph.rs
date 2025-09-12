use std::collections::{HashMap, HashSet};

use crate::Types;

fn dfs_finish_order<'a, T: Types>(
    node: &'a T::KVar,
    graph: &'a HashMap<T::KVar, Vec<T::KVar>>,
    visited: &mut HashSet<T::KVar>,
    order: &mut Vec<T::KVar>,
) {
    if visited.contains(node) {
        return;
    }

    visited.insert(node.clone());

    if let Some(neighbors) = graph.get(node) {
        for neighbor in neighbors {
            dfs_finish_order::<T>(neighbor, graph, visited, order);
        }
    }

    order.push(node.clone());
}

fn reverse_graph<T: Types>(
    graph: &HashMap<T::KVar, Vec<T::KVar>>,
) -> HashMap<T::KVar, Vec<T::KVar>> {
    let mut reversed = HashMap::new();

    for (node, neighbors) in graph {
        for neighbor in neighbors {
            reversed
                .entry(neighbor.clone())
                .or_insert_with(Vec::new)
                .push(node.clone());
        }
    }

    for node in graph.keys() {
        reversed.entry(node.clone()).or_insert_with(Vec::new);
    }

    reversed
}

fn dfs_collect_scc<'a, T: Types>(
    node: &'a T::KVar,
    graph: &'a HashMap<T::KVar, Vec<T::KVar>>,
    visited: &mut HashSet<T::KVar>,
    scc: &mut Vec<T::KVar>,
) {
    if visited.contains(node) {
        return;
    }

    visited.insert(node.clone());
    scc.push(node.clone());

    if let Some(neighbors) = graph.get(node) {
        for neighbor in neighbors {
            dfs_collect_scc::<T>(neighbor, graph, visited, scc);
        }
    }
}

fn find_sccs<T: Types>(graph: &HashMap<T::KVar, Vec<T::KVar>>) -> Vec<Vec<T::KVar>> {
    let mut visited = HashSet::new();
    let mut order = Vec::new();

    // First pass: original graph
    for node in graph.keys() {
        if !visited.contains(node) {
            dfs_finish_order::<T>(node, graph, &mut visited, &mut order);
        }
    }

    let reversed = reverse_graph::<T>(graph);
    visited.clear();
    let mut sccs = Vec::new();

    // Second pass: reversed graph in reverse finishing order
    while let Some(node) = order.pop() {
        if !visited.contains(&node) {
            let mut scc = Vec::new();
            dfs_collect_scc::<T>(&node, &reversed, &mut visited, &mut scc);
            sccs.push(scc);
        }
    }

    sccs
}

pub fn topological_sort_sccs<T: Types>(
    graph: &HashMap<T::KVar, Vec<T::KVar>>,
) -> Vec<Vec<T::KVar>> {
    let sccs = find_sccs::<T>(graph);

    // Map each node to its SCC index
    let mut node_to_scc = HashMap::new();
    for (i, scc) in sccs.iter().enumerate() {
        for node in scc {
            node_to_scc.insert(node.clone(), i);
        }
    }

    // Build condensed graph (DAG of SCCs)
    let mut condensed_graph: HashMap<usize, HashSet<usize>> = HashMap::new();
    for (node, neighbors) in graph {
        let &from = node_to_scc.get(node).unwrap();
        for neighbor in neighbors {
            let &to = node_to_scc.get(neighbor).unwrap();
            if from != to {
                condensed_graph.entry(from).or_default().insert(to);
            }
        }
    }

    // Perform topological sort on SCC graph using DFS
    fn dfs_topo(
        node: usize,
        graph: &HashMap<usize, HashSet<usize>>,
        visited: &mut HashSet<usize>,
        result: &mut Vec<usize>,
    ) {
        if visited.contains(&node) {
            return;
        }

        visited.insert(node);

        if let Some(neighbors) = graph.get(&node) {
            for &neighbor in neighbors {
                dfs_topo(neighbor, graph, visited, result);
            }
        }

        result.push(node);
    }

    let mut visited = HashSet::new();
    let mut result = Vec::new();

    for i in 0..sccs.len() {
        if !visited.contains(&i) {
            dfs_topo(i, &condensed_graph, &mut visited, &mut result);
        }
    }

    result.reverse(); // topological order
    result.into_iter().map(|i| sccs[i].clone()).collect()
}
