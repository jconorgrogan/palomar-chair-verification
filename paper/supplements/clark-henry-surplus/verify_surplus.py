#!/usr/bin/env python3
"""Independent finite-graph audit. Python standard library only."""
import json
from collections import Counter, deque
from itertools import combinations

def pair_mask(pair):
    return sum(1 << (i - 1) for i in pair)

def axis_pairs(p):
    return set(combinations(range(1, p + 1), 2))

def local_pairs(p):
    return {pair for j in range(1, p, 2)
            for pair in combinations((j, j + 1, j + 2), 2)}

def graph(p, pairs):
    vertices = [v for v in range(1 << p) if v.bit_count() % 2 == 0]
    masks = [pair_mask(pair) for pair in sorted(pairs)]
    return {v: [v ^ mask for mask in masks] for v in vertices}

def graph_report(p, pairs):
    g = graph(p, pairs)
    visited = set()
    component_summaries = []
    for root in g:
        if root in visited:
            continue
        colors = {root: 0}
        queue = deque([root])
        bipartite = True
        while queue:
            u = queue.popleft()
            for v in g[u]:
                if v not in colors:
                    colors[v] = 1 - colors[u]
                    queue.append(v)
                elif colors[v] == colors[u]:
                    bipartite = False
        visited.update(colors)
        edges = sum(len(g[v]) for v in colors) // 2
        sides = sorted(Counter(colors.values()).values()) if bipartite else None
        complete_bipartite = bool(bipartite and len(sides) == 2
                                  and edges == sides[0] * sides[1])
        component_summaries.append({
            "vertices": len(colors),
            "edges": edges,
            "bipartite": bipartite,
            "bipartition_sizes": sides,
            "complete_bipartite": complete_bipartite,
        })
    compressed = Counter(json.dumps(item, sort_keys=True)
                         for item in component_summaries)
    return {
        "vertices": len(g),
        "degree": len(pairs),
        "edges": len(g) * len(pairs) // 2,
        "components": len(component_summaries),
        "component_types": [
            dict(json.loads(item), multiplicity=n)
            for item, n in sorted(compressed.items())
        ],
    }

report = {
    "method": "Independent enumeration of even-weight vectors; standard library only",
    "proof_status": "Finite checks supplement ordinary mathematical proofs; not Lean-verified",
    "odd_dimensions": {},
}
for p in (3, 5, 7, 9, 11):
    local = local_pairs(p)
    full = axis_pairs(p)
    surplus = full - local
    found_edges = (1 << (p - 2)) * len(full)
    expected_edges = (1 << (p - 2)) * len(local)
    assert len(local) == 3 * (p - 1) // 2
    assert 3 * found_edges == p * expected_edges
    addresses = [0]
    for j in range(1, p, 2):
        factor = [0] + [pair_mask(pair)
                        for pair in combinations((j, j + 1, j + 2), 2)]
        addresses = [a ^ b for a in addresses for b in factor]
    assert len(addresses) == len(set(addresses)) == 1 << (p - 1)
    assert set(addresses) == set(graph(p, full))
    full_report = graph_report(p, full)
    local_report = graph_report(p, local)
    assert full_report["edges"] == found_edges
    assert local_report["edges"] == expected_edges
    assert local_report["components"] == 1
    report["odd_dimensions"][str(p)] = {
        "direct_sum_addresses_are_unique": True,
        "local_pairs": [list(pair) for pair in sorted(local)],
        "surplus_pairs": [list(pair) for pair in sorted(surplus)],
        "expected_edges": expected_edges,
        "found_edges": found_edges,
        "full_graph": full_report,
        "within_copy_graph": local_report,
        "surplus": graph_report(p, surplus),
    }

adjacent = {(1, 4), (1, 5), (2, 4), (2, 5)}
report["henry_first_adjacent_pair"] = graph_report(7, adjacent)
report["adjacent_copy_checks"] = {}
for p in (5, 7, 9, 11):
    checks = []
    for j in range(1, p - 2, 2):
        pairs = {(a, b) for a in (j, j + 1) for b in (j + 3, j + 4)}
        check = graph_report(p, pairs)
        assert check["component_types"] == [{
            "bipartite": True, "bipartition_sizes": [4, 4],
            "complete_bipartite": True, "edges": 16, "vertices": 8,
            "multiplicity": 1 << (p - 4)}]
        checks.append({"first_copy_index": (j + 1) // 2, "graph": check})
    report["adjacent_copy_checks"][str(p)] = checks
assert report["odd_dimensions"]["5"]["surplus"]["component_types"] == [{
    "bipartite": True, "bipartition_sizes": [4, 4],
    "complete_bipartite": True, "edges": 16, "vertices": 8, "multiplicity": 2}]
assert report["henry_first_adjacent_pair"]["component_types"] == [{
    "bipartite": True, "bipartition_sizes": [4, 4],
    "complete_bipartite": True, "edges": 16, "vertices": 8, "multiplicity": 8}]
for p in (7, 9, 11):
    surplus = report["odd_dimensions"][str(p)]["surplus"]
    assert surplus["components"] == 1
    assert not surplus["component_types"][0]["bipartite"]

g7 = graph(7, axis_pairs(7) - local_pairs(7))
triangle = [0, pair_mask((1, 4)), pair_mask((1, 6))]
assert all(triangle[(i + 1) % 3] in g7[triangle[i]] for i in range(3))
report["henry_explicit_triangle_axes_1_to_7"] = [
    "".join(str((v >> i) & 1) for i in range(7)) for v in triangle]
report["all_assertions_passed"] = True
print(json.dumps(report, indent=2, sort_keys=True))

