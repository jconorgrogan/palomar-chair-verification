# Supplement: parity contact graphs and the CLARK–HENRY surplus

## Status and scope

The propositions below are ordinary mathematical statements with explicit proofs. They have **not been formalized or verified in Lean**. The accompanying [independent Python checker](verify_surplus.py) performs finite enumerations; its [captured results](surplus_verification_results.json) corroborate the stated examples, rather than replacing the proofs for arbitrary dimension.

The supplied research memo motivated these questions and was treated as a collection of claims to audit. Its unavailable session scripts and reported diffusion values are not used as evidence here. No novelty or prime-specific conclusion is asserted. The names Chair44, CLARK, and HENRY refer in this section to the parity constructions at dimensions \(3\), \(5\), and \(7\), respectively.

## 1. The finite graphs

Let \(p=2m+1\geq3\), and define the even-weight vector space
\[
E_p=\left\{b\in\mathbb F_2^p:\sum_{i=1}^{p}b_i=0\right\}.
\]
All vector sums in this section are over \(\mathbb F_2\). Write \(ij\) for the generator \(e_i+e_j\), where \(i<j\).

The **full pair graph** \(G_p\) has vertex set \(E_p\), with an edge between \(b\) and \(b+ij\) for every coordinate pair \(i<j\). For
\[
T_j=\{2j-1,2j,2j+1\},\qquad 1\leq j\leq m,
\]
let \(L_p\) consist of the coordinate pairs contained in one of the triples \(T_j\). The **within-copy graph** \(Q_p\) retains only the generators in \(L_p\). The **surplus graph** \(S_p\) retains the remaining generators. Thus \(G_p\) is the edge-disjoint union of \(Q_p\) and \(S_p\), on the same vertex set.

A component or bipartition of \(S_p\), or of a restricted surplus subgraph, need not be a component or bipartition of \(G_p\).

### Proposition 1. Direct-sum decomposition and counts

Let \(V_j\subseteq E_p\) be the even-parity subspace supported on \(T_j\). Then
\[
E_p=V_1\oplus\cdots\oplus V_m,\qquad
Q_p\cong \underbrace{K_4\,\square\cdots\square\,K_4}_{m\text{ factors}}.
\]
Moreover,
\[
|E(G_p)|=2^{p-2}\binom p2,\qquad
|E(Q_p)|=2^{p-2}\frac{3(p-1)}2,
\]
and hence
\[
\frac{|E(G_p)|}{|E(Q_p)|}=\frac p3,\qquad
\frac{|E(S_p)|}{|E(Q_p)|}=\frac{p-3}{3}.
\]

**Proof.** In each \(V_j\), choose the two basis vectors
\(e_{2j-1}+e_{2j}\) and \(e_{2j}+e_{2j+1}\). Together these are precisely the \(p-1\) consecutive-edge vectors of the path on coordinate positions \(1,\ldots,p\). They are linearly independent: successively inspecting coordinates \(1,2,\ldots,p-1\) forces every coefficient in a zero linear combination to vanish. They therefore form a basis of the \((p-1)\)-dimensional space \(E_p\), proving the direct sum.

Each \(V_j\) has four states, and its three nonzero vectors join every pair of distinct states. Allowing a change in exactly one factor gives the Cartesian product of \(K_4\) graphs.

The full graph has \(2^{p-1}\) vertices and degree \(\binom p2\). Distinct triples share at most one coordinate, so their internal coordinate pairs are distinct; consequently \(Q_p\) has degree \(3m\). Dividing vertex-count times degree by two gives the formulas. \(\square\)

For the first three cases:

| Construction | \(p\) | Within-copy edges | Full pair edges | Surplus edges |
|---|---:|---:|---:|---:|
| Chair44 | 3 | 6 | 6 | 0 |
| CLARK | 5 | 48 | 80 | 32 |
| HENRY | 7 | 288 | 672 | 384 |

These identities hold for **every odd integer \(p\geq3\)**, including composite values. The equation \(p/3=2\) formally gives \(p=6\), outside the domain of this triangle-chain decomposition. This observation does not establish an even-dimensional comparison or a claim about prime tiles.

## 2. CLARK: two complete bipartite blocks

### Proposition 2. The five-dimensional surplus

The graph \(S_5\) is the disjoint union of two copies of \(K_{4,4}\). Its two components are distinguished by the value of coordinate \(b_3\).

**Proof.** Write uniquely \(b=A+B\), with \(A\in V_1\) supported on \(123\) and \(B\in V_2\) supported on \(345\). Then
\[
A_3=b_1+b_2,\qquad B_3=b_4+b_5,\qquad b_3=A_3+B_3.
\]
The four surplus generators are
\[
14,\quad15,\quad24,\quad25.
\]
Each changes one coordinate in \(\{1,2\}\) and one in \(\{4,5\}\), so it flips both \(A_3\) and \(B_3\), while preserving \(b_3\).

Fix \(b_3=t\). The eight vertices divide into the classes
\[
(A_3,B_3)=(0,t)\quad\text{and}\quad(1,1+t).
\]
Each class has four vertices: a prescribed parity on either private two-coordinate set permits two choices. Between any vertex in one class and any vertex in the other, exactly one coordinate in \(\{1,2\}\) differs, and exactly one in \(\{4,5\}\) differs. Their difference is therefore one of the four surplus generators. All sixteen cross-class edges are present, and there are no within-class edges. Each value of \(t\) gives a \(K_{4,4}\). \(\square\)

The “agreement/disagreement bit” \(A_3+B_3\) is exactly the existing global coordinate \(b_3\). The surplus graph preserves this bit and supplies complete cross-class adjacency inside each of its two level sets. It does not, by this argument alone, supply an additional bit absent from the labeled component states. Nor does the abstract unlabeled graph canonically identify which component has label \(b_3=0\).

## 3. HENRY and the higher-dimensional surplus

### Proposition 3. Connectedness and nonbipartiteness

For every odd \(p\geq7\), the graph \(S_p\) is connected and nonbipartite. In particular, \(S_7\) has 64 vertices, degree 12, and 384 edges.

**Proof.** Form an auxiliary graph on the \(p\) coordinate positions, with an edge \(ij\) for every surplus generator. If this auxiliary graph is connected, its edge vectors span \(E_p\): summing along a path gives the vector associated with its two endpoints. Therefore the Cayley graph \(S_p\) is connected.

At \(p=7\), the surplus pairs
\[
14,\ 15,\ 16,\ 17,\ 24,\ 36
\]
form a spanning tree on the seven coordinate positions. For every additional coordinate \(i\geq8\), the pair \(1i\) is also a surplus pair, extending connectivity to every \(p\geq7\) under consideration.

The surplus generators \(14,46,16\) satisfy \(14+46+16=0\). They yield the triangle
\[
0,\quad e_1+e_4,\quad e_1+e_6,\quad0
\]
in \(S_p\), proving nonbipartiteness. For \(p=7\), the degree is \(\binom72-9=12\), giving \(64\cdot12/2=384\) edges. \(\square\)

For HENRY, the complete surplus generator set is
\[
14,15,16,17,\ 24,25,26,27,\ 36,37,\ 46,47.
\]
Coordinate 3 changes along generators \(36,37\); coordinate 5 changes along \(15,25\). Thus neither shared coordinate is invariant on the entire surplus graph.

### Proposition 4. Adjacent-copy blocks survive inside HENRY

On \(E_7\), the subgraph generated only by \(14,15,24,25\) is a disjoint union of **eight** copies of \(K_{4,4}\), with 128 edges in total. Every edge preserves coordinate 3.

**Proof.** These generators preserve \(b_3,b_6,b_7\). Fix any of the eight values of this triple. Overall even parity leaves eight assignments to \(b_1,b_2,b_4,b_5\). Partition them by \(b_1+b_2\). Each class has four vertices, and any pair in opposite classes differs in precisely one coordinate from \(\{1,2\}\) and one from \(\{4,5\}\). Thus the induced restricted graph on these eight vertices is \(K_{4,4}\), by the same argument as Proposition 2. \(\square\)

Equivalently, for each of the third copy's four states, the first two copies retain two CLARK-style blocks. Consequently the proposed HENRY adjacent-copy completeness and shared-axis invariance test is already a consequence of the definitions; the entire 64-vertex restricted graph has eight blocks, rather than two.

The same argument applies to any selected adjacent pair of copies at odd \(p\geq5\). Fix the coordinates outside their five-coordinate union and their shared coordinate. The restricted surplus graph is a disjoint union of \(2^{p-4}\) copies of \(K_{4,4}\).

## 4. Geometric contact dimensions

To relate the graph to the stated self-similar construction, define \(K_q\subseteq[0,1]^q\) by
\[
K_q=\bigcup_{b\in E_q}\frac{K_q+b}{2}.
\]
There are \(2^{q-1}\) similarities, each with ratio \(1/2\). Their images of the open unit cube are disjoint and lie within that cube. The open-set condition therefore gives
\[
\dim_{\mathrm H}K_q=q-1.
\]

For two first-level pieces whose addresses differ in \(d\) coordinates, intersection forces those coordinates to the common half-cube boundary. On the remaining \(p-d\) coordinates, the finer binary digits satisfy a fixed parity condition. An odd-parity version is a coordinate reflection of the even-parity version. Thus, for the odd-dimensional cases considered here, the contact is a half-scale copy, possibly reflected, of \(K_{p-d}\), with
\[
\dim_{\mathrm H}(\text{contact})=p-d-1.
\]

In particular, the distance-2 contacts counted by \(G_p\) have Hausdorff dimension \(p-3\):

| \(p\) | Contact for distance 2 | Hausdorff dimension |
|---:|---|---:|
| 3 | \(K_1\), a point | 0 |
| 5 | \(K_3\), a Sierpiński tetrahedron | 2 |
| 7 | \(K_5\) | 4 |

Accordingly, HENRY's 672 distance-2 contacts are four-dimensional in the Hausdorff sense. HENRY also has two-dimensional contacts at distance 4 and point contacts at distance 6, but these are different edge classes. The statement that all contacts “from CLARK up” are two-dimensional is incorrect.

## 5. Interpretation and open questions

The exact direct sum is a statement about binary addresses, and \(Q_p\) is a Cartesian **graph** product. Applying the address decomposition digit by digit does not establish a Euclidean product of the corresponding fractals, a product of physical tilings, or a factorization of fine-scale spatial cell graphs. Bitwise XOR does not preserve ordinary addition, integer carries, distances, or all geometric adjacencies.

The following questions remain separate from the finite-graph propositions.

1. **Resistance clock.** For the memo's proposed fine-scale cell graph and terminal choice, the resistance increments and their ratios require an independent, reproducible numerical calculation and convergence analysis. Adding edges decreases fixed-terminal effective resistance by Rayleigh monotonicity, but this does not by itself establish monotonicity of a ratio of resistance differences across levels. This supplement makes no new quantitative claim about the clock, its limiting value, or the proposed level-6 interval \([5.35,5.55]\).

2. **Local readability in a physical tiling.** The proposed radius-4 success criterion and radius-8 failure criterion require a specified tiling encoding, patch metric, scale convention, and rule associating patches with parity addresses. The identity \(A_3+B_3=b_3\) does not prove that this label can be recovered from an unlabeled bounded-radius geometric patch.

3. **Knot and tile interpretation.** A claim relating these graphs to prime knots or prime tiles requires a defined correspondence and an explicit notion of “smallest” admissible knot. The graph results above neither establish nor disprove such a correspondence. Their validity at composite odd dimensions prevents a prime-specific conclusion from being inferred from the count law alone.

## 6. Reproducible finite checks

The accompanying [checker](verify_surplus.py) uses only the Python standard library and requires Python 3.10 or later. From the directory containing the three files, run:

~~~sh
python verify_surplus.py > surplus_verification_results.json
~~~

It independently constructs the even-vector graphs for \(p=3,5,7,9,11\), checks uniqueness of the direct-sum addresses, counts edges, determines components and bipartitions, verifies every adjacent-copy restricted subgraph in those dimensions, and exhibits HENRY's triangle. It does not execute code supplied by the research memo.

The [captured JSON output](surplus_verification_results.json) records all assertions as passed. Selected results are:

| \(p\) | Within-copy edges | Full pair edges | Surplus edges | Surplus components |
|---:|---:|---:|---:|---|
| 3 | 6 | 6 | 0 | Four isolated vertices |
| 5 | 48 | 80 | 32 | Two \(K_{4,4}\) |
| 7 | 288 | 672 | 384 | One, nonbipartite |
| 9 | 1,536 | 4,608 | 3,072 | One, nonbipartite |
| 11 | 7,680 | 28,160 | 20,480 | One, nonbipartite |

The checker supplies finite corroboration. The proofs above supply the statements for arbitrary odd dimension.

