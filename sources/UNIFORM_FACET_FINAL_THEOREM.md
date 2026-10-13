# Uniform exact facet closure for primes p = 3 modulo 4

Date: 2026-10-05. Status: ordinary mathematical theorem, with an independent AI mathematical audit of the underlying proof draft. This version makes two audited proof steps explicit. It is not a formal-kernel/NF result, a peer-reviewed publication, or a novelty claim.

The reviewed [original draft](DRAFT.md) is preserved byte-for-byte at SHA-256 `e7a046c447322dec7b78b62da32f8ca8736bc99a0546215eb63a33462a6c42fe`. The [independent audit](../audit_uniform_facet_closure_20261005/INDEPENDENT_AUDIT.md) checks the uniform proof and records separate exact finite sanity checks.

## Theorem

For every prime p>=3 with p=3 mod4, use the completed substitution rule mu=1, g=-1, identity center frame, and identity empty-role frame described below. Let E be its exact least sibling/cross-child contact language. Let F(E) be the proper registered, interior-disjoint full-profile mating relation of the **full free signed-permutation tangent-orbit facet compiler**, with no quotient of sites or tangent frames. Let CL(E) be the exact child-legal parent contact language, with offsets tested rather than discarded. Then, as sets of complete frame-and-translation poses,

    F(E)=CL(E),
    |F(E)|=2(2^p-1)+3p^2+p.

For the specifically defined rational keyed construction T(E) in the dimension-free registration theorem, there is at least one tiling by congruent copies, and every such tiling has a finite Euclidean symmetry group. Thus these constructions give an infinite family of nonempty strongly aperiodic rational polyhedral balls, in the prime dimensions p=3 mod4. Here “strongly aperiodic” means that every admitted tiling has finite full Euclidean symmetry group.

The physical conclusion uses the stated ordinary hierarchy, global CL-to-E, nonemptiness, and registration results. It concerns this explicit keyed construction, not an unspecified earlier physical solid.

## Setting

Let p>=3 be prime with p=3 mod4. Use the completed formula rule mu=1,g=-1, the [exact E catalog](../uniform_prime_certificate_20261005/HOLE_GRAPH_AND_SYMBOLIC_E.md), and the [full free signed-permutation orbit facet compiler](../dimension_free_facet_registration_20261005/REGISTRATION_THEOREM.md). Write I=F_p. For a proper support A, epsilon_A=(-1)^|A| and z_A=mean(A) when nonempty, z_empty=0. Put h_A=D_A P_fA, fA(i)=epsilon_A(i-z_A), with row convention (P_f x)_i=x_f(i). Here D_A flips precisely the coordinates in A, and 1 denotes the all-one vector. The centre and empty role have identity frame; there is no full outer role A=I. Vectors of sets below are their indicator vectors.

The carrier P is the union of the unit cubes A+[0,1]^p over binary vectors A other than the all-one vector. The outer children have poses (h_A,4A), while the central child has pose (identity,1); refinement of (H,t) uses (Hh_r,2t+Hu_r). A signed frame G with negative mask D takes occupied cell b to the cell with lower corner t+Gb-1_D. Its bounding-box lower corner is t-2*1_D. All vectors of subsets mean indicator vectors unless a set image is explicitly intended.

For definiteness, E consists of the incoming hole poses

    T_A=(h_A,4A-1), A proper,

and their inverses, together with these wall families and the indicated inverses:

- P(j,c): index map -i+c, negative mask {j}, translation 4e_j; allowed pairs j=0 with any c, or j!=0 with c!=0
- M(j): index map -i, negative mask {j}, translation 0; every j
- B(c): index map i+c, negative mask I\{0}, translation 2*1; every c
- B(c)^(-1): index map i-c, negative mask I\{c}, translation 2*1-4e_c

The prior ordinary E theorem identifies this list with the least substitution contact language; that theorem is an input here.

To fix the compiler exactly, use increasing ambient tangent-axis order at every facet f. Let B_m be the full signed-permutation group in m=p-1 tangent dimensions, q0=(1,2,...,m)/(4p), Q=B_m q0, and retain every site (f,q), q in Q. Each q has one unique A_q in B_m with q=A_q q0. For each generating contact pair all sites across every shared unit facet. Its undirected edge imposes a_u=-a_v. Put chi_u=det([I_f A_q,n_f]); number the resulting graph components by the lexicographic least-site order specified in the registration theorem, and set a_u=j(u)chi_u. Every coefficient is nonzero.

F(E) comprises all proper signed-permutation, integer-translation, interior-disjoint carrier face contacts for which **every paired site on every shared unit facet** has opposite coefficients. CL(E) comprises the aligned poses of all child-legal parent face contacts; the prior [coarse-legality theorem](../uniform_prime_certificate_20261005/UNIFORM_COARSE_LEGALITY.md) proves that all child-legal offsets are aligned and supplies its exact catalog. No facet-closure enumeration is assumed in the proof below.

## 1. Hole contacts turn the base facet graph into p stars

Every exposed unit facet is either an inner facet V_k (center b_k=(3/2)1-(1/2)e_k, outward normal e_k), or an outer facet O(A,j), A a proper binary cell and j any axis. The outer facet has outward normal (2A_j-1)e_j. There are p inner facets and p(2^p-1) outer facets.

The incoming contact T_A=(h_A,4A-1) takes native inner facet V_k to root outer facet O(A,j) exactly when k=fA(j). Directly,

    b_O(A,j)=h_A b_k + (4A-1).

Its normals are opposite. These are exactly the hole-contact edges (and their reverses). Each outer facet is a unique leaf, and each V_k has one leaf per proper role A, because fA is a permutation. Thus hole edges alone form p stars, each with 2^p base facets. Use h_A as the ambient frame gauge of that leaf relative to V_k.

## 2. Every wall edge has the same gauged transport

Define L_k=D_{ {k} } P_-, where P_-(i)=-i. L_k takes e_-k to -e_k and is proper because multiplication by -1 is odd when p=3 mod4. Also L_-k L_k=identity, and L_0 has order two.

For a wall contact G mapping the companion to the root, let its paired outer facets be O(A,j) and O(B,j'). The gauged ambient transport is h_A^-1 G h_B. We claim it is always L_k, with k=fA(j) and fB(j')=-k.

For P(j,c), G=D_{ {j} }P_(-i+c), root A_j=1, and B=-A+c. Cardinalities agree, z_B=-z_A+c, and a direct signed-frame multiplication gives slope -1, intercept 0, and negative mask {k} for h_A^-1 G h_B. The target inner label is -k. This uses only P contacts actually listed in E, not unlisted intercepts.

For M(j), the same calculation has c=0, A_j=0 and B=-A. It includes A=empty by the stipulated endpoint. In particular the facet A=empty gives k=j for every j, so these M edges supply every bridge V_-k to V_k.

For B(c), the wall axis is 0, A_0=1, and B=(I\A)+c. Here epsilon_B=-epsilon_A and z_B=z_A+c, because the field sum is zero. Multiplication again gives exactly L_k. Inverse-B edges give the inverse transport L_-k.

These exhaust E's wall types. Consequently the base components are:
- one component at inner label 0, with 2^p facets and tangent holonomy of order 2;
- (p-1)/2 components joining labels k and -k, each with 2^(p+1) facets and trivial holonomy.

The zero holonomy generator restricts to i->-i on the nonzero tangent labels and is nonidentity. Every other cycle cancels successive L_k,L_-k. Thus this is a proof of the group structure, not an inference from its orders.

For the full free tangent group B_(p-1), the full-site component count is p|B_(p-1)|/2; every full-site component has 2^(p+1) sites.

## 3. Proper full-profile mates are characterized by odd paths

Along every generating contact edge the coefficient orientation character chi changes sign. Thus opposite-coefficient matching requires an odd graph path. The free key orbit makes equality of transported sites equality of the entire tangent signed-permutation matrix. Adding the required reversed normal identifies the entire proper ambient matrix.

After the star gauges above, the only odd inner-to-inner transport is L_k from V_-k to V_k (including k=0). The even same-label transport is identity. Therefore:

- A mate pairing an inner facet and an outer facet yields exactly T_A or its inverse, according to which facet belongs to the root.
- Inner-to-inner mating would have G=L_k and t=b_k-L_k b_-k=2e_k. Its lower box corner is zero. The two chairs occupy the same side-two box and have at least 2^p-2 occupied cells in common, so the pose is rejected.
- For an outer-to-outer mate, necessarily

      G=h_A L_k h_B^-1,  fB(j')=-k,
      t=(4A-1)-G(4B-1)+2h_A e_k.

The proper-frame hypothesis and opposite coefficient signs exclude the even-path alternatives. The same odd path transports every free-orbit site, so these conditions characterize full profiles, not merely one sampled feature.

## 4. Every non-hole mate is a single-axis wall

Let D be the negative mask of G, and k=fA(j). Then h_A e_k=(1-2A_j)e_j. From h_B 1=1-2B and G h_B=h_A L_k,

    G B = A-D+h_A e_k.

Substitution into the formula for t gives

    t=2D-2h_A e_k,
    lower(GP+t)=t-2D=2(2A_j-1)e_j.

Thus no other integer displacement survives full-profile matching. The unsigned part of G is affine, with

    a=-epsilon_A epsilon_B in {+1,-1},
    c=z_B-a z_A.

Fix the wall axis j and side tau=+/-1. For any shared unit facet, let A be the root cell, so A_j=(1+tau)/2. Put C=f_G^-1(B), where this denotes the inverse image of the subset B under the index map, hence B=a C+c. Comparing the sign masks gives

    C=A symmetric-difference K,  K=D symmetric-difference {j}.

The exact availability statement is important: **the shared unit facets are precisely all proper A with this prescribed membership of j for which C=A△K is also proper**. To verify both directions directly, the outer facet has center and normal

    b_O(A,j)=A+(1/2)1+(A_j-1/2)e_j,
    n_O(A,j)=(2A_j-1)e_j.

For a wall with t=2*1_D+2tau e_j, equality of the transverse center coordinates and opposition of normals force C=A△D△{j}. Conversely that identity, the prescribed A_j, and B=f_G(C) make the centers coincide and the normals oppose, with source axis j'=f_G(j). The facets exist exactly when neither occupied-cell role is full. Thus the two holes remove only A=I or C=I; they remove no other case used below.

Whenever A,C are nonempty proper, mean(B)=a mean(C)+c, so the intercept identity is exactly mean(A)=mean(C). It must therefore hold for **every** nonempty proper A of the prescribed side whose toggle is nonempty proper. Empty endpoints are handled below, not by dividing by zero.

## 5. Mean lemma

Claim: if a fixed K satisfies mean(A)=mean(A△K) for every nonempty proper A with a fixed prescribed membership of j for which A△K is also nonempty proper, then K is empty or I.

It suffices first to treat j not in K, with K nonempty proper and m=|K|.

Positive face (j in A):
- If m=p-1, take A={j,k} with k in K. Its toggle is I\{k}; equality forces (j+k)/2=k, impossible.
- If m=p-2, write I\K={j,r}. Take A={j}; its toggle is I\{r}, whose mean is r, not j.
- If 1<=m<=p-3, use A={j} and A={j,k}, k in K. The first equality forces sum K=mj. The second then forces (m+2)(k-j)=0, impossible.

Negative face (j not in A):
- If I\K={j}, take A={k}, k in K. Its toggle is I\{j,k}; equality forces k=(j+k)/2, impossible.
- If I\K={j,r}, take A={r}; its toggle is I\{j}, whose mean is j, not r.
- Otherwise take two distinct r,s in (I\K)\{j}. The equalities for A={r} and A={s} require sum K=mr=ms, impossible.

All chosen sets and their toggles are nonempty and proper. If j is in K, replace K by I\K and use mean(C)=mean(I\C) for every nonempty proper C. The preceding failure transfers to K. This proves the claim for either wall side.

## 6. Exactly the CL wall catalog survives

The mean lemma leaves only K=empty or K=I.

K=empty gives D={j}, a=-1, C=A. On the positive side A is nonempty, so every c is permitted, giving P(j,c) with translation 4e_j. On the negative side the shared facet A=C=empty exists. Its completed endpoint forces c=0, giving M(j) with translation 0.

K=I gives D=I\{j}, a=+1, C=I\A. Every actual shared facet has A and C nonempty proper (the empty/full combination is not a shared carrier facet). Their means agree, so all c are permitted. The positive translation is 2*1; the negative translation is 2*1-4e_j. These are exactly the positive and negative complement-axis wall families in the uniform CL catalog.

Conversely, on every shared facet each listed wall satisfies the slope, intercept, and sign-mask identities. These reconstruct the complete matrix G=h_A L_k h_B^-1 and the label condition f_B(j')=-k. The M(empty) bridges supply the corresponding odd path for every k. That one path transports every free-orbit site of the facet, so all its coefficient equations hold. This verifies full profiles on every shared facet, not just one feature. The carrier boxes have disjoint interiors and their holes cannot remove the entire wall interface for p>=3. Hole contacts were already included in E and hence in F(E). The disjoint lists give

    |F(E)|=2(2^p-1)+3p^2+p,
    F(E)=CL(E)

as pose sets, using the existing exact CL description. This is stronger than a counting comparison.

## 7. Nonempty physical construction and finite Euclidean symmetry

Apply the dimension-free registration theorem to the finite proper contact language E. It specifies an explicit rational polyhedral p-ball T(E), obtained by its keyed normal-graph construction from the coefficients above. The theorem applies to tilings by arbitrary congruent copies, initially allowing rotations, reflections, translations, partial contacts, and split contacts. It proves registration after one ambient isometry and exact correspondence with F(E)-legal carrier tilings. The present equality therefore decodes every physical tiling as CL(E)-legal.

The existing full-world CL-to-E theorem makes that carrier tiling E-legal. The star-completion and coarse-legality results give its unique iterated hierarchy. The explicit exhausting substitution-world construction supplies an E-legal full tiling, so the physical tiling problem is nonempty.

The hierarchy excludes nonzero translations. As explained in the registration theorem, possible self-symmetries of the unmarked body do not invalidate this transfer: if a physical tiling had a translation period, choose native pose representatives on translation orbits and propagate them by that period. Registration would decode a translation-periodic framed carrier tiling, contradicting the hierarchy theorem.

For completeness, finite **full Euclidean** symmetry follows as well. After registration the tile orientations belong to a finite signed-permutation group. Since T(E) is a bounded full-dimensional polyhedron with finitely many facets, the unit facet-normal vectors occurring in the whole tiling, taking both signs, form a finite set S spanning R^p. Every Euclidean symmetry of the tiling permutes S. Its orthogonal linear part therefore belongs to a finite group, since a linear map is determined by its values on a spanning set. The homomorphism from tiling symmetries to their linear parts has only translations in its kernel, and that kernel is trivial. Hence the full Euclidean symmetry group is finite.

There are infinitely many primes 3 modulo 4: if their finite list had product Q, then 4Q-1 is 3 modulo 4 and has a prime divisor 3 modulo 4 that divides none of Q. Thus the stated dimensions form an infinite family.

## 8. Dependencies, verification, and boundaries

The ordinary inputs, with their roles, are:

1. [Uniform reduction and conventions](../uniform_prime_certificate_20261005/UNIFORM_REDUCTION_PROOF.md): signed row action, cell correction, proper frames, exact dissection, and exact hole catalog
2. [Exact symbolic E](../uniform_prime_certificate_20261005/HOLE_GRAPH_AND_SYMBOLIC_E.md), Section 4: the complete g=-1 contact language and closure
3. [Coarse legality and CL](../uniform_prime_certificate_20261005/UNIFORM_COARSE_LEGALITY.md), Sections 1–6: aligned offsets, exact CL pose catalog, full-world CL-to-E, and hierarchical iteration
4. [Star completion](../uniform_prime_certificate_20261005/UNIFORM_STAR_COMPLETION.md): unique complete parents in every E-legal world
5. [Nonemptiness and aperiodicity](../uniform_prime_certificate_20261005/NONEMPTINESS_AND_APERIODICITY.md): exhausting substitution worlds and the hierarchy's exclusion of translations
6. [Dimension-free keyed registration](../dimension_free_facet_registration_20261005/REGISTRATION_THEOREM.md), Sections 1–7: the specific rational p-ball, all-congruent-copy registration, and exact physical/carrier tiling correspondence
7. [Independent audit of the present argument](../audit_uniform_facet_closure_20261005/INDEPENDENT_AUDIT.md): direct checking of the uniform steps and the two expansions incorporated here

Input identities are frozen in [FINAL_SOURCE_PINS.txt](FINAL_SOURCE_PINS.txt). The [independent finite-check source](../audit_uniform_facet_closure_20261005/independent_check.py) and its [retained stdout](../audit_uniform_facet_closure_20261005/CHECK_OUTPUT.jsonl) separately reproduce exact F=CL pose sets for p=3 and p=7, and test every K and wall-side availability case in those dimensions. None of these finite calculations proves the uniform statement.

No unresolved mathematical gap was found in the stated ordinary proof at independent review. This is not a claim of formal-kernel or full NF verification, peer review, novelty, publication priority, proof for other dimensions, or equivalence to an earlier unspecified solid. The separate 5D quotient theorem is unchanged. The conclusion depends on the exact free-orbit compiler, complete shared-facet profiles, proper registered pose convention, and completed empty endpoint stated here; changing them requires a new argument.
