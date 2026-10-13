# Dimension-free registration of rational keyed facet chairs

Date: 2026-10-05. Status: ordinary mathematical construction and proof. Not a proof-assistant result, not a replay of the reported 5D/7D facet census, and not a claim about unspecified earlier symmetric bump shapes.

## Result

For every integer d >= 3 and every finite language A of proper, lattice-registered, interior-disjoint face contacts of the d-dimensional chair, the construction below gives one explicitly defined rational polyhedral d-ball T(A). It has these properties:

1. Every tiling by arbitrary congruent copies of T(A), initially allowing all rotations, reflections, and translations, becomes lattice registered after one ambient isometry. All relative frames are proper signed permutations and all translations are integral.
2. No face-to-face, whole-feature, or connected-contact-graph assumption is used. Partial and split contacts, fractional slides, and mixed handedness are excluded by the proof.
3. Its full-profile registered mating relation is exactly the signed facet-equation closure F(A), defined below, and its tilings correspond to F(A)-legal carrier tilings. In particular it preserves every A-legal carrier tiling. A mating relation can contain dead contacts that never occur in a complete tiling.
4. Therefore, if F(A)-legal carrier tilings exist and are aperiodic, T(A) is an aperiodic unmarked shape. The supplied construction does not establish the needed 5D/7D equalities identifying F(A).

The construction is a keyed replacement for the facet-height compiler. It preserves that compiler's proper registered full-profile mating relation. Mere pairwise nonoverlap or touching somewhere on a flat face is a weaker condition and is not called mating here. It need not be congruent to a previously drawn or unspecified symmetric-tent design.

This generalizes the existing 4D asymmetric-key argument in `REGISTRATION_SOURCE_PACKAGE_inspected/REGISTRATION_SCAFFOLD.md`. The dimension-dependent cone and retained-core estimates are provided explicitly here.

## 1. Carrier, contact graph, and coefficients

Let

P_d = union of a+[0,1]^d over a in {0,1}^d except a=(1,...,1).

An exposed unit facet f has unit-facet center b_f, outward normal n_f in {+/-e_i}, and tangent inclusion I_f whose ordered columns are the increasing ambient coordinate axes other than the normal axis. There are d*2^d exposed unit facets.

Put m=d-1 and

q0=(1,2,...,m)/(4d),  Q=B_m q0,

where B_m is the full signed-permutation group. This orbit is free. Consequently each q in Q has one and only one A_q in B_m with A_q q0=q. The sites are u=(f,q), with center c_u=b_f+I_f q and keyed tangent frame I_f A_q.

For every prescribed contact g P_d+t in A and every unit facet shared with P_d, pair each root site u with the other tile's native site v whose center maps to it. Put an undirected edge u--v. Equivalently the signed-height relation along every edge is a_u=-a_v. This is the full facet equation graph, with no quotient of facet sites or tangent frames.

Define

chi_u = det([I_f A_q, n_f]) in {+1,-1}.

For every graph edge, g is proper, the tangent orbit frames transport identically, and the outward normals reverse. Hence

g I_v A_v=I_u A_u,  g n_v=-n_u,

and taking determinants gives chi_v=-chi_u.

Thus the graph is automatically bipartite: no odd signed cycle and no forced-zero site can occur for this full free-orbit compiler with proper generating contacts. This conclusion is structural, not numerical.

Order native sites by the lexicographic tuple (b_f, n_f, q), each vector using increasing ambient or tangent coordinate order. Order connected components by their least site, and number them j=1,...,J. Assign

a_u=j(u)*chi_u.

Every coefficient is nonzero and satisfies every required signed relation. Different components have different absolute magnitudes. Choosing a different overall sign independently on a component would yield the same proper registered contact language, but the displayed choice fixes one unambiguous body.

For an arbitrary proper registered nonoverlapping carrier contact, call it a member of F(A) precisely when every one of its shared-facet site pairs satisfies a_u=-a_v. Because proper transport always flips chi, this is equivalent to requiring the paired sites to belong to the same graph component. Thus F(A) depends only on the exact facet graph, not on our chosen magnitudes or prime parameters.

The graph is finite. Its site count is d*2^d * 2^(d-1)*(d-1)!. This is 61,440 sites for d=5 and 41,287,680 for d=7. Those are formula counts; no graph traversal or component census is claimed here.

## 2. Exact rational key and margins

Choose the first 2m primes strictly greater than J, in increasing order, and call them

p_1^-, p_1^+, p_2^-, p_2^+, ..., p_m^-, p_m^+.

Let p_max=p_m^+. Set

delta=1/(16d),  eta=1/(128d),  rho=1/(32d),

and let N be the first prime strictly greater than 32d J p_max.

Define the asymmetric tangent box

K=product_i [-eta/p_i^-, eta/p_i^+]

and its tent

psi(u)=max(0, min_i {1+p_i^- u_i/eta, 1-p_i^+ u_i/eta}).

At site (f,q), replace the flat facet by the normal graph

z=(eta a_u/N) psi(A_q^(-1) I_f^(-1)(x-c_u)),

with z measured in direction n_f. The expression involving I_f^(-1) is used only on the tangent hyperplane. Keep the native body on the inward side of the graph. All coordinates and polyhedral vertices are rational.

Use tubes with normal half-width rho and tangent base I_f A_q K. The maximum height is eta J/N < rho. A direct ambient deformation in each tube is

(u,z) -> (u, z+max(0,1-|z|/rho) h(u)),

where h is the signed tent height. It is strictly increasing in z, is the identity on the tube boundary, and fixes the complement of the tubes.

All tubes are disjoint. Every orbit center has tangent distance greater than 1/4 from each integer hyperplane. Base half-widths are less than eta. Distinct sites in one unit facet differ in some tangent coordinate by at least 1/(4d), whereas twice the maximal half-width is less than 2 eta=1/(64d). Adjacent coplanar unit facets have their supports bounded away from their common integer boundary. Parallel distinct facet planes are at least one apart. For different normal axes an intersection would require one coordinate both within rho of an integer and at least 1/4-eta from an integer, which is impossible. These separation statements hold for every registered signed-permutation translate as well; matching world sites coincide and all other sites remain disjoint.

Each occupied cell retains the closed core

C_a=a+[delta,1-delta]^d

strictly inside the physical body, since all modifications occur at normal distance below rho=delta/2 from integer facet planes. In particular the body contains a radius-1/4 ball about each occupied unit-cell center.

The tube deformations form an ambient homeomorphism taking P_d to T(A). The carrier has a strict star center at (1/2,...,1/2): for x in P_d, one coordinate of x is at most 1, and the segment to any point of (0,1)^d retains that property. Its positive radial function gives a homeomorphism with the closed d-ball. Hence T(A) is a rational polyhedral d-ball.

## 3. Complete codimension-two angle inventory

Every nonzero graph gradient has length j p/N for some j in {1,...,J} and prime p from the displayed list. Write

L=J p_max/N < 1/(32d).

A base crease has absolute deviation from a flat dihedral

alpha_(j,p)=arctan(jp/N).

A side-side crease between distinct tangent axes, with slope numerators b,c, has deviation

beta_(b,c)=arccos(1/sqrt((1+b^2/N^2)(1+c^2/N^2))).

Opposite side facets from the same tangent axis meet only at the apex and create no additional codimension-two creases. For d>=3 all genuine codimension-two key strata belong to the preceding two classes.

Every deviation lies strictly between 0 and pi/4. Distinct pairs (j,p) give distinct alpha values: jp=kq with different primes p,q>J would force p to divide k<=J. No alpha equals any beta. Such an equality would imply

N^2(a^2-b^2-c^2)=b^2 c^2,

impossible because N is prime and 0<b,c<N. Distinctness between different beta values is unnecessary.

Outside the keys the boundary is orthogonal. At a generic codimension-two stratum its perpendicular planar material section contributes a nonzero integer multiple of pi/2. The local support separation excludes hybrid key/carrier-edge angles.

## 4. Whole companions are forced without a face-to-face hypothesis

### 4.1 Local finiteness and generic transverse sections

Every packing by congruent copies of T(A) is locally finite: carry one fixed interior radius-1/4 ball with each tile, use disjoint interiors of those balls, and bounded tile diameter.

Fix the affine (d-2)-plane of a root key crease. Remove intersections with the finitely many nearby tile strata of dimension at most d-3, with noncoplanar (d-2)-strata, and with facet hyperplanes not containing that plane. These are finitely many proper affine subsets. At every remaining point, all incident boundary pieces have the transverse two-dimensional angle types listed above. No other tile can contain this point in its interior, because root interior points accumulate there.

The root supplies a key sector strictly between 3pi/4 and 5pi/4. Three key sectors cannot fit in angle 2pi. Two key sectors plus any ordinary sector cannot fit either. One key sector plus only ordinary sectors cannot sum to 2pi, because its nonzero deviation from pi has size below pi/4 while ordinary contributions are multiples of pi/2. Thus exactly one other tile supplies a complementary key sector. At a root base crease, alpha/beta separation and alpha uniqueness identify the other crease as a base crease with the same magnitude j and prime p.

### 4.2 A dimension-dependent cone bound prevents switching

At every point of a key graph, including base vertices and apex, the body is locally a hypograph with Lipschitz constant at most L. Its tangent cone contains

{(v,w) in R^(d-1) x R : w < -L ||v||}.

Its normalized spherical measure equals the probability of this event for an isotropic standard Gaussian (V,W). Conditioning on R=||V|| and bounding the one-dimensional Gaussian density by 1/sqrt(2pi) gives

Pr(W<-LR) >= 1/2 - L E(R)/sqrt(2pi)
             >= 1/2 - L sqrt(d-1)/sqrt(2pi)
             > 1/3.

The final inequality follows from L<1/(32d). Tangent cones of distinct tile interiors have disjoint interiors. Therefore no point can lie on key graphs of three distinct tiles.

Let C(F) be the closed crease complex of a root feature: all its base and side-side codimension-two faces, including their boundaries. For d>=3 it is connected, compact, and the relative interiors of its codimension-two faces are dense. For each of the finitely many other tiles S meeting it, intersect C(F) with the union of S's closed key crease complexes. The resulting sets are closed; generic complementary matching makes their union dense, hence all of C(F); and the cone bound makes them pairwise disjoint. A connected space cannot have a nontrivial finite disjoint closed partition. Hence one tile supplies all companions. Its distinct native key complexes are disjoint compact sets, so the root complex is contained in one companion complex C(F').

This includes possible switching at every lower-dimensional junction. Whole-key matching has been derived rather than assumed.

### 4.3 Containment is equality and recovers the signed tangent frame

A generic root base point identifies the same height magnitude j in F'. The two crease complexes are therefore congruent. A compact metric space cannot contain a proper isometric copy of itself: a point outside the compact image has positive distance from it, and its iterates would give infinitely many points separated by that positive distance. Thus C(F)=C(F').

The convex hull of C(F) is the d-dimensional pyramid over K. Its base facet has 2^(d-1) vertices; each side facet has 2^(d-2)+1. These differ for every d>=3. Hence the base hyperplane and the unique off-base apex are intrinsically recognized.

The m side lengths eta(1/p_i^-+1/p_i^+) are strictly decreasing. A box isometry can therefore only reverse individually identified axes. The apex projection is 0 and differs from the box center in every coordinate, since p_i^- != p_i^+. Fixing the projection forbids all those reversals. The keyed tangent frame has trivial stabilizer.

The equal whole feature bounds opposite tile interiors, forcing opposite outward normals and opposite signed coefficients.

## 5. Arbitrary rotations, fractional translations, and mixed handedness disappear

Normalize a root tile pose to (I,0). Let an actual companion have initially arbitrary orthogonal map G and translation t, pairing native sites u=(f,q), v=(f',q'). Intrinsic key rigidity gives

G I_f' A_q'=I_f A_q,  G n_f'=-n_f.

Thus G is a signed permutation. Equality of the apex projections gives G c_v+t=c_u. The orbit-frame identity also transports the offset A_q' q0 exactly to A_q q0. Subtraction therefore yields

G b_f'+t=b_f.

The normal coordinate is an integer and tangent coordinates are half-integers, so t is integral. This direct recovery of the unit-facet center eliminates all fractional slides, without a finite pose census.

Equal magnitudes identify the same graph component; opposite signed coefficients and a_u=j chi_u imply chi_v=-chi_u. Taking determinants of the actual frame identities gives

det(G) chi_v=-chi_u.

Consequently det(G)=+1. Every companion has proper relative frame. This argument rules out mixed handedness but, as it must, permits a global mirror through the ambient normalization.

## 6. Local companions register the entire tiling

Take one feature-companion component containing a normalized root. Every tile in it has pose in B_d^+ semidirect Z^d. Two of its carrier chairs cannot share a unit cell, since their untouched retained cores would overlap in physical interiors.

Let W be the set of their carrier cells. For a cell in W, every face-adjacent cell either belongs to the same chair or lies across an exposed facet. Every exposed facet has nonzero keys. A whole companion across any such key belongs to this component and, by recovered facet center and opposite normal, owns the exact adjacent cell. Thus W is nonempty and closed under every lattice step, so W=Z^d.

Suppose some physical tile belonged to another component. Let x be the center of its carried radius-1/4 interior ball. Choose a unit cell containing x and its unique owner in the first component. Coordinatewise clamping x into that owner's retained core gives an interior point y satisfying

||x-y|| <= sqrt(d) delta=1/(16sqrt(d)) < 1/4.

Then y lies in the interiors of both tiles, a contradiction. Every tile belongs to the same component. This proves global registration without assuming the companion graph connected.

## 7. Exact registered language and existence transfer

After registration, the registered carriers own the integer cells exactly once by the preceding argument. For each shared carrier unit facet, registered tube separation means that only its two adjacent carrier owners can contribute changed material at one of its key sites. Coverage and disjoint interiors therefore force opposite signed coefficients at every paired site. Its contact belongs to F(A).

Conversely, in an F(A)-legal registered carrier tiling, every paired key has the same transported asymmetric footprint and opposite coefficients. The two normal graphs agree, so each tube is filled exactly once. Distinct world tubes are disjoint and outside them the carrier tiling is unchanged. Thus the same poses give a physical tiling of T(A).

This establishes exact correspondence at the level of carrier poses and F(A) contacts. It is more than a necessary-contact test. It also proves nonvacuity whenever at least one A-legal tiling is known, because A is contained in F(A).

For aperiodicity, nontrivial proper body symmetries do not create a loophole. If an unmarked physical tiling had a nonzero translation period, choose body-frame representatives along each orbit of tiles under that translation and propagate them by the period. This gives a translation-periodic framed realization of the same tiling. Registration and exact decoding make it an F(A)-legal periodic carrier tiling, a contradiction if that language is aperiodic.

## 8. Application boundary for the reported 5D and 7D results

The symbolic uniform family supplies finite proper languages for (p,g)=(5,2) and (7,6), with |E|=116 and 318 respectively. One may feed these exact languages, or the exact alternate generating language actually used by the facet compiler, into the construction above. No geometric synthesis solver is needed to define the result.

What this proves now is a dimension-independent registration upgrade with exact rational construction. It does not replay or certify these pasted claims:

- F(E_7)=CL(E_7), reportedly without extra registered contacts
- the exact 62-contact excess in dimension 5
- that every extra contact is a hidden proper relabeling, and that arbitrary physical tilings of the resulting full language still force the intended hierarchy
- the stated 4D periodic witness and all solver certificates

To conclude the proposed 7D monotile result, supply the exact frozen input language, facet transport conventions, and a reproducible equality/certificate for F(A)=CL(E_7), then use the independently justified global CL-to-E hierarchy theorem. To conclude the 5D result, additionally supply the exact surplus-contact list and an all-tilings gauge-lifting or hierarchy argument, rather than just one finite corona count.

The uploaded text contains none of the 5D/7D facet graph tables, shape coordinates, source code, or exact census receipts. Therefore it cannot identify or validate an earlier physical solid. The keyed T(A) here is a newly specified upgrade; all-congruent-copy grid and orientation rigidity are proved for this construction, not retrospectively attributed to an unspecified shape.

## Local source basis

- Existing 4D construction and detailed ordinary audit: `locate7d_sources_20261005_1112/REGISTRATION_SOURCE_PACKAGE_inspected/REGISTRATION_SCAFFOLD.md` and `INDEPENDENT_REGISTRATION_AUDIT.md`
- Existing exact 4D finite-data snapshot: `EXACT_SCAFFOLD_DATA.json` in the same directory
- Exact uniform E formula and its limitations: `uniform_prime_certificate_20261005/HOLE_GRAPH_AND_SYMBOLIC_E.md` and `THEOREM_SUMMARY.md`
- New pasted report: Library item `libfile_43a4729767d4819183c0977f18150397`, 86 lines, uploaded 2026-10-05 19:12:24 UTC

No untrusted uploaded code was run and no high-dimensional facet enumeration was performed for this proof.
