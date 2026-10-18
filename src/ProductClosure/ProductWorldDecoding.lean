module

public import ProductClosure.ProductWorldRelative
public import ProductClosure.ProductWorldRealization
public import ProductClosure.ProductWorldProper

@[expose] public section

/-!
# End-to-end registered ambient product-world decoding

A complete ambient world starts with unrestricted registered signed poses.
Its local relative product mate language first forces one common block
chart; the world is then actually reframed and split, and Cartesian
factorization follows from the proved local owner law. The final factors
retain complete poses, have full coverage, and have Euclidean realizations.
-/
namespace ProductClosure.World

open Set
noncomputable section

namespace CompleteTiling
variable {m n : ℕ} {S : Finset (Lattice m)} {T : Finset (Lattice n)}
variable {MA : RegisteredPrime.Pose m → Prop} {MB : RegisteredPrime.Pose n → Prop}

/-- Exact unary relative product contact closure implies the binary factor
state law in the complete split world. -/
theorem splitWorld_relative_legal
    (W : CompleteTiling (placedCells (Polycube.productCells S T)))
    (hblock : ∀ q ∈ W.tiles, PreservesBlocks q)
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => RelativeProductLanguage MA MB (q.relative r))) :
    (W.splitWorld hblock).IsLegal ProductAdjacent
      (ProductLanguage (fun a b => MA (a.relative b)) (fun a b => MB (a.relative b))) := by
  apply W.splitWorld_legal hblock
  intro q r hne hcontact
  obtain ⟨x, y, hx, hy, hadj⟩ := hcontact
  have hqx := W.owner_eq_of_mem q.property hx
  have hry := W.owner_eq_of_mem r.property hy
  have hn : W.owner x ≠ W.owner y := by simpa only [hqx, hry] using hne
  have hc := hlocal x y hadj hn
  rw [hqx, hry] at hc
  exact productLanguage_of_relative q.val r.val (hblock _ q.property) (hblock _ r.property) hc

/-- Full registered ambient-to-Cartesian theorem. Absolute poses are not
assumed block-preserving; only actual neighboring relative mates are in the
product language. Coverage, normalization, splitting and factor coverage
are all conclusions of the previously proved constructions. -/
theorem decode_registered_product_world
    (W : CompleteTiling (placedCells (Polycube.productCells S T)))
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => RelativeProductLanguage MA MB (q.relative r)))
    (hsepA : Separates (placedCells S) (fun a b => MA (a.relative b)))
    (hsepB : Separates (placedCells T) (fun a b => MB (a.relative b))) :
    ∃ root ∈ W.tiles, ∃ hblock : ∀ q ∈ (W.reframe root).tiles, PreservesBlocks q,
      ∃ (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)),
        WA.IsLegal LatticeAdjacent (fun a b => MA (a.relative b)) ∧
        WB.IsLegal LatticeAdjacent (fun a b => MB (a.relative b)) ∧
        Set.range ((W.reframe root).splitState hblock) = WA.tiles ×ˢ WB.tiles ∧
        ∀ z, ((W.reframe root).splitWorld hblock).owner z = (WA.owner z.1, WB.owner z.2) := by
  let root := W.owner 0
  have hr : root ∈ W.tiles := W.owner_mem 0
  have hblocks : W.IsLegal LatticeAdjacent (fun q r => PreservesBlocks (q.relative r)) := by
    intro x y hadj hne
    exact (hlocal x y hadj hne).choose
  let N := W.reframe root
  have hb : ∀ q ∈ N.tiles, PreservesBlocks q := W.reframe_preservesBlocks hblocks hr
  have hN := W.reframe_legal root hlocal
  let C := N.splitWorld hb
  have hl := N.splitWorld_relative_legal hb hN
  refine ⟨root, hr, hb, C.activeFactor hl hsepA hsepB, C.passiveFactor hl hsepA hsepB,
    C.activeFactor_legal hl hsepA hsepB, C.passiveFactor_legal hl hsepA hsepB,
    C.tiles_cartesian hl hsepA hsepB, ?_⟩
  intro z
  simp only [activeFactor_owner, passiveFactor_owner]
  exact C.owner_factorizes hl hsepA hsepB z.1 z.2

end CompleteTiling

/-- Actual Euclidean registered product-carrier tilings, even with arbitrary
ambient signed poses, decode after one proved common chart to complete
legal factor worlds. These factor cell worlds themselves have actual
Euclidean realizations by `CompleteTiling.realize`. -/
theorem physical_registered_product_decodes {m n : ℕ}
    {S : Finset (Lattice (m + 1))} {T : Finset (Lattice (n + 1))}
    (hS : S.Nonempty) (hT : T.Nonempty)
    (W : RegisteredCarrierTiling (d := m + 1 + n)
      (Polycube.productCells (m := m + 1) (n := n + 1) S T))
    {MA : RegisteredPrime.Pose (m + 1) → Prop} {MB : RegisteredPrime.Pose (n + 1) → Prop}
    (hcontact : ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r → W.CellFacetContact q r →
      RelativeProductLanguage MA MB (q.relative r))
    (hA : ∀ q r, MA (q.relative r) →
      Disjoint (interior (placedCarrier S q)) (interior (placedCarrier S r)))
    (hB : ∀ q r, MB (q.relative r) →
      Disjoint (interior (placedCarrier T q)) (interior (placedCarrier T r))) :
    ∃ root ∈ W.tiles,
      ∃ hblock : ∀ q ∈ ((W.toCellWorld (Polycube.productCells_nonempty hS hT)).reframe root).tiles,
        PreservesBlocks (m := m + 1) (n := n + 1) q,
      ∃ (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)),
        WA.IsLegal LatticeAdjacent (fun a b => MA (a.relative b)) ∧
        WB.IsLegal LatticeAdjacent (fun a b => MB (a.relative b)) ∧
        Set.range (((W.toCellWorld (Polycube.productCells_nonempty hS hT)).reframe root).splitState hblock) =
          WA.realize.tiles ×ˢ WB.realize.tiles ∧
        ∀ z, (((W.toCellWorld (Polycube.productCells_nonempty hS hT)).reframe root).splitWorld hblock).owner z =
          (WA.owner z.1, WB.owner z.2) := by
  apply (W.toCellWorld (Polycube.productCells_nonempty hS hT)).decode_registered_product_world
  · exact W.toCellWorld_legal _ hcontact
  · intro q r hqr
    exact placedCells_disjoint_of_interiors S q r (hA q r hqr)
  · intro q r hqr
    exact placedCells_disjoint_of_interiors T q r (hB q r hqr)

#print axioms CompleteTiling.decode_registered_product_world
#print axioms physical_registered_product_decodes

end
end ProductClosure.World
