module

public import ProductClosure.ProductWorldBlockPose
public import ProductClosure.ProductWorldRealization

@[expose] public section

/-! Actual complete registered ambient product-generator worlds are built
from the factor worlds, with all cell coverage and legal contacts proved. -/
namespace ProductClosure.World
open Set
noncomputable section
universe u v
variable {m n : ℕ}

theorem relativeProductLanguage_blockPose
    {MA : RegisteredPrime.Pose m → Prop} {MB : RegisteredPrime.Pose n → Prop}
    (q r : RegisteredPrime.Pose m × RegisteredPrime.Pose n)
    (h : ProductLanguage (fun a b => MA (a.relative b)) (fun a b => MB (a.relative b)) q r) :
    RelativeProductLanguage MA MB ((blockPose q.1 q.2).relative (blockPose r.1 r.2)) := by
  let hq := blockPose_preservesBlocks q.1 q.2
  let hr := blockPose_preservesBlocks r.1 r.2
  refine ⟨hq.relative hr, ?_⟩
  obtain h | h := h
  · apply Or.inl
    constructor
    · rw [leftPose_relative _ _ hq hr, leftPose_blockPose, leftPose_blockPose]
      exact h.1
    · rw [rightPose_relative _ _ hq hr, rightPose_blockPose, rightPose_blockPose]
      exact (relative_identity_iff _ _).mpr h.2
  · apply Or.inr
    constructor
    · rw [leftPose_relative _ _ hq hr, leftPose_blockPose, leftPose_blockPose]
      exact (relative_identity_iff _ _).mpr h.1
    · rw [rightPose_relative _ _ hq hr, rightPose_blockPose, rightPose_blockPose]
      exact h.2

namespace CompleteTiling
variable {S : Finset (Lattice m)} {T : Finset (Lattice n)}

/-- Literal product-generator world in the full ambient registered-pose
representation, not merely a pair-state surrogate. -/
def ambientProduct (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)) :
    CompleteTiling (placedCells (Polycube.productCells S T)) where
  tiles := (fun p : RegisteredPrime.Pose m × RegisteredPrime.Pose n => blockPose p.1 p.2) ''
    (WA.tiles ×ˢ WB.tiles)
  cover z := by
    let a := WA.owner (Polycube.leftIndex z)
    let b := WB.owner (Polycube.rightIndex z)
    refine ⟨blockPose a b, ⟨(a, b), ⟨WA.owner_mem _, WB.owner_mem _⟩, rfl⟩, ?_⟩
    apply (placedCells_product_iff S T _ (blockPose_preservesBlocks a b) z).mpr
    simpa only [leftPose_blockPose, rightPose_blockPose] using
      And.intro (WA.mem_owner (Polycube.leftIndex z)) (WB.mem_owner (Polycube.rightIndex z))
  disjoint p hp q hq hne := Set.disjoint_left.mpr (by
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    have hab : a ≠ b := fun he => hne (congrArg (fun p => blockPose p.1 p.2) he)
    intro z hz hz'
    have ha' := (placedCells_product_iff S T _ (blockPose_preservesBlocks a.1 a.2) z).mp hz
    have hb' := (placedCells_product_iff S T _ (blockPose_preservesBlocks b.1 b.2) z).mp hz'
    simp only [leftPose_blockPose, rightPose_blockPose] at ha' hb'
    have hza : (Polycube.leftIndex z, Polycube.rightIndex z) ∈ productCells (placedCells S) (placedCells T) a := ha'
    have hzb : (Polycube.leftIndex z, Polycube.rightIndex z) ∈ productCells (placedCells S) (placedCells T) b := hb'
    exact Set.disjoint_left.mp ((WA.prod WB).disjoint a ha b hb hab) hza hzb)
  nonempty p hp := by
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨x, hx⟩ := WA.nonempty q.1 hq.1
    obtain ⟨y, hy⟩ := WB.nonempty q.2 hq.2
    refine ⟨Fin.append x y, (placedCells_product_iff S T _
      (blockPose_preservesBlocks q.1 q.2) _).mpr ?_⟩
    simpa only [Polycube.leftIndex_append, Polycube.rightIndex_append,
      leftPose_blockPose, rightPose_blockPose] using And.intro hx hy

/-- Exact ambient owner function for the constructed product world. -/
theorem ambientProduct_owner (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T))
    (z : Lattice (m + n)) : (WA.ambientProduct WB).owner z =
      blockPose (WA.owner (Polycube.leftIndex z)) (WB.owner (Polycube.rightIndex z)) := by
  apply (WA.ambientProduct WB).owner_eq_of_mem
  · exact ⟨(_, _), ⟨WA.owner_mem _, WB.owner_mem _⟩, rfl⟩
  · apply (placedCells_product_iff S T _ (blockPose_preservesBlocks _ _) z).mpr
    simpa only [leftPose_blockPose, rightPose_blockPose] using
      And.intro (WA.mem_owner (Polycube.leftIndex z)) (WB.mem_owner (Polycube.rightIndex z))

set_option maxHeartbeats 800000 in
/-- Complete legal factor generator worlds give a complete legal ambient
product-generator world for the exact unary relative language. -/
theorem ambientProduct_legal
    {MA : RegisteredPrime.Pose m → Prop} {MB : RegisteredPrime.Pose n → Prop}
    (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T))
    (hA : WA.IsLegal LatticeAdjacent (fun a b => MA (a.relative b)))
    (hB : WB.IsLegal LatticeAdjacent (fun a b => MB (a.relative b))) :
    (WA.ambientProduct WB).IsLegal LatticeAdjacent
      (fun q r => RelativeProductLanguage MA MB (q.relative r)) := by
  intro z w hadj hne
  simp only [ambientProduct_owner] at hne
  have hprodAdj : ProductAdjacent (Polycube.leftIndex z, Polycube.rightIndex z)
      (Polycube.leftIndex w, Polycube.rightIndex w) := by
    apply (productAdjacent_iff_append _ _).mpr
    simpa only [Polycube.append_leftIndex_rightIndex] using hadj
  have hprodNe : (WA.prod WB).owner (Polycube.leftIndex z, Polycube.rightIndex z) ≠
      (WA.prod WB).owner (Polycube.leftIndex w, Polycube.rightIndex w) := by
    simp only [prod_owner]
    intro he
    exact hne (congrArg (fun p => blockPose p.1 p.2) he)
  have hp := (WA.prod_legal WB hA hB) _ _ hprodAdj hprodNe
  simp only [prod_owner] at hp
  have hc := relativeProductLanguage_blockPose
    (WA.owner (Polycube.leftIndex z), WB.owner (Polycube.rightIndex z))
    (WA.owner (Polycube.leftIndex w), WB.owner (Polycube.rightIndex w)) hp
  simpa only [ambientProduct_owner] using hc

/-- Product existence can be realized as a genuine Euclidean tiling by
congruent copies of the finite product carrier. -/
theorem ambientProduct_physical_exists {a b : ℕ}
    {S : Finset (Lattice (a + 1))} {T : Finset (Lattice (b + 1))}
    (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)) :
    Nonempty (RegisteredCarrierTiling (d := a + 1 + b)
      (Polycube.productCells (m := a + 1) (n := b + 1) S T)) :=
  ⟨(WA.ambientProduct WB).realize⟩

#print axioms ambientProduct
#print axioms ambientProduct_legal
#print axioms ambientProduct_physical_exists

end CompleteTiling
end
end ProductClosure.World
