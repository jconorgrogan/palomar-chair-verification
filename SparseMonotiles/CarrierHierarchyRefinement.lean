module

public import SparseMonotiles.CarrierHierarchyParentCells

@[expose] public section

/-! Forward geometric substitution of undecorated carriers. A registered chair
world refines to another covering, nonoverlapping registered chair world for
any canonical child permutation rule. Contact legality is a separate finite
forward-closure obligation; no decorated-body rep-tile identity is used. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def dilatePose {d : ℕ} (p : Pose d) : Pose d where
  perm := p.perm
  negative := p.negative
  shift := fun i => 2 * p.shift i

def halfCell {d : ℕ} (c : Cell d) : Cell d := fun i => c i / 2

theorem dilatePose_inverse_half {d : ℕ} (p : Pose d) (c : Cell d) (i : Fin d) :
    (dilatePose p).inverseCell c i / 2 = p.inverseCell (halfCell c) i := by
  rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm i)) with h | h <;>
    simp [dilatePose, Pose.inverseCell, Pose.sign, halfCell, h] <;> omega

theorem doubleCell_half_iff {d : ℕ} (c : Cell d) : DoubleCell c ↔ IsChairCell (halfCell c) := by
  constructor
  · rintro ⟨hb, i, hi⟩
    constructor
    · intro j
      have hj := hb j
      simp only [halfCell]
      omega
    · refine ⟨i, ?_⟩
      have hj := hb i
      simp only [halfCell]
      omega
  · rintro ⟨hb, i, hi⟩
    constructor
    · intro j
      have hj := hb j
      simp only [halfCell] at hj
      omega
    · refine ⟨i, ?_⟩
      simp only [halfCell] at hi
      omega

theorem dilated_parent_occupies {d : ℕ} (p : Pose d) (c : Cell d) :
    ParentOccupies (dilatePose p) c ↔ Occupies p (halfCell c) := by
  rw [ParentOccupies, doubleCell_half_iff]
  have he : halfCell ((dilatePose p).inverseCell c) = p.inverseCell (halfCell c) := by
    funext i
    exact dilatePose_inverse_half p c i
  rw [he]
  rfl

/-- Two children of one canonical parent sharing a cell are the same posed
child. This derives uniqueness from the actual dissection geometry. -/
theorem children_cell_unique {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (p : Pose d)
    {s t : Pose d} (hs : s ∈ children σ p) (ht : t ∈ children σ p) {c : Cell d}
    (hsc : Occupies s c) (htc : Occupies t c) : s = t := by
  rcases hs with rfl | ⟨a, ha, rfl⟩ <;> rcases ht with rfl | ⟨b, hb, rfl⟩
  · rfl
  · have hc : Occupies (centralPose d) (p.inverseCell c) := by
      apply (occupies_compose_cell p _ _).mp
      simpa only [compose_central, Pose.cell_inverseCell] using hsc
    have ho : Occupies (outerPose b (σ b)) (p.inverseCell c) := by
      apply (occupies_compose_cell p _ _).mp
      simpa only [Pose.cell_inverseCell] using htc
    exact False.elim (central_outer_disjoint ((occupies_central _).mp hc) ((occupies_outer _ _ _).mp ho))
  · have ho : Occupies (outerPose a (σ a)) (p.inverseCell c) := by
      apply (occupies_compose_cell p _ _).mp
      simpa only [Pose.cell_inverseCell] using hsc
    have hc : Occupies (centralPose d) (p.inverseCell c) := by
      apply (occupies_compose_cell p _ _).mp
      simpa only [compose_central, Pose.cell_inverseCell] using htc
    exact False.elim (central_outer_disjoint ((occupies_central _).mp hc) ((occupies_outer _ _ _).mp ho))
  · have hoa : Occupies (outerPose a (σ a)) (p.inverseCell c) := by
      apply (occupies_compose_cell p _ _).mp
      simpa only [Pose.cell_inverseCell] using hsc
    have hob : Occupies (outerPose b (σ b)) (p.inverseCell c) := by
      apply (occupies_compose_cell p _ _).mp
      simpa only [Pose.cell_inverseCell] using htc
    have hab := outer_role_unique ((occupies_outer _ _ _).mp hoa) ((occupies_outer _ _ _).mp hob)
    subst b
    rfl

def refinedTiles {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (tiles : Set (Pose d)) : Set (Pose d) :=
  {q | ∃ p ∈ tiles, q ∈ children σ (dilatePose p)}

theorem refinedTiles_support {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (tiles : Set (Pose d)) (c : Cell d) :
    (∃ q ∈ refinedTiles σ tiles, Occupies q c) ↔ ∃ p ∈ tiles, Occupies p (halfCell c) := by
  constructor
  · rintro ⟨q, ⟨p, hp, hq⟩, hqc⟩
    exact ⟨p, hp, (dilated_parent_occupies p c).mp
      ((parent_support_dissection σ _ c).mpr ⟨q, hq, hqc⟩)⟩
  · rintro ⟨p, hp, hpc⟩
    obtain ⟨q, hq, hqc⟩ := (parent_support_dissection σ _ c).mp
      ((dilated_parent_occupies p c).mpr hpc)
    exact ⟨q, ⟨p, hp, hq⟩, hqc⟩

theorem refinedTiles_disjoint {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (tiles : Set (Pose d))
    (hd : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c, Occupies p c → Occupies q c → p = q) :
    ∀ p ∈ refinedTiles σ tiles, ∀ q ∈ refinedTiles σ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q := by
  rintro p ⟨P, hP, hp⟩ q ⟨Q, hQ, hq⟩ c hpc hqc
  have hPc := (dilated_parent_occupies P c).mp
    ((parent_support_dissection σ _ c).mpr ⟨p, hp, hpc⟩)
  have hQc := (dilated_parent_occupies Q c).mp
    ((parent_support_dissection σ _ c).mpr ⟨q, hq, hqc⟩)
  have heq := hd P hP Q hQ (halfCell c) hPc hQc
  subst Q
  exact children_cell_unique σ (dilatePose P) hp hq hpc hqc

/-- Actual forward refinement preserves registered cell coverage and disjointness. -/
def RegisteredWorld.refine {d : ℕ} (W : RegisteredWorld d) (σ : Bits d → Equiv.Perm (Fin d)) :
    RegisteredWorld d where
  tiles := refinedTiles σ W.tiles
  covers := fun c => (refinedTiles_support σ W.tiles c).mpr (W.covers (halfCell c))
  disjoint := refinedTiles_disjoint σ W.tiles W.disjoint

#print axioms dilated_parent_occupies
#print axioms children_cell_unique
#print axioms refinedTiles_support
#print axioms RegisteredWorld.refine
end SparseMonotiles.CarrierHierarchy
