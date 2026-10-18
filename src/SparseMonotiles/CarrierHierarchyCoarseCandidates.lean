module

public import SparseMonotiles.CarrierHierarchyExactStages
public import Mathlib.Data.Finset.Union

@[expose] public section

/-!
Exhaustive sparse parent witnesses, with unscaled integer offsets retained.
Physical right gauges are included explicitly in the child table, so this
completeness theorem requires no lift into a smaller framed language.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def parentCandidate {d : ℕ} (a b k : Pose d) : Pose d :=
  compose a (compose k (inversePose b))

/-- The child-contact witness determines the entire unscaled relative parent
pose, including its integer translation; no parity projection is performed. -/
theorem parent_witness_reconstruction {d : ℕ} (P Q a b : Pose d) :
    normalize P Q = parentCandidate a b (normalize (compose P a) (compose Q b)) := by
  let k := normalize (compose P a) (compose Q b)
  have hc : compose (compose P a) k = compose Q b := compose_normalize _ _
  have he : compose P (compose a k) = compose P (compose (normalize P Q) b) := by
    rw [← compose_assoc, hc, ← compose_assoc, compose_normalize]
  have hi := congrArg (fun p => compose p (inversePose b)) (compose_left_injective P he)
  simp only [compose_assoc, compose_inversePose, compose_root_right] at hi
  exact hi.symm

def expandedChildren {d : ℕ} (r : Equiv.Perm (Fin d)) (C : Finset (Pose d)) : Finset (Pose d) :=
  C ∪ C.image (rightGauge r)

def parentCandidates {d : ℕ} (r : Equiv.Perm (Fin d))
    (C L : Finset (Pose d)) : Finset (Pose d) :=
  (expandedChildren r C).biUnion fun a => (expandedChildren r C).biUnion fun b =>
    L.image (parentCandidate a b)

/-- The finite canonical table must contain the centre and every proper outer
role. This is an ordinary finite-table obligation, not a parent-existence axiom. -/
def CoversCanonicalChildren {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (C : Finset (Pose d)) : Prop :=
  centralPose d ∈ C ∧ ∀ a, Proper a → outerPose a (σ a) ∈ C

private theorem child_table_form {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {C : Finset (Pose d)} (hC : CoversCanonicalChildren σ C)
    (P : Pose d) {q : Pose d} (hq : q ∈ children σ P) :
    ∃ a ∈ C, q = compose P a := by
  rcases hq with rfl | ⟨a, ha, rfl⟩
  · exact ⟨centralPose _, hC.1, (compose_central P).symm⟩
  · exact ⟨outerPose a (σ a), hC.2 a ha, rfl⟩

private theorem physical_child_table_form {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    {C : Finset (Pose d)} (hC : CoversCanonicalChildren σ C)
    {P t : Pose d} (ht : ParentContains σ r P t) :
    ∃ a ∈ expandedChildren r C, t = compose P a := by
  obtain ⟨q, hq, hg⟩ := ht
  obtain ⟨a, ha, rfl⟩ := child_table_form hC P hq
  rcases hg with rfl | rfl
  · exact ⟨a, Finset.mem_union_left _ ha, rfl⟩
  · exact ⟨rightGauge r a, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩),
      (compose_rightGauge r P a).symm⟩

/-- Every actual touching pair of complete distinct parents occurs in the
finite child-witness generator, including each physical gauge choice. -/
theorem RegisteredWorld.parent_candidate_complete {d : ℕ} (W : RegisteredWorld d)
    (hd : 2 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (C L : Finset (Pose d)) (hC : CoversCanonicalChildren σ C)
    (hl : W.Legal (L : Set (Pose d)))
    {P Q : Pose d} (hP : CompleteParent σ r W.tiles P) (hQ : CompleteParent σ r W.tiles Q)
    (hne : physicalClass r hr P ≠ physicalClass r hr Q)
    {c b : Cell d} (hPc : ParentOccupies P c) (hQb : ParentOccupies Q b)
    (hadj : AdjacentCells c b) : normalize P Q ∈ parentCandidates r C L := by
  obtain ⟨s, hs, hPs, hsc⟩ := hP.owns_cell hPc
  obtain ⟨t, ht, hQt, htb⟩ := hQ.owns_cell hQb
  have hst : s ≠ t := by
    intro h
    subst t
    exact hne (complete_parent_unique hd hr he W.tiles W.disjoint hP hQ hPs hQt)
  have hk : normalize s t ∈ L := hl s hs t ht hst ⟨c, b, hsc, htb, hadj⟩
  obtain ⟨a, ha, rfl⟩ := physical_child_table_form hC hPs
  obtain ⟨b, hb, rfl⟩ := physical_child_table_form hC hQt
  rw [parent_witness_reconstruction P Q a b]
  exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr
    ⟨b, hb, Finset.mem_image.mpr ⟨_, hk, rfl⟩⟩⟩

#print axioms parent_witness_reconstruction
#print axioms RegisteredWorld.parent_candidate_complete
end SparseMonotiles.CarrierHierarchy
