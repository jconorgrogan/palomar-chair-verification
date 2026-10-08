module

public import SparseMonotiles.CarrierHierarchyCoarseCandidates
public import SparseMonotiles.CarrierHierarchyWitnessChecker

@[expose] public section

/-!
Stable finite-certificate API for necessary coarse legality. Only unscaled
parent poses are encoded. Every rejection has an explicit occupied-cell witness;
accepted rows need only identify the halved pose in the supplied language.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

structure GaugeClosed {d : ℕ} (r : Equiv.Perm (Fin d)) (L : Set (Pose d)) : Prop where
  left : ∀ k ∈ L, compose (unsignedPose r) k ∈ L
  right : ∀ k ∈ L, rightGauge r k ∈ L

def IsCanonicalTable {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (C : Finset (Pose d)) : Prop :=
  CoversCanonicalChildren σ C ∧ ∀ a ∈ C, a ∈ children σ (rootPose d)

inductive CoarseWitness (d : ℕ) where
  | member
  | overlap (cell : Cell d)
  | illegalChild (left right : Pose d) (leftCell rightCell : Cell d)

def CoarseWitness.Valid {d : ℕ} (C : Finset (Pose d)) (L : Set (Pose d))
    (F : Pose d) : CoarseWitness d → Prop
  | .member => coarsePose (fun _ => 0) F ∈ L
  | .overlap c => ParentOccupies (rootPose d) c ∧ ParentOccupies F c
  | .illegalChild a b c e => a ∈ C ∧ b ∈ C ∧ Occupies a c ∧
      Occupies (compose F b) e ∧ AdjacentCells c e ∧ normalize a (compose F b) ∉ L

instance coarseDecidableParentOccupies {d : ℕ} (p : Pose d) (c : Cell d) :
    Decidable (ParentOccupies p c) := inferInstanceAs (Decidable (_ ∧ _))

instance coarseDecidableAdjacentCells {d : ℕ} (c b : Cell d) :
    Decidable (AdjacentCells c b) := inferInstanceAs (Decidable (∃ _, _ ∧ _))

instance coarseDecidableValid {d : ℕ} (C : Finset (Pose d)) (L : Set (Pose d))
    [DecidablePred L] (F : Pose d) (w : CoarseWitness d) : Decidable (w.Valid C L F) := by
  cases w with
  | member => exact ‹DecidablePred L› _
  | overlap c => exact inferInstanceAs (Decidable (ParentOccupies (rootPose d) c ∧ ParentOccupies F c))
  | illegalChild a b c e =>
      exact inferInstanceAs (Decidable (a ∈ C ∧ b ∈ C ∧ Occupies a c ∧
        Occupies (compose F b) e ∧ AdjacentCells c e ∧ ¬ L (normalize a (compose F b))))

structure CoarseRow (d : ℕ) where
  pose : Pose d
  witness : CoarseWitness d

theorem normalize_rightGauge_right {d : ℕ} (r : Equiv.Perm (Fin d)) (p q : Pose d) :
    normalize p (rightGauge r q) = rightGauge r (normalize p q) :=
  compose_rightGauge r (inversePose p) q

theorem normalize_rightGauge_left {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) (p q : Pose d) :
    normalize (rightGauge r p) q = compose (unsignedPose r) (normalize p q) := by
  apply compose_left_injective (rightGauge r p)
  rw [compose_normalize, rightGauge_eq_compose, compose_assoc,
    ← compose_assoc (unsignedPose r) (unsignedPose r), unsignedPose_involution r hr,
    compose_root_left, compose_normalize]

/-- Independent endpoint gauges preserve the supplied language. -/
theorem GaugeClosed.normal_congr {d : ℕ} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) {L : Set (Pose d)} (hL : GaugeClosed r L)
    {p q p' q' : Pose d} (hp : GaugeRel r p p') (hq : GaugeRel r q q')
    (hk : normalize p q ∈ L) : normalize p' q' ∈ L := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact hk
  · rw [normalize_rightGauge_right]
    exact hL.right _ hk
  · rw [normalize_rightGauge_left r hr]
    exact hL.left _ hk
  · rw [normalize_rightGauge_right, normalize_rightGauge_left r hr]
    exact hL.right _ (hL.left _ hk)

theorem normalize_common_left {d : ℕ} (P a b : Pose d) :
    normalize (compose P a) (compose P b) = normalize a b := by
  apply compose_left_injective (compose P a)
  rw [compose_normalize, compose_assoc, compose_normalize]

theorem normalized_parent_children {d : ℕ} (P Q a b : Pose d) :
    normalize (compose P a) (compose Q b) = normalize a (compose (normalize P Q) b) := by
  rw [← normalize_common_left P a (compose (normalize P Q) b),
    ← compose_assoc P (normalize P Q), compose_normalize]

theorem canonical_child_form {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {C : Finset (Pose d)} (hC : CoversCanonicalChildren σ C)
    (P : Pose d) {q : Pose d} (hq : q ∈ children σ P) :
    ∃ a ∈ C, q = compose P a := by
  rcases hq with rfl | ⟨a, ha, rfl⟩
  · exact ⟨centralPose _, hC.1, (compose_central P).symm⟩
  · exact ⟨outerPose a (σ a), hC.2 a ha, rfl⟩

/-- Canonical32-child witness reduction is justified by checked endpoint-gauge
closure, rather than an assumed global222-pose frame lift. -/
theorem RegisteredWorld.canonical_parent_witness {d : ℕ} (W : RegisteredWorld d)
    (hd : 2 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : CoversCanonicalChildren σ C)
    (hGauge : GaugeClosed r L) (hl : W.Legal L)
    {P Q : Pose d} (hP : CompleteParent σ r W.tiles P) (hQ : CompleteParent σ r W.tiles Q)
    (hne : physicalClass r hr P ≠ physicalClass r hr Q)
    {c b : Cell d} (hPc : ParentOccupies P c) (hQb : ParentOccupies Q b)
    (hadj : AdjacentCells c b) :
    ∃ a ∈ C, ∃ b ∈ C, ∃ k ∈ L, normalize P Q = parentCandidate a b k := by
  obtain ⟨s, hs, ⟨u, hu, hus⟩, hsc⟩ := hP.owns_cell hPc
  obtain ⟨t, ht, ⟨v, hv, hvt⟩, htb⟩ := hQ.owns_cell hQb
  have hst : s ≠ t := by
    intro h
    subst t
    exact hne (complete_parent_unique hd hr he W.tiles W.disjoint hP hQ
      ⟨u, hu, hus⟩ ⟨v, hv, hvt⟩)
  have hk := hGauge.normal_congr hr (hus.symm hr) (hvt.symm hr)
    (hl s hs t ht hst ⟨c, b, hsc, htb, hadj⟩)
  obtain ⟨a, ha, rfl⟩ := canonical_child_form hC P hu
  obtain ⟨b, hb, rfl⟩ := canonical_child_form hC Q hv
  exact ⟨a, ha, b, hb, _, hk, parent_witness_reconstruction P Q a b⟩

#print axioms GaugeClosed.normal_congr
#print axioms RegisteredWorld.canonical_parent_witness
end SparseMonotiles.CarrierHierarchy
