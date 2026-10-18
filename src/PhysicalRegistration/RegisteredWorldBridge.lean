module

public import PhysicalRegistration.PhysicalProfileLaw
public import RegisteredPrime.FiniteSupertiles

@[expose] public section

/-! Exact bridge to the pre-existing integer-cell RegisteredWorld. The row
convention and negative-cell correction are explicit. A world is constructed
from physical coverage and retained-core nonoverlap, not supplied as input. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- The original registered hierarchy's row-convention pose, from an actual
signed column permutation and integer translation. -/
def poseFromColumnData {m : ℕ} (p : Equiv.Perm (Fin (m+1)))
    (b : Fin (m+1) → Bool) (t : LatticeIndex m) : RegisteredPrime.Pose (m+1) where
  frame := {
    perm := p.symm
    inverse := p
    left_inverse := p.apply_symm_apply
    right_inverse := p.symm_apply_apply
    negative := fun i => !(b (p.symm i)) }
  anchor := t

/-- The literal real-coordinate meaning of a hierarchy pose. -/
def RegisteredPoseRealizes {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (e : Space m ≃ᵢ Space m) : Prop :=
  ∀ (x : Space m) (i : Fin (m+1)), e x i =
    (q.frame.sign i : ℝ) * x (q.frame.perm i) + (q.anchor i : ℝ)

theorem poseFromColumnData_cell {m : ℕ} (p : Equiv.Perm (Fin (m+1)))
    (b : Fin (m+1) → Bool) (t z : LatticeIndex m) :
    (poseFromColumnData p b t).cell z = integralCellIndex p b t z := by
  funext i
  unfold RegisteredPrime.Pose.cell RegisteredPrime.RegisteredFrame.linear
    RegisteredPrime.RegisteredFrame.sign RegisteredPrime.bit poseFromColumnData integralCellIndex
  cases h : b (p.symm i) <;> simp [h] <;> omega

theorem exists_registeredPoseRealizes {m : ℕ} (e : Space m ≃ᵢ Space m)
    (he : HasIntegralSignedPermutation e) :
    ∃ q : RegisteredPrime.Pose (m+1), RegisteredPoseRealizes q e := by
  obtain ⟨p, b, t, hb, ht⟩ := he
  refine ⟨poseFromColumnData p b t, ?_⟩
  intro x i
  have h := integral_signed_permutation_apply e p b t hb ht x (p.symm i)
  rw [p.apply_symm_apply] at h
  cases hbi : b (p.symm i) <;>
    simpa [poseFromColumnData, RegisteredPrime.RegisteredFrame.sign, sign, hbi] using h

theorem cellIndex_unitChairCell {m : ℕ} (c : Cell m) :
    RegisteredPrime.UnitChairCell (cellIndex c) := by
  constructor
  · intro i
    cases hc : c.val i <;> simp [cellIndex, hc]
  · have hnot : ¬ ∀ i, c.val i = true := by
      intro h
      exact c.property (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    refine ⟨i, ?_⟩
    cases hc : c.val i <;> simp_all [cellIndex]

theorem unitChairCell_exists_native {m : ℕ} (z : LatticeIndex m)
    (hz : RegisteredPrime.UnitChairCell z) : ∃ c : Cell m, cellIndex c = z := by
  let c : Cell m := ⟨fun i => decide (z i = 1), by
    intro h
    obtain ⟨i, hi⟩ := hz.2
    have hh := congrFun h i
    simp [hi] at hh⟩
  refine ⟨c, ?_⟩
  funext i
  rcases hz.1 i with h | h <;> simp [cellIndex, c, h]

theorem occupies_iff_native_cell {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (z : LatticeIndex m) :
    RegisteredPrime.Occupies q z ↔ ∃ c : Cell m, q.cell (cellIndex c) = z := by
  constructor
  · rintro ⟨b, hb, hcell⟩
    obtain ⟨c, rfl⟩ := unitChairCell_exists_native b hb
    exact ⟨c, hcell⟩
  · rintro ⟨c, hc⟩
    exact ⟨cellIndex c, cellIndex_unitChairCell c, hc⟩

/-- The negative-cell correction is exactly the one needed for actual center
transport; there is no half-integral or offset alignment assumption. -/
theorem RegisteredPoseRealizes.map_latticeCenter {m : ℕ}
    {q : RegisteredPrime.Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (h : RegisteredPoseRealizes q e) (z : LatticeIndex m) :
    e (latticeCenter z) = latticeCenter (q.cell z) := by
  ext i
  rw [h]
  change (q.frame.sign i : ℝ) * ((z (q.frame.perm i) : ℝ) + 1 / 2) +
    (q.anchor i : ℝ) = (q.cell z i : ℝ) + 1 / 2
  unfold RegisteredPrime.Pose.cell RegisteredPrime.RegisteredFrame.linear
    RegisteredPrime.RegisteredFrame.sign RegisteredPrime.bit
  cases hneg : q.frame.negative i <;> simp [hneg] <;> ring

/-- The actual registered pose range covers every integer cell. -/
theorem PhysicalTiling.selectedPoses_cover
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    (z : LatticeIndex m) : ∃ i, RegisteredPrime.Occupies (q i) z := by
  obtain ⟨i, _, c, hc⟩ := T.componentCell_all hm root z
  refine ⟨i, (occupies_iff_native_cell (q i) z).mpr ⟨c, ?_⟩⟩
  apply latticeCenter_injective
  have hh := (hq i).map_latticeCenter (cellIndex c)
  rw [latticeCenter_cellIndex] at hh
  exact hh.symm.trans hc

/-- Actual physical interior disjointness gives uniqueness of cell-owning
selected poses. Marked-frame nonoverlap is not an extra assumption. -/
theorem PhysicalTiling.selectedPoses_nonoverlap
    {m J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    {i j : ι} (z : LatticeIndex m)
    (hi : RegisteredPrime.Occupies (q i) z) (hj : RegisteredPrime.Occupies (q j) z) :
    i = j := by
  obtain ⟨c, hc⟩ := (occupies_iff_native_cell (q i) z).mp hi
  obtain ⟨d, hd⟩ := (occupies_iff_native_cell (q j) z).mp hj
  apply T.relative_cellCenter_owner_unique root c d
  have hci := (hq i).map_latticeCenter (cellIndex c)
  have hdj := (hq j).map_latticeCenter (cellIndex d)
  rw [latticeCenter_cellIndex, hc] at hci
  rw [latticeCenter_cellIndex, hd] at hdj
  exact hci.trans hdj.symm

/-- The literal hierarchy world extracted from selected physical pose
representatives, with complete coverage and nonoverlap proved. -/
def PhysicalTiling.selectedRegisteredWorld
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i))) :
    RegisteredPrime.RegisteredWorld (m+1) where
  tiles := fun r => ∃ i, q i = r
  covers := by
    intro z
    obtain ⟨i, hi⟩ := T.selectedPoses_cover hm root q hq z
    exact ⟨q i, ⟨i, rfl⟩, hi⟩
  nonoverlap := by
    rintro r s ⟨i, rfl⟩ ⟨j, rfl⟩ z hi hj
    have he := T.selectedPoses_nonoverlap root q hq z hi hj
    subst j
    exact RegisteredPrime.Pose.Same.refl _

/-- An actual registered world and real pose binding exist for every
arbitrary-isometry physical tiling. No initial registered world is supplied. -/
theorem PhysicalTiling.exists_registeredWorld
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) :
    ∃ (q : ι → RegisteredPrime.Pose (m+1)) (W : RegisteredPrime.RegisteredWorld (m+1)),
      (∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i))) ∧
      W.tiles = fun r => ∃ i, q i = r := by
  have he : ∀ i, ∃ q, RegisteredPoseRealizes q (relativePlacement (f root) (f i)) :=
    fun i => exists_registeredPoseRealizes _ (T.global_integral_registration hm root i)
  choose q hq using he
  exact ⟨q, T.selectedRegisteredWorld hm root q hq, hq, rfl⟩

end
end PhysicalRegistration.NativeChair
