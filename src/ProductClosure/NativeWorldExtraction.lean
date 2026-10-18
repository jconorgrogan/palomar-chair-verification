module

public import ProductClosure.PhysicalProfileLaw
public import ProductClosure.RegisteredTubeOwners
public import ProductClosure.ProductWorldRealization
public import PhysicalRegistration.RegisteredPoseProperness

@[expose] public section

/-! Actual arbitrary physical placements determine a complete finite-cell
registered world. No chair occupancy or registered-world assumption is used. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}
variable [Nonempty (Polycube.Cell S)]

/-- The old real pose predicate is carrier-independent and transports the
literal centers of arbitrary integer cells. -/
theorem registeredPoseRealizes_map_latticeCenter
    {q : RegisteredPrime.Pose (m + 1)} {e : Space m ≃ᵢ Space m}
    (h : RegisteredPoseRealizes q e) (z : LatticeIndex m) :
    e (latticeCenter z) = latticeCenter (q.cell z) := h.map_latticeCenter z

theorem PhysicalTiling.selectedPoses_cover
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    (z : LatticeIndex m) : ∃ i, z ∈ World.placedCells S (q i) := by
  obtain ⟨i, _, c, hc⟩ := T.componentCell_all hm root z
  refine ⟨i, (occupies_iff_native_cell (q i) z).mpr ⟨c, ?_⟩⟩
  apply latticeCenter_injective
  have hh := registeredPoseRealizes_map_latticeCenter (hq i) (cellIndex c)
  rw [latticeCenter_cellIndex] at hh
  exact hh.symm.trans hc

/-- Retained cell centers force unique physical ownership of each lattice cell. -/
theorem PhysicalTiling.selectedPoses_nonoverlap
    {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    {i j : ι} (z : LatticeIndex m)
    (hi : z ∈ World.placedCells S (q i)) (hj : z ∈ World.placedCells S (q j)) : i = j := by
  obtain ⟨c, hc⟩ := (occupies_iff_native_cell (q i) z).mp hi
  obtain ⟨d, hd⟩ := (occupies_iff_native_cell (q j) z).mp hj
  apply T.relative_cellCenter_owner_unique root c d
  have hci := registeredPoseRealizes_map_latticeCenter (hq i) (cellIndex c)
  have hdj := registeredPoseRealizes_map_latticeCenter (hq j) (cellIndex d)
  rw [latticeCenter_cellIndex, hc] at hci
  rw [latticeCenter_cellIndex, hd] at hdj
  exact hci.trans hdj.symm

/-- Complete actual occupancy, extracted from the literal physical tiling. -/
def PhysicalTiling.selectedCellWorld
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i))) :
    World.CompleteTiling (World.placedCells S) where
  tiles := Set.range q
  cover z := by
    obtain ⟨i, hi⟩ := T.selectedPoses_cover hm root q hq z
    exact ⟨q i, ⟨i, rfl⟩, hi⟩
  disjoint := by
    rintro r ⟨i, rfl⟩ s ⟨j, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact hne (congrArg q (T.selectedPoses_nonoverlap root q hq z hi hj))
  nonempty := by
    intro r _
    obtain ⟨c⟩ := (inferInstance : Nonempty (Polycube.Cell S))
    exact World.placedCells_nonempty ⟨c.val, c.property⟩ r

/-- Every actual physical tiling yields registered poses and a complete
finite-cell world in one common root coordinate system. -/
theorem PhysicalTiling.exists_cellWorld
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) :
    ∃ (q : ι → RegisteredPrime.Pose (m+1)) (W : World.CompleteTiling (World.placedCells S)),
      (∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i))) ∧
      W.tiles = Set.range q := by
  have he : ∀ i, ∃ q, RegisteredPoseRealizes q (relativePlacement (f root) (f i)) :=
    fun i => exists_registeredPoseRealizes _ (T.global_integral_registration hm root i)
  choose q hq using he
  exact ⟨q, T.selectedCellWorld hm root q hq, hq, rfl⟩

/-- Common normalization cancels exactly from a relative placement. -/
theorem relativePlacement_normalized (h f g : Space m ≃ᵢ Space m) :
    relativePlacement (relativePlacement h f) (relativePlacement h g) = relativePlacement f g := by
  apply IsometryEquiv.ext
  intro x
  simp [relativePlacement]

theorem registeredPoseRealizes_relative
    {q r : RegisteredPrime.Pose (m+1)} {h f g : Space m ≃ᵢ Space m}
    (hq : RegisteredPoseRealizes q (relativePlacement h f))
    (hr : RegisteredPoseRealizes r (relativePlacement h g)) :
    RegisteredPoseRealizes (q.relative r) (relativePlacement f g) := by
  have he : poseIsometry (q.relative r) = relativePlacement f g := by
    rw [poseIsometry_relative, ← hq.eq_poseIsometry, ← hr.eq_poseIsometry,
      relativePlacement_normalized]
  rw [← he]
  exact poseIsometry_realizes _

/-- All full site-profile equations hold on every pair of extracted world poses. -/
theorem PhysicalTiling.selected_world_fullProfileMating
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    (W : World.CompleteTiling (World.placedCells S)) (hW : W.tiles = Set.range q) :
    ∀ r s, r ∈ W.tiles → s ∈ W.tiles →
      FullProfileMating a (poseIsometry (r.relative s)) := by
  intro r s hr hs
  rw [hW] at hr hs
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hs
  rw [← (registeredPoseRealizes_relative (hq i) (hq j)).eq_poseIsometry]
  exact T.full_profile_mating hm i j

/-- Graph-compiled physical tilings recover proper full marked poses too. -/
theorem PhysicalTiling.compiled_selected_world_proper
    [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients (S := S) hm A hA) f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    (W : World.CompleteTiling (World.placedCells S)) (hW : W.tiles = Set.range q) :
    ∀ r ∈ W.tiles, r.frame.IsProper := by
  intro r hr
  rw [hW] at hr
  obtain ⟨i, rfl⟩ := hr
  exact (hq i).isProper_iff.mp (T.compiled_global_proper_integral_registration hm A hA root i).2

#print axioms PhysicalTiling.exists_cellWorld
#print axioms PhysicalTiling.selected_world_fullProfileMating
#print axioms PhysicalTiling.compiled_selected_world_proper
end
end ProductClosure.NativeCompiler
