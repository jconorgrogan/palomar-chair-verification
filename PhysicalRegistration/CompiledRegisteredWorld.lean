module

public import PhysicalRegistration.UnmarkedPeriodTransfer

@[expose] public section

/-! Exact properness and full-profile laws on the actual historical world
extracted from a graph-compiled unmarked physical tiling. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

@[simp] theorem poseIsometry_inv {m : ℕ} (q : RegisteredPrime.Pose (m+1)) :
    poseIsometry q.inv = (poseIsometry q).symm := by
  apply IsometryEquiv.ext
  intro x
  apply (poseIsometry q).injective
  have h := congrArg (fun e : Space m ≃ᵢ Space m => e x) (poseIsometry_comp q q.inv)
  rw [RegisteredPrime.Pose.comp_inv, poseIsometry_identity] at h
  change x = poseIsometry q (poseIsometry q.inv x) at h
  simpa only [IsometryEquiv.apply_symm_apply] using h.symm

/-- The old row-pose relative operation is the literal relative isometry. -/
theorem poseIsometry_relative {m : ℕ} (q r : RegisteredPrime.Pose (m+1)) :
    poseIsometry (q.relative r) = relativePlacement (poseIsometry q) (poseIsometry r) := by
  rw [RegisteredPrime.Pose.relative, poseIsometry_comp, poseIsometry_inv]
  rfl

/-- A common ambient normalization cancels from relative placements. -/
theorem relativePlacement_normalized {m : ℕ} (h f g : Space m ≃ᵢ Space m) :
    relativePlacement (relativePlacement h f) (relativePlacement h g) = relativePlacement f g := by
  apply IsometryEquiv.ext
  intro x
  simp [relativePlacement]

/-- Exact pose binding is compatible with relative maps in the original world. -/
theorem RegisteredPoseRealizes.relative {m : ℕ}
    {q r : RegisteredPrime.Pose (m+1)} {h f g : Space m ≃ᵢ Space m}
    (hq : RegisteredPoseRealizes q (relativePlacement h f))
    (hr : RegisteredPoseRealizes r (relativePlacement h g)) :
    RegisteredPoseRealizes (q.relative r) (relativePlacement f g) := by
  have he : poseIsometry (q.relative r) = relativePlacement f g := by
    rw [poseIsometry_relative, ← hq.eq_poseIsometry, ← hr.eq_poseIsometry,
      relativePlacement_normalized]
  rw [← he]
  exact poseIsometry_realizes _

/-- The genuine world extracted from graph-compiled coefficients has proper
historical signed frames; physical placements were not required to be proper. -/
theorem PhysicalTiling.compiled_selected_world_proper
    {m : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients hm A hA) f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    (W : RegisteredPrime.RegisteredWorld (m+1)) (hW : W.tiles = Set.range q) : W.Proper := by
  intro r hr
  rw [hW] at hr
  obtain ⟨i, rfl⟩ := hr
  exact (hq i).isProper_iff.mp (T.compiled_global_proper_integral_registration hm A hA root i).2

/-- The actual full profile equations hold for every pair in the extracted
world, interpreted through the exact original relative-pose operation. -/
theorem PhysicalTiling.selected_world_fullProfileMating
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι)
    (q : ι → RegisteredPrime.Pose (m+1))
    (hq : ∀ i, RegisteredPoseRealizes (q i) (relativePlacement (f root) (f i)))
    (W : RegisteredPrime.RegisteredWorld (m+1)) (hW : W.tiles = Set.range q) :
    ∀ r s, W.tiles r → W.tiles s →
      FullProfileMating a (poseIsometry (r.relative s)) := by
  intro r s hr hs
  rw [hW] at hr hs
  obtain ⟨i, rfl⟩ := hr
  obtain ⟨j, rfl⟩ := hs
  rw [← ((hq i).relative (hq j)).eq_poseIsometry]
  exact T.full_profile_mating hm i j

/-- The physical-to-historical interface needed for arithmetic language
closure: proper world, literal full-profile matching, and simultaneous
unmarked-period lifting all follow from the unmarked physical tiling alone. -/
theorem compiled_unmarked_exists_world
    {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {tiles : Set (Set (Space m))}
    (ht : SparseMonotiles.IsTiling (body (compiledCoefficients hm A hA)) tiles) :
    ∃ (g : tiles → Space m ≃ᵢ Space m) (root : tiles)
      (q : tiles → RegisteredPrime.Pose (m+1))
      (W : RegisteredPrime.RegisteredWorld (m+1)),
      PhysicalTiling (compiledCoefficients hm A hA) g ∧
      (∀ B : tiles, (B : Set (Space m)) = g B '' body (compiledCoefficients hm A hA)) ∧
      (∀ B, RegisteredPoseRealizes (q B) (relativePlacement (g root) (g B))) ∧
      W.tiles = Set.range q ∧ W.Proper ∧
      (∀ r s, W.tiles r → W.tiles s →
        FullProfileMating (compiledCoefficients hm A hA) (poseIsometry (r.relative s))) ∧
      ∀ v, SparseMonotiles.IsPeriod tiles v →
        ∃ w : LatticeIndex m, placedNormal (g root).symm v = integerPoint w ∧
          RegisteredPrime.AtlasPeriods.TranslationPeriod W w := by
  obtain ⟨g, root, q, W, T, hg, hq, hW, hp⟩ :=
    unmarked_exists_registeredWorld_with_period_lift hm ht
  exact ⟨g, root, q, W, T, hg, hq, hW,
    T.compiled_selected_world_proper hm A hA root q hq W hW,
    T.selected_world_fullProfileMating hm root q hq W hW, hp⟩

end
end PhysicalRegistration.NativeChair
