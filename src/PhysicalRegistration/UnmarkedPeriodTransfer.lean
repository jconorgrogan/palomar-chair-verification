module

public import PhysicalRegistration.RegisteredPoseProperness
public import SparseMonotiles.CompactTranslationFrames
public import AtlasPeriods.Translation

@[expose] public section

/-! Genuine periods of an unmarked physical tile collection lift to integer
periods of its actual extracted registered world. Frames are selected
translation-equivariantly even when the body has self-symmetries. -/
namespace SparseMonotiles
open Set

@[simp] theorem translate_neg_cancel {d : ℕ} (v : Point d) (A : Set (Point d)) :
    translate (-v) (translate v A) = A := by
  simp only [translate, Set.image_image]
  have hf : (fun x : Point d => (x+v)+ -v) = id := by funext x; simp
  rw [hf, Set.image_id]

@[simp] theorem translate_add_neg_cancel {d : ℕ} (v : Point d) (A : Set (Point d)) :
    translate v (translate (-v) A) = A := by
  simpa only [neg_neg] using translate_neg_cancel (-v) A

theorem IsPeriod.neg {d : ℕ} {tiles : Set (Set (Point d))} {v : Point d}
    (hv : IsPeriod tiles v) : IsPeriod tiles (-v) := by
  intro A
  simpa only [translate_add_neg_cancel] using (hv (translate (-v) A)).symm

def periodTile {d : ℕ} {tiles : Set (Set (Point d))}
    {v : Point d} (hv : IsPeriod tiles v) (A : tiles) : tiles :=
  ⟨translate v A, (hv A).mp A.property⟩

@[simp] theorem periodTile_neg {d : ℕ} {tiles : Set (Set (Point d))}
    {v : Point d} (hv : IsPeriod tiles v) (A : tiles) :
    periodTile hv (periodTile hv.neg A) = A := by
  apply Subtype.ext
  exact translate_add_neg_cancel v A

end SparseMonotiles
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- Set-indexed physical representatives satisfy the literal native tiling
hypothesis, without any assumptions on their chosen orientations. -/
theorem unmarked_representatives_physicalTiling {m J : ℕ} [NeZero m]
    {a : Coefficients m J} {tiles : Set (Set (Space m))}
    (ht : SparseMonotiles.IsTiling (body a) tiles)
    (g : tiles → Space m ≃ᵢ Space m)
    (hg : ∀ A : tiles, (A : Set (Space m)) = g A '' body a) :
    PhysicalTiling a g where
  interiors_disjoint := by
    intro A B hne
    have hAB : (A : Set (Space m)) ≠ B := fun h => hne (Subtype.ext h)
    simpa only [hg A, hg B, placedBody] using ht.2.2 A A.property B B.property hAB
  covers := by
    intro x
    obtain ⟨A, hA, hx⟩ := ht.2.1 x
    refine ⟨⟨A, hA⟩, ?_⟩
    have he := hg ⟨A, hA⟩
    change A = g ⟨A,hA⟩ '' body a at he
    change x ∈ g ⟨A,hA⟩ '' body a
    rwa [← he]

/-- Compactness supplies actual frames that commute with every physical
period simultaneously and satisfy the proved geometric tiling interface. -/
theorem unmarked_exists_equivariant_physicalTiling {m J : ℕ} [NeZero m]
    {a : Coefficients m J} {tiles : Set (Set (Space m))}
    (ht : SparseMonotiles.IsTiling (body a) tiles) :
    ∃ g : tiles → Space m ≃ᵢ Space m,
      PhysicalTiling a g ∧
      (∀ A : tiles, (A : Set (Space m)) = g A '' body a) ∧
      ∀ v, ∀ hp : SparseMonotiles.IsPeriod tiles v, ∀ A : tiles,
        g (SparseMonotiles.periodTile hp A) =
          (g A).trans (SparseMonotiles.translationIsometry v) := by
  obtain ⟨g, hg, he⟩ := ht.exists_translation_equivariant_representatives (body_isCompact a)
  exact ⟨g, unmarked_representatives_physicalTiling ht g hg, hg, he⟩

@[simp] theorem integerPoint_zero {m : ℕ} : integerPoint (0 : LatticeIndex m) = 0 := by
  ext i
  simp [integerPoint]

/-- Translation in the recovered marked-pose model is literal translation
of the Euclidean realization. -/
theorem poseIsometry_translate {m : ℕ} (w : LatticeIndex m)
    (q : RegisteredPrime.Pose (m+1)) (x : Space m) :
    poseIsometry (RegisteredPrime.AtlasPeriods.translate w q) x =
      poseIsometry q x + integerPoint w := by
  ext i
  simp [poseIsometry_apply, RegisteredPrime.AtlasPeriods.translate, integerPoint]
  ring

theorem registered_translate_neg_cancel {m : ℕ} (w : LatticeIndex m)
    (q : RegisteredPrime.Pose (m+1)) :
    RegisteredPrime.AtlasPeriods.translate (-w)
      (RegisteredPrime.AtlasPeriods.translate w q) = q := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  simp [RegisteredPrime.AtlasPeriods.translate]

/-- Every physical period lifts to an integer translation of the actual
pose range. The integer vector is constructed from two actual anchors. -/
theorem unmarked_period_lifts_to_integer_pose_period {m : ℕ}
    {tiles : Set (Set (Space m))}
    (g : tiles → Space m ≃ᵢ Space m) (root : tiles)
    (hequiv : ∀ v, ∀ hv : SparseMonotiles.IsPeriod tiles v, ∀ A : tiles,
      g (SparseMonotiles.periodTile hv A) =
        (g A).trans (SparseMonotiles.translationIsometry v))
    (q : tiles → RegisteredPrime.Pose (m+1))
    (hq : ∀ A, RegisteredPoseRealizes (q A) (relativePlacement (g root) (g A)))
    {v : Space m} (hv : SparseMonotiles.IsPeriod tiles v) :
    ∃ w : LatticeIndex m, placedNormal (g root).symm v = integerPoint w ∧
      ∀ p, p ∈ Set.range q ↔ RegisteredPrime.AtlasPeriods.translate w p ∈ Set.range q := by
  let w : LatticeIndex m := fun i =>
    (q (SparseMonotiles.periodTile hv root)).anchor i - (q root).anchor i
  have hmove (B : tiles) (x : Space m) :
      poseIsometry (q (SparseMonotiles.periodTile hv B)) x =
        poseIsometry (q B) x + placedNormal (g root).symm v := by
    rw [← (hq _).eq_poseIsometry, ← (hq B).eq_poseIsometry]
    change (g root).symm (g (SparseMonotiles.periodTile hv B) x) =
      (g root).symm (g B x) + placedNormal (g root).symm v
    rw [hequiv]
    change (g root).symm (g B x + v) = _
    simpa using isometry_map_add_smul (g root).symm (g B x) v 1
  have hw : placedNormal (g root).symm v = integerPoint w := by
    ext i
    have h := congrArg (fun x : Space m => x i) (hmove root 0)
    simp only [poseIsometry_apply, PiLp.zero_apply, mul_zero, zero_add, PiLp.add_apply] at h
    change _ = (w i : ℝ)
    dsimp [w]
    push_cast
    linarith
  have hqmove (B : tiles) : q (SparseMonotiles.periodTile hv B) =
      RegisteredPrime.AtlasPeriods.translate w (q B) := by
    apply poseIsometry_injective
    apply IsometryEquiv.ext
    intro x
    rw [hmove, hw, poseIsometry_translate]
  refine ⟨w, hw, ?_⟩
  intro p
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨SparseMonotiles.periodTile hv B, hqmove B⟩
  · rintro ⟨B, hB⟩
    refine ⟨SparseMonotiles.periodTile hv.neg B, ?_⟩
    have h := hqmove (SparseMonotiles.periodTile hv.neg B)
    rw [SparseMonotiles.periodTile_neg, hB] at h
    have h' := congrArg (RegisteredPrime.AtlasPeriods.translate (-w)) h
    simpa only [registered_translate_neg_cancel] using h'.symm

/-- The registered zero-period endpoint therefore applies to the original
unmarked collection, not only to a chosen system of marked representatives. -/
theorem unmarked_period_zero_of_registered_world {m : ℕ}
    {tiles : Set (Set (Space m))}
    (g : tiles → Space m ≃ᵢ Space m) (root : tiles)
    (hequiv : ∀ v, ∀ hv : SparseMonotiles.IsPeriod tiles v, ∀ A : tiles,
      g (SparseMonotiles.periodTile hv A) =
        (g A).trans (SparseMonotiles.translationIsometry v))
    (q : tiles → RegisteredPrime.Pose (m+1))
    (hq : ∀ A, RegisteredPoseRealizes (q A) (relativePlacement (g root) (g A)))
    (W : RegisteredPrime.RegisteredWorld (m+1)) (hW : W.tiles = Set.range q)
    (hzero : ∀ w, RegisteredPrime.AtlasPeriods.TranslationPeriod W w → w = 0)
    {v : Space m} (hv : SparseMonotiles.IsPeriod tiles v) : v = 0 := by
  obtain ⟨w, hw, hp⟩ := unmarked_period_lifts_to_integer_pose_period g root hequiv q hq hv
  have hw0 : w = 0 := hzero w (by
    unfold RegisteredPrime.AtlasPeriods.TranslationPeriod
    rw [hW]
    exact hp)
  rw [hw0, integerPoint_zero] at hw
  exact (g root).symm.toRealAffineIsometryEquiv.linearIsometryEquiv.injective (by simpa [placedNormal] using hw)


/-- Unconditional extraction from an unmarked physical tiling: a genuine
registered world exists, and every physical period becomes one of its integer
periods in a single common coordinate frame. Language legality is separate. -/
theorem unmarked_exists_registeredWorld_with_period_lift
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {a : Coefficients m J} {tiles : Set (Set (Space m))}
    (ht : SparseMonotiles.IsTiling (body a) tiles) :
    ∃ (g : tiles → Space m ≃ᵢ Space m) (root : tiles)
      (q : tiles → RegisteredPrime.Pose (m+1))
      (W : RegisteredPrime.RegisteredWorld (m+1)),
      PhysicalTiling a g ∧
      (∀ A : tiles, (A : Set (Space m)) = g A '' body a) ∧
      (∀ A, RegisteredPoseRealizes (q A) (relativePlacement (g root) (g A))) ∧
      W.tiles = Set.range q ∧
      ∀ v, SparseMonotiles.IsPeriod tiles v →
        ∃ w : LatticeIndex m, placedNormal (g root).symm v = integerPoint w ∧
          RegisteredPrime.AtlasPeriods.TranslationPeriod W w := by
  obtain ⟨g, T, hg, hequiv⟩ := unmarked_exists_equivariant_physicalTiling ht
  obtain ⟨A, hA, _⟩ := ht.2.1 (0 : Space m)
  let root : tiles := ⟨A, hA⟩
  obtain ⟨q, W, hq, hW⟩ := T.exists_registeredWorld hm root
  refine ⟨g, root, q, W, T, hg, hq, hW, ?_⟩
  intro v hv
  obtain ⟨w, hw, hp⟩ := unmarked_period_lifts_to_integer_pose_period g root hequiv q hq hv
  refine ⟨w, hw, ?_⟩
  unfold RegisteredPrime.AtlasPeriods.TranslationPeriod
  rw [hW]
  exact hp

end
end PhysicalRegistration.NativeChair
