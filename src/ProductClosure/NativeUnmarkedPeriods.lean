module

public import ProductClosure.NativeWorldExtraction
public import PhysicalRegistration.UnmarkedPeriodTransfer

@[expose] public section

/-! Arbitrary unmarked physical tilings yield complete finite-cell pose worlds.
All physical periods lift simultaneously to literal pose-set translations. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}
variable [Nonempty (Polycube.Cell S)]

theorem unmarked_representatives_physicalTiling {J : ℕ} [NeZero m]
    {a : Coefficients S J} {tiles : Set (Set (Space m))}
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

/-- Compactness supplies frame representatives equivariant under every
physical translation period, even when the body has self-isometries. -/
theorem unmarked_exists_equivariant_physicalTiling {J : ℕ} [NeZero m]
    {a : Coefficients S J} {tiles : Set (Set (Space m))}
    (ht : SparseMonotiles.IsTiling (body a) tiles) :
    ∃ g : tiles → Space m ≃ᵢ Space m,
      PhysicalTiling a g ∧
      (∀ A : tiles, (A : Set (Space m)) = g A '' body a) ∧
      ∀ v, ∀ hp : SparseMonotiles.IsPeriod tiles v, ∀ A : tiles,
        g (SparseMonotiles.periodTile hp A) =
          (g A).trans (SparseMonotiles.translationIsometry v) := by
  obtain ⟨g, hg, he⟩ := ht.exists_translation_equivariant_representatives (body_isCompact a)
  exact ⟨g, unmarked_representatives_physicalTiling ht g hg, hg, he⟩

/-- The carrier-independent compact frame argument produces an integer
translation of the exact recovered pose range. -/
theorem unmarked_period_lifts_to_integer_pose_period
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
  exact PhysicalRegistration.NativeChair.unmarked_period_lifts_to_integer_pose_period
    g root hequiv q hq hv

/-- Membership invariance under the genuine bijective pose translation is
exact equality of the translated full pose set. -/
theorem cellWorld_hasStatePeriod_of_iff
    (W : World.CompleteTiling (World.placedCells S)) (w : LatticeIndex m)
    (hp : ∀ p, p ∈ W.tiles ↔ RegisteredPrime.AtlasPeriods.translate w p ∈ W.tiles) :
    W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate w) := by
  change RegisteredPrime.AtlasPeriods.translate w '' W.tiles = W.tiles
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hp q).mp hq
  · intro hmem
    have he : RegisteredPrime.AtlasPeriods.translate w
        (RegisteredPrime.AtlasPeriods.translate (-w) p) = p := by
      simpa only [neg_neg] using registered_translate_neg_cancel (-w) p
    refine ⟨RegisteredPrime.AtlasPeriods.translate (-w) p, ?_, he⟩
    apply (hp _).mpr
    rwa [he]

/-- Zero literal pose-set periods imply zero physical periods. -/
theorem unmarked_period_zero_of_cellWorld
    {tiles : Set (Set (Space m))}
    (g : tiles → Space m ≃ᵢ Space m) (root : tiles)
    (hequiv : ∀ v, ∀ hv : SparseMonotiles.IsPeriod tiles v, ∀ A : tiles,
      g (SparseMonotiles.periodTile hv A) =
        (g A).trans (SparseMonotiles.translationIsometry v))
    (q : tiles → RegisteredPrime.Pose (m+1))
    (hq : ∀ A, RegisteredPoseRealizes (q A) (relativePlacement (g root) (g A)))
    (W : World.CompleteTiling (World.placedCells S)) (hW : W.tiles = Set.range q)
    (hzero : ∀ w, W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate w) → w = 0)
    {v : Space m} (hv : SparseMonotiles.IsPeriod tiles v) : v = 0 := by
  obtain ⟨w, hw, hp⟩ := unmarked_period_lifts_to_integer_pose_period g root hequiv q hq hv
  have hw0 : w = 0 := hzero w (cellWorld_hasStatePeriod_of_iff W w (by rwa [hW]))
  rw [hw0, integerPoint_zero] at hw
  exact (g root).symm.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    (by simpa [placedNormal] using hw)

/-- Complete physical-to-world extraction with full profiles and simultaneous
lifting of every unmarked physical period to the literal pose-set action. -/
theorem unmarked_exists_cellWorld_with_period_lift
    {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {a : Coefficients S J} {tiles : Set (Set (Space m))}
    (ht : SparseMonotiles.IsTiling (body a) tiles) :
    ∃ (g : tiles → Space m ≃ᵢ Space m) (root : tiles)
      (q : tiles → RegisteredPrime.Pose (m+1))
      (W : World.CompleteTiling (World.placedCells S)),
      PhysicalTiling a g ∧
      (∀ A : tiles, (A : Set (Space m)) = g A '' body a) ∧
      (∀ A, RegisteredPoseRealizes (q A) (relativePlacement (g root) (g A))) ∧
      W.tiles = Set.range q ∧
      (∀ r s, r ∈ W.tiles → s ∈ W.tiles →
        FullProfileMating a (poseIsometry (r.relative s))) ∧
      ∀ v, SparseMonotiles.IsPeriod tiles v →
        ∃ w : LatticeIndex m, placedNormal (g root).symm v = integerPoint w ∧
          W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate w) := by
  obtain ⟨g, T, hg, hequiv⟩ := unmarked_exists_equivariant_physicalTiling ht
  obtain ⟨A, hA, _⟩ := ht.2.1 (0 : Space m)
  let root : tiles := ⟨A, hA⟩
  obtain ⟨q, W, hq, hW⟩ := T.exists_cellWorld hm root
  refine ⟨g, root, q, W, T, hg, hq, hW,
    T.selected_world_fullProfileMating hm root q hq W hW, ?_⟩
  intro v hv
  obtain ⟨w, hw, hp⟩ := unmarked_period_lifts_to_integer_pose_period g root hequiv q hq hv
  exact ⟨w, hw, cellWorld_hasStatePeriod_of_iff W w (by rwa [hW])⟩

/-- The graph compiler additionally recovers proper full marked poses, while
physical input placements remain entirely unrestricted. -/
theorem compiled_unmarked_exists_cellWorld
    [NeZero m] (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {tiles : Set (Set (Space m))}
    (ht : SparseMonotiles.IsTiling (body (compiledCoefficients (S := S) hm A hA)) tiles) :
    ∃ (g : tiles → Space m ≃ᵢ Space m) (root : tiles)
      (q : tiles → RegisteredPrime.Pose (m+1))
      (W : World.CompleteTiling (World.placedCells S)),
      PhysicalTiling (compiledCoefficients (S := S) hm A hA) g ∧
      (∀ B : tiles, (B : Set (Space m)) = g B '' body (compiledCoefficients (S := S) hm A hA)) ∧
      (∀ B, RegisteredPoseRealizes (q B) (relativePlacement (g root) (g B))) ∧
      W.tiles = Set.range q ∧ (∀ r ∈ W.tiles, r.frame.IsProper) ∧
      (∀ r s, r ∈ W.tiles → s ∈ W.tiles →
        FullProfileMating (compiledCoefficients (S := S) hm A hA) (poseIsometry (r.relative s))) ∧
      ∀ v, SparseMonotiles.IsPeriod tiles v →
        ∃ w : LatticeIndex m, placedNormal (g root).symm v = integerPoint w ∧
          W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate w) := by
  obtain ⟨g, root, q, W, T, hg, hq, hW, hprofile, hp⟩ :=
    unmarked_exists_cellWorld_with_period_lift hm ht
  exact ⟨g, root, q, W, T, hg, hq, hW,
    T.compiled_selected_world_proper hm A hA root q hq W hW, hprofile, hp⟩

#print axioms unmarked_period_lifts_to_integer_pose_period
#print axioms unmarked_exists_cellWorld_with_period_lift
#print axioms compiled_unmarked_exists_cellWorld
end
end ProductClosure.NativeCompiler
