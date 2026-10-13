module

public import PhysicalRegistration.PhysicalTilingGerms
public import SparseMonotiles.Model

@[expose] public section

/-!
# From indexed actual placements to unmarked tilings

The unmarked tile collection forgets the chosen indices and frames. It remains
a genuine physical tiling: unequal image sets necessarily have unequal indices,
so the original indexed interior-disjointness theorem applies. No injectivity
or symmetry-breaking assumption on the placements or body is introduced.
-/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- The literal set of physical tile images of an indexed physical tiling. -/
def unmarkedTiles {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m) : Set (Set (Space m)) :=
  Set.range (fun i => f i '' body a)

/-- Actual indexed body coverage and interior-disjointness imply the original
unmarked `SparseMonotiles.IsTiling` target, with unrestricted isometries. -/
theorem PhysicalTiling.unmarkedIsTiling
    {m J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients m J}
    {f : ι → Space m ≃ᵢ Space m} (T : PhysicalTiling a f) :
    SparseMonotiles.IsTiling (body a) (Set.range (fun i => f i '' body a)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro A ⟨i, rfl⟩
    exact ⟨f i, rfl⟩
  · intro x
    obtain ⟨i, hi⟩ := T.covers x
    exact ⟨f i '' body a, ⟨i, rfl⟩, hi⟩
  · rintro A ⟨i, rfl⟩ B ⟨j, rfl⟩ hne
    have hij : i ≠ j := by
      intro h
      exact hne (h ▸ rfl)
    exact T.interiors_disjoint hij

/-- Nonvacuous unmarked tiling existence follows from the constructed physical
placement family, rather than from an assumed decorated tiling. -/
theorem PhysicalTiling.hasTiling
    {m J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients m J}
    {f : ι → Space m ≃ᵢ Space m} (T : PhysicalTiling a f) :
    SparseMonotiles.HasTiling (body a) :=
  ⟨unmarkedTiles a f, T.unmarkedIsTiling⟩

/-- Final compact nonvacuous monotile packaging when universal unmarked
aperiodicity has been independently proved for this same literal body. -/
theorem PhysicalTiling.isAperiodicMonotile
    {m J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients m J}
    {f : ι → Space m ≃ᵢ Space m} (T : PhysicalTiling a f)
    (haper : SparseMonotiles.IsAperiodic (body a)) :
    SparseMonotiles.IsAperiodicMonotile (body a) :=
  ⟨body_isCompact a, T.hasTiling, haper⟩

#print axioms PhysicalTiling.unmarkedIsTiling
#print axioms PhysicalTiling.hasTiling
#print axioms PhysicalTiling.isAperiodicMonotile
end
end PhysicalRegistration.NativeChair
