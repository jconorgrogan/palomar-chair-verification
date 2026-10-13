module

public import PrimeFacetClosure.RealizedFacetClosure
public import PhysicalRegistration.CompiledRegisteredWorld
public import AtlasPeriods.Aperiodicity

@[expose] public section

/-! Unmarked physical aperiodicity of the literal finite compiled body in
every prime dimension congruent to three modulo four. Actual isometries,
including reflections, are allowed in the input tiling. Existence of a tiling
is a separate theorem and is not silently included in this endpoint. -/
namespace PhysicalRegistration.NativeChair.GeneratedCompiler
noncomputable section
open RegisteredPrime RegisteredPrime.PrimeFacetClosure

/-- Every translational symmetry of every genuine unmarked physical tiling
by this explicit compiler body is zero. Registration, language closure,
coarse legality, hierarchy and period transfer are all proved dependencies. -/
theorem body_isAperiodic {m : ℕ} [NeZero m]
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :
    SparseMonotiles.IsAperiodic (body (coefficients hp hmod)) := by
  intro tiles ht v hv
  obtain ⟨g, root, q, W, _T, _hg, _hq, _hW, _hproper, hprofile, hperiod⟩ :=
    compiled_unmarked_exists_world (nativeDimension_ge_two hmod)
      (generators hp hmod) (generators_proper hp hmod) ht
  have hl := fullProfile_world_arithmetic_atlas hp hmod W hprofile
  obtain ⟨w, hw, hpw⟩ := hperiod v hv
  have hwzero := AtlasPeriods.arithmetic_atlas_translation_aperiodic
    (minusParameters (m+1) hp hmod) W hl w hpw
  change w = 0 at hwzero
  rw [hwzero, integerPoint_zero] at hw
  exact (g root).symm.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    (by simpa [placedNormal] using hw)


/-- The same explicit body is compact and contains an open ball. This records
geometric nondegeneracy without claiming the still-separate tiling existence. -/
theorem body_compact_interior_aperiodic {m : ℕ} [NeZero m]
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :
    IsCompact (body (coefficients hp hmod)) ∧
      (interior (body (coefficients hp hmod))).Nonempty ∧
      SparseMonotiles.IsAperiodic (body (coefficients hp hmod)) :=
  ⟨body_isCompact _, interior_body_nonempty _, body_isAperiodic hp hmod⟩

/-- Ordinary Mathlib primality and the actual Euclidean dimension, with no
manual predecessor or NeZero witness required from the caller. HasTiling is
intentionally absent until physical existence gluing is proved. -/
theorem prime_three_mod_four_exists_compact_aperiodic_body {p : ℕ}
    (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    ∃ T : Set (EuclideanSpace ℝ (Fin p)), IsCompact T ∧
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodic T := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
  let : NeZero m := ⟨by omega⟩
  have hprime : Uniform.IsPrime (m+1) :=
    ⟨hp.two_le, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩
  exact ⟨body (coefficients hprime hmod), body_compact_interior_aperiodic hprime hmod⟩

end
end PhysicalRegistration.NativeChair.GeneratedCompiler
