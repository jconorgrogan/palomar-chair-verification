module

public import PrimeFacetClosure.PhysicalAperiodicity
public import PhysicalRegistration.RegisteredMaterialExistence

@[expose] public section

/-! Nonvacuous physical aperiodic monotiles in every prime dimension congruent
to three modulo four. The exact finite free-orbit coefficient compiler,
physical tiling existence, arbitrary-isometry registration, arithmetic atlas
closure and unmarked period exclusion are all proved dependencies. -/
namespace PhysicalRegistration.NativeChair.GeneratedCompiler
noncomputable section

/-- The literal graph-compiled native chair is a compact physical aperiodic
monotile. HasTiling is proved by actual registered-world material gluing. -/
theorem body_isAperiodicMonotile {m : ℕ} [NeZero m]
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :
    SparseMonotiles.IsAperiodicMonotile (body (coefficients hp hmod)) :=
  ⟨body_isCompact _, body_hasTiling hp hmod, body_isAperiodic hp hmod⟩

/-- Nonempty interior is supplied by the retained open ball of this same
literal body, rather than included in the tiling definition as an assumption. -/
theorem body_isAperiodicMonotile_nonemptyInterior {m : ℕ} [NeZero m]
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :
    SparseMonotiles.IsAperiodicMonotile (body (coefficients hp hmod)) ∧
      (interior (body (coefficients hp hmod))).Nonempty :=
  ⟨body_isAperiodicMonotile hp hmod, interior_body_nonempty _⟩

/-- Unconditional ordinary-prime family in the actual Euclidean dimension.
Tilings are sets of unmarked physical copies under unrestricted isometries;
existence and universal absence of nonzero translation periods are conclusions. -/
theorem prime_three_mod_four_physical_monotile {p : ℕ}
    (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    ∃ T : Set (EuclideanSpace ℝ (Fin p)),
      SparseMonotiles.IsAperiodicMonotile T ∧ (interior T).Nonempty := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
  let : NeZero m := ⟨by omega⟩
  have hprime : Uniform.IsPrime (m+1) :=
    ⟨hp.two_le, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩
  exact ⟨body (coefficients hprime hmod), body_isAperiodicMonotile_nonemptyInterior hprime hmod⟩

end
end PhysicalRegistration.NativeChair.GeneratedCompiler
