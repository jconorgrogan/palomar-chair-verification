module

public import SparseMonotiles.PhysicalT5PeriodComposition
public import SparseMonotiles.PrescribedContactProfiles5
public import SparseMonotiles.Targets

@[expose] public section

/-! Unconditional absence of nonzero translation periods in every physical
T5 tiling, allowing arbitrary Euclidean isometries. Existence is a separate
checked construction/finite-package branch, so the final monotile conjunction
is not asserted here without that premise. -/
namespace SparseMonotiles

theorem T5_isAperiodic : IsAperiodic T5 := by
  apply T5_isAperiodic_of_native_contact_law
  intro tiles ht g hg A B p hBA hp hcontact
  exact T5_native_contact_legal ht g hg A B p hBA hp hcontact

theorem T5_period_eq_zero {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) (v : Point 5) (hv : IsPeriod tiles v) : v=0 :=
  T5_isAperiodic tiles ht v hv

theorem T5_aperiodicMonotile_of_hasTiling (hex : HasTiling T5) : T5Goal :=
  ⟨T5_isCompact,hex,T5_isAperiodic⟩

#print axioms T5_isAperiodic
#print axioms T5_period_eq_zero
#print axioms T5_aperiodicMonotile_of_hasTiling
end SparseMonotiles
