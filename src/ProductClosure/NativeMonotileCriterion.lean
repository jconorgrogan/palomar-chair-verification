module

public import ProductClosure.NativeUnmarkedPeriods
public import ProductClosure.RegisteredMaterialExistence

@[expose] public section

/-!
# A general physical monotile criterion for literal finite-polycube compilers

This is a proved implication. Its remaining premises are explicit statements
about complete integer-cell worlds and their full coefficient profiles. It is
not a product-family monotile theorem until those algebraic premises are
instantiated for the specified coefficient compiler.
-/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m J : ℕ} {S : Finset (LatticeIndex m)}
variable [NeZero m] [Nonempty (Polycube.Cell S)]

/-- Full coefficient profiles on every actual pair of placed world states. -/
def CellWorldFullProfile (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S)) : Prop :=
  ∀ q r, q ∈ W.tiles → r ∈ W.tiles →
    FullProfileMating a (poseIsometry (q.relative r))

/-- If every full-profile complete cell world has only the zero literal
pose-set translation period, every arbitrary unmarked physical tiling is
aperiodic. Registration, world extraction and the period lift are derived. -/
theorem body_isAperiodic_of_profile_worlds (hm : 2 ≤ m) (a : Coefficients S J)
    (hzero : ∀ W : World.CompleteTiling (World.placedCells S),
      CellWorldFullProfile a W → ∀ w : LatticeIndex m,
      W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate w) → w = 0) :
    SparseMonotiles.IsAperiodic (body a) := by
  intro tiles ht v hv
  obtain ⟨g, root, q, W, _, _, _, _, hprofile, hlift⟩ :=
    unmarked_exists_cellWorld_with_period_lift hm ht
  obtain ⟨w, hw, hp⟩ := hlift v hv
  have hw0 : w = 0 := hzero W hprofile w hp
  rw [hw0, integerPoint_zero] at hw
  exact (g root).symm.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    (by simpa [placedNormal] using hw)

/-- One concrete complete full-profile world gives actual physical tiling
existence through the proved tube-ownership and material-gluing construction. -/
theorem body_hasTiling_of_profile_world (hm : 2 ≤ m) (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S)) (hprofile : CellWorldFullProfile a W) :
    SparseMonotiles.HasTiling (body a) := by
  apply registered_world_body_hasTiling hm a W
  intro q hq r hr _
  rw [← poseIsometry_relative]
  exact hprofile q r hq hr

/-- A nonvacuous compact aperiodic monotile follows once the actual full-profile
world existence and algebraic zero-period obligations are discharged. -/
theorem body_isAperiodicMonotile_of_profile_worlds (hm : 2 ≤ m) (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S)) (hprofile : CellWorldFullProfile a W)
    (hzero : ∀ W' : World.CompleteTiling (World.placedCells S),
      CellWorldFullProfile a W' → ∀ w : LatticeIndex m,
      W'.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate w) → w = 0) :
    SparseMonotiles.IsAperiodicMonotile (body a) :=
  ⟨body_isCompact a, body_hasTiling_of_profile_world hm a W hprofile,
    body_isAperiodic_of_profile_worlds hm a hzero⟩

/-- The same criterion also records the independently proved genuine interior:
this body contains the retained open ball around an occupied cell center. -/
theorem body_nonemptyInterior_aperiodicMonotile_of_profile_worlds
    (hm : 2 ≤ m) (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S)) (hprofile : CellWorldFullProfile a W)
    (hzero : ∀ W' : World.CompleteTiling (World.placedCells S),
      CellWorldFullProfile a W' → ∀ w : LatticeIndex m,
      W'.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate w) → w = 0) :
    (interior (body a)).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile (body a) := by
  refine ⟨?_, body_isAperiodicMonotile_of_profile_worlds hm a W hprofile hzero⟩
  obtain ⟨c⟩ := (inferInstance : Nonempty (Polycube.Cell S))
  exact ⟨cellCenter c, cellCenter_mem_interior_body a c⟩

#print axioms body_isAperiodic_of_profile_worlds
#print axioms body_hasTiling_of_profile_world
#print axioms body_isAperiodicMonotile_of_profile_worlds
#print axioms body_nonemptyInterior_aperiodicMonotile_of_profile_worlds
end
end ProductClosure.NativeCompiler
