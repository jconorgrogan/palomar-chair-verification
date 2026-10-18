module

public import ClarkSeed.Compiler
public import ClarkSeed.HierarchyAdapter
public import SparseMonotiles.CarrierExistenceConcrete5
public import ProductClosure.WorldProfileContacts
public import ProductClosure.NativeProfileSelf

@[expose] public section

/-! Every actual complete world of the exact recovered M5 language satisfies
the newly compiled dense full profiles. Universal site matches produce actual
neighboring owners, and identity pairs are discharged by carrier geometry. -/
namespace ClarkSeed
noncomputable section
open ProductClosure NativeCompiler SparseMonotiles
open PoseAdapter

/-- Recover the exact finite generator from a pair's old relative-language
membership, retaining its complete signed pose. -/
theorem profileLanguage_of_catalog (q r : RegisteredPrime.Pose 5)
    (h : toContact (q.relative r) ∈ CarrierHierarchy.M5) :
    compilerData.ProfileLanguage q r := by
  have hp := compilerData_generator_fullProfile (toContact (q.relative r)) h
  simpa only [CompilerData.ProfileLanguage, Generators.realize, toRegistered_toContact] using hp

/-- A complete recovered M5-legal world has all actual dense profile equations
on every pair, not just on the original neighboring-owner comparisons. -/
theorem catalogWorld_fullProfile (V : CarrierHierarchy.RegisteredWorld 5)
    (hV : V.Legal CarrierHierarchy.M5) :
    CellWorldFullProfile compilerData.coefficients (toWorld V) := by
  have hL := toWorld_legal V CarrierHierarchy.M5 hV
  have hN : (toWorld V).IsLegal World.LatticeAdjacent compilerData.ProfileLanguage := by
    intro x y hxy hne
    exact profileLanguage_of_catalog _ _ (hL x y hxy hne)
  apply CellWorldFullProfile_of_distinct
  intro q r hq hr hne
  exact fullProfiles_of_neighbor_profiles compilerData.coefficients (toWorld V) hN q hq r hr hne

/-- No physical old-body assumption is needed for the new dense compiler's
world existence; the exact recovered registered carrier world suffices. -/
theorem compilerData_hasWorld_of_catalogWorld (V : CarrierHierarchy.RegisteredWorld 5)
    (hV : V.Legal CarrierHierarchy.M5) : compilerData.HasWorld :=
  ⟨toWorld V, catalogWorld_fullProfile V hV⟩

/-- The concrete nested construction is already an actual complete cell world.
Its finite forward-rule proof is isolated in the final replayed endpoint. -/
def seedWorld : World.CompleteTiling (World.placedCells compilerData.cells) :=
  toWorld CarrierHierarchy.Existence.Catalog5World.registered

theorem seedWorld_fullProfile_of_forward
    (hforward : CarrierHierarchy.ForwardRules
      CarrierHierarchy.CoarseContactCertificates5.C CarrierHierarchy.M5) :
    CellWorldFullProfile compilerData.coefficients seedWorld :=
  catalogWorld_fullProfile CarrierHierarchy.Existence.Catalog5World.registered
    (CarrierHierarchy.Existence.Catalog5World.legal hforward)

#print axioms catalogWorld_fullProfile
#print axioms compilerData_hasWorld_of_catalogWorld
#print axioms seedWorld_fullProfile_of_forward
end
end ClarkSeed
