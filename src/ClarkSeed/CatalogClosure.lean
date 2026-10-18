module

public import ClarkSeed.WorldDecoding
public import SparseMonotiles.CarrierHierarchyContactBinding5

@[expose] public section

/-! Unconditional exact binding of the new dense compiler to the recovered
literal 284-pose CLARK language, with every original profile retained. -/
namespace ClarkSeed
noncomputable section
open ProductClosure NativeCompiler SparseMonotiles
open PoseAdapter DenseProfiles

/-- The recovered exact contact theorem proves the sparse law on every
original generator; this is not a property assumed of arbitrary candidates. -/
theorem sparse_generator_profiles :
    OddWalkProfiles.GeneratorProfiles compilerData.generators sparseProfile := by
  apply generator_profiles_of_catalog_legal
  intro p hp
  exact (CarrierHierarchy.ContactBinding5.registered_contact_exact_catalog p).mpr hp

/-- Every dense legal actual contact belongs to the exact recovered catalog. -/
theorem dense_contact_catalog (p : Contact.Pose 5)
    (hf : FullProfileMating compilerData.coefficients (Generators.realize p))
    (hd : ProductGraphCarrierDisjoint.CarrierDisjoint compilerData.cells (Generators.realize p))
    (ht : ∃ u v : Site compilerData.cells, SiteTransport (Generators.realize p) u v) :
    p ∈ CarrierHierarchy.M5 :=
  (CarrierHierarchy.ContactBinding5.registered_contact_exact_catalog p).mp
    (dense_contact_legal sparse_generator_profiles p hf hd ht)

/-- Universal complete-world decoding into the original exact M5 language.
No catalog, contact, sparse-profile or geometry callback remains. -/
theorem denseWorld_exact_catalog
    (W : World.CompleteTiling (World.placedCells compilerData.cells))
    (hW : W.IsLegal World.LatticeAdjacent compilerData.ProfileLanguage) :
    (fromWorld W).Legal CarrierHierarchy.M5 :=
  denseWorld_catalog_legal sparse_generator_profiles
    (fun p => (CarrierHierarchy.ContactBinding5.registered_contact_exact_catalog p).mp) W hW

#print axioms sparse_generator_profiles
#print axioms dense_contact_catalog
#print axioms denseWorld_exact_catalog
end
end ClarkSeed
