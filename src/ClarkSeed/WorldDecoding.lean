module

public import ClarkSeed.DenseProfiles
public import ClarkSeed.PeriodAdapter
public import ProductClosure.WorldNeighborProfiles

@[expose] public section

/-! Every dense complete world decodes to the original literal sparse facet
law. All contact and carrier hypotheses come from actual neighboring owners. -/
namespace ClarkSeed
noncomputable section
open ProductClosure NativeCompiler SparseMonotiles
open PoseAdapter DenseProfiles

/-- The original finite vertex equations are forced on every neighboring
pair of a dense world; no assumed world factorization or contact witness. -/
theorem denseWorld_sparse_legal
    (hP : OddWalkProfiles.GeneratorProfiles compilerData.generators sparseProfile)
    (W : World.CompleteTiling (World.placedCells compilerData.cells))
    (hW : W.IsLegal World.LatticeAdjacent compilerData.ProfileLanguage) :
    W.IsLegal World.LatticeAdjacent
      (language {p : Contact.Pose 5 | Contact.IndexedData5.geometry.LegalContact p}) := by
  intro x y hxy hne
  obtain ⟨ht,hd⟩ := neighbor_owners_dense_contact W hxy hne
  let p := toContact ((W.owner x).relative (W.owner y))
  have he : Generators.realize p =
      PhysicalRegistration.NativeChair.poseIsometry ((W.owner x).relative (W.owner y)) := by
    simp only [Generators.realize,p,toRegistered_toContact]
  change Contact.IndexedData5.geometry.LegalContact p
  apply dense_contact_legal hP p
  · rw [he]
    exact hW x y hxy hne
  · rwa [he]
  · rwa [he]

/-- Transport the checked sparse relative-contact classification to the
entire decoded complete world. Both input laws are later discharged by the
original exact finite catalog theorem. -/
theorem denseWorld_catalog_legal
    (hP : OddWalkProfiles.GeneratorProfiles compilerData.generators sparseProfile)
    (hc : ∀ p : Contact.Pose 5, Contact.IndexedData5.geometry.LegalContact p →
      p ∈ CarrierHierarchy.M5)
    (W : World.CompleteTiling (World.placedCells compilerData.cells))
    (hW : W.IsLegal World.LatticeAdjacent compilerData.ProfileLanguage) :
    (fromWorld W).Legal CarrierHierarchy.M5 := by
  apply fromWorld_legal W CarrierHierarchy.M5
  intro x y hxy hne
  exact hc _ (denseWorld_sparse_legal hP W hW x y hxy hne)

#print axioms denseWorld_sparse_legal
#print axioms denseWorld_catalog_legal
end
end ClarkSeed
