module

public import ClarkSeed.Compiler
public import ClarkSeed.LiteralProfiles
public import ClarkSeed.FacetBridge
public import ClarkSeed.SharedGeometry
public import ClarkSeed.CellAdapter
public import ClarkSeed.SpatialAdapter
public import ProductClosure.PolycubePacking
public import ProductClosure.ProductGraphCarrierDisjoint

@[expose] public section

/-! Faithful recovery of every original sparse CLARK facet equation from
actual dense full-profile mating. Input-generator legality is isolated here
and discharged by the original exact contact theorem in the next module. -/
namespace ClarkSeed.DenseProfiles
noncomputable section
open ProductClosure NativeCompiler SparseMonotiles.Contact
open FacetBridge

/-- Preserve the entire original finite vertex profile on each exposed facet;
the added full-frame index does not erase any original key. -/
def sparseProfile (u : Site compilerData.cells) : ProfileMating.Profile (Space 4) :=
  LiteralProfiles.literalProfile 19200
    ((IndexedData5.geometry.profile (nativeFacetEquiv.symm u.1)).image BoxKey.literal)

/-- Original generator legality supplies the sparse mating law on every
actual full-frame site transport. -/
theorem generator_profiles_of_catalog_legal
    (hl : ∀ p ∈ SparseMonotiles.CarrierHierarchy.Catalog5.supplied,
      IndexedData5.geometry.LegalContact p) :
    OddWalkProfiles.GeneratorProfiles compilerData.generators sparseProfile := by
  intro g hg u v ht
  obtain ⟨p,hp,rfl⟩ := (Generators.mem_generators g).mp hg
  have hs := SharedGeometry.siteTransport_shared p u v ht
  have hs' : Shared p (IndexedData5.geometry.facet (nativeFacetEquiv.symm u.1))
      (IndexedData5.geometry.facet (nativeFacetEquiv.symm v.1)) := by
    rw [indexed_facet_of_native u.1, indexed_facet_of_native v.1]
    exact hs
  have he := (hl p hp).2.2 _ _ hs'
  exact (LiteralProfiles.literalProfile_mating_iff 19200 (by decide) p _ _).mpr he

/-- Dense mating forces the original exact finite vertex equation on each
shared carrier facet, including facets not chosen for initial contact. -/
theorem dense_shared_profile
    (hP : OddWalkProfiles.GeneratorProfiles compilerData.generators sparseProfile)
    (p : Pose 5) (hf : FullProfileMating compilerData.coefficients (Generators.realize p))
    (i j : Fin 160) (hs : Shared p (IndexedData5.geometry.facet i)
      (IndexedData5.geometry.facet j)) :
    (IndexedData5.geometry.profile i).image BoxKey.literal =
      ((IndexedData5.geometry.profile j).image BoxKey.literal).image
        (p.key IndexedData5.geometry.denominator) := by
  have hs' : Shared p (NativeFacets.toContact (nativeFacetEquiv i))
      (NativeFacets.toContact (nativeFacetEquiv j)) := hs
  obtain ⟨u,v,hu,hv,ht⟩ := SharedGeometry.shared_exists_siteTransport p
    (nativeFacetEquiv i) (nativeFacetEquiv j) hs'
  have he := compilerData_sparse_profiles sparseProfile hP (Generators.realize p) hf u v ht
  simp only [sparseProfile, hu, hv, Equiv.symm_apply_apply] at he
  exact (LiteralProfiles.literalProfile_mating_iff 19200 (by decide) p _ _).mp he

/-- Actual Euclidean carrier nonoverlap is exactly sufficient for the old
integer occupied-cell disjointness test. -/
theorem carrierDisjoint_cells (p : Pose 5)
    (hd : ProductGraphCarrierDisjoint.CarrierDisjoint compilerData.cells (Generators.realize p)) :
    Disjoint IndexedData5.geometry.cells (IndexedData5.geometry.cells.image p.cell) := by
  change Disjoint (interior (Polycube.carrier (ChairBridge.cells 4)))
    (interior (PoseAdapter.realization p '' Polycube.carrier (ChairBridge.cells 4))) at hd
  rw [PoseAdapter.realization_image_carrier] at hd
  have hc := Polycube.carrier_interiors_disjoint_iff.mp hd
  change Disjoint (chairCells 5) ((chairCells 5).image p.cell)
  rw [PoseAdapter.chairCells_eq]
  exact hc

/-- No candidate catalog premise is used: geometric nonoverlap, one genuine
contact, and dense profile equations recover original literal legality. -/
theorem dense_contact_legal
    (hP : OddWalkProfiles.GeneratorProfiles compilerData.generators sparseProfile)
    (p : Pose 5) (hf : FullProfileMating compilerData.coefficients (Generators.realize p))
    (hd : ProductGraphCarrierDisjoint.CarrierDisjoint compilerData.cells (Generators.realize p))
    (ht : ∃ u v : Site compilerData.cells, SiteTransport (Generators.realize p) u v) :
    IndexedData5.geometry.LegalContact p := by
  refine ⟨carrierDisjoint_cells p hd, ?_, dense_shared_profile hP p hf⟩
  obtain ⟨u,v,huv⟩ := ht
  refine ⟨nativeFacetEquiv.symm u.1,nativeFacetEquiv.symm v.1,?_⟩
  rw [indexed_facet_of_native u.1, indexed_facet_of_native v.1]
  exact SharedGeometry.siteTransport_shared p u v huv

#print axioms generator_profiles_of_catalog_legal
#print axioms dense_contact_legal
end
end ClarkSeed.DenseProfiles
