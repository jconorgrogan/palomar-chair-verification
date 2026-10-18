module

public import ClarkSeed.NativeFacets
public import ClarkSeed.PoseAdapter
public import SparseMonotiles.ContactCertificateDataIndexed5Base

@[expose] public section

/-! Exact bijection between all 160 indexed CLARK facets and the exposed
facets of the actual generalized 5D chair carrier. -/
namespace ClarkSeed.FacetBridge
open ProductClosure SparseMonotiles.Contact
noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem indexed_exposed : ∀ i : Fin 160,
    ¬ IsChairCell (IndexedData5.geometry.facet i).neighbor := by decide

def indexedFacet (i : Fin 160) : Polycube.Facet (ChairBridge.cells 4) where
  cell := ⟨(IndexedData5.geometry.facet i).cell,
    (ChairBridge.mem_cells _).mpr (IndexedData5.owned_checked i)⟩
  axis := (IndexedData5.geometry.facet i).axis
  positive := (IndexedData5.geometry.facet i).positive
  outside := by
    intro h
    exact indexed_exposed i ((ChairBridge.mem_cells _).mp h)

@[simp] theorem toContact_indexedFacet (i : Fin 160) :
    NativeFacets.toContact (indexedFacet i) = IndexedData5.geometry.facet i := rfl

theorem indexedFacet_injective : Function.Injective indexedFacet := by
  intro i j h
  apply IndexedData5.facet_injective
  exact congrArg NativeFacets.toContact h

set_option maxRecDepth 100000 in
theorem nativeFacet_card : Fintype.card (Polycube.Facet (ChairBridge.cells 4)) = 160 := by
  rw [← Fintype.card_congr (ChairBridge.facetEquiv 4)]
  decide

theorem indexedFacet_bijective : Function.Bijective indexedFacet := by
  apply (Fintype.bijective_iff_injective_and_card indexedFacet).mpr
  exact ⟨indexedFacet_injective, by rw [Fintype.card_fin, nativeFacet_card]⟩

def nativeFacetEquiv : Fin 160 ≃ Polycube.Facet (ChairBridge.cells 4) :=
  Equiv.ofBijective indexedFacet indexedFacet_bijective

@[simp] theorem toContact_nativeFacetEquiv (i : Fin 160) :
    NativeFacets.toContact (nativeFacetEquiv i) = IndexedData5.geometry.facet i := rfl

@[simp] theorem indexed_facet_of_native (f : Polycube.Facet (ChairBridge.cells 4)) :
    IndexedData5.geometry.facet (nativeFacetEquiv.symm f) = NativeFacets.toContact f := by
  rw [← toContact_nativeFacetEquiv, nativeFacetEquiv.apply_symm_apply]

end
end ClarkSeed.FacetBridge
