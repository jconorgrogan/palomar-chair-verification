module

public import SparseMonotiles.CarrierExistenceProfileRules
public import SparseMonotiles.CarrierExistenceSupportCovariance
public import SparseMonotiles.CarrierHierarchyExactStages
public import SparseMonotiles.CarrierHierarchyAcceptanceBinding5
public import SparseMonotiles.AtlasBindings5
public import SparseMonotiles.AtlasCertificates5

@[expose] public section

/-! Discharge of actual complementary profiles for the exact T5 language.
The acceptance-only mate certificates provide a source facet for every occupied
exterior cell. Full BoxKey equality is transported to actual whole solids and
closed coordinate supports, and the reverse atlas binding supplies a literal
source key. No global physical-tiling premise is used. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact Set Canonical

private theorem apex_mem_coordinateSupport {d : ℕ} (k : KeyData d) :
    rationalPoint k.apex ∈ keyCoordinateSupport k := by
  intro i
  exact ⟨min_le_right _ _, le_max_right _ _⟩

/-- The chosen exposed support facet is the same actual facet as the indexed
atlas entry, since both collars contain the literal apex. -/
theorem assigned_facet5_eq_indexed (A : KeyFacetAssignment keys5)
    (k : KeyData 5) (hk : k ∈ keys5) (i : Fin 160) (root : BoxKey 5)
    (hr : root ∈ IndexedData5.geometry.profile i) (he : root.toKeyData 19200 = k) :
    A.facet k hk = IndexedData5.geometry.facet i := by
  have hs : keyCoordinateSupport k ⊆
      gridFacetCollar (IndexedData5.geometry.facet i).gridFacet := by
    rw [← he]
    exact BoxKey.coordinateSupport_subset_collar (by decide) ((atlas5_checked i).2.1 root hr)
  have hp := apex_mem_coordinateSupport k
  exact Facet.eq_of_gridFacet_eq (A.exposed k hk) (IndexedData5.owned_checked i)
    (GridFacet.eq_of_mem_collars (A.support k hk hp) (hs hp))

/-- Every exact M5 acceptance has a literal, opposite-coefficient mate for
every key whose exposed exterior cell is occupied by the source. -/
theorem complementaryProfiles5_of_literal_binding
    (reverse : ∀ (i : Fin 160) (b : BoxKey 5), b ∈ IndexedData5.geometry.profile i →
      b.toKeyData 19200 ∈ keys5) (A : KeyFacetAssignment keys5) :
    ComplementaryProfiles A M5 := by
  intro p hp k hk hocc
  obtain ⟨i, root, hr, he⟩ := everyKey5_in_atlas k hk
  have hf := assigned_facet5_eq_indexed A k hk i root hr he
  have hocc' : Occupies p (IndexedData5.geometry.facet i).neighbor := by
    simpa only [hf] using hocc
  have occupied : (IndexedData5.geometry.facet i).neighbor ∈
      IndexedData5.geometry.cells.image p.cell := by
    refine Finset.mem_image.mpr ⟨p.inverseCell (IndexedData5.geometry.facet i).neighbor, ?_,
      p.cell_inverseCell _⟩
    rw [IndexedData5.cells_eq, mem_chairCells]
    exact hocc'
  obtain ⟨j, source, hs, _, hm⟩ := AcceptanceBinding5.catalog_key_mate hp occupied hr
  change root = p.boxKey 19200 source at hm
  refine ⟨source.toKeyData 19200, reverse j source hs, ?_, ?_, ?_⟩
  · simpa only [he] using p.boxKey_match_solid (by decide : (19200 : ℤ) ≠ 0) hm
  · simpa only [he] using p.boxKey_match_support (by decide : (19200 : ℤ) ≠ 0) hm
  · rw [← he]
    change source.bump = !root.bump
    rw [p.boxKey_match_coefficient 19200 hm]
    simp

#print axioms assigned_facet5_eq_indexed
#print axioms complementaryProfiles5_of_literal_binding
end SparseMonotiles.CarrierHierarchy.Existence
