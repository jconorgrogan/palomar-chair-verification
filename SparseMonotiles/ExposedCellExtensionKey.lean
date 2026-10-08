module

public import SparseMonotiles.ExposedCellExtensionRelative
public import SparseMonotiles.KeyCompanionFeatureMatchingRegistration
public import SparseMonotiles.ContactMatchedFacet

@[expose] public section

/-! # An actual facet key forces an occupied registered neighboring cell
The physical companion and its integer relative pose come from K3. Actual key
collars and disjoint interiors force Shared; the exact signed lower-cell
correction then identifies the companion's occupied cell across the facet.
-/
namespace SparseMonotiles
open Set Canonical Contact

theorem T5_key_on_facet_has_registered_shared_companion
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A : tiles)
    (f : Facet 5) (hf : IsChairCell f.cell)
    (root : BoxKey 5) (hroot : root.toKeyData 19200 ∈ keys5)
    (hcollar : root.CollarValid 19200 f) :
    ∃ B : tiles, B ≠ A ∧ ∃ p : Pose 5,
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv ∧
      ∃ b : Facet 5, IsChairCell b.cell ∧ Shared p f b ∧ p.cell b.cell=f.neighbor := by
  obtain ⟨B,hBA,l,hl,hmatch,p,hp⟩ := T5_key_has_registered_whole_key_companion ht g hg A hroot
  obtain ⟨j,source,hsource,hdecode⟩ := everyKey5_in_atlas l hl
  have hsourceCell : IsChairCell (IndexedData5.geometry.facet j).cell := IndexedData5.owned_checked j
  have hsourceCollar : source.CollarValid 19200 (IndexedData5.geometry.facet j) :=
    (atlas5_checked j).2.1 source hsource
  have hdis : Disjoint (interior T5) (interior (p.euclidean '' T5)) := by
    have h := ht.relative_copies_interior_disjoint g hg A B hBA
    rw [hp] at h
    exact h
  have hsolid : keySolid (root.toKeyData 19200)=p.euclidean '' keySolid (source.toKeyData 19200) := by
    have h := relative_isometry_image_of_coincidence
      (keySolid (root.toKeyData 19200)) (keySolid l) (g A) (g B) hmatch
    rw [hp,← hdecode] at h
    exact h.symm
  have hshared := T5_shared_of_physical_matched_keySolids (by norm_num : (0 : ℤ)<19200)
    hf hsourceCell hdis hcollar hsourceCollar hsolid
  exact ⟨B,hBA,p,hp,IndexedData5.geometry.facet j,hsourceCell,hshared,shared_cell_neighbor hshared⟩

/-- Native local extension interface consumed by registered-component growth. -/
theorem T5_key_on_facet_has_registered_neighbor
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5) (A : tiles)
    (f : Facet 5) (hf : IsChairCell f.cell)
    (root : BoxKey 5) (hroot : root.toKeyData 19200 ∈ keys5)
    (hcollar : root.CollarValid 19200 f) :
    ∃ B : tiles, B ≠ A ∧ ∃ p : Pose 5,
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv ∧
      IsChairCell (p.inverseCell f.neighbor) := by
  obtain ⟨B,hBA,p,hp,b,hb,hshared,hcell⟩ :=
    T5_key_on_facet_has_registered_shared_companion ht g hg A f hf root hroot hcollar
  refine ⟨B,hBA,p,hp,?_⟩
  rw [← hcell,p.inverseCell_cell]
  exact hb

#print axioms T5_key_on_facet_has_registered_shared_companion
#print axioms T5_key_on_facet_has_registered_neighbor

theorem T7_key_on_facet_has_registered_shared_companion
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A : tiles)
    (f : Facet 7) (hf : IsChairCell f.cell)
    (root : BoxKey 7) (hroot : root.toKeyData 188160 ∈ keys7)
    (hcollar : root.CollarValid 188160 f) :
    ∃ B : tiles, B ≠ A ∧ ∃ p : Pose 7,
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv ∧
      ∃ b : Facet 7, IsChairCell b.cell ∧ Shared p f b ∧ p.cell b.cell=f.neighbor := by
  obtain ⟨B,hBA,l,hl,hmatch,p,hp⟩ := T7_key_has_registered_whole_key_companion ht g hg A hroot
  obtain ⟨j,source,hsource,hdecode⟩ := everyKey7_in_atlas l hl
  have hsourceCell : IsChairCell (IndexedData7.geometry.facet j).cell := IndexedData7.owned_checked j
  have hsourceCollar : source.CollarValid 188160 (IndexedData7.geometry.facet j) :=
    (atlas7_checked j).2.1 source hsource
  have hdis : Disjoint (interior T7) (interior (p.euclidean '' T7)) := by
    have h := ht.relative_copies_interior_disjoint g hg A B hBA
    rw [hp] at h
    exact h
  have hsolid : keySolid (root.toKeyData 188160)=p.euclidean '' keySolid (source.toKeyData 188160) := by
    have h := relative_isometry_image_of_coincidence
      (keySolid (root.toKeyData 188160)) (keySolid l) (g A) (g B) hmatch
    rw [hp,← hdecode] at h
    exact h.symm
  have hshared := T7_shared_of_physical_matched_keySolids (by norm_num : (0 : ℤ)<188160)
    hf hsourceCell hdis hcollar hsourceCollar hsolid
  exact ⟨B,hBA,p,hp,IndexedData7.geometry.facet j,hsourceCell,hshared,shared_cell_neighbor hshared⟩

/-- Native local extension interface consumed by registered-component growth. -/
theorem T7_key_on_facet_has_registered_neighbor
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7) (A : tiles)
    (f : Facet 7) (hf : IsChairCell f.cell)
    (root : BoxKey 7) (hroot : root.toKeyData 188160 ∈ keys7)
    (hcollar : root.CollarValid 188160 f) :
    ∃ B : tiles, B ≠ A ∧ ∃ p : Pose 7,
      (g B).trans (g A).symm=p.euclidean.toIsometryEquiv ∧
      IsChairCell (p.inverseCell f.neighbor) := by
  obtain ⟨B,hBA,p,hp,b,hb,hshared,hcell⟩ :=
    T7_key_on_facet_has_registered_shared_companion ht g hg A f hf root hroot hcollar
  refine ⟨B,hBA,p,hp,?_⟩
  rw [← hcell,p.inverseCell_cell]
  exact hb

#print axioms T7_key_on_facet_has_registered_shared_companion
#print axioms T7_key_on_facet_has_registered_neighbor

end SparseMonotiles
