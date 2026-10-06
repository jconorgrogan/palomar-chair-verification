module

public import SparseMonotiles.ExposedCellExtensionKey
public import SparseMonotiles.PhysicalCellOwnerUniqueness

@[expose] public section

/-! # A root key matches the prescribed physical tile across a shared facet
K3 supplies a possibly different companion. Both own the same adjacent integer
cell, so physical owner uniqueness identifies them before matching atlas facets.
-/
namespace SparseMonotiles
open Set Canonical Contact

theorem T5_root_key_matches_prescribed_shared_tile
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 5)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    {i j : Fin 160} (hshared : Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j))
    {root : BoxKey 5} (hr : root ∈ IndexedData5.geometry.profile i)
    (hroot : root.toKeyData 19200 ∈ keys5) :
    ∃ source ∈ IndexedData5.geometry.profile j,
      keySolid (root.toKeyData 19200)=p.euclidean '' keySolid (source.toKeyData 19200) := by
  obtain ⟨C,hCA,l,hl,hmatch,q,hq⟩ := T5_key_has_registered_whole_key_companion ht g hg A hroot
  obtain ⟨s,source,hs,hdecode⟩ := everyKey5_in_atlas l hl
  have hrootCollar : root.CollarValid 19200 (IndexedData5.geometry.facet i) := (atlas5_checked i).2.1 root hr
  have hsourceCollar : source.CollarValid 19200 (IndexedData5.geometry.facet s) := (atlas5_checked s).2.1 source hs
  have hdisq : Disjoint (interior T5) (interior (q.euclidean '' T5)) := by
    have h := ht.relative_copies_interior_disjoint g hg A C hCA
    rw [hq] at h
    exact h
  have hsolidq : keySolid (root.toKeyData 19200)=q.euclidean '' keySolid (source.toKeyData 19200) := by
    have h := relative_isometry_image_of_coincidence
      (keySolid (root.toKeyData 19200)) (keySolid l) (g A) (g C) hmatch
    rw [hq,← hdecode] at h
    exact h.symm
  have hsharedq := T5_shared_of_physical_matched_keySolids (by norm_num : (0 : ℤ)<19200)
    (IndexedData5.owned_checked i) (IndexedData5.owned_checked s) hdisq hrootCollar hsourceCollar hsolidq
  have hoccB : IsChairCell (p.inverseCell (IndexedData5.geometry.facet i).neighbor) := by
    rw [← shared_cell_neighbor hshared,p.inverseCell_cell]
    exact IndexedData5.owned_checked j
  have hoccC : IsChairCell (q.inverseCell (IndexedData5.geometry.facet i).neighbor) := by
    change IsChairCell (q.inverseCell (IndexedData5.facet i).neighbor)
    rw [← shared_cell_neighbor hsharedq,q.inverseCell_cell]
    exact IndexedData5.owned_checked s
  have hBC := T5_physical_tiles_eq_of_shared_registered_cell ht g hg A B C p q hp hq
    (IndexedData5.geometry.facet i).neighbor hoccB hoccC
  rw [← hBC] at hmatch
  have hsolidp : keySolid (root.toKeyData 19200)=p.euclidean '' keySolid (source.toKeyData 19200) := by
    have h := relative_isometry_image_of_coincidence
      (keySolid (root.toKeyData 19200)) (keySolid l) (g A) (g B) hmatch
    rw [hp,← hdecode] at h
    exact h.symm
  have hdisp : Disjoint (interior T5) (interior (p.euclidean '' T5)) := by
    have h := ht.relative_copies_interior_disjoint g hg A B hBA
    rw [hp] at h
    exact h
  have hsharedp := T5_shared_of_physical_matched_keySolids (by norm_num : (0 : ℤ)<19200)
    (IndexedData5.owned_checked i) (IndexedData5.owned_checked s) hdisp hrootCollar hsourceCollar hsolidp
  have hjs : j=s := IndexedData5.facet_injective (shared_source_unique hshared hsharedp)
  exact ⟨source,hjs.symm ▸ hs,hsolidp⟩

#print axioms T5_root_key_matches_prescribed_shared_tile

theorem T7_root_key_matches_prescribed_shared_tile
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (A B : tiles) (hBA : B ≠ A) (p : Pose 7)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    {i j : Fin 896} (hshared : Shared p (IndexedData7.geometry.facet i) (IndexedData7.geometry.facet j))
    {root : BoxKey 7} (hr : root ∈ IndexedData7.geometry.profile i)
    (hroot : root.toKeyData 188160 ∈ keys7) :
    ∃ source ∈ IndexedData7.geometry.profile j,
      keySolid (root.toKeyData 188160)=p.euclidean '' keySolid (source.toKeyData 188160) := by
  obtain ⟨C,hCA,l,hl,hmatch,q,hq⟩ := T7_key_has_registered_whole_key_companion ht g hg A hroot
  obtain ⟨s,source,hs,hdecode⟩ := everyKey7_in_atlas l hl
  have hrootCollar : root.CollarValid 188160 (IndexedData7.geometry.facet i) := (atlas7_checked i).2.1 root hr
  have hsourceCollar : source.CollarValid 188160 (IndexedData7.geometry.facet s) := (atlas7_checked s).2.1 source hs
  have hdisq : Disjoint (interior T7) (interior (q.euclidean '' T7)) := by
    have h := ht.relative_copies_interior_disjoint g hg A C hCA
    rw [hq] at h
    exact h
  have hsolidq : keySolid (root.toKeyData 188160)=q.euclidean '' keySolid (source.toKeyData 188160) := by
    have h := relative_isometry_image_of_coincidence
      (keySolid (root.toKeyData 188160)) (keySolid l) (g A) (g C) hmatch
    rw [hq,← hdecode] at h
    exact h.symm
  have hsharedq := T7_shared_of_physical_matched_keySolids (by norm_num : (0 : ℤ)<188160)
    (IndexedData7.owned_checked i) (IndexedData7.owned_checked s) hdisq hrootCollar hsourceCollar hsolidq
  have hoccB : IsChairCell (p.inverseCell (IndexedData7.geometry.facet i).neighbor) := by
    rw [← shared_cell_neighbor hshared,p.inverseCell_cell]
    exact IndexedData7.owned_checked j
  have hoccC : IsChairCell (q.inverseCell (IndexedData7.geometry.facet i).neighbor) := by
    change IsChairCell (q.inverseCell (IndexedData7.facet i).neighbor)
    rw [← shared_cell_neighbor hsharedq,q.inverseCell_cell]
    exact IndexedData7.owned_checked s
  have hBC := T7_physical_tiles_eq_of_shared_registered_cell ht g hg A B C p q hp hq
    (IndexedData7.geometry.facet i).neighbor hoccB hoccC
  rw [← hBC] at hmatch
  have hsolidp : keySolid (root.toKeyData 188160)=p.euclidean '' keySolid (source.toKeyData 188160) := by
    have h := relative_isometry_image_of_coincidence
      (keySolid (root.toKeyData 188160)) (keySolid l) (g A) (g B) hmatch
    rw [hp,← hdecode] at h
    exact h.symm
  have hdisp : Disjoint (interior T7) (interior (p.euclidean '' T7)) := by
    have h := ht.relative_copies_interior_disjoint g hg A B hBA
    rw [hp] at h
    exact h
  have hsharedp := T7_shared_of_physical_matched_keySolids (by norm_num : (0 : ℤ)<188160)
    (IndexedData7.owned_checked i) (IndexedData7.owned_checked s) hdisp hrootCollar hsourceCollar hsolidp
  have hjs : j=s := IndexedData7.facet_injective (shared_source_unique hshared hsharedp)
  exact ⟨source,hjs.symm ▸ hs,hsolidp⟩

#print axioms T7_root_key_matches_prescribed_shared_tile

end SparseMonotiles
