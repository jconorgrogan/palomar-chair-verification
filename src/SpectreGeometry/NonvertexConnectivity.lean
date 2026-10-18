module

public import SpectreGeometry.ContactConnectivity
public import SpectreGeometry.CountableComplement
public import Mathlib.Topology.Bases

@[expose] public section


/-! The actual tile contact graph remains connected after excluding every
placed vertex. This does not yet prove collinearity or whole-edge matching. -/
namespace SpectreGeometry.CompactTilingIncidence
noncomputable section
open Set
abbrev Plane := CompactPacking.Space 2

def ContactAway {ι : Type*} (F : ι → Set Plane) (S : Set Plane) (i j : ι) : Prop :=
  ∃ x, x ∈ F i ∧ x ∈ F j ∧ x ∉ S

theorem plane_rank_gt_one : 1 < Module.rank ℝ Plane := by
  rw [←Module.finrank_eq_rank]
  simp [Plane,CompactPacking.Space]

/-- Countably many excluded points cannot disconnect a planar closed-tile
contact graph when every tile retains nonempty interior. -/
theorem contact_connected_away_countable {ι : Type*} (F : ι → Set Plane)
    (hlocal : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hinterior : ∀ i, (interior (F i)).Nonempty) (hcover : ∀ x, ∃ i, x ∈ F i)
    (S : Set Plane) (hS : S.Countable) (i j : ι) :
    Relation.ReflTransGen (ContactAway F S) i j := by
  letI : PreconnectedSpace (Sᶜ : Set Plane) :=
    Subtype.preconnectedSpace (countable_compl_connected plane_rank_gt_one hS).isPreconnected
  let G : ι → Set (Sᶜ : Set Plane) := fun k => Subtype.val ⁻¹' F k
  have hGlocal : LocallyFinite G := hlocal.preimage_continuous continuous_subtype_val
  have hGclosed : ∀ k, IsClosed (G k) := fun k => (hclosed k).preimage continuous_subtype_val
  have hGnonempty : ∀ k, (G k).Nonempty := by
    intro k
    obtain ⟨x,hxS,hxI⟩ := (hS.dense_compl ℝ).exists_mem_open isOpen_interior (hinterior k)
    refine ⟨⟨x,hxS⟩,?_⟩
    change x ∈ F k
    exact interior_subset hxI
  have hGcover : ∀ x : (Sᶜ : Set Plane), ∃ k, x ∈ G k := fun x => hcover x
  have h := contact_connected G hGlocal hGclosed hGnonempty hGcover i j
  apply Relation.ReflTransGen.mono (r := Contact G) (p := ContactAway F S) ?_ i j h
  intro a b hab
  obtain ⟨x,hxa,hxb⟩ := hab
  exact ⟨x,hxa,hxb,x.property⟩

/-- Any arbitrary isometric packing of the body has a countable tile index. -/
theorem polygon_packing_countable {ι : Type*}
    (f : ι → Plane ≃ᵢ Plane)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody))) :
    Countable ι := by
  apply hdisjoint.countable_of_isOpen_disjoint (fun _ => isOpen_interior)
  intro i
  exact (euclideanBody_interior_nonempty.image (f i)).mono
    ((f i).toHomeomorph.isOpenMap.image_interior_subset _)

def placedVertices {ι : Type*} (f : ι → Plane ≃ᵢ Plane) : Set Plane :=
  Set.range (fun p : ι × Fin 14 => f p.1 (euclideanVertex p.2))

theorem placedVertices_countable {ι : Type*}
    (f : ι → Plane ≃ᵢ Plane)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody))) :
    (placedVertices f).Countable := by
  letI := polygon_packing_countable f hdisjoint
  exact Set.countable_range _

/-- The derived path can be chosen with each contact avoiding every vertex
of every tile in the original unrestricted-isometry physical tiling. -/
theorem polygon_tiling_nonvertex_contact_connected {ι : Type*}
    (f : ι → Plane ≃ᵢ Plane)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (i j : ι) :
    Relation.ReflTransGen (ContactAway (fun k => f k '' euclideanBody) (placedVertices f)) i j := by
  apply contact_connected_away_countable _ (CompactPacking.polygon_packing_locallyFinite f hdisjoint)
    (fun k => (euclideanBody_compact.image (f k).continuous).isClosed)
    _ hcover _ (placedVertices_countable f hdisjoint)
  intro k
  exact (euclideanBody_interior_nonempty.image (f k)).mono
    ((f k).toHomeomorph.isOpenMap.image_interior_subset _)

end
end SpectreGeometry.CompactTilingIncidence
