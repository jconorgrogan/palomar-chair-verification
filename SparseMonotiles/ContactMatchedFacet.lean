module

public import SparseMonotiles.ContactFacetCovariance
public import SparseMonotiles.ContactPhysicalOverlapTiles
public import SparseMonotiles.KeySupportAtlas

@[expose] public section

/-!
A registered physical solid match determines opposed full carrier facets.
Collar containment gives their common unoriented facet; disjoint physical
interiors exclude coincident owner cells using the checked unit-cell centres.
The concrete T5/T7 corollaries discharge those centre premises with their exact
whole-core certificates. Contact-to-solid coincidence is a separate input.
-/
namespace SparseMonotiles.Contact

/-- This adapter works for arbitrary cell-supported bodies and actual nonempty
solids; neither a material coefficient nor a shared-facet premise is assumed. -/
theorem Pose.shared_of_physical_matched_solids {d : ℕ} {p : Pose d}
    {A B K L : Set (Point d)} {rootCells sourceCells : Finset (Cell d)}
    (root_centres : ∀ c ∈ rootCells, cellCentre c ∈ interior A)
    (source_centres : ∀ c ∈ sourceCells, cellCentre c ∈ interior B)
    {a b : Facet d} (ha : a.cell ∈ rootCells) (hb : b.cell ∈ sourceCells)
    (disjoint : Disjoint (interior A) (interior (p.euclidean '' B)))
    (hne : L.Nonempty)
    (hK : K ⊆ gridFacetCollar a.gridFacet) (hL : L ⊆ gridFacetCollar b.gridFacet)
    (heq : K = p.euclidean '' L) : Shared p a b := by
  apply p.shared_of_matched_solids hne hK hL heq
  intro he
  have hd := carrier_disjoint_of_physical_interiors root_centres source_centres disjoint
  exact Finset.disjoint_left.mp hd ha (Finset.mem_image.mpr ⟨b.cell, hb, he.symm⟩)

/-- Integer collar certificates suffice for actual decoded pyramid solids. -/
theorem Pose.shared_of_physical_matched_keySolids {d : ℕ} {p : Pose d} {den : ℤ}
    (hd : 0 < den) {A B : Set (Point d)} {rootCells sourceCells : Finset (Cell d)}
    (root_centres : ∀ c ∈ rootCells, cellCentre c ∈ interior A)
    (source_centres : ∀ c ∈ sourceCells, cellCentre c ∈ interior B)
    {a b : Facet d} (ha : a.cell ∈ rootCells) (hb : b.cell ∈ sourceCells)
    (disjoint : Disjoint (interior A) (interior (p.euclidean '' B)))
    {root source : BoxKey d} (hr : root.CollarValid den a) (hs : source.CollarValid den b)
    (heq : keySolid (root.toKeyData den) = p.euclidean '' keySolid (source.toKeyData den)) :
    Shared p a b := by
  apply p.shared_of_physical_matched_solids root_centres source_centres ha hb disjoint
    ⟨SparseMonotiles.rationalPoint (source.toKeyData den).apex, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
    (BoxKey.keySolid_subset_collar hd hr) (BoxKey.keySolid_subset_collar hd hs) heq

/-- For the actual five-dimensional tile, occupied owner cells and the checked
collars turn a registered key-solid match into `Shared`. -/
theorem T5_shared_of_physical_matched_keySolids {p : Pose 5} {den : ℤ}
    (hd : 0 < den) {a b : Facet 5} (ha : IsChairCell a.cell) (hb : IsChairCell b.cell)
    (disjoint : Disjoint (interior T5) (interior (p.euclidean '' T5)))
    {root source : BoxKey 5} (hr : root.CollarValid den a) (hs : source.CollarValid den b)
    (heq : keySolid (root.toKeyData den) = p.euclidean '' keySolid (source.toKeyData den)) :
    Shared p a b := by
  exact p.shared_of_physical_matched_keySolids hd
    (rootCells := chairCells 5) (sourceCells := chairCells 5)
    (fun c hc => T5_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    (fun c hc => T5_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    ((mem_chairCells _).mpr ha) ((mem_chairCells _).mpr hb) disjoint hr hs heq

/-- The analogous adapter for the actual seven-dimensional tile. -/
theorem T7_shared_of_physical_matched_keySolids {p : Pose 7} {den : ℤ}
    (hd : 0 < den) {a b : Facet 7} (ha : IsChairCell a.cell) (hb : IsChairCell b.cell)
    (disjoint : Disjoint (interior T7) (interior (p.euclidean '' T7)))
    {root source : BoxKey 7} (hr : root.CollarValid den a) (hs : source.CollarValid den b)
    (heq : keySolid (root.toKeyData den) = p.euclidean '' keySolid (source.toKeyData den)) :
    Shared p a b := by
  exact p.shared_of_physical_matched_keySolids hd
    (rootCells := chairCells 7) (sourceCells := chairCells 7)
    (fun c hc => T7_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    (fun c hc => T7_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    ((mem_chairCells _).mpr ha) ((mem_chairCells _).mpr hb) disjoint hr hs heq

#print axioms Pose.shared_of_physical_matched_solids
#print axioms T5_shared_of_physical_matched_keySolids
#print axioms T7_shared_of_physical_matched_keySolids
end SparseMonotiles.Contact
