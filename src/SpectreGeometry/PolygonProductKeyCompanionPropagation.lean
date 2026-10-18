module

public import PhysicalRegistration.ConnectedCover
public import SpectreGeometry.PolygonProductKeyCreaseCompactness
public import SpectreGeometry.PolygonProductKeyPacking

@[expose] public section


/-! Actual no-switching on a complete optimized P×P key crease complex. Local
complementary-crease matches on dense base/side subsets are the only matching
input. Compactness, finite neighbors, disjoint actual collars, and the proved
three-key exclusion upgrade them to one whole companion complex. -/
namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration
open scoped InnerProductSpace Topology
open Set
noncomputable section

/-- Arbitrary-index form of the proved three-key exclusion. -/
theorem no_three_distinct_key_incidents {ι : Type*}
    (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i))) (interior (placedPolygonProductKeyBody (f j))))
    (r i j : ι) (hri : r ≠ i) (hrj : r ≠ j) (hij : i ≠ j)
    (u v w : ProductKeySite) (x : EFour)
    (hr : x ∈ placedProductKeyGraphWindow (f r) u)
    (hi : x ∈ placedProductKeyGraphWindow (f i) v)
    (hj : x ∈ placedProductKeyGraphWindow (f j) w) : False := by
  let idx : Fin 3 → ι := ![r, i, j]
  have hinj : Function.Injective idx := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all [idx]
  apply no_three_placed_polygon_product_key_graph_windows (fun k => f (idx k)) ![u, v, w] x
  · intro k
    fin_cases k
    · simpa [idx] using hr
    · simpa [idx] using hi
    · simpa [idx] using hj
  · intro k l hkl
    exact hdisjoint (fun h => hkl (hinj h))

/-- Placed closed key complexes are actual subsets of the placed body. -/
theorem placed_creaseComplex_subset_body  (f : EFour ≃ᵢ EFour) (u : ProductKeySite) :
    f '' creaseComplex u ⊆ placedPolygonProductKeyBody f := by
  apply image_mono
  exact (creaseComplex_subset_frontier u).trans polygon_product_key_body_isClosed.frontier_subset

/-- The full actual root complex has exactly one other indexed key complex
as companion once dense local base/side complementary matches are supplied.
No whole-feature or connected-contact-graph premise is used. -/
theorem whole_crease_companion_of_dense_matches
    {ι : Type*} (f : ι → EFour ≃ᵢ EFour)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedPolygonProductKeyBody (f i))) (interior (placedPolygonProductKeyBody (f j))))
    (root : ι) (u : ProductKeySite)
    (hbase : ∀ s : ProductKeySide, ∃ D : Set (EFour),
      closure D = f root '' baseCrease u s ∧
      ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : ProductKeySite, x ∈ f i '' creaseComplex v)
    (hside : ∀ s t : ProductKeySide, s.1 ≠ t.1 → ∃ D : Set (EFour),
      closure D = f root '' sideCrease u s t ∧
      ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : ProductKeySite, x ∈ f i '' creaseComplex v) :
    ∃! iv : ι × ProductKeySite, iv.1 ≠ root ∧
      f root '' creaseComplex u ⊆ f iv.1 '' creaseComplex iv.2 := by
  classical
  let C := f root '' creaseComplex u
  have hCcompact : IsCompact C := (creaseComplex_isCompact u).image (f root).continuous
  have hCconnected : IsConnected C :=
    (creaseComplex_isConnected u).image (f root) (f root).continuous.continuousOn
  let I : Set ι := {i | i ≠ root ∧ (placedPolygonProductKeyBody (f i) ∩ C).Nonempty}
  have hI : I.Finite := (finite_placedPolygonProductKeyBody_inter_compact f hdisjoint C hCcompact).subset
    (fun _ hi => hi.2)
  let : Fintype I := hI.fintype
  let K : I × ProductKeySite → Set (EFour) := fun iv => f iv.1.val '' creaseComplex iv.2
  have hK : ∀ iv, IsClosed (K iv) := fun iv =>
    ((creaseComplex_isCompact iv.2).image (f iv.1.val).continuous).isClosed
  have hmatch (D : Set (EFour)) (hDC : D ⊆ C)
      (hmatches : ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : ProductKeySite, x ∈ f i '' creaseComplex v) :
      D ⊆ ⋃ iv, K iv := by
    intro x hx
    obtain ⟨i, hir, v, hv⟩ := hmatches x hx
    have hi : i ∈ I := ⟨hir, x, placed_creaseComplex_subset_body (f i) v hv, hDC hx⟩
    exact mem_iUnion.mpr ⟨(⟨i, hi⟩, v), hv⟩
  have hcover : C ⊆ ⋃ iv, K iv := by
    rintro x ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
      obtain ⟨D, hD, hlocal⟩ := hbase s
      have hDC : closure D ⊆ C := by rw [hD]; exact image_mono (baseCrease_subset_creaseComplex u s)
      exact closure_minimal (hmatch D (subset_closure.trans hDC) hlocal)
        (isClosed_iUnion_of_finite hK) (by rw [hD]; exact ⟨y, hs, rfl⟩)
    · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
      obtain ⟨t, ht⟩ := mem_iUnion.mp hs
      obtain ⟨D, hD, hlocal⟩ := hside s t.val t.property
      have hDC : closure D ⊆ C := by
        rw [hD]; exact image_mono (sideCrease_subset_creaseComplex u s t.val t.property)
      exact closure_minimal (hmatch D (subset_closure.trans hDC) hlocal)
        (isClosed_iUnion_of_finite hK) (by rw [hD]; exact ⟨y, ht, rfl⟩)
  have hsep : Pairwise fun iv jv : I × ProductKeySite => Disjoint (C ∩ K iv) (C ∩ K jv) := by
    intro iv jv hij
    apply Set.disjoint_left.mpr
    rintro x ⟨hxC, hxi⟩ ⟨_, hxj⟩
    by_cases htiles : iv.1.val = jv.1.val
    · have hsites : iv.2 ≠ jv.2 := by
        intro hs
        apply hij
        exact Prod.ext (Subtype.ext htiles) hs
      obtain ⟨y, hy, hxy⟩ := hxi
      obtain ⟨z, hz, hxz⟩ := hxj
      have hyz : y = z := (f iv.1.val).injective (by simpa [htiles] using hxy.trans hxz.symm)
      subst z
      exact Set.disjoint_left.mp (creaseComplex_pairwise_disjoint hsites) hy hz
    · have hrootkey : x ∈ placedProductKeyGraphWindow (f root) u := image_mono (creaseComplex_subset_graphWindow u) hxC
      have hikey : x ∈ placedProductKeyGraphWindow (f iv.1.val) iv.2 :=
        image_mono (creaseComplex_subset_graphWindow iv.2) hxi
      have hjkey : x ∈ placedProductKeyGraphWindow (f jv.1.val) jv.2 :=
        image_mono (creaseComplex_subset_graphWindow jv.2) hxj
      exact no_three_distinct_key_incidents f hdisjoint root iv.1.val jv.1.val
        (Ne.symm iv.1.property.1) (Ne.symm jv.1.property.1) htiles u iv.2 jv.2 x
        hrootkey hikey hjkey
  obtain ⟨iv, hiv, huniq⟩ := connected_unique_closed_companion hCconnected K hK hcover hsep
  refine ⟨(iv.1.val, iv.2), ⟨iv.1.property.1, hiv⟩, ?_⟩
  rintro ⟨j, v⟩ ⟨hjr, hj⟩
  obtain ⟨x, hxC⟩ := hCconnected.nonempty
  have hjI : j ∈ I := ⟨hjr, x, placed_creaseComplex_subset_body (f j) v (hj hxC), hxC⟩
  have he : (⟨j, hjI⟩, v) = iv := huniq _ hj
  exact congrArg (fun z : I × ProductKeySite => (z.1.val, z.2)) he

end
end SpectreGeometry.ProductCrease
