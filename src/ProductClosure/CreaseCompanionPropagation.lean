module

public import PhysicalRegistration.ConnectedCover
public import ProductClosure.CreaseConnectivity
public import ProductClosure.PhysicalTilingGerms

@[expose] public section

/-! Actual no-switching on a complete native key crease complex. Local
complementary-crease matches on dense base/side subsets are the only matching
input. Compactness, finite neighbors, disjoint native tubes, and the proved
three-key exclusion upgrade them to one whole companion complex. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- Arbitrary-index form of the proved three-key exclusion. -/
theorem no_three_distinct_key_incidents {J : ℕ} [NeZero m] {ι : Type*}
    (hm : 2 ≤ m) (a : Coefficients polyCells J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (r i j : ι) (hri : r ≠ i) (hrj : r ≠ j) (hij : i ≠ j)
    (u v w : Site polyCells) (x : Space m)
    (hr : x ∈ placedKeyGraph a (f r) u)
    (hi : x ∈ placedKeyGraph a (f i) v)
    (hj : x ∈ placedKeyGraph a (f j) w) : False := by
  let idx : Fin 3 → ι := ![r, i, j]
  have hinj : Function.Injective idx := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all [idx]
  apply no_three_placed_key_graphs hm a (fun k => f (idx k)) ![u, v, w] x
  · intro k
    fin_cases k
    · simpa [idx] using hr
    · simpa [idx] using hi
    · simpa [idx] using hj
  · intro k l hkl
    exact hdisjoint (fun h => hkl (hinj h))

/-- Two distinct native key complexes are separated by actual disjoint tubes. -/
theorem creaseComplex_pairwise_disjoint {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) : Pairwise fun u v : Site polyCells =>
      Disjoint (creaseComplex a u) (creaseComplex a v) := by
  intro u v huv
  apply (closedTube_pairwise_disjoint hm huv).mono
  · intro x hx
    exact (creaseComplex_subset_keyGraph a u hx).1
  · intro x hx
    exact (creaseComplex_subset_keyGraph a v hx).1

/-- Placed closed key complexes are actual subsets of the placed body. -/
theorem placed_creaseComplex_subset_body {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (f : Space m ≃ᵢ Space m) (u : Site polyCells) :
    f '' creaseComplex a u ⊆ placedBody a f := by
  apply image_mono
  exact (creaseComplex_subset_keyGraph a u).trans
    ((keyGraph_subset_frontier_body hm a u).trans (body_isCompact a).isClosed.frontier_subset)

/-- The full actual root complex has exactly one other indexed key complex
as companion once dense local base/side complementary matches are supplied.
No whole-feature or connected-contact-graph premise is used. -/
theorem whole_crease_companion_of_dense_matches
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (root : ι) (u : Site polyCells)
    (hbase : ∀ s : Side m, ∃ D : Set (Space m),
      closure D = f root '' baseCrease a u s ∧
      ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : Site polyCells, x ∈ f i '' creaseComplex a v)
    (hside : ∀ s t : Side m, s.1 ≠ t.1 → ∃ D : Set (Space m),
      closure D = f root '' sideCrease a u s t ∧
      ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : Site polyCells, x ∈ f i '' creaseComplex a v) :
    ∃! iv : ι × Site polyCells, iv.1 ≠ root ∧
      f root '' creaseComplex a u ⊆ f iv.1 '' creaseComplex a iv.2 := by
  classical
  let C := f root '' creaseComplex a u
  have hCcompact : IsCompact C := (creaseComplex_isCompact a u).image (f root).continuous
  have hCconnected : IsConnected C :=
    (creaseComplex_isConnected hm a u).image (f root) (f root).continuous.continuousOn
  let I : Set ι := {i | i ≠ root ∧ (placedBody a (f i) ∩ C).Nonempty}
  have hI : I.Finite := (finite_placedBody_inter_compact a f hdisjoint C hCcompact).subset
    (fun _ hi => hi.2)
  let : Fintype I := hI.fintype
  let K : I × Site polyCells → Set (Space m) := fun iv => f iv.1.val '' creaseComplex a iv.2
  have hK : ∀ iv, IsClosed (K iv) := fun iv =>
    ((creaseComplex_isCompact a iv.2).image (f iv.1.val).continuous).isClosed
  have hmatch (D : Set (Space m)) (hDC : D ⊆ C)
      (hmatches : ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : Site polyCells, x ∈ f i '' creaseComplex a v) :
      D ⊆ ⋃ iv, K iv := by
    intro x hx
    obtain ⟨i, hir, v, hv⟩ := hmatches x hx
    have hi : i ∈ I := ⟨hir, x, placed_creaseComplex_subset_body hm a (f i) v hv, hDC hx⟩
    exact mem_iUnion.mpr ⟨(⟨i, hi⟩, v), hv⟩
  have hcover : C ⊆ ⋃ iv, K iv := by
    rintro x ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
      obtain ⟨D, hD, hlocal⟩ := hbase s
      have hDC : closure D ⊆ C := by rw [hD]; exact image_mono (baseCrease_subset_creaseComplex a u s)
      exact closure_minimal (hmatch D (subset_closure.trans hDC) hlocal)
        (isClosed_iUnion_of_finite hK) (by rw [hD]; exact ⟨y, hs, rfl⟩)
    · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
      obtain ⟨t, ht⟩ := mem_iUnion.mp hs
      obtain ⟨D, hD, hlocal⟩ := hside s t.val t.property
      have hDC : closure D ⊆ C := by
        rw [hD]; exact image_mono (sideCrease_subset_creaseComplex a u s t.val t.property)
      exact closure_minimal (hmatch D (subset_closure.trans hDC) hlocal)
        (isClosed_iUnion_of_finite hK) (by rw [hD]; exact ⟨y, ht, rfl⟩)
  have hsep : Pairwise fun iv jv : I × Site polyCells => Disjoint (C ∩ K iv) (C ∩ K jv) := by
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
      exact Set.disjoint_left.mp (creaseComplex_pairwise_disjoint hm a hsites) hy hz
    · have hrootkey : x ∈ placedKeyGraph a (f root) u := image_mono (creaseComplex_subset_keyGraph a u) hxC
      have hikey : x ∈ placedKeyGraph a (f iv.1.val) iv.2 :=
        image_mono (creaseComplex_subset_keyGraph a iv.2) hxi
      have hjkey : x ∈ placedKeyGraph a (f jv.1.val) jv.2 :=
        image_mono (creaseComplex_subset_keyGraph a jv.2) hxj
      exact no_three_distinct_key_incidents hm a f hdisjoint root iv.1.val jv.1.val
        (Ne.symm iv.1.property.1) (Ne.symm jv.1.property.1) htiles u iv.2 jv.2 x
        hrootkey hikey hjkey
  obtain ⟨iv, hiv, huniq⟩ := connected_unique_closed_companion hCconnected K hK hcover hsep
  refine ⟨(iv.1.val, iv.2), ⟨iv.1.property.1, hiv⟩, ?_⟩
  rintro ⟨j, v⟩ ⟨hjr, hj⟩
  obtain ⟨x, hxC⟩ := hCconnected.nonempty
  have hjI : j ∈ I := ⟨hjr, x, placed_creaseComplex_subset_body hm a (f j) v (hj hxC), hxC⟩
  have he : (⟨j, hjI⟩, v) = iv := huniq _ hj
  exact congrArg (fun z : I × Site polyCells => (z.1.val, z.2)) he

end
end ProductClosure.NativeCompiler
