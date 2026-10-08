module

public import SparseMonotiles.StripCreaseCrossingRank

@[expose] public section

/-! # The selected crossing crease has genuine ambient codimension two -/
namespace SparseMonotiles
open Set

/-- Any affine locus satisfying two distinct genuine key facet equations has
codimension at least two, without an active-point or non-apex premise. -/
theorem keyFacet_pair_locus_codimension {n : ℕ} (hn : 1 ≤ n)
    (k : KeyData (n+1)) (hh : 0 < keyPyramidHeight k)
    (hd : ∀ j b, 0 < keySideDistance k j b)
    (a b : PyramidFacetIndex n) (hab : a ≠ b)
    (L : AffineSubspace ℝ (Point (n+1)))
    (ha : ∀ x ∈ L, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) x = 0)
    (hb : ∀ x ∈ L, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex b) x = 0) :
    Module.finrank ℝ L.direction + 2 ≤ n+1 := by
  classical
  by_cases hL : (L : Set (Point (n+1))).Nonempty
  · obtain ⟨p,hp⟩ := hL
    let f : Fin 2 → PyramidFacetIndex n := ![a,b]
    let N : Fin 2 → Point (n+1) :=
      ![pyramidFacetSlopeNormal (keySideSlope k) a,pyramidFacetSlopeNormal (keySideSlope k) b]
    have hN : LinearIndependent ℝ N := pyramidFacetSlopeNormal_pair_linearIndependent
      (keySideSlope k) (fun j c => div_pos hh (hd j c)) a b hab
    have hzero (j : Fin 2) (x : Point (n+1)) (hx : x ∈ L) :
        keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (f j)) x = 0 := by
      fin_cases j
      · exact ha x hx
      · exact hb x hx
    have hm (j : Fin 2) : N j ∈ L.directionᗮ := by
      have hj : N j = pyramidFacetSlopeNormal (keySideSlope k) (f j) := by fin_cases j <;> rfl
      apply normal_mem_ridge_orthogonal ⟨p,hp⟩ (le_refl L)
        (c := inner (𝕜 := ℝ) (N j) p)
      intro x hx
      rw [hj]
      apply (key_facet_form_eq_iff_normal_inner_eq k hd (f j) x p).mp
      exact (sub_eq_zero.mp (hzero j x hx)).symm.trans (sub_eq_zero.mp (hzero j p hp))
    have hN' : LinearIndependent ℝ (fun j => (⟨N j,hm j⟩ : L.directionᗮ)) :=
      LinearIndependent.of_comp L.directionᗮ.subtype hN
    have hdim := hN'.fintype_card_le_finrank
    have hsum := L.direction.finrank_add_finrank_orthogonal
    simp only [Fintype.card_fin,finrank_euclideanSpace_fin] at hdim hsum
    omega
  · have hbot : L = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.mp hL)
    rw [hbot,AffineSubspace.direction_bot,finrank_bot]
    omega

/-- A nonempty affine equation has direction the kernel of its linear part. -/
theorem affineFormPlane_direction_of_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →ᵃ[ℝ] ℝ) {p : E} (hp : f p = 0) :
    (affineFormPlane f 0).direction = LinearMap.ker f.linear := by
  have heq : affineFormPlane f 0 = AffineSubspace.mk' p (LinearMap.ker f.linear) := by
    ext x
    rw [mem_affineFormPlane,AffineSubspace.mem_mk',LinearMap.mem_ker]
    have hx := f.linearMap_vsub x p
    change f.linear (x-p) = f x-f p at hx
    change f x = 0 ↔ f.linear (x-p) = 0
    rw [hx,hp,sub_zero]
  rw [heq,AffineSubspace.direction_mk']

/-- In an intrinsic isomorphic-dimensional chart of a selected side plane,
each nonempty pruned boundary plane has dimension exactly `n−1`, and its
ambient image is a genuine codimension-two ridge. -/
theorem keySideBoundary_chart_crease_codimension {n : ℕ} (hn : 2 ≤ n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : KeyData (n+1)) (hh : 0 < keyPyramidHeight k)
    (hd : ∀ j b, 0 < keySideDistance k j b) (i : Fin n) (b : Bool)
    (chart : E →ᵃ[ℝ] Point (n+1)) (hinj : Function.Injective chart)
    (hdim : Module.finrank ℝ E = n)
    (hselected : ∀ x, keyPyramidHalfspaceSlack k (.inr (i,b)) (chart x) = 0)
    (a : PyramidSideBoundaryIndex i) {p : E}
    (hp : keySideBoundarySlack k i chart a p = 0) :
    Module.finrank ℝ (affineFormPlane (keySideBoundarySlack k i chart a) 0).direction + 1 = n ∧
    Module.finrank ℝ ((affineFormPlane (keySideBoundarySlack k i chart a) 0).map chart).direction
      + 2 = n+1 := by
  let f := keySideBoundarySlack k i chart a
  let L := affineFormPlane f 0
  have hne : some (i,b) ≠ pyramidSideBoundaryFacet i a := by
    cases a with
    | none => simp [pyramidSideBoundaryFacet]
    | some a =>
        rcases a with ⟨j,c⟩
        intro heq
        have hh := congrArg (fun a : PyramidFacetIndex n => a.map Prod.fst) heq
        have hij : i = j.val := by simpa [pyramidSideBoundaryFacet] using hh
        exact j.property hij.symm
  have hcodim := keyFacet_pair_locus_codimension (by omega : 1 ≤ n) k hh hd
    (some (i,b)) (pyramidSideBoundaryFacet i a) hne (L.map chart)
    (by rintro x ⟨y,hy,rfl⟩; exact hselected y)
    (by rintro x ⟨y,hy,rfl⟩; exact (mem_affineFormPlane _ _ _).mp hy)
  have heq : Module.finrank ℝ L.direction = Module.finrank ℝ (L.map chart).direction := by
    rw [AffineSubspace.map_direction]
    exact (L.direction.equivMapOfInjective chart.linear
      (chart.linear_injective_iff.mpr hinj)).finrank_eq
  have hker : L.direction = LinearMap.ker f.linear := affineFormPlane_direction_of_zero f hp
  have hnullity := f.linear.finrank_range_add_finrank_ker
  have hrange := (LinearMap.range f.linear).finrank_le
  simp only [Module.finrank_self] at hrange
  rw [← hker,hdim] at hnullity
  change Module.finrank ℝ L.direction+1 = n ∧ Module.finrank ℝ (L.map chart).direction+2=n+1
  omega

#print axioms keyFacet_pair_locus_codimension
#print axioms affineFormPlane_direction_of_zero
#print axioms keySideBoundary_chart_crease_codimension
end SparseMonotiles
