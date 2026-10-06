module

public import SparseMonotiles.StripCreaseCrossingPyramid
public import SparseMonotiles.GenericRidgePoints

@[expose] public section

/-! # Exact rank bounds for the pruned side-face boundary equations -/
namespace SparseMonotiles
open Set

theorem pyramidSideBoundaryFacet_injective {n : ℕ} (i : Fin n) :
    Function.Injective (pyramidSideBoundaryFacet i) := by
  intro a b h
  cases a with
  | none => cases b <;> simpa [pyramidSideBoundaryFacet] using h
  | some a =>
      cases b with
      | none => simpa [pyramidSideBoundaryFacet] using h
      | some b =>
          rcases a with ⟨a,c⟩
          rcases b with ⟨b,d⟩
          have hh : a.val = b.val ∧ c = d := by simpa [pyramidSideBoundaryFacet] using h
          have hab : a = b := Subtype.ext hh.1
          simp [hab,hh.2]

/-- Every retained boundary normal has zero selected-axis coordinate. -/
theorem pyramidSideBoundary_normal_selected_zero {n : ℕ}
    (s : Fin n → Bool → ℝ) (i : Fin n) (a : PyramidSideBoundaryIndex i) :
    pyramidFacetSlopeNormal s (pyramidSideBoundaryFacet i a) i.castSucc = 0 := by
  cases a with
  | none => simp [pyramidSideBoundaryFacet,pyramidFacetSlopeNormal,pyramidBaseNormal,
      EuclideanSpace.single_apply,Ne.symm (Fin.castSucc_ne_last i)]
  | some a =>
      rcases a with ⟨j,b⟩
      exact pyramidSlopeNormal_other i j.val (Ne.symm j.property) b (s j.val b)

/-- The selected side normal and any two distinct retained boundary normals
are genuinely independent, even for an opposite pair on another axis. -/
theorem pyramidSideBoundary_triple_linearIndependent {n : ℕ}
    (s : Fin n → Bool → ℝ) (hs : ∀ i b, 0 < s i b)
    (i : Fin n) (b : Bool) (a c : PyramidSideBoundaryIndex i) (hac : a ≠ c) :
    LinearIndependent ℝ ![pyramidFacetSlopeNormal s (some (i,b)),
      pyramidFacetSlopeNormal s (pyramidSideBoundaryFacet i a),
      pyramidFacetSlopeNormal s (pyramidSideBoundaryFacet i c)] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have hz := congrArg (fun v : Point (n+1) => v i.castSucc) hg
  have hz' : g 0*(if b then s i b else -s i b) = 0 := by
    simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two] at hz
    change g 0 * pyramidFacetSlopeNormal s (some (i,b)) i.castSucc +
      g 1 * pyramidFacetSlopeNormal s (pyramidSideBoundaryFacet i a) i.castSucc +
      g 2 * pyramidFacetSlopeNormal s (pyramidSideBoundaryFacet i c) i.castSucc = 0 at hz
    rw [pyramidSideBoundary_normal_selected_zero,pyramidSideBoundary_normal_selected_zero,
      mul_zero,mul_zero,add_zero,add_zero] at hz
    simpa only [pyramidFacetSlopeNormal,pyramidSlopeNormal_same] using hz
  have hne : (if b then s i b else -s i b) ≠ 0 := by
    cases b
    · exact neg_ne_zero.mpr (ne_of_gt (hs i false))
    · exact ne_of_gt (hs i true)
  have hg0 : g 0 = 0 := (mul_eq_zero.mp hz').resolve_right hne
  have hind := pyramidFacetSlopeNormal_pair_linearIndependent s hs
    (pyramidSideBoundaryFacet i a) (pyramidSideBoundaryFacet i c)
    (fun heq => hac (pyramidSideBoundaryFacet_injective i heq))
  have hpair : ∀ j : Fin 2, (![g 1,g 2] : Fin 2 → ℝ) j = 0 :=
    Fintype.linearIndependent_iff.mp hind ![g 1,g 2] (by
      simpa [Fin.sum_univ_two,Fin.sum_univ_three,hg0] using hg)
  intro j
  fin_cases j
  · exact hg0
  · exact hpair 0
  · exact hpair 1

/-- Any affine locus satisfying those three actual key equations has ambient
codimension at least three. Empty loci are included without a nonemptiness
premise. -/
theorem keySideBoundary_triple_locus_codimension {n : ℕ} (hn : 2 ≤ n)
    (k : KeyData (n+1)) (hh : 0 < keyPyramidHeight k)
    (hd : ∀ j b, 0 < keySideDistance k j b)
    (i : Fin n) (b : Bool) (a c : PyramidSideBoundaryIndex i) (hac : a ≠ c)
    (L : AffineSubspace ℝ (Point (n+1)))
    (hselected : ∀ x ∈ L, keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0)
    (ha : ∀ x ∈ L, keyPyramidHalfspaceSlack k
      (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) x = 0)
    (hc : ∀ x ∈ L, keyPyramidHalfspaceSlack k
      (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i c)) x = 0) :
    Module.finrank ℝ L.direction + 3 ≤ n+1 := by
  classical
  by_cases hL : (L : Set (Point (n+1))).Nonempty
  · obtain ⟨p,hp⟩ := hL
    let f : Fin 3 → PyramidFacetIndex n :=
      ![some (i,b),pyramidSideBoundaryFacet i a,pyramidSideBoundaryFacet i c]
    let N : Fin 3 → Point (n+1) := fun j => pyramidFacetSlopeNormal (keySideSlope k) (f j)
    have hN : LinearIndependent ℝ N := by
      have heq : N = ![pyramidFacetSlopeNormal (keySideSlope k) (some (i,b)),
          pyramidFacetSlopeNormal (keySideSlope k) (pyramidSideBoundaryFacet i a),
          pyramidFacetSlopeNormal (keySideSlope k) (pyramidSideBoundaryFacet i c)] := by
        funext j; fin_cases j <;> rfl
      rw [heq]
      exact pyramidSideBoundary_triple_linearIndependent (keySideSlope k)
        (fun j c => div_pos hh (hd j c)) i b a c hac
    have hzero (j : Fin 3) (x : Point (n+1)) (hx : x ∈ L) :
        keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (f j)) x = 0 := by
      fin_cases j
      · exact hselected x hx
      · exact ha x hx
      · exact hc x hx
    have hm (j : Fin 3) : N j ∈ L.directionᗮ := by
      apply normal_mem_ridge_orthogonal ⟨p,hp⟩ (le_refl L)
        (c := inner (𝕜 := ℝ) (N j) p)
      intro x hx
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

/-- A pruned genuine side-face slack in any intrinsic affine chart. -/
noncomputable def keySideBoundarySlack {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (k : KeyData (n+1)) (i : Fin n)
    (chart : E →ᵃ[ℝ] Point (n+1)) (a : PyramidSideBoundaryIndex i) : E →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ E
      (keyPyramidHalfspaceBound k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a))) -
    (keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex
      (pyramidSideBoundaryFacet i a))).toAffineMap.comp chart

@[simp] theorem keySideBoundarySlack_apply {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (k : KeyData (n+1)) (i : Fin n)
    (chart : E →ᵃ[ℝ] Point (n+1)) (a : PyramidSideBoundaryIndex i) (x : E) :
    keySideBoundarySlack k i chart a x = keyPyramidHalfspaceSlack k
      (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) (chart x) := rfl

/-- Exact intrinsic codimension-two bound for every pair of distinct pruned
side-face boundary equations. This proves the avoidance hypothesis of the
strip-crossing theorem from positive actual key slopes. -/
theorem keySideBoundary_chart_pair_codimension {n : ℕ} (hn : 2 ≤ n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : KeyData (n+1)) (hh : 0 < keyPyramidHeight k)
    (hd : ∀ j b, 0 < keySideDistance k j b) (i : Fin n) (b : Bool)
    (chart : E →ᵃ[ℝ] Point (n+1)) (hinj : Function.Injective chart)
    (hdim : Module.finrank ℝ E = n)
    (hselected : ∀ x, keyPyramidHalfspaceSlack k (.inr (i,b)) (chart x) = 0)
    (a c : PyramidSideBoundaryIndex i) (hac : a ≠ c) :
    Module.finrank ℝ ((affineFormPlane (keySideBoundarySlack k i chart a) 0 ⊓
      affineFormPlane (keySideBoundarySlack k i chart c) 0).direction) + 2 ≤
        Module.finrank ℝ E := by
  let L := affineFormPlane (keySideBoundarySlack k i chart a) 0 ⊓
    affineFormPlane (keySideBoundarySlack k i chart c) 0
  have hcodim := keySideBoundary_triple_locus_codimension hn k hh hd i b a c hac (L.map chart)
    (by
      rintro x ⟨y,hy,rfl⟩
      exact hselected y)
    (by
      rintro x ⟨y,hy,rfl⟩
      exact (mem_affineFormPlane _ _ _).mp hy.1)
    (by
      rintro x ⟨y,hy,rfl⟩
      exact (mem_affineFormPlane _ _ _).mp hy.2)
  have heq : Module.finrank ℝ L.direction = Module.finrank ℝ (L.map chart).direction := by
    rw [AffineSubspace.map_direction]
    exact (L.direction.equivMapOfInjective chart.linear
      (chart.linear_injective_iff.mpr hinj)).finrank_eq
  change Module.finrank ℝ L.direction+2 ≤ Module.finrank ℝ E
  rw [heq,hdim]
  omega

#print axioms keySideBoundary_chart_pair_codimension
#print axioms pyramidSideBoundaryFacet_injective
#print axioms pyramidSideBoundary_triple_linearIndependent
#print axioms keySideBoundary_triple_locus_codimension
end SparseMonotiles
