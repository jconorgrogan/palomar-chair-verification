module

public import SpectreGeometry.PolygonProductKeyNormalAngles
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section


/-!
# Exact rank obstructions for the actual 56-site product-key normals

Every vector here is the literal outward or affine-branch normal of
`PolygonProductKeyNormalAngles`. Independence follows from the actual
orthonormal site frames and the nonzero, distinct signed prime slopes.
No normal-rank, stratum-inventory, or certificate premise is assumed.
-/

namespace SpectreGeometry
open scoped InnerProductSpace
open Set
noncomputable section

/-- Each actual signed branch slope is nonzero. -/
theorem product_key_side_slope_ne_zero (u : ProductKeySite) (s : ProductKeySide) :
    productKeySideSlope u s ≠ 0 := by
  intro h
  have hs := (product_key_side_slope_sq u s).1
  simp [h] at hs

/-- The six signed prime slopes at one actual site distinguish branch labels. -/
theorem product_key_side_slope_injective (u : ProductKeySite) :
    Function.Injective (productKeySideSlope u) := by
  intro s t h
  have hlabel : (productKeySignedLabel u : ℝ) ≠ 0 := by
    exact_mod_cast productKeySignedLabel_ne_zero u
  have hN : (productKeyN : ℝ) ≠ 0 := by norm_num [productKeyN]
  simp only [productKeySideSlope] at h
  have hnum := (div_left_inj' hN).mp h
  rw [mul_assoc, mul_assoc] at hnum
  have hsigned := mul_left_cancel₀ hlabel hnum
  rcases s with ⟨i, b⟩
  rcases t with ⟨j, c⟩
  fin_cases i <;> cases b <;> fin_cases j <;> cases c <;>
    first | rfl | norm_num [productKeyPrime, productKeyPrimePairs] at hsigned

/-- The tangent component of an actual side normal, including the repeated-axis
case needed for the two opposite sides of one coordinate. -/
theorem product_key_side_normal_inner_tangent (u : ProductKeySite)
    (s : ProductKeySide) (i : Fin 3) :
    ⟪productKeySideNormal u s, productKeyTangent u i⟫_ℝ =
      if s.1 = i then -productKeySideSlope u s else 0 := by
  have horth : ⟪productKeyOutwardNormal u, productKeyTangent u i⟫_ℝ = 0 :=
    productKeyOutwardNormal_inner_tangent u i
  simp only [productKeySideNormal, inner_sub_left, real_inner_smul_left, horth, productKeyTangent_inner]
  split_ifs <;> simp

/-- The outward normal and an actual side normal are independent. -/
theorem product_key_base_normals_combination_eq_zero (u : ProductKeySite)
    (s : ProductKeySide) (c d : ℝ)
    (h : c • productKeyOutwardNormal u + d • productKeySideNormal u s = 0) :
    c = 0 ∧ d = 0 := by
  have ht := congrArg (fun v : EFour => ⟪v, productKeyTangent u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left,
    productKeyOutwardNormal_inner_tangent, product_key_side_normal_inner_tangent,
    ↓reduceIte, mul_zero, zero_add, inner_zero_left] at ht
  have hd : d = 0 :=
    (mul_eq_zero.mp ht).resolve_right (neg_ne_zero.mpr (product_key_side_slope_ne_zero u s))
  have hn := congrArg (fun v : EFour => ⟪v, productKeyOutwardNormal u⟫_ℝ) h
  simp [hd, real_inner_smul_left, real_inner_self_eq_norm_sq,
    productKeyOutwardNormal_norm] at hn
  exact ⟨hn, hd⟩

/-- Distinct tangent axes make two actual side normals independent. -/
theorem product_key_side_normals_combination_eq_zero (u : ProductKeySite)
    (s t : ProductKeySide) (hst : s.1 ≠ t.1) (c d : ℝ)
    (h : c • productKeySideNormal u s + d • productKeySideNormal u t = 0) :
    c = 0 ∧ d = 0 := by
  have ht := congrArg (fun v : EFour => ⟪v, productKeyTangent u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left,
    product_key_side_normal_inner_tangent, hst.symm, ↓reduceIte,
    mul_zero, add_zero, inner_zero_left] at ht
  have hc : c = 0 :=
    (mul_eq_zero.mp ht).resolve_right (neg_ne_zero.mpr (product_key_side_slope_ne_zero u s))
  have hn := congrArg (fun v : EFour => ⟪v, productKeyOutwardNormal u⟫_ℝ) h
  simp [hc, real_inner_smul_left, product_key_side_normal_inner_outward] at hn
  exact ⟨hc, hn⟩

/-- The two opposite side labels on an axis also give independent normals. -/
theorem product_key_same_axis_side_normals_combination_eq_zero (u : ProductKeySite)
    (s t : ProductKeySide)
    (haxis : s.1 = t.1) (hst : s ≠ t) (c d : ℝ)
    (h : c • productKeySideNormal u s + d • productKeySideNormal u t = 0) :
    c = 0 ∧ d = 0 := by
  have hn := congrArg (fun v : EFour => ⟪v, productKeyOutwardNormal u⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, product_key_side_normal_inner_outward,
    mul_one, inner_zero_left] at hn
  have ht := congrArg (fun v : EFour => ⟪v, productKeyTangent u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, product_key_side_normal_inner_tangent,
    haxis.symm, ↓reduceIte, inner_zero_left] at ht
  have hslope : productKeySideSlope u s - productKeySideSlope u t ≠ 0 :=
    sub_ne_zero.mpr (fun heq => hst (product_key_side_slope_injective u heq))
  have hc : c = 0 := by
    apply (mul_eq_zero.mp (show c * (productKeySideSlope u s - productKeySideSlope u t) = 0 by
      have hd : d = -c := by linarith
      rw [hd] at ht
      nlinarith [ht])).resolve_right hslope
  exact ⟨hc, by linarith⟩

/-- Any two distinct labels give independent actual side-plane normals. -/
theorem product_key_distinct_side_normals_combination_eq_zero (u : ProductKeySite)
    (s t : ProductKeySide) (hst : s ≠ t)
    (c d : ℝ) (h : c • productKeySideNormal u s + d • productKeySideNormal u t = 0) :
    c = 0 ∧ d = 0 := by
  by_cases haxis : s.1 = t.1
  · exact product_key_same_axis_side_normals_combination_eq_zero u s t haxis hst c d h
  · exact product_key_side_normals_combination_eq_zero u s t haxis c d h

/-- An axis has only two side labels. A third label distinct from both must use
another tangent axis. -/
theorem product_key_third_side_axis_ne (s t r : ProductKeySide)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r) (haxis : s.1 = t.1) :
    s.1 ≠ r.1 := by
  intro hr
  rcases s with ⟨i, b⟩
  rcases t with ⟨j, c⟩
  rcases r with ⟨k, d⟩
  simp only at haxis hr
  subst j
  subst k
  cases b <;> cases c <;> cases d <;> simp_all

/-- A coefficient on a tangent axis unused by the other two branches vanishes
in any zero combination of their actual normals. -/
theorem product_key_side_normal_coefficient_zero_of_unique_axis (u : ProductKeySite)
    (s t r : ProductKeySide)
    (hst : s.1 ≠ t.1) (hsr : s.1 ≠ r.1) (c d e : ℝ)
    (h : c • productKeySideNormal u s + d • productKeySideNormal u t +
      e • productKeySideNormal u r = 0) : c = 0 := by
  have ht := congrArg (fun v : EFour => ⟪v, productKeyTangent u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, product_key_side_normal_inner_tangent,
    hst.symm, hsr.symm, ↓reduceIte, mul_zero, add_zero, inner_zero_left] at ht
  exact (mul_eq_zero.mp ht).resolve_right (neg_ne_zero.mpr (product_key_side_slope_ne_zero u s))

/-- Every three distinct side labels give linearly independent actual normals.
This includes an opposite pair on one axis and a third side on another axis. -/
theorem product_key_three_side_normals_combination_eq_zero (u : ProductKeySite)
    (s t r : ProductKeySide)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r) (c d e : ℝ)
    (h : c • productKeySideNormal u s + d • productKeySideNormal u t +
      e • productKeySideNormal u r = 0) : c = 0 ∧ d = 0 ∧ e = 0 := by
  by_cases hstaxis : s.1 = t.1
  · have hsr_axis := product_key_third_side_axis_ne s t r hst hsr htr hstaxis
    have htr_axis : t.1 ≠ r.1 := by simpa only [← hstaxis] using hsr_axis
    have he : e = 0 := product_key_side_normal_coefficient_zero_of_unique_axis u r s t
      hsr_axis.symm htr_axis.symm e c d (by simpa only [add_comm, add_left_comm,
        add_assoc] using h)
    have hpair : c = 0 ∧ d = 0 := product_key_distinct_side_normals_combination_eq_zero
      u s t hst c d (by simpa only [he, zero_smul, add_zero] using h)
    exact ⟨hpair.1, hpair.2, he⟩
  · by_cases hsr_axis : s.1 = r.1
    · have htr_axis : t.1 ≠ r.1 := by simpa only [← hsr_axis] using (Ne.symm hstaxis)
      have hd : d = 0 := product_key_side_normal_coefficient_zero_of_unique_axis u t s r
        (Ne.symm hstaxis) htr_axis d c e (by simpa only [add_comm, add_left_comm,
          add_assoc] using h)
      have hpair : c = 0 ∧ e = 0 := product_key_distinct_side_normals_combination_eq_zero
        u s r hsr c e (by simpa only [hd, zero_smul, add_zero] using h)
      exact ⟨hpair.1, hd, hpair.2⟩
    · have hc := product_key_side_normal_coefficient_zero_of_unique_axis u s t r
        hstaxis hsr_axis c d e h
      have hpair : d = 0 ∧ e = 0 := product_key_distinct_side_normals_combination_eq_zero
        u t r htr d e (by simpa only [hc, zero_smul, zero_add] using h)
      exact ⟨hc, hpair.1, hpair.2⟩

/-- The outward normal together with two side normals on distinct tangent axes. -/
theorem product_key_outward_side_side_normals_combination_eq_zero (u : ProductKeySite)
    (s t : ProductKeySide) (hst : s.1 ≠ t.1)
    (c d e : ℝ) (h : c • productKeyOutwardNormal u + d • productKeySideNormal u s +
      e • productKeySideNormal u t = 0) : c = 0 ∧ d = 0 ∧ e = 0 := by
  have horth : ⟪productKeyOutwardNormal u, productKeyTangent u s.1⟫_ℝ = 0 :=
    productKeyOutwardNormal_inner_tangent u s.1
  have ht := congrArg (fun v : EFour => ⟪v, productKeyTangent u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, horth, product_key_side_normal_inner_tangent,
    hst.symm, ↓reduceIte, mul_zero, zero_add, add_zero, inner_zero_left] at ht
  have hd : d = 0 :=
    (mul_eq_zero.mp ht).resolve_right (neg_ne_zero.mpr (product_key_side_slope_ne_zero u s))
  have hpair := product_key_base_normals_combination_eq_zero u t c e
    (by simpa only [hd, zero_smul, add_zero] using h)
  exact ⟨hpair.1, hd, hpair.2⟩

/-- Finite-family formulation of the exact three-side rank obstruction. -/
theorem product_key_three_side_normals_linearIndependent (u : ProductKeySite)
    (s t r : ProductKeySide)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r) :
    LinearIndependent ℝ ![productKeySideNormal u s, productKeySideNormal u t, productKeySideNormal u r] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hg
  have hz := product_key_three_side_normals_combination_eq_zero u s t r hst hsr htr
    (g 0) (g 1) (g 2) hg
  fin_cases i <;> simp_all

/-- Finite-family formulation for the outward normal and two distinct-axis side normals. -/
theorem product_key_outward_side_side_normals_linearIndependent (u : ProductKeySite)
    (s t : ProductKeySide) (hst : s.1 ≠ t.1) :
    LinearIndependent ℝ ![productKeyOutwardNormal u, productKeySideNormal u s, productKeySideNormal u t] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hg
  have hz := product_key_outward_side_side_normals_combination_eq_zero u s t hst
    (g 0) (g 1) (g 2) hg
  fin_cases i <;> simp_all

/-- The abstract obstruction needs no independence assumption on the two
spanning vectors: even a span of dimension at most two cannot contain three
independent vectors. All dimension lemmas are already in the import closure. -/
theorem three_independent_not_mem_span_pair {V : Type*} [AddCommGroup V] [Module ℝ V]
    (x y z p q : V) (hli : LinearIndependent ℝ ![x, y, z]) :
    ¬(x ∈ Submodule.span ℝ ({p, q} : Set V) ∧
      y ∈ Submodule.span ℝ ({p, q} : Set V) ∧
      z ∈ Submodule.span ℝ ({p, q} : Set V)) := by
  classical
  rintro ⟨hx, hy, hz⟩
  have hpair : Set.range ![p, q] = ({p, q} : Set V) := by
    ext v
    simp [Matrix.range_cons, or_comm]
  let : Module.Finite ℝ (Submodule.span ℝ ({p, q} : Set V)) :=
    Module.Finite.span_of_finite ℝ (Set.toFinite _)
  have hbound : Module.finrank ℝ (Submodule.span ℝ ({p, q} : Set V)) ≤ 2 := by
    rw [← hpair]
    exact finrank_range_le_card (R := ℝ) ![p, q]
  have hspan : Submodule.span ℝ (Set.range ![x, y, z]) ≤
      Submodule.span ℝ ({p, q} : Set V) := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  have hdim := (Submodule.finrank_mono hspan).trans hbound
  rw [finrank_span_eq_card hli] at hdim
  norm_num at hdim

/-- Three distinct actual side normals cannot all lie in any two-vector span. -/
theorem product_key_three_side_normals_not_mem_span_pair (u : ProductKeySite)
    (s t r : ProductKeySide)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r) (p q : EFour) :
    ¬(productKeySideNormal u s ∈ Submodule.span ℝ ({p, q} : Set EFour) ∧
      productKeySideNormal u t ∈ Submodule.span ℝ ({p, q} : Set EFour) ∧
      productKeySideNormal u r ∈ Submodule.span ℝ ({p, q} : Set EFour)) :=
  three_independent_not_mem_span_pair _ _ _ p q
    (product_key_three_side_normals_linearIndependent u s t r hst hsr htr)

/-- The outward normal and two distinct-axis actual side normals cannot all lie in any
two-vector span. -/
theorem product_key_outward_side_side_normals_not_mem_span_pair (u : ProductKeySite)
    (s t : ProductKeySide) (hst : s.1 ≠ t.1)
    (p q : EFour) :
    ¬(productKeyOutwardNormal u ∈ Submodule.span ℝ ({p, q} : Set EFour) ∧
      productKeySideNormal u s ∈ Submodule.span ℝ ({p, q} : Set EFour) ∧
      productKeySideNormal u t ∈ Submodule.span ℝ ({p, q} : Set EFour)) :=
  three_independent_not_mem_span_pair _ _ _ p q
    (product_key_outward_side_side_normals_linearIndependent u s t hst)

/-- A two-dimensional transverse normal space contains at most two actual
branch normals, with the branch labels counted directly. -/
theorem side_labels_in_span_pair_card_le_two (u : ProductKeySite)
    (S : Finset ProductKeySide) (p q : EFour)
    (hS : ∀ s ∈ S, productKeySideNormal u s ∈ Submodule.span ℝ ({p, q} : Set EFour)) :
    S.card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨s, hs, t, ht, r, hr, hst, hsr, htr⟩ :=
    Finset.two_lt_card.mp (show 2 < S.card by omega)
  exact product_key_three_side_normals_not_mem_span_pair u s t r hst hsr htr p q
    ⟨hS s hs, hS t ht, hS r hr⟩

/-- If a two-vector span contains the outward normal and two side normals, those sides
must be on the same tangent axis. -/
theorem side_axes_eq_of_outward_and_side_normals_mem_span_pair (u : ProductKeySite)
    (s t : ProductKeySide) (p q : EFour)
    (hn : productKeyOutwardNormal u ∈ Submodule.span ℝ ({p, q} : Set EFour))
    (hs : productKeySideNormal u s ∈ Submodule.span ℝ ({p, q} : Set EFour))
    (ht : productKeySideNormal u t ∈ Submodule.span ℝ ({p, q} : Set EFour)) :
    s.1 = t.1 := by
  by_contra hst
  exact product_key_outward_side_side_normals_not_mem_span_pair u s t hst p q ⟨hn, hs, ht⟩

end
end SpectreGeometry
