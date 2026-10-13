module

public import PhysicalRegistration.CreasePlaneGerms

@[expose] public section

/-!
# Exact rank obstructions for native key normals

All normals below are those of the literal native affine branches. Independence
is derived from the nonzero signed prime slopes and native orthogonal frame.
In particular, no boundary-stratum inventory or rank hypothesis is assumed.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- The literal signed slopes distinguish all side labels of one native key.
This follows from the already computed prime-labelled base normal invariant. -/
theorem sideSlope_injective {m J : ℕ} (a : Coefficients m J) (u : Site m) :
    Function.Injective (sideSlope a u) := by
  intro s t h
  apply (base_normalCosSq_injective a a u u s t ?_).2
  rw [base_normalCosSq, base_normalCosSq, h]

/-- The tangent component of an actual side normal, including the repeated-axis
case needed for the two opposite sides of one coordinate. -/
theorem sideNormal_inner_siteAxis {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) (i : Fin m) :
    ⟪sideNormal a u s, siteAxis u i⟫_ℝ =
      if s.1 = i then -sideSlope a u s else 0 := by
  have horth : ⟪outward u.1, siteAxis u i⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact siteAxis_outward_inner u i
  simp only [sideNormal, inner_sub_left, real_inner_smul_left, horth, siteAxis_inner]
  split_ifs <;> simp

/-- The two opposite side labels on an axis also give independent normals. -/
theorem same_axis_side_normals_combination_eq_zero {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t : Side m)
    (haxis : s.1 = t.1) (hst : s ≠ t) (c d : ℝ)
    (h : c • sideNormal a u s + d • sideNormal a u t = 0) :
    c = 0 ∧ d = 0 := by
  have hn := congrArg (fun v : Space m => ⟪v, outward u.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, sideNormal_inner_outward,
    mul_one, inner_zero_left] at hn
  have ht := congrArg (fun v : Space m => ⟪v, siteAxis u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, sideNormal_inner_siteAxis,
    haxis.symm, ↓reduceIte, inner_zero_left] at ht
  have hslope : sideSlope a u s - sideSlope a u t ≠ 0 :=
    sub_ne_zero.mpr (fun heq => hst (sideSlope_injective a u heq))
  have hc : c = 0 := by
    apply (mul_eq_zero.mp (show c * (sideSlope a u s - sideSlope a u t) = 0 by
      have hd : d = -c := by linarith
      rw [hd] at ht
      nlinarith [ht])).resolve_right hslope
  exact ⟨hc, by linarith⟩

/-- Any two distinct labels give independent native side-plane normals. -/
theorem distinct_side_normals_combination_eq_zero {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t : Side m) (hst : s ≠ t)
    (c d : ℝ) (h : c • sideNormal a u s + d • sideNormal a u t = 0) :
    c = 0 ∧ d = 0 := by
  by_cases haxis : s.1 = t.1
  · exact same_axis_side_normals_combination_eq_zero a u s t haxis hst c d h
  · exact side_normals_combination_eq_zero a u s t haxis c d h

/-- An axis has only two side labels. A third label distinct from both must use
another tangent axis. -/
theorem third_side_axis_ne {m : ℕ} (s t r : Side m)
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
theorem side_normal_coefficient_zero_of_unique_axis {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t r : Side m)
    (hst : s.1 ≠ t.1) (hsr : s.1 ≠ r.1) (c d e : ℝ)
    (h : c • sideNormal a u s + d • sideNormal a u t +
      e • sideNormal a u r = 0) : c = 0 := by
  have ht := congrArg (fun v : Space m => ⟪v, siteAxis u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, sideNormal_inner_siteAxis,
    hst.symm, hsr.symm, ↓reduceIte, mul_zero, add_zero, inner_zero_left] at ht
  exact (mul_eq_zero.mp ht).resolve_right (neg_ne_zero.mpr (sideSlope_ne_zero a u s))

/-- Every three distinct side labels give linearly independent actual normals.
This includes an opposite pair on one axis and a third side on another axis. -/
theorem three_side_normals_combination_eq_zero {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t r : Side m)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r) (c d e : ℝ)
    (h : c • sideNormal a u s + d • sideNormal a u t +
      e • sideNormal a u r = 0) : c = 0 ∧ d = 0 ∧ e = 0 := by
  by_cases hstaxis : s.1 = t.1
  · have hsr_axis := third_side_axis_ne s t r hst hsr htr hstaxis
    have htr_axis : t.1 ≠ r.1 := by simpa only [← hstaxis] using hsr_axis
    have he : e = 0 := side_normal_coefficient_zero_of_unique_axis a u r s t
      hsr_axis.symm htr_axis.symm e c d (by simpa only [add_comm, add_left_comm,
        add_assoc] using h)
    have hpair : c = 0 ∧ d = 0 := distinct_side_normals_combination_eq_zero
      a u s t hst c d (by simpa only [he, zero_smul, add_zero] using h)
    exact ⟨hpair.1, hpair.2, he⟩
  · by_cases hsr_axis : s.1 = r.1
    · have htr_axis : t.1 ≠ r.1 := by simpa only [← hsr_axis] using (Ne.symm hstaxis)
      have hd : d = 0 := side_normal_coefficient_zero_of_unique_axis a u t s r
        (Ne.symm hstaxis) htr_axis d c e (by simpa only [add_comm, add_left_comm,
          add_assoc] using h)
      have hpair : c = 0 ∧ e = 0 := distinct_side_normals_combination_eq_zero
        a u s r hsr c e (by simpa only [hd, zero_smul, add_zero] using h)
      exact ⟨hpair.1, hd, hpair.2⟩
    · have hc := side_normal_coefficient_zero_of_unique_axis a u s t r
        hstaxis hsr_axis c d e h
      have hpair : d = 0 ∧ e = 0 := distinct_side_normals_combination_eq_zero
        a u t r htr d e (by simpa only [hc, zero_smul, zero_add] using h)
      exact ⟨hc, hpair.1, hpair.2⟩

/-- Carrier normal together with two side normals on distinct tangent axes. -/
theorem carrier_side_side_normals_combination_eq_zero {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1)
    (c d e : ℝ) (h : c • outward u.1 + d • sideNormal a u s +
      e • sideNormal a u t = 0) : c = 0 ∧ d = 0 ∧ e = 0 := by
  have horth : ⟪outward u.1, siteAxis u s.1⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact siteAxis_outward_inner u s.1
  have ht := congrArg (fun v : Space m => ⟪v, siteAxis u s.1⟫_ℝ) h
  simp only [inner_add_left, real_inner_smul_left, horth, sideNormal_inner_siteAxis,
    hst.symm, ↓reduceIte, mul_zero, zero_add, add_zero, inner_zero_left] at ht
  have hd : d = 0 :=
    (mul_eq_zero.mp ht).resolve_right (neg_ne_zero.mpr (sideSlope_ne_zero a u s))
  have hpair := base_normals_combination_eq_zero a u t c e
    (by simpa only [hd, zero_smul, add_zero] using h)
  exact ⟨hpair.1, hd, hpair.2⟩

/-- Finite-family formulation of the exact three-side rank obstruction. -/
theorem three_side_normals_linearIndependent {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t r : Side m)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r) :
    LinearIndependent ℝ ![sideNormal a u s, sideNormal a u t, sideNormal a u r] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hg
  have hz := three_side_normals_combination_eq_zero a u s t r hst hsr htr
    (g 0) (g 1) (g 2) hg
  fin_cases i <;> simp_all

/-- Finite-family formulation for a carrier and two distinct-axis side normals. -/
theorem carrier_side_side_normals_linearIndependent {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    LinearIndependent ℝ ![outward u.1, sideNormal a u s, sideNormal a u t] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hg
  have hz := carrier_side_side_normals_combination_eq_zero a u s t hst
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

/-- Three distinct native side normals cannot all lie in any two-vector span. -/
theorem three_side_normals_not_mem_span_pair {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t r : Side m)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r) (p q : Space m) :
    ¬(sideNormal a u s ∈ Submodule.span ℝ ({p, q} : Set (Space m)) ∧
      sideNormal a u t ∈ Submodule.span ℝ ({p, q} : Set (Space m)) ∧
      sideNormal a u r ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :=
  three_independent_not_mem_span_pair _ _ _ p q
    (three_side_normals_linearIndependent a u s t r hst hsr htr)

/-- A carrier and two distinct-axis native side normals cannot all lie in any
two-vector span. -/
theorem carrier_side_side_normals_not_mem_span_pair {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1)
    (p q : Space m) :
    ¬(outward u.1 ∈ Submodule.span ℝ ({p, q} : Set (Space m)) ∧
      sideNormal a u s ∈ Submodule.span ℝ ({p, q} : Set (Space m)) ∧
      sideNormal a u t ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :=
  three_independent_not_mem_span_pair _ _ _ p q
    (carrier_side_side_normals_linearIndependent a u s t hst)

/-- A two-dimensional transverse normal space contains at most two native
branch normals, with the branch labels counted directly. -/
theorem side_labels_in_span_pair_card_le_two {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (S : Finset (Side m)) (p q : Space m)
    (hS : ∀ s ∈ S, sideNormal a u s ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    S.card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨s, hs, t, ht, r, hr, hst, hsr, htr⟩ :=
    Finset.two_lt_card.mp (show 2 < S.card by omega)
  exact three_side_normals_not_mem_span_pair a u s t r hst hsr htr p q
    ⟨hS s hs, hS t ht, hS r hr⟩

/-- If a two-vector span contains the carrier and two side normals, those sides
must be on the same tangent axis. -/
theorem side_axes_eq_of_carrier_and_side_normals_mem_span_pair {m J : ℕ}
    (a : Coefficients m J) (u : Site m) (s t : Side m) (p q : Space m)
    (hn : outward u.1 ∈ Submodule.span ℝ ({p, q} : Set (Space m)))
    (hs : sideNormal a u s ∈ Submodule.span ℝ ({p, q} : Set (Space m)))
    (ht : sideNormal a u t ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    s.1 = t.1 := by
  by_contra hst
  exact carrier_side_side_normals_not_mem_span_pair a u s t hst p q ⟨hn, hs, ht⟩

#print axioms sideSlope_injective
#print axioms distinct_side_normals_combination_eq_zero
#print axioms three_side_normals_combination_eq_zero
#print axioms carrier_side_side_normals_combination_eq_zero
#print axioms three_side_normals_linearIndependent
#print axioms carrier_side_side_normals_linearIndependent
#print axioms three_independent_not_mem_span_pair
#print axioms three_side_normals_not_mem_span_pair
#print axioms carrier_side_side_normals_not_mem_span_pair
#print axioms side_labels_in_span_pair_card_le_two
#print axioms side_axes_eq_of_carrier_and_side_normals_mem_span_pair

end
end PhysicalRegistration.NativeChair
