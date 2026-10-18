module

public import PhysicalRegistration.KeyCreaseGeometry
public import PhysicalRegistration.CreaseConnectivity

@[expose] public section

/-!
# Density of literal generic native creases

Strictly active branches are exhibited at actual prime-coordinate points, and
convex interpolation proves density in the closed native crease pieces.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- A literal base crease with just one zero branch. -/
def genericBaseCrease {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s : Side m) : Set (Space m) :=
  {x | x ∈ baseCrease a u s ∧ branchProfile J u s x = 0 ∧
    ∀ t, t ≠ s → 0 < branchProfile J u t x}

/-- A literal side crease with exactly the displayed two positive active branches.
Distinct-axis hypotheses belong to the nonemptiness and density statements. -/
def genericSideCrease {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s t : Side m) : Set (Space m) :=
  {x | x ∈ sideCrease a u s t ∧ 0 < branchProfile J u s x ∧
    branchProfile J u s x = branchProfile J u t x ∧
    ∀ r, r ≠ s → r ≠ t → branchProfile J u s x < branchProfile J u r x}

/-- The center of one actual footprint side. -/
def genericBasePoint {m : ℕ} (J : ℕ) (u : Site m) (s : Side m) : Space m :=
  keyCoordinatePoint u (fun i => if i = s.1 then sideEndpoint J s else 0) 0

theorem genericBasePoint_mem_closedTube {m : ℕ} (J : ℕ) (u : Site m)
    (s : Side m) : genericBasePoint J u s ∈ closedTube J u := by
  refine ⟨?_, fun i => ?_⟩
  · simp only [genericBasePoint, keyCoordinatePoint_normal, abs_zero]
    exact (rho_pos m).le
  · simp only [genericBasePoint, keyCoordinatePoint_tangent]
    have hlo : -eta m / pMinus J i ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (eta_pos m).le) (pMinus_pos J i).le
    have hhi : 0 ≤ eta m / pPlus J i := div_nonneg (eta_pos m).le (pPlus_pos J i).le
    by_cases hi : i = s.1
    · subst i
      simp only [ite_true, sideEndpoint]
      split_ifs <;> exact ⟨by first | exact hlo.trans hhi | rfl,
        by first | exact hlo.trans hhi | rfl⟩
    · simp only [hi, ite_false]
      exact ⟨hlo, hhi⟩

theorem genericBasePoint_branch_zero {m : ℕ} (J : ℕ) (u : Site m)
    (s : Side m) : branchProfile J u s (genericBasePoint J u s) = 0 := by
  rcases s with ⟨i, b⟩
  have he := (eta_pos m).ne'
  have hm := (pMinus_pos J i).ne'
  have hp := (pPlus_pos J i).ne'
  cases b
  · rw [branchProfile_false]
    simp only [genericBasePoint, keyCoordinatePoint_tangent, ite_true, sideEndpoint,
      Bool.false_eq_true, ite_false]
    field_simp
    ring
  · rw [branchProfile_true]
    simp only [genericBasePoint, keyCoordinatePoint_tangent, ite_true, sideEndpoint]
    field_simp
    ring

theorem genericBasePoint_other_axis {m : ℕ} (J : ℕ) (u : Site m)
    (s t : Side m) (hst : t.1 ≠ s.1) :
    branchProfile J u t (genericBasePoint J u s) = 1 := by
  simp [branchProfile, genericBasePoint, hst]

theorem genericBasePoint_other_branch {m : ℕ} (J : ℕ) (u : Site m)
    (s t : Side m) (hst : t ≠ s) :
    1 ≤ branchProfile J u t (genericBasePoint J u s) := by
  by_cases haxis : t.1 = s.1
  · rcases s with ⟨i, b⟩
    rcases t with ⟨j, c⟩
    simp only at haxis
    subst j
    cases b <;> cases c
    · exact (hst rfl).elim
    · rw [branchProfile_true]
      simp only [genericBasePoint, keyCoordinatePoint_tangent, ite_true, sideEndpoint,
        Bool.false_eq_true, ite_false]
      have h : pPlus J i * (-eta m / pMinus J i) / eta m ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (pPlus_pos J i).le
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (eta_pos m).le)
              (pMinus_pos J i).le)) (eta_pos m).le
      linarith
    · rw [branchProfile_false]
      simp only [genericBasePoint, keyCoordinatePoint_tangent, ite_true, sideEndpoint]
      have h : 0 ≤ pMinus J i * (eta m / pPlus J i) / eta m :=
        div_nonneg (mul_nonneg (pMinus_pos J i).le
          (div_nonneg (eta_pos m).le (pPlus_pos J i).le)) (eta_pos m).le
      linarith
    · exact (hst rfl).elim
  · rw [genericBasePoint_other_axis J u s t haxis]

theorem genericBasePoint_mem_genericBaseCrease {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (u : Site m) (s : Side m) :
    genericBasePoint J u s ∈ genericBaseCrease a u s := by
  have hz := genericBasePoint_branch_zero J u s
  exact ⟨mem_baseCrease_of_branch_zero a u s _
      (genericBasePoint_mem_closedTube J u s) (by simp [genericBasePoint]) hz,
    hz, fun t ht => lt_of_lt_of_le (by norm_num) (genericBasePoint_other_branch J u s t ht)⟩

theorem genericBaseCrease_nonempty {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s : Side m) : (genericBaseCrease a u s).Nonempty :=
  ⟨genericBasePoint J u s, genericBasePoint_mem_genericBaseCrease a u s⟩

theorem baseCrease_branch_zero {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s : Side m) (x : Space m) (hx : x ∈ baseCrease a u s) :
    branchProfile J u s x = 0 := by
  have hh := hx.1.1.2
  unfold siteHeight keyHeight at hh
  rw [native_profile_eq_branch J u s x hx.1.2, hx.2] at hh
  have ha : (a.value u : ℝ) ≠ 0 := by exact_mod_cast a.nonzero u
  have hn : (denominator m J : ℝ) ≠ 0 := by exact_mod_cast (denominator_prime m J).ne_zero
  exact (mul_eq_zero.mp hh.symm).resolve_left (div_ne_zero (mul_ne_zero (eta_pos m).ne' ha) hn)

/-- Two half-endpoints with the actual signed half-height. -/
def genericSidePoint {m J : ℕ} (a : Coefficients m J) (u : Site m)
    (s t : Side m) : Space m :=
  keyCoordinatePoint u
    (fun i => ((if i = s.1 then sideEndpoint J s else 0) +
      (if i = t.1 then sideEndpoint J t else 0)) / 2)
    (eta m * (a.value u : ℝ) / denominator m J / 2)

theorem genericSidePoint_branch {m J : ℕ} (a : Coefficients m J) (u : Site m)
    (s t r : Side m) :
    branchProfile J u r (genericSidePoint a u s t) =
      (branchProfile J u r (genericBasePoint J u s) +
        branchProfile J u r (genericBasePoint J u t)) / 2 := by
  simp only [branchProfile, genericSidePoint, genericBasePoint, keyCoordinatePoint_tangent]
  ring

theorem genericSidePoint_selected_branches {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    branchProfile J u s (genericSidePoint a u s t) = 1 / 2 ∧
    branchProfile J u t (genericSidePoint a u s t) = 1 / 2 := by
  constructor
  · rw [genericSidePoint_branch, genericBasePoint_branch_zero,
      genericBasePoint_other_axis J u t s hst]
    norm_num
  · rw [genericSidePoint_branch, genericBasePoint_branch_zero,
      genericBasePoint_other_axis J u s t hst.symm]
    norm_num

theorem genericSidePoint_other_branch {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t r : Side m) (hrs : r ≠ s) (hrt : r ≠ t) :
    1 / 2 < branchProfile J u r (genericSidePoint a u s t) := by
  rw [genericSidePoint_branch]
  have hs := genericBasePoint_other_branch J u s r hrs
  have ht := genericBasePoint_other_branch J u t r hrt
  linarith

theorem genericSidePoint_mem_genericSideCrease {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    genericSidePoint a u s t ∈ genericSideCrease a u s t := by
  let x := genericSidePoint a u s t
  obtain ⟨hs, ht⟩ := genericSidePoint_selected_branches a u s t hst
  have hmin : ∀ r, 1 / 2 ≤ branchProfile J u r x := by
    intro r
    by_cases hrs : r = s
    · subst r; exact hs.ge
    by_cases hrt : r = t
    · subst r; exact ht.ge
    exact (genericSidePoint_other_branch a u s t r hrs hrt).le
  have hregs : x ∈ branchRegion J u s := by
    exact ⟨by change 0 ≤ branchProfile J u s (genericSidePoint a u s t); rw [hs]; norm_num,
      fun r => hs.trans_le (hmin r)⟩
  have hregt : x ∈ branchRegion J u t := by
    exact ⟨by change 0 ≤ branchProfile J u t (genericSidePoint a u s t); rw [ht]; norm_num,
      fun r => ht.trans_le (hmin r)⟩
  have hheight : normalCoord u x = siteHeight a u x := by
    unfold siteHeight keyHeight
    rw [native_profile_eq_branch J u s x hregs]
    change normalCoord u (genericSidePoint a u s t) = _
    rw [hs]
    simp only [genericSidePoint, keyCoordinatePoint_normal]
    ring
  have htube : x ∈ closedTube J u := by
    refine ⟨?_, fun i => ?_⟩
    · rw [hheight]
      exact (siteHeight_abs_lt_rho a u x).le
    · have hsi := (genericBasePoint_mem_closedTube J u s).2 i
      have hti := (genericBasePoint_mem_closedTube J u t).2 i
      simp only [genericBasePoint, keyCoordinatePoint_tangent] at hsi hti
      change -eta m / pMinus J i ≤ tangentCoord u (genericSidePoint a u s t) i ∧
        tangentCoord u (genericSidePoint a u s t) i ≤ eta m / pPlus J i
      simp only [genericSidePoint, keyCoordinatePoint_tangent]
      constructor <;> linarith [hsi.1, hsi.2, hti.1, hti.2]
  refine ⟨⟨⟨⟨htube, hheight⟩, hregs⟩, ⟨⟨htube, hheight⟩, hregt⟩⟩, ?_, ?_, ?_⟩
  · rw [hs]; norm_num
  · exact hs.trans ht.symm
  · intro r hrs hrt
    rw [hs]
    exact genericSidePoint_other_branch a u s t r hrs hrt

theorem genericSideCrease_nonempty {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    (genericSideCrease a u s t).Nonempty :=
  ⟨genericSidePoint a u s t, genericSidePoint_mem_genericSideCrease a u s t hst⟩

/-- An elementary metric form of interpolation density. The approximating
points have an explicit positive parameter tending to zero. -/
theorem mem_closure_of_positive_interpolation {m : ℕ} {S : Set (Space m)}
    (x y : Space m)
    (h : ∀ q : ℝ, 0 < q → q ≤ 1 → (1 - q) • x + q • y ∈ S) :
    x ∈ closure S := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let q : ℝ := min (1 / 2) (ε / (2 * (1 + ‖x - y‖)))
  have hd : 0 < 1 + ‖x - y‖ := by positivity
  have hq : 0 < q := lt_min (by norm_num) (div_pos hε (by positivity))
  have hqhalf : q ≤ 1 / 2 := min_le_left _ _
  have hqone : q ≤ 1 := hqhalf.trans (by norm_num)
  have hbound : q * (2 * (1 + ‖x - y‖)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨(1 - q) • x + q • y, h q hq hqone, ?_⟩
  have heq : x - ((1 - q) • x + q • y) = q • (x - y) := by module
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
  nlinarith [mul_nonneg hq.le (norm_nonneg (x - y))]

theorem genericBaseCrease_closure {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s : Side m) : closure (genericBaseCrease a u s) = baseCrease a u s := by
  apply subset_antisymm
  · exact closure_minimal (fun _ hx => hx.1) (baseCrease_isCompact a u s).isClosed
  · intro x hx
    obtain ⟨y, hy⟩ := genericBaseCrease_nonempty a u s
    apply mem_closure_of_positive_interpolation x y
    intro q hq hqone
    have hr : 0 ≤ 1 - q := sub_nonneg.mpr hqone
    have hsum : (1 - q) + q = 1 := by ring
    refine ⟨baseCrease_convex a u s hx hy.1 hr hq.le hsum, ?_, ?_⟩
    · rw [branchProfile_combination J u s x y (1 - q) q hsum,
        baseCrease_branch_zero a u s x hx, hy.2.1]
      ring
    · intro t hts
      rw [branchProfile_combination J u t x y (1 - q) q hsum]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg hr (branchProfile_nonneg_of_mem_closedTube J u t x hx.1.1.1))
        (mul_pos hq (hy.2.2 t hts))

theorem sideCrease_branch_eq {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s t : Side m) (x : Space m) (hx : x ∈ sideCrease a u s t) :
    branchProfile J u s x = branchProfile J u t x :=
  le_antisymm (hx.1.2.2 t) (hx.2.2.2 s)

theorem genericSideCrease_closure {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    closure (genericSideCrease a u s t) = sideCrease a u s t := by
  apply subset_antisymm
  · exact closure_minimal (fun _ hx => hx.1) (sideCrease_isCompact a u s t).isClosed
  · intro x hx
    obtain ⟨y, hy⟩ := genericSideCrease_nonempty a u s t hst
    apply mem_closure_of_positive_interpolation x y
    intro q hq hqone
    have hr : 0 ≤ 1 - q := sub_nonneg.mpr hqone
    have hsum : (1 - q) + q = 1 := by ring
    refine ⟨sideCrease_convex a u s t hx hy.1 hr hq.le hsum, ?_, ?_, ?_⟩
    · rw [branchProfile_combination J u s x y (1 - q) q hsum]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hr hx.1.2.1) (mul_pos hq hy.2.1)
    · rw [branchProfile_combination J u s x y (1 - q) q hsum,
        branchProfile_combination J u t x y (1 - q) q hsum,
        sideCrease_branch_eq a u s t x hx, hy.2.2.1]
    · intro r hrs hrt
      rw [branchProfile_combination J u s x y (1 - q) q hsum,
        branchProfile_combination J u r x y (1 - q) q hsum]
      exact add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left (hx.1.2.2 r) hr)
        (mul_lt_mul_of_pos_left (hy.2.2.2 r hrs hrt) hq)

#print axioms genericBaseCrease_nonempty
#print axioms genericSideCrease_nonempty
#print axioms genericBaseCrease_closure
#print axioms genericSideCrease_closure

end
end PhysicalRegistration.NativeChair
