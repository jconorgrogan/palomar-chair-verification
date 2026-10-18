module

public import ProductClosure.GenericCreaseDensity

@[expose] public section

/-!
# Dense native generic creases survive finite affine exceptions

This is the precise deletion operation in the manuscript's generic transverse
section step. Each excluded hyperplane must genuinely fail to contain the
selected concrete crease; that properness is an explicit hypothesis, to be
established when the neighboring tile strata are classified.
-/

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- A finite family of ambient affine hyperplanes is excluded literally. -/
def avoidsHyperplanes  {ι : Type*} (I : Finset ι)
    (n : ι → Space m) (c : ι → ℝ) : Set (Space m) :=
  {x | ∀ i ∈ I, ⟪n i, x⟫_ℝ ≠ c i}

theorem convex_subset_closure_avoid_hyperplane  (C : Set (Space m))
    (hC : Convex ℝ C) (n : Space m) (c : ℝ)
    (hproper : ∃ y ∈ C, ⟪n, y⟫_ℝ ≠ c) :
    C ⊆ closure (C ∩ {x | ⟪n, x⟫_ℝ ≠ c}) := by
  intro x hx
  by_cases he : ⟪n, x⟫_ℝ = c
  · obtain ⟨y, hy, hny⟩ := hproper
    apply mem_closure_of_positive_interpolation x y
    intro q hq hqone
    refine ⟨hC hx hy (sub_nonneg.mpr hqone) hq.le (by ring), ?_⟩
    change ⟪n, (1 - q) • x + q • y⟫_ℝ ≠ c
    simp only [inner_add_right, real_inner_smul_right, he]
    intro h
    have hz : q * (⟪n, y⟫_ℝ - c) = 0 := by nlinarith
    have hyc := (mul_eq_zero.mp hz).resolve_left hq.ne'
    exact hny (sub_eq_zero.mp hyc)
  · exact subset_closure ⟨hx, he⟩

private theorem dense_in_closed_inter_open 
    (C A V : Set (Space m)) (hA : C ⊆ closure A) (hV : IsOpen V)
    (hCV : C ⊆ closure (C ∩ V)) : C ⊆ closure (A ∩ V) := by
  apply hCV.trans
  have hh : C ∩ V ⊆ closure (A ∩ V) := by
    intro x hx
    exact hV.closure_inter ⟨hA hx.1, hx.2⟩
  exact (closure_mono hh).trans_eq closure_closure

/-- No density hypothesis is hidden in the hyperplane exclusions: properness
and convexity supply each deletion, while `hG` identifies the existing generic
subset whose density was already proved from explicit native coordinates. -/
theorem convex_generic_finite_avoidance  {ι : Type*}
    (C G : Set (Space m)) (hC : Convex ℝ C) (hClosed : IsClosed C)
    (hG : closure G = C) (I : Finset ι) (n : ι → Space m) (c : ι → ℝ)
    (hproper : ∀ i ∈ I, ∃ y ∈ C, ⟪n i, y⟫_ℝ ≠ c i) :
    closure (G ∩ avoidsHyperplanes I n c) = C := by
  classical
  have hlower : C ⊆ closure (G ∩ avoidsHyperplanes I n c) := by
    induction I using Finset.induction_on with
    | empty => simp [avoidsHyperplanes, hG]
    | @insert i I hi ih =>
      have hrest : ∀ j ∈ I, ∃ y ∈ C, ⟪n j, y⟫_ℝ ≠ c j :=
        fun j hj => hproper j (Finset.mem_insert_of_mem hj)
      have hcurrent : ∃ y ∈ C, ⟪n i, y⟫_ℝ ≠ c i :=
        hproper i (Finset.mem_insert_self i I)
      have hopen : IsOpen {x : Space m | ⟪n i, x⟫_ℝ ≠ c i} :=
        (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
      have h := dense_in_closed_inter_open C (G ∩ avoidsHyperplanes I n c)
        {x | ⟪n i, x⟫_ℝ ≠ c i} (ih hrest) hopen
        (convex_subset_closure_avoid_hyperplane C hC (n i) (c i) hcurrent)
      simpa only [avoidsHyperplanes, Finset.mem_insert, forall_eq_or_imp,
        ofPred_and, inter_assoc, inter_left_comm, inter_comm] using h
  apply subset_antisymm _ hlower
  apply closure_minimal _ hClosed
  intro x hx
  rw [← hG]
  exact subset_closure hx.1

/-- Every native base crease still has dense genuinely generic points after
any finite list of affine hyperplanes that do not contain that crease is removed. -/
theorem genericBaseCrease_finite_avoidance {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m)
    (I : Finset ι) (n : ι → Space m) (c : ι → ℝ)
    (hproper : ∀ i ∈ I, ∃ y ∈ baseCrease a u s, ⟪n i, y⟫_ℝ ≠ c i) :
    closure (genericBaseCrease a u s ∩ avoidsHyperplanes I n c) = baseCrease a u s :=
  convex_generic_finite_avoidance _ _ (baseCrease_convex a u s)
    (baseCrease_isCompact a u s).isClosed (genericBaseCrease_closure a u s) I n c hproper

/-- The corresponding finite-exception density result for every actual
side-side crease with distinct tangent axes. -/
theorem genericSideCrease_finite_avoidance {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1)
    (I : Finset ι) (n : ι → Space m) (c : ι → ℝ)
    (hproper : ∀ i ∈ I, ∃ y ∈ sideCrease a u s t, ⟪n i, y⟫_ℝ ≠ c i) :
    closure (genericSideCrease a u s t ∩ avoidsHyperplanes I n c) = sideCrease a u s t :=
  convex_generic_finite_avoidance _ _ (sideCrease_convex a u s t)
    (sideCrease_isCompact a u s t).isClosed (genericSideCrease_closure a u s t hst)
    I n c hproper

end
end ProductClosure.NativeCompiler
