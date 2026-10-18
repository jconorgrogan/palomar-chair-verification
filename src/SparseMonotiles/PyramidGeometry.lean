module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Coordinate pyramids and their finite halfspace description

The ambient real vector space is `(Fin k → ℝ) × ℝ`: tangential coordinates
followed by the normal coordinate. The apex has strictly positive height.
Neither a nondegenerate base nor an apex projection inside the base is needed.
In particular, the halfspace theorem remains true for empty or degenerate boxes.
-/
namespace SparseMonotiles

abbrev PyramidPoint (k : ℕ) := (Fin k → ℝ) × ℝ

/-- The possibly degenerate axis-aligned base in the height-zero hyperplane. -/
def pyramidBase {k : ℕ} (lo hi : Fin k → ℝ) : Set (PyramidPoint k) :=
  {p | p.2 = 0 ∧ ∀ i, lo i ≤ p.1 i ∧ p.1 i ≤ hi i}

/-- The closed convex hull of the base and the positive-height apex. -/
def pyramidSolid {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ) : Set (PyramidPoint k) :=
  convexHull ℝ (insert (o, h) (pyramidBase lo hi))

/-- Explicit inequalities for all points of a coordinate pyramid. -/
def pyramidHalfspaces {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ) :
    Set (PyramidPoint k) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ h ∧ ∀ i,
    (h - p.2) * lo i + p.2 * o i ≤ h * p.1 i ∧
    h * p.1 i ≤ (h - p.2) * hi i + p.2 * o i}

@[simp] theorem mem_pyramidBase {k : ℕ} (lo hi : Fin k → ℝ) (p : PyramidPoint k) :
    p ∈ pyramidBase lo hi ↔ p.2 = 0 ∧ ∀ i, lo i ≤ p.1 i ∧ p.1 i ≤ hi i := Iff.rfl

@[simp] theorem mem_pyramidHalfspaces {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ)
    (p : PyramidPoint k) :
    p ∈ pyramidHalfspaces lo hi o h ↔ 0 ≤ p.2 ∧ p.2 ≤ h ∧ ∀ i,
      (h - p.2) * lo i + p.2 * o i ≤ h * p.1 i ∧
      h * p.1 i ≤ (h - p.2) * hi i + p.2 * o i := Iff.rfl

/-- The displayed inequalities are convex, independently of the height sign. -/
theorem convex_pyramidHalfspaces {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ) :
    Convex ℝ (pyramidHalfspaces lo hi o h) := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hp0, hph, hp⟩
  rcases hq with ⟨hq0, hqh, hq⟩
  change 0 ≤ a * p.2 + b * q.2 ∧ a * p.2 + b * q.2 ≤ h ∧ _
  refine ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0), ?_, ?_⟩
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hph),
      mul_nonneg hb (sub_nonneg.mpr hqh)]
  · intro i
    change (h - (a * p.2 + b * q.2)) * lo i + (a * p.2 + b * q.2) * o i ≤
        h * (a * p.1 i + b * q.1 i) ∧
      h * (a * p.1 i + b * q.1 i) ≤
        (h - (a * p.2 + b * q.2)) * hi i + (a * p.2 + b * q.2) * o i
    constructor
    · have h₁ := mul_le_mul_of_nonneg_left (hp i).1 ha
      have h₂ := mul_le_mul_of_nonneg_left (hq i).1 hb
      nlinarith [congrArg (fun z : ℝ => z * (h * lo i)) hab]
    · have h₁ := mul_le_mul_of_nonneg_left (hp i).2 ha
      have h₂ := mul_le_mul_of_nonneg_left (hq i).2 hb
      nlinarith [congrArg (fun z : ℝ => z * (h * hi i)) hab]

/-- The apex satisfies all inequalities when the height is nonnegative. -/
theorem apex_mem_pyramidHalfspaces {k : ℕ} (lo hi o : Fin k → ℝ) {h : ℝ}
    (hh : 0 ≤ h) : (o, h) ∈ pyramidHalfspaces lo hi o h := by
  simp [pyramidHalfspaces, hh]

/-- Every base point satisfies the pyramid inequalities at nonnegative height. -/
theorem pyramidBase_subset_halfspaces {k : ℕ} (lo hi o : Fin k → ℝ) {h : ℝ}
    (hh : 0 ≤ h) : pyramidBase lo hi ⊆ pyramidHalfspaces lo hi o h := by
  intro p hp
  rcases hp with ⟨hp0, hp⟩
  refine ⟨by simp [hp0], by simpa [hp0], ?_⟩
  intro i
  simpa [hp0] using And.intro (mul_le_mul_of_nonneg_left (hp i).1 hh)
    (mul_le_mul_of_nonneg_left (hp i).2 hh)

/-- At maximal height the inequalities force the unique apex. -/
theorem eq_apex_of_mem_pyramidHalfspaces_of_height_eq {k : ℕ}
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h) {p : PyramidPoint k}
    (hp : p ∈ pyramidHalfspaces lo hi o h) (hph : p.2 = h) : p = (o, h) := by
  apply Prod.ext
  · funext i
    have hpi := hp.2.2 i
    simp only [hph, sub_self, zero_mul, zero_add] at hpi
    nlinarith [hpi.1, hpi.2]
  · exact hph

/-- A point below apex height has an explicit base projection along the apex ray. -/
noncomputable def pyramidBaseProjection {k : ℕ} (o : Fin k → ℝ) (h : ℝ)
    (p : PyramidPoint k) : PyramidPoint k :=
  (fun i => (h * p.1 i - p.2 * o i) / (h - p.2), 0)

theorem pyramidBaseProjection_mem {k : ℕ} (lo hi o : Fin k → ℝ) {h : ℝ}
    {p : PyramidPoint k} (hp : p ∈ pyramidHalfspaces lo hi o h) (hph : p.2 < h) :
    pyramidBaseProjection o h p ∈ pyramidBase lo hi := by
  refine ⟨rfl, ?_⟩
  intro i
  change lo i ≤ (h * p.1 i - p.2 * o i) / (h - p.2) ∧
    (h * p.1 i - p.2 * o i) / (h - p.2) ≤ hi i
  have hd : 0 < h - p.2 := sub_pos.mpr hph
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [(hp.2.2 i).1]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [(hp.2.2 i).2]

/-- The ray parameter is the normal coordinate divided by the apex height. -/
theorem pyramid_convex_combination {k : ℕ} (o : Fin k → ℝ) {h : ℝ}
    (hh : 0 < h) (p : PyramidPoint k) (hph : p.2 < h) :
    (1 - p.2 / h) • pyramidBaseProjection o h p + (p.2 / h) • (o, h) = p := by
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hd0 : h - p.2 ≠ 0 := ne_of_gt (sub_pos.mpr hph)
  apply Prod.ext
  · funext i
    change (1 - p.2 / h) * ((h * p.1 i - p.2 * o i) / (h - p.2)) +
      (p.2 / h) * o i = p.1 i
    field_simp
    ring
  · change (1 - p.2 / h) * 0 + (p.2 / h) * h = p.2
    field_simp
    ring

/-- Exact H-representation. Strictly positive height is the only hypothesis. -/
theorem pyramidSolid_eq_halfspaces {k : ℕ} (lo hi o : Fin k → ℝ) {h : ℝ}
    (hh : 0 < h) : pyramidSolid lo hi o h = pyramidHalfspaces lo hi o h := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_pyramidHalfspaces lo hi o h)
    exact Set.insert_subset (apex_mem_pyramidHalfspaces lo hi o (le_of_lt hh))
      (pyramidBase_subset_halfspaces lo hi o (le_of_lt hh))
  · intro p hp
    by_cases hph : p.2 = h
    · have hpa := eq_apex_of_mem_pyramidHalfspaces_of_height_eq lo hi o hh hp hph
      rw [hpa]
      exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · have hplt : p.2 < h := lt_of_le_of_ne hp.2.1 hph
      rw [← pyramid_convex_combination o hh p hplt]
      apply (convex_convexHull ℝ _)
      · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (pyramidBaseProjection_mem lo hi o hp hplt))
      · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      · exact sub_nonneg.mpr ((div_le_one₀ hh).mpr hp.2.1)
      · exact div_nonneg hp.1 (le_of_lt hh)
      · ring

/-- Direct membership criterion, convenient for the later facet arguments. -/
theorem mem_pyramidSolid_iff {k : ℕ} (lo hi o : Fin k → ℝ) {h : ℝ}
    (hh : 0 < h) (p : PyramidPoint k) :
    p ∈ pyramidSolid lo hi o h ↔ 0 ≤ p.2 ∧ p.2 ≤ h ∧ ∀ i,
      (h - p.2) * lo i + p.2 * o i ≤ h * p.1 i ∧
      h * p.1 i ≤ (h - p.2) * hi i + p.2 * o i := by
  rw [pyramidSolid_eq_halfspaces lo hi o hh]
  rfl

/-- Two height inequalities and two side inequalities per tangential coordinate. -/
abbrev PyramidHalfspaceIndex (k : ℕ) := Bool ⊕ (Fin k × Bool)

@[simp] theorem card_pyramidHalfspaceIndex (k : ℕ) :
    Fintype.card (PyramidHalfspaceIndex k) = 2 + 2 * k := by
  simp [PyramidHalfspaceIndex, Nat.mul_comm]

/-- Outward linear forms. `false` selects the lower height or lower side. -/
noncomputable def pyramidHalfspaceNormal {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ)
    (j : PyramidHalfspaceIndex k) : PyramidPoint k →ₗ[ℝ] ℝ where
  toFun p := match j with
    | .inl false => -p.2
    | .inl true => p.2
    | .inr (i, false) => (o i - lo i) * p.2 - h * p.1 i
    | .inr (i, true) => h * p.1 i + (hi i - o i) * p.2
  map_add' := by
    intro p q
    rcases j with b | ⟨i, b⟩ <;> cases b <;> simp <;> ring
  map_smul' := by
    intro a p
    rcases j with b | ⟨i, b⟩ <;> cases b <;> simp <;> ring

/-- Bounds paired with `pyramidHalfspaceNormal`. -/
noncomputable def pyramidHalfspaceBound {k : ℕ} (lo hi : Fin k → ℝ) (h : ℝ) :
    PyramidHalfspaceIndex k → ℝ
  | .inl false => 0
  | .inl true => h
  | .inr (i, false) => -h * lo i
  | .inr (i, true) => h * hi i

/-- Explicit finite closed halfspaces, each expressed by a genuine linear map. -/
def pyramidClosedHalfspace {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ)
    (j : PyramidHalfspaceIndex k) : Set (PyramidPoint k) :=
  {p | pyramidHalfspaceNormal lo hi o h j p ≤ pyramidHalfspaceBound lo hi h j}

theorem mem_pyramidHalfspaces_iff_forall_halfspace {k : ℕ}
    (lo hi o : Fin k → ℝ) (h : ℝ) (p : PyramidPoint k) :
    p ∈ pyramidHalfspaces lo hi o h ↔
      ∀ j, p ∈ pyramidClosedHalfspace lo hi o h j := by
  constructor
  · rintro ⟨hp0, hph, hp⟩ j
    rcases j with b | ⟨i, b⟩ <;> cases b
    · change -p.2 ≤ 0
      linarith
    · exact hph
    · change (o i - lo i) * p.2 - h * p.1 i ≤ -h * lo i
      nlinarith [(hp i).1]
    · change h * p.1 i + (hi i - o i) * p.2 ≤ h * hi i
      nlinarith [(hp i).2]
  · intro hp
    have hp0 := hp (.inl false)
    have hph := hp (.inl true)
    change -p.2 ≤ 0 at hp0
    refine ⟨by linarith, hph, ?_⟩
    intro i
    have hlo := hp (.inr (i, false))
    have hhi := hp (.inr (i, true))
    change (o i - lo i) * p.2 - h * p.1 i ≤ -h * lo i at hlo
    change h * p.1 i + (hi i - o i) * p.2 ≤ h * hi i at hhi
    constructor <;> nlinarith

/-- The H-representation is an intersection over exactly `2 + 2*k` inequalities. -/
theorem pyramidSolid_eq_iInter_halfspaces {k : ℕ} (lo hi o : Fin k → ℝ) {h : ℝ}
    (hh : 0 < h) :
    pyramidSolid lo hi o h = ⋂ j : PyramidHalfspaceIndex k,
      pyramidClosedHalfspace lo hi o h j := by
  rw [pyramidSolid_eq_halfspaces lo hi o hh]
  ext p
  simp only [Set.mem_iInter, mem_pyramidHalfspaces_iff_forall_halfspace]

theorem convex_pyramidClosedHalfspace {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ)
    (j : PyramidHalfspaceIndex k) : Convex ℝ (pyramidClosedHalfspace lo hi o h j) :=
  (convex_Iic (pyramidHalfspaceBound lo hi h j)).linear_preimage
    (pyramidHalfspaceNormal lo hi o h j)

theorem isClosed_pyramidClosedHalfspace {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ)
    (j : PyramidHalfspaceIndex k) : IsClosed (pyramidClosedHalfspace lo hi o h j) :=
  isClosed_le (pyramidHalfspaceNormal lo hi o h j).continuous_of_finiteDimensional
    continuous_const

theorem isClosed_pyramidSolid {k : ℕ} (lo hi o : Fin k → ℝ) {h : ℝ}
    (hh : 0 < h) : IsClosed (pyramidSolid lo hi o h) := by
  rw [pyramidSolid_eq_iInter_halfspaces lo hi o hh]
  exact isClosed_iInter (isClosed_pyramidClosedHalfspace lo hi o h)

#print axioms pyramidSolid_eq_halfspaces
#print axioms mem_pyramidSolid_iff
#print axioms pyramidSolid_eq_iInter_halfspaces
#print axioms isClosed_pyramidSolid

end SparseMonotiles
