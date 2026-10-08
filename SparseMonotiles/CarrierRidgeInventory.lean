module

public import SparseMonotiles.GlobalBodyAffine
public import SparseMonotiles.OrthogonalTransverseSection

@[expose] public section

/-!
# Literal carrier germs at generic codimension-two ridges

The finite inventory below is derived from the closed chair's Boolean formula.
In particular, inner coordinate boundaries are retained. No sector inventory is
an input to this argument.
-/
namespace SparseMonotiles

open Set

/-- Coordinates carrying one of the actual carrier equations at the base point. -/
noncomputable def carrierCriticalAxes {d : ℕ} (p : Point d) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun i => p i = 0 ∨ p i = 1 ∨ p i = 2

@[simp] theorem mem_carrierCriticalAxes {d : ℕ} (p : Point d) (i : Fin d) :
    i ∈ carrierCriticalAxes p ↔ p i = 0 ∨ p i = 1 ∨ p i = 2 := by
  classical
  simp [carrierCriticalAxes]

/-- The displacement cone obtained by freezing the actual closed-chair formula. -/
def carrierLinearCone {d : ℕ} (p : Point d) : Set (Point d) :=
  {v | (∀ i, 0 ≤ p i ∧ p i ≤ 2) ∧
    (∀ i, p i = 0 → 0 ≤ v i) ∧ (∀ i, p i = 2 → v i ≤ 0) ∧
    ((∃ i, p i < 1) ∨ ∃ i, p i = 1 ∧ v i ≤ 0)}

private theorem carrier_frozen_lower {d : ℕ} (p v : Point d) (i : Fin d) :
    frozenHalfspacePredicates carrierHalfspaceSlack p (p + v) (i, 0) ↔
      0 ≤ p i ∧ (p i = 0 → 0 ≤ v i) := by
  simp only [frozenHalfspacePredicates, carrierHalfspaceSlack, if_true]
  by_cases h : p i = 0 <;> simp [h]

private theorem carrier_frozen_upper {d : ℕ} (p v : Point d) (i : Fin d) :
    frozenHalfspacePredicates carrierHalfspaceSlack p (p + v) (i, 1) ↔
      p i ≤ 2 ∧ (p i = 2 → v i ≤ 0) := by
  change (if 2 - p i = 0 then 0 ≤ 2 - (p i + v i) else 0 ≤ 2 - p i) ↔ _
  by_cases h : p i = 2
  · simp [h]
  · have h' : 2 - p i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simp [h, h', sub_nonneg]

private theorem carrier_frozen_inner {d : ℕ} (p v : Point d) (i : Fin d) :
    frozenHalfspacePredicates carrierHalfspaceSlack p (p + v) (i, 2) ↔
      p i < 1 ∨ p i = 1 ∧ v i ≤ 0 := by
  change (if 1 - p i = 0 then 0 ≤ 1 - (p i + v i) else 0 ≤ 1 - p i) ↔ _
  by_cases h : p i = 1
  · simp [h]
  · have h' : 1 - p i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simp only [h', if_false, h, false_and, or_false, sub_nonneg]
    exact ⟨fun hle => lt_of_le_of_ne hle h, le_of_lt⟩

/-- Exact equality, not merely agreement away from boundary rays. -/
theorem mem_frozen_carrier_iff {d : ℕ} (p v : Point d) :
    p + v ∈ ((carrierHalfspaceFormula d).freeze carrierHalfspaceSlack p).region
      carrierHalfspaceSlack ↔ v ∈ carrierLinearCone p := by
  change ((carrierHalfspaceFormula d).freeze carrierHalfspaceSlack p).eval
      (fun j => 0 ≤ carrierHalfspaceSlack j (p + v)) ↔ _
  rw [HalfspaceFormula.eval_freeze]
  simp [carrierHalfspaceFormula, HalfspaceFormula.eval,
    HalfspaceFormula.eval_allAtoms, HalfspaceFormula.eval_anyAtoms,
    carrier_frozen_lower, carrier_frozen_upper, carrier_frozen_inner,
    carrierLinearCone, forall_and, exists_or]
  tauto

/-- Signed coordinate halfspaces use inward, unit Euclidean normals. -/
def carrierAxisHalfspace {d : ℕ} (i : Fin d) (positive : Bool) : Set (Point d) :=
  {v | if positive then 0 ≤ v i else v i ≤ 0}

/-- A literal, closed-set inventory with each used axis certified active. -/
inductive IsCarrierCoordinateCone {d : ℕ} (p : Point d) : Set (Point d) → Prop
  | empty : IsCarrierCoordinateCone p ∅
  | univ : IsCarrierCoordinateCone p univ
  | half (i : Fin d) (b : Bool) (hi : i ∈ carrierCriticalAxes p) :
      IsCarrierCoordinateCone p (carrierAxisHalfspace i b)
  | quadrant (i j : Fin d) (b c : Bool) (hij : i ≠ j)
      (hi : i ∈ carrierCriticalAxes p) (hj : j ∈ carrierCriticalAxes p) :
      IsCarrierCoordinateCone p (carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c)
  | reflex (i j : Fin d) (hij : i ≠ j)
      (hi : p i = 1) (hj : p j = 1) :
      IsCarrierCoordinateCone p (carrierAxisHalfspace i false ∪ carrierAxisHalfspace j false)

/-- Outer-box contribution of one coordinate, retaining its closed face. -/
def carrierOuterCoordinateCone {d : ℕ} (p : Point d) (i : Fin d) : Set (Point d) :=
  {v | (p i = 0 → 0 ≤ v i) ∧ (p i = 2 → v i ≤ 0)}

private theorem carrierOuterCoordinateCone_eq {d : ℕ} (p : Point d) (i : Fin d) :
    carrierOuterCoordinateCone p i =
      if p i = 0 then carrierAxisHalfspace i true else
      if p i = 2 then carrierAxisHalfspace i false else univ := by
  classical
  by_cases h0 : p i = 0
  · have h2 : p i ≠ 2 := by linarith
    ext v; simp [carrierOuterCoordinateCone, carrierAxisHalfspace, h0, h2]
  · by_cases h2 : p i = 2 <;>
      ext v <;> simp [carrierOuterCoordinateCone, carrierAxisHalfspace, h0, h2]

/-- Two slots suffice for all active coordinate equations, including empty or
singleton inventories. Extra slots do not impose inequalities. -/
theorem carrierCriticalAxes_covered_by_pair {d : ℕ} (hd : 2 ≤ d) (p : Point d)
    (hcard : (carrierCriticalAxes p).card ≤ 2) :
    ∃ i j : Fin d, i ≠ j ∧ ∀ k ∈ carrierCriticalAxes p, k = i ∨ k = j := by
  classical
  obtain ⟨s, hs, _, hsc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (carrierCriticalAxes p)) hcard
    (by simpa using hd : 2 ≤ (Finset.univ : Finset (Fin d)).card)
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hsc
  exact ⟨i, j, hij, fun k hk => by simpa using hs hk⟩

/-- Exact two-slot reduction of the carrier Boolean formula. -/
theorem carrierLinearCone_pair_formula {d : ℕ} (p : Point d)
    (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 2) (i j : Fin d)
    (hcover : ∀ k ∈ carrierCriticalAxes p, k = i ∨ k = j) :
    carrierLinearCone p = carrierOuterCoordinateCone p i ∩ carrierOuterCoordinateCone p j ∩
      {v | (∃ k, p k < 1) ∨ (p i = 1 ∧ v i ≤ 0) ∨ (p j = 1 ∧ v j ≤ 0)} := by
  ext v
  constructor
  · rintro ⟨_, h0, h2, h1⟩
    refine ⟨⟨⟨h0 i, h2 i⟩, ⟨h0 j, h2 j⟩⟩, ?_⟩
    rcases h1 with h1 | ⟨k, hk, hv⟩
    · exact Or.inl h1
    · rcases hcover k (by simp [hk]) with rfl | rfl
      · exact Or.inr (Or.inl ⟨hk, hv⟩)
      · exact Or.inr (Or.inr ⟨hk, hv⟩)
  · rintro ⟨⟨hi, hj⟩, h1⟩
    refine ⟨hp, ?_, ?_, ?_⟩
    · intro k hk
      rcases hcover k (by simp [hk]) with rfl | rfl
      · exact hi.1 hk
      · exact hj.1 hk
    · intro k hk
      rcases hcover k (by simp [hk]) with rfl | rfl
      · exact hi.2 hk
      · exact hj.2 hk
    · rcases h1 with h1 | hi | hj
      · exact Or.inl h1
      · exact Or.inr ⟨i, hi⟩
      · exact Or.inr ⟨j, hj⟩



private theorem carrierOuterCoordinateCone_cases {d : ℕ} (p : Point d) (i : Fin d) :
    carrierOuterCoordinateCone p i = univ ∨
      ∃ b, i ∈ carrierCriticalAxes p ∧
        carrierOuterCoordinateCone p i = carrierAxisHalfspace i b := by
  classical
  rw [carrierOuterCoordinateCone_eq]
  by_cases h0 : p i = 0
  · exact Or.inr ⟨true, by simp [h0], by simp [h0]⟩
  · by_cases h2 : p i = 2
    · exact Or.inr ⟨false, by simp [h2], by simp [h0, h2]⟩
    · exact Or.inl (by simp [h0, h2])

private theorem carrier_outer_pair_inventory {d : ℕ} (p : Point d)
    (i j : Fin d) (hij : i ≠ j) :
    IsCarrierCoordinateCone p (carrierOuterCoordinateCone p i ∩ carrierOuterCoordinateCone p j) := by
  rcases carrierOuterCoordinateCone_cases p i with hi | ⟨b, hi, hbi⟩
  · rw [hi, univ_inter]
    rcases carrierOuterCoordinateCone_cases p j with hj | ⟨c, hj, hcj⟩
    · rw [hj]; exact .univ
    · rw [hcj]; exact .half j c hj
  · rw [hbi]
    rcases carrierOuterCoordinateCone_cases p j with hj | ⟨c, hj, hcj⟩
    · rw [hj, inter_univ]; exact .half i b hi
    · rw [hcj]; exact .quadrant i j b c hij hi hj

private theorem carrier_inner_outer_inventory {d : ℕ} (p : Point d)
    (i j : Fin d) (hij : i ≠ j) (hi : p i = 1) :
    IsCarrierCoordinateCone p (carrierAxisHalfspace i false ∩ carrierOuterCoordinateCone p j) := by
  rcases carrierOuterCoordinateCone_cases p j with hj | ⟨c, hj, hcj⟩
  · rw [hj, inter_univ]; exact .half i false (by simp [hi])
  · rw [hcj]; exact .quadrant i j false c hij (by simp [hi]) hj

/-- Complete literal carrier classification. The rank bound is used only to
limit the number of distinct coordinate axes, not to assume any sector shape. -/
theorem carrierLinearCone_inventory {d : ℕ} (hd : 2 ≤ d) (p : Point d)
    (hcard : (carrierCriticalAxes p).card ≤ 2) :
    IsCarrierCoordinateCone p (carrierLinearCone p) := by
  classical
  by_cases hp : ∀ k, 0 ≤ p k ∧ p k ≤ 2
  · obtain ⟨i, j, hij, hcover⟩ := carrierCriticalAxes_covered_by_pair hd p hcard
    rw [carrierLinearCone_pair_formula p hp i j hcover]
    by_cases hinner : ∃ k, p k < 1
    · simp only [hinner, true_or, setOf_true, inter_univ]
      exact carrier_outer_pair_inventory p i j hij
    · simp only [hinner, false_or]
      by_cases hi : p i = 1
      · have hi0 : p i ≠ 0 := by linarith
        have hi2 : p i ≠ 2 := by linarith
        have hOi : carrierOuterCoordinateCone p i = univ := by
          ext v; simp [carrierOuterCoordinateCone, hi]
        rw [hOi, univ_inter]
        simp only [hi, true_and]
        by_cases hj : p j = 1
        · have hj0 : p j ≠ 0 := by linarith
          have hj2 : p j ≠ 2 := by linarith
          have hOj : carrierOuterCoordinateCone p j = univ := by
            ext v; simp [carrierOuterCoordinateCone, hj]
          rw [hOj, univ_inter]
          simp only [hj, true_and]
          exact .reflex i j hij hi hj
        · simp only [hj, false_and, or_false]
          rw [inter_comm]
          exact carrier_inner_outer_inventory p i j hij hi
      · by_cases hj : p j = 1
        · have hj0 : p j ≠ 0 := by linarith
          have hj2 : p j ≠ 2 := by linarith
          have hOj : carrierOuterCoordinateCone p j = univ := by
            ext v; simp [carrierOuterCoordinateCone, hj]
          rw [hOj, inter_univ]
          simp only [hi, false_and, false_or, hj, true_and]
          rw [inter_comm]
          exact carrier_inner_outer_inventory p j i hij.symm hj
        · simp only [hi, hj, false_and, false_or, setOf_false, inter_empty]
          exact .empty
  · have heq : carrierLinearCone p = ∅ := by
      ext v
      simp [carrierLinearCone, hp]
    rw [heq]
    exact .empty

/-- A coordinate plane containing the ridge contributes its actual unit normal
to the common normal space. -/
theorem carrier_axis_mem_ridge_orthogonal {d : ℕ}
    (R : AffineSubspace ℝ (Point d)) {p : Point d} (hp : p ∈ R)
    (hactive : ∀ a : CarrierHalfspaceIndex d, carrierSlackAffine a p = 0 →
      R ≤ affineFormPlane (carrierSlackAffine a) 0)
    {i : Fin d} (hi : i ∈ carrierCriticalAxes p) :
    EuclideanSpace.single i (1 : ℝ) ∈ R.directionᗮ := by
  have hconst : ∀ x ∈ R, x i = p i := by
    rcases (mem_carrierCriticalAxes p i).mp hi with hi | hi | hi
    · have ha : carrierSlackAffine (i, 0) p = 0 := by
        simpa [carrierSlackAffine_apply, carrierHalfspaceSlack] using hi
      intro x hx
      have he := (mem_affineFormPlane _ _ _).mp (hactive (i, 0) ha hx)
      simpa [carrierSlackAffine_apply, carrierHalfspaceSlack, hi] using he
    · have ha : carrierSlackAffine (i, 2) p = 0 := by
        simp [carrierSlackAffine_apply, carrierHalfspaceSlack, hi]
      intro x hx
      have he := (mem_affineFormPlane _ _ _).mp (hactive (i, 2) ha hx)
      simp [carrierSlackAffine_apply, carrierHalfspaceSlack] at he
      linarith
    · have ha : carrierSlackAffine (i, 1) p = 0 := by
        simp [carrierSlackAffine_apply, carrierHalfspaceSlack, hi]
      intro x hx
      have he := (mem_affineFormPlane _ _ _).mp (hactive (i, 1) ha hx)
      simp [carrierSlackAffine_apply, carrierHalfspaceSlack] at he
      linarith
  exact normal_mem_ridge_orthogonal ⟨p, hp⟩ (le_refl R)
    (fun x hx => by simpa [EuclideanSpace.inner_single_left] using hconst x hx)

/-- Orthogonality of distinct coordinate axes proves the required rank bound. -/
theorem carrierCriticalAxes_card_le_two {d : ℕ}
    (R : AffineSubspace ℝ (Point d)) {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ a : CarrierHalfspaceIndex d, carrierSlackAffine a p = 0 →
      R ≤ affineFormPlane (carrierSlackAffine a) 0) :
    (carrierCriticalAxes p).card ≤ 2 := by
  classical
  have hm (i : ↥(carrierCriticalAxes p)) :
      EuclideanSpace.single i.1 (1 : ℝ) ∈ R.directionᗮ :=
    carrier_axis_mem_ridge_orthogonal R hp hactive i.property
  have hlin : LinearIndependent ℝ
      (fun i : ↥(carrierCriticalAxes p) => EuclideanSpace.single i.1 (1 : ℝ)) :=
    (EuclideanSpace.orthonormal_single.comp Subtype.val Subtype.val_injective).linearIndependent
  have hlin' : LinearIndependent ℝ
      (fun i : ↥(carrierCriticalAxes p) =>
        (⟨EuclideanSpace.single i.1 (1 : ℝ), hm i⟩ : R.directionᗮ)) :=
    LinearIndependent.of_comp R.directionᗮ.subtype hlin
  have hr : Module.finrank ℝ R.directionᗮ = 2 :=
    ridge_orthogonal_finrank_two R (by simpa [Point] using hcodim)
  simpa only [hr, Fintype.card_coe] using hlin'.fintype_card_le_finrank

section NormalInventory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Closed inward halfspace, intrinsic to the indicated inner-product space. -/
def normalHalfspace (n : E) : Set E := {v | 0 ≤ inner (𝕜 := ℝ) n v}

/-- The complete normal-cone inventory; all nontrivial normals are unit, and
all pairs are orthogonal. Thus no zero or parallel normal is hidden here. -/
inductive IsRightAngleCone : Set E → Prop
  | empty : IsRightAngleCone ∅
  | univ : IsRightAngleCone univ
  | half (n : E) (hn : ‖n‖ = 1) : IsRightAngleCone (normalHalfspace n)
  | quadrant (n m : E) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
      (hnm : inner (𝕜 := ℝ) n m = 0) :
      IsRightAngleCone (normalHalfspace n ∩ normalHalfspace m)
  | reflex (n m : E) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
      (hnm : inner (𝕜 := ℝ) n m = 0) :
      IsRightAngleCone (normalHalfspace n ∪ normalHalfspace m)

/-- Boundary sectors exclude the empty and full-plane cases explicitly. -/
def IsRightAngleBoundaryCone (S : Set E) : Prop :=
  (∃ n, ‖n‖ = 1 ∧ S = normalHalfspace n) ∨
  ∃ n m, ‖n‖ = 1 ∧ ‖m‖ = 1 ∧ inner (𝕜 := ℝ) n m = 0 ∧
    (S = normalHalfspace n ∩ normalHalfspace m ∨
      S = normalHalfspace n ∪ normalHalfspace m)

theorem IsRightAngleCone.isClosed {S : Set E} (h : IsRightAngleCone S) : IsClosed S := by
  have hc (n : E) : IsClosed (normalHalfspace n) :=
    isClosed_le continuous_const (continuous_const.inner continuous_id)
  cases h with
  | empty => exact isClosed_empty
  | univ => exact isClosed_univ
  | half n _ => exact hc n
  | quadrant n m _ _ _ => exact (hc n).inter (hc m)
  | reflex n m _ _ _ => exact (hc n).union (hc m)

theorem IsRightAngleCone.boundary {S : Set E} (h : IsRightAngleCone S)
    (hne : S ≠ ∅) (hfull : S ≠ Set.univ) : IsRightAngleBoundaryCone S := by
  cases h with
  | empty => exact False.elim (hne rfl)
  | univ => exact False.elim (hfull rfl)
  | half n hn => exact Or.inl ⟨n, hn, rfl⟩
  | quadrant n m hn hm hnm => exact Or.inr ⟨n, m, hn, hm, hnm, Or.inl rfl⟩
  | reflex n m hn hm hnm => exact Or.inr ⟨n, m, hn, hm, hnm, Or.inr rfl⟩

noncomputable def signedAxisNormal {d : ℕ} (e : Point d ≃ₗᵢ[ℝ] E)
    (V : Submodule ℝ E) (i : Fin d) (hi : e (EuclideanSpace.single i 1) ∈ V)
    (b : Bool) : V :=
  if b then ⟨e (EuclideanSpace.single i 1), hi⟩ else -⟨e (EuclideanSpace.single i 1), hi⟩

theorem norm_signedAxisNormal {d : ℕ} (e : Point d ≃ₗᵢ[ℝ] E)
    (V : Submodule ℝ E) (i : Fin d) (hi : e (EuclideanSpace.single i 1) ∈ V)
    (b : Bool) : ‖signedAxisNormal e V i hi b‖ = 1 := by
  cases b <;> simp [signedAxisNormal]

theorem inner_signedAxisNormal {d : ℕ} (e : Point d ≃ₗᵢ[ℝ] E)
    (V : Submodule ℝ E) (i j : Fin d)
    (hi : e (EuclideanSpace.single i 1) ∈ V)
    (hj : e (EuclideanSpace.single j 1) ∈ V)
    (b c : Bool) (hij : i ≠ j) :
    inner (𝕜 := ℝ) (signedAxisNormal e V i hi b) (signedAxisNormal e V j hj c) = 0 := by
  have hz : inner (𝕜 := ℝ) (e (EuclideanSpace.single i 1))
      (e (EuclideanSpace.single j 1)) = 0 := by
    rw [e.inner_map_map]
    simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hij]
  cases b <;> cases c <;>
    simpa [signedAxisNormal, Submodule.coe_inner] using hz

theorem normalHalfspace_signedAxisNormal {d : ℕ} (e : Point d ≃ₗᵢ[ℝ] E)
    (V : Submodule ℝ E) (i : Fin d) (hi : e (EuclideanSpace.single i 1) ∈ V)
    (b : Bool) :
    normalHalfspace (signedAxisNormal e V i hi b) =
      (fun v : V => e.symm (v : E)) ⁻¹' carrierAxisHalfspace i b := by
  ext v
  have heq : inner (𝕜 := ℝ) (e (EuclideanSpace.single i 1)) (v : E) = e.symm v i := by
    conv_lhs => rw [← e.apply_symm_apply (v : E)]
    rw [e.inner_map_map]
    simp [EuclideanSpace.inner_single_left]
  cases b <;>
    simp [normalHalfspace, signedAxisNormal, carrierAxisHalfspace, Submodule.coe_inner, heq]

/-- Every coordinate-shape conclusion becomes an intrinsic normal cone in any
orthogonal physical frame. All normals are actual active-coordinate normals. -/
theorem IsCarrierCoordinateCone.normal_inventory {d : ℕ}
    (e : Point d ≃ₗᵢ[ℝ] E) (V : Submodule ℝ E) (p : Point d)
    (hmem : ∀ i ∈ carrierCriticalAxes p, e (EuclideanSpace.single i 1) ∈ V)
    {S : Set (Point d)} (h : IsCarrierCoordinateCone p S) :
    IsRightAngleCone ((fun v : V => e.symm (v : E)) ⁻¹' S) := by
  cases h with
  | empty => simpa using (IsRightAngleCone.empty : IsRightAngleCone (∅ : Set V))
  | univ => simpa using (IsRightAngleCone.univ : IsRightAngleCone (Set.univ : Set V))
  | half i b hi =>
      rw [← normalHalfspace_signedAxisNormal e V i (hmem i hi) b]
      exact .half _ (norm_signedAxisNormal _ _ _ _ _)
  | quadrant i j b c hij hi hj =>
      rw [preimage_inter, ← normalHalfspace_signedAxisNormal e V i (hmem i hi) b,
        ← normalHalfspace_signedAxisNormal e V j (hmem j hj) c]
      exact .quadrant _ _ (norm_signedAxisNormal _ _ _ _ _)
        (norm_signedAxisNormal _ _ _ _ _) (inner_signedAxisNormal _ _ _ _ _ _ _ _ hij)
  | reflex i j hij hi hj =>
      rw [preimage_union,
        ← normalHalfspace_signedAxisNormal e V i (hmem i (by simp [hi])) false,
        ← normalHalfspace_signedAxisNormal e V j (hmem j (by simp [hj])) false]
      exact .reflex _ _ (norm_signedAxisNormal _ _ _ _ _)
        (norm_signedAxisNormal _ _ _ _ _) (inner_signedAxisNormal _ _ _ _ _ _ _ _ hij)

end NormalInventory

/-- The generic-ridge hypotheses imply the complete canonical normal inventory. -/
theorem carrier_ridge_normal_cone_inventory {d : ℕ}
    (R : AffineSubspace ℝ (Point d)) {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ a : CarrierHalfspaceIndex d, carrierSlackAffine a p = 0 →
      R ≤ affineFormPlane (carrierSlackAffine a) 0) :
    IsRightAngleCone ((fun v : R.directionᗮ => (v : Point d)) ⁻¹' carrierLinearCone p) := by
  have hInv := carrierLinearCone_inventory (by omega : 2 ≤ d) p
    (carrierCriticalAxes_card_le_two R hp hcodim hactive)
  exact hInv.normal_inventory (LinearIsometryEquiv.refl ℝ (Point d)) R.directionᗮ p
    (fun i hi => carrier_axis_mem_ridge_orthogonal R hp hactive hi)

/-- The cone classified above is exactly the actual frozen normal section. -/
theorem carrier_frozenRidgeSection_eq {d : ℕ}
    (R : AffineSubspace ℝ (Point d)) (p : Point d) :
    frozenRidgeSection R p carrierSlackAffine (carrierHalfspaceFormula d) =
      (fun v : R.directionᗮ => (v : Point d)) ⁻¹' carrierLinearCone p := by
  have hf : (fun a => (carrierSlackAffine a : Point d → ℝ)) = carrierHalfspaceSlack := by
    funext a x; exact carrierSlackAffine_apply a x
  ext v
  change p + (v : Point d) ∈ ((carrierHalfspaceFormula d).freeze
    (fun a => (carrierSlackAffine a : Point d → ℝ)) p).region
    (fun a => (carrierSlackAffine a : Point d → ℝ)) ↔ _
  rw [hf]
  exact mem_frozen_carrier_iff p (v : Point d)

/-- Closure adds no boundary rays to this carrier section: every listed
halfspace, quadrant, and reflex union already includes its entire boundary. -/
theorem carrier_closed_frozenRidgeSection_inventory {d : ℕ}
    (R : AffineSubspace ℝ (Point d)) {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ a : CarrierHalfspaceIndex d, carrierSlackAffine a p = 0 →
      R ≤ affineFormPlane (carrierSlackAffine a) 0) :
    IsRightAngleCone (closure
      (frozenRidgeSection R p carrierSlackAffine (carrierHalfspaceFormula d))) := by
  rw [carrier_frozenRidgeSection_eq]
  have h := carrier_ridge_normal_cone_inventory R hp hcodim hactive
  rwa [h.isClosed.closure_eq]

/-- Pull back the literal carrier equations through any physical affine frame.
The map `a` sends world coordinates to canonical carrier coordinates. -/
noncomputable def carrierFrameFields {d : ℕ} (a : Point d ≃ᵃⁱ[ℝ] Point d)
    (j : CarrierHalfspaceIndex d) : Point d →ᵃ[ℝ] ℝ :=
  (carrierSlackAffine j).comp a.toAffineEquiv.toAffineMap

@[simp] theorem carrierFrameFields_apply {d : ℕ} (a : Point d ≃ᵃⁱ[ℝ] Point d)
    (j : CarrierHalfspaceIndex d) (x : Point d) :
    carrierFrameFields a j x = carrierHalfspaceSlack j (a x) :=
  carrierSlackAffine_apply j (a x)

private theorem coordinate_eq_of_active_carrier_slacks {d : ℕ} (p x : Point d)
    (hactive : ∀ j : CarrierHalfspaceIndex d,
      carrierHalfspaceSlack j p = 0 → carrierHalfspaceSlack j x = 0)
    {i : Fin d} (hi : i ∈ carrierCriticalAxes p) : x i = p i := by
  rcases (mem_carrierCriticalAxes p i).mp hi with hi | hi | hi
  · have h := hactive (i, 0) (by simp [carrierHalfspaceSlack, hi])
    simpa [carrierHalfspaceSlack, hi] using h
  · have h := hactive (i, 2) (by simp [carrierHalfspaceSlack, hi])
    simp [carrierHalfspaceSlack] at h
    linarith
  · have h := hactive (i, 1) (by simp [carrierHalfspaceSlack, hi])
    simp [carrierHalfspaceSlack] at h
    linarith

/-- Active normals in an arbitrary physical frame lie in the genuine world
ridge's orthogonal complement. No signed-permutation restriction is used. -/
theorem carrier_frame_axis_mem_ridge_orthogonal {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0)
    {i : Fin d} (hi : i ∈ carrierCriticalAxes (a p)) :
    a.linearIsometryEquiv.symm (EuclideanSpace.single i 1) ∈ R.directionᗮ := by
  have hconst (x : Point d) (hx : x ∈ R) : a x i = a p i := by
    apply coordinate_eq_of_active_carrier_slacks (a p) (a x) _ hi
    intro j hj
    have hj' : carrierFrameFields a j p = 0 := by simpa using hj
    simpa using (mem_affineFormPlane _ _ _).mp (hactive j hj' hx)
  apply normal_mem_ridge_orthogonal ⟨p, hp⟩ (le_refl R)
    (N := a.linearIsometryEquiv.symm (EuclideanSpace.single i 1))
    (c := inner (𝕜 := ℝ) (a.linearIsometryEquiv.symm (EuclideanSpace.single i 1)) p)
  intro x hx
  have hmap := a.map_vsub x p
  change a.linearIsometryEquiv (x - p) = a x - a p at hmap
  have hz : inner (𝕜 := ℝ)
      (a.linearIsometryEquiv.symm (EuclideanSpace.single i 1)) (x - p) = 0 := by
    rw [← a.linearIsometryEquiv.inner_map_map,
      a.linearIsometryEquiv.apply_symm_apply, hmap]
    simp [EuclideanSpace.inner_single_left, hconst x hx]
  rw [inner_sub_right] at hz
  exact sub_eq_zero.mp hz

/-- Independence bounds active physical coordinate axes before any cone shape
is considered. -/
theorem carrier_frame_criticalAxes_card_le_two {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0) :
    (carrierCriticalAxes (a p)).card ≤ 2 := by
  classical
  let e := a.linearIsometryEquiv.symm
  have hm (i : ↥(carrierCriticalAxes (a p))) :
      e (EuclideanSpace.single i.1 1) ∈ R.directionᗮ :=
    carrier_frame_axis_mem_ridge_orthogonal a R hp hactive i.property
  have hlin : LinearIndependent ℝ
      (fun i : ↥(carrierCriticalAxes (a p)) => e (EuclideanSpace.single i.1 1)) :=
    ((EuclideanSpace.orthonormal_single.comp Subtype.val Subtype.val_injective).comp_linearIsometryEquiv e).linearIndependent
  have hlin' : LinearIndependent ℝ
      (fun i : ↥(carrierCriticalAxes (a p)) =>
        (⟨e (EuclideanSpace.single i.1 1), hm i⟩ : R.directionᗮ)) :=
    LinearIndependent.of_comp R.directionᗮ.subtype hlin
  have hr : Module.finrank ℝ R.directionᗮ = 2 :=
    ridge_orthogonal_finrank_two R (by simpa [Point] using hcodim)
  simpa only [hr, Fintype.card_coe] using hlin'.fintype_card_le_finrank

/-- Exact identification of the actual frozen carrier section in its arbitrary
physical frame with the displacement formula already classified above. -/
theorem carrier_frame_frozenRidgeSection_eq {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d)) (p : Point d) :
    frozenRidgeSection R p (carrierFrameFields a) (carrierHalfspaceFormula d) =
      (fun v : R.directionᗮ => a.linearIsometryEquiv (v : Point d)) ⁻¹'
        carrierLinearCone (a p) := by
  ext v
  have hmap := a.map_vadd p (v : Point d)
  change a ((v : Point d) + p) = a.linearIsometryEquiv (v : Point d) + a p at hmap
  have hmap' : a (p + (v : Point d)) = a p + a.linearIsometryEquiv (v : Point d) := by
    simpa only [add_comm] using hmap
  change ((carrierHalfspaceFormula d).freeze
    (fun j => (carrierFrameFields a j : Point d → ℝ)) p).eval
      (fun j => 0 ≤ carrierFrameFields a j (p + (v : Point d))) ↔ _
  rw [HalfspaceFormula.eval_freeze]
  rw [show (v ∈ (fun v : R.directionᗮ => a.linearIsometryEquiv (v : Point d)) ⁻¹'
      carrierLinearCone (a p)) ↔ a.linearIsometryEquiv (v : Point d) ∈
      carrierLinearCone (a p) from Iff.rfl]
  rw [← mem_frozen_carrier_iff]
  change _ ↔ ((carrierHalfspaceFormula d).freeze carrierHalfspaceSlack (a p)).eval _
  rw [HalfspaceFormula.eval_freeze]
  have heq : frozenHalfspacePredicates (fun j => (carrierFrameFields a j : Point d → ℝ))
      p (p + (v : Point d)) = frozenHalfspacePredicates carrierHalfspaceSlack (a p)
        (a p + a.linearIsometryEquiv (v : Point d)) := by
    funext j
    simp only [frozenHalfspacePredicates, carrierFrameFields_apply, hmap']
  rw [heq]

/-- Every generic physical carrier cone has only the five listed possibilities,
proved from the actual closed-chair formula and the ridge rank equation. -/
theorem carrier_frame_frozenRidgeSection_inventory {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0) :
    IsRightAngleCone (frozenRidgeSection R p (carrierFrameFields a)
      (carrierHalfspaceFormula d)) := by
  rw [carrier_frame_frozenRidgeSection_eq]
  have h := carrierLinearCone_inventory (by omega : 2 ≤ d) (a p)
    (carrier_frame_criticalAxes_card_le_two a R hp hcodim hactive)
  exact h.normal_inventory a.linearIsometryEquiv.symm R.directionᗮ (a p)
    (fun i hi => carrier_frame_axis_mem_ridge_orthogonal a R hp hactive hi)

/-- The framed formula is the actual carrier in world coordinates. -/
theorem carrier_frame_region {d : ℕ} (a : Point d ≃ᵃⁱ[ℝ] Point d) :
    (carrierHalfspaceFormula d).region (fun j => carrierFrameFields a j) =
      a ⁻¹' carrier d := by
  ext x
  change (carrierHalfspaceFormula d).eval (fun j => 0 ≤ carrierFrameFields a j x) ↔
    a x ∈ carrier d
  simp only [carrierFrameFields_apply]
  change a x ∈ (carrierHalfspaceFormula d).region carrierHalfspaceSlack ↔ _
  rw [carrierHalfspaceFormula_region]

/-- An arbitrary physical carrier has the classified exact closed normal germ. -/
theorem carrier_frame_localSetEq_normal_section {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0) :
    LocalSetEq p (a ⁻¹' carrier d)
      (ridgeNormalProjection R p ⁻¹' closure
        (frozenRidgeSection R p (carrierFrameFields a) (carrierHalfspaceFormula d))) := by
  have hc : IsClosed (a ⁻¹' carrier d) := (carrier_isClosed d).preimage a.continuous
  have h := localSetEq_closed_normal_section R hp (carrierFrameFields a)
    (carrierHalfspaceFormula d)
    (fun j hj y hy => (mem_affineFormPlane _ _ _).mp (hactive j hj hy))
  simpa only [carrier_frame_region, hc.closure_eq] using h

/-- The final closure retains the same exact five-case physical inventory. -/
theorem carrier_frame_closed_normal_inventory {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0) :
    IsRightAngleCone (closure (frozenRidgeSection R p (carrierFrameFields a)
      (carrierHalfspaceFormula d))) := by
  have h := carrier_frame_frozenRidgeSection_inventory a R hp hcodim hactive
  rwa [h.isClosed.closure_eq]

/-- A boundary point cannot have an empty or universal local material model.
The exclusion uses the literal topological frontier, not an asserted angle. -/
theorem IsRightAngleCone.boundary_of_localSetEq
    {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [TopologicalSpace X]
    {S : Set E} {T : Set X} {p : X} {f : X → E}
    (h : IsRightAngleCone S) (hlocal : LocalSetEq p T (f ⁻¹' S))
    (hp : p ∈ frontier T) : IsRightAngleBoundaryCone S := by
  have hb : p ∈ frontier (f ⁻¹' S) := hlocal.frontier.mem_iff.mp hp
  apply h.boundary
  · intro he
    simp only [he, preimage_empty, frontier_empty, mem_empty_iff_false] at hb
  · intro he
    simp only [he, preimage_univ, frontier_univ, mem_empty_iff_false] at hb

/-- At a genuine carrier boundary point only π/2, π, or 3π/2 shape types remain. -/
theorem carrier_frame_boundary_normal_inventory {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0)
    (hboundary : p ∈ frontier (a ⁻¹' carrier d)) :
    IsRightAngleBoundaryCone (closure (frozenRidgeSection R p (carrierFrameFields a)
      (carrierHalfspaceFormula d))) :=
  (carrier_frame_closed_normal_inventory a R hp hcodim hactive).boundary_of_localSetEq
    (carrier_frame_localSetEq_normal_section a R hp hactive) hboundary

/-- Transfer the derived carrier inventory to any actual homogeneous tile cone
whose ambient material germ is the carrier germ. Equality of cones follows
from positive homogeneity and the open normal projection. -/
theorem normal_model_inventory_of_carrier_germ {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0)
    {T : Set (Point d)} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hcarrier : LocalSetEq p T (a ⁻¹' carrier d)) : IsRightAngleCone S := by
  have hlocal := hmodel.symm.trans
    (hcarrier.trans (carrier_frame_localSetEq_normal_section a R hp hactive))
  have heq := normalCones_eq_of_localSetEq R p hS
    (closure_frozenRidgeSection_isPositiveCone R p (carrierFrameFields a)
      (carrierHalfspaceFormula d)) hlocal
  rw [heq]
  exact carrier_frame_closed_normal_inventory a R hp hcodim hactive

/-- The carrier branch of a literal physical tile boundary has only right-angle,
straight, or reflex-right-angle sectors. Empty/full cones are ruled out. -/
theorem boundary_normal_model_inventory_of_carrier_germ {d : ℕ}
    (a : Point d ≃ᵃⁱ[ℝ] Point d) (R : AffineSubspace ℝ (Point d))
    {p : Point d} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = d)
    (hactive : ∀ j : CarrierHalfspaceIndex d, carrierFrameFields a j p = 0 →
      R ≤ affineFormPlane (carrierFrameFields a j) 0)
    {T : Set (Point d)} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hcarrier : LocalSetEq p T (a ⁻¹' carrier d))
    (hboundary : p ∈ frontier T) : IsRightAngleBoundaryCone S :=
  (normal_model_inventory_of_carrier_germ a R hp hcodim hactive hS hmodel hcarrier).boundary_of_localSetEq hmodel hboundary

/-- The reflex model is the complement of an open quadrant, so both boundary
rays are retained, exactly as required by the closed material convention. -/
theorem normalHalfspace_union_eq_compl_open_quadrant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n m : E) :
    normalHalfspace n ∪ normalHalfspace m =
      {v | inner (𝕜 := ℝ) n v < 0 ∧ inner (𝕜 := ℝ) m v < 0}ᶜ := by
  ext v
  simp only [normalHalfspace, mem_union, mem_setOf_eq, mem_compl_iff, not_and_or, not_lt]

/-- The inverse physical frame's carrier preimage is precisely the physical
isometric carrier copy. -/
theorem inverse_frame_carrier_preimage {d : ℕ} (g : Point d ≃ᵢ Point d) :
    g.symm.toRealAffineIsometryEquiv ⁻¹' carrier d = g '' carrier d := by
  ext x
  change g.symm x ∈ carrier d ↔ x ∈ g '' carrier d
  constructor
  · intro hx
    exact ⟨g.symm x, hx, g.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [g.symm_apply_apply] using hy

/-- T5's actual global affine-plane family supplies the carrier-branch bridge
without any coordinate registration of the physical isometry. -/
theorem T5_boundary_normal_model_inventory_of_carrier_germ
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {T : Set (Point 5)} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hcarrier : LocalSetEq p T (g '' carrier 5))
    (hboundary : p ∈ frontier T) : IsRightAngleBoundaryCone S := by
  apply boundary_normal_model_inventory_of_carrier_germ
    g.symm.toRealAffineIsometryEquiv R hp hcodim
    (fun j hj => hactive (.inl j) hj) hS hmodel _ hboundary
  simpa only [inverse_frame_carrier_preimage] using hcarrier

/-- The same bridge for T7 uses its actual world-plane inventory. -/
theorem T7_boundary_normal_model_inventory_of_carrier_germ
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {T : Set (Point 7)} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hcarrier : LocalSetEq p T (g '' carrier 7))
    (hboundary : p ∈ frontier T) : IsRightAngleBoundaryCone S := by
  apply boundary_normal_model_inventory_of_carrier_germ
    g.symm.toRealAffineIsometryEquiv R hp hcodim
    (fun j hj => hactive (.inl j) hj) hS hmodel _ hboundary
  simpa only [inverse_frame_carrier_preimage] using hcarrier

#print axioms mem_frozen_carrier_iff
#print axioms carrierLinearCone_inventory
#print axioms carrierCriticalAxes_card_le_two
#print axioms carrier_closed_frozenRidgeSection_inventory
#print axioms carrier_frame_frozenRidgeSection_inventory
#print axioms carrier_frame_boundary_normal_inventory
#print axioms boundary_normal_model_inventory_of_carrier_germ
#print axioms T5_boundary_normal_model_inventory_of_carrier_germ
#print axioms T7_boundary_normal_model_inventory_of_carrier_germ

end SparseMonotiles
