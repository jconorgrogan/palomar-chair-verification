module

public import SparseMonotiles.Interior
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Full open cores of the carrier cells

A key whose base has an integer normal coordinate and whose apex stays within
`mu` of that integer is confined to the corresponding closed coordinate band.
Consequently it misses the full `mu`-core of every integer grid cell. For each
binary carrier cell other than the all-one cell, the entire open core lies in
`interior (body ks)`. No registration or tiling hypothesis is used.
-/
namespace SparseMonotiles

/-- Exact rational certificate that one normal direction stays near an integer. -/
def HasNormalIntegerBand {d : ℕ} (mu : ℚ) (k : KeyData d) : Prop :=
  ∃ i : Fin d, ∃ n : ℤ,
    k.radius i = 0 ∧ k.centre i = (n : ℚ) ∧ |k.apex i - (n : ℚ)| ≤ mu

/-- The closed band of width `2 * mu` about an integer coordinate hyperplane. -/
def normalIntegerBand {d : ℕ} (mu : ℚ) (i : Fin d) (n : ℤ) : Set (Point d) :=
  {x | |x i - (n : ℝ)| ≤ (mu : ℝ)}

/-- The whole open box `c + (mu, 1 - mu)^d`, for an integer grid cell. -/
def integerCellCore {d : ℕ} (mu : ℚ) (c : Fin d → ℤ) : Set (Point d) :=
  {x | ∀ i, (c i : ℝ) + (mu : ℝ) < x i ∧
    x i < (c i : ℝ) + 1 - (mu : ℝ)}

/-- The full open core of a binary cell, in the coordinates used by `carrier`. -/
def carrierCellCore {d : ℕ} (mu : ℚ) (c : Fin d → Bool) : Set (Point d) :=
  integerCellCore mu (fun i => if c i then 1 else 0)

private theorem cellCore_keyBase_coordinate {d : ℕ} (k : KeyData d)
    (i : Fin d) (hr : k.radius i = 0) {x : Point d}
    (hx : x ∈ keyBase k) : x i = (k.centre i : ℝ) := by
  have hi := hx i
  rw [hr] at hi
  norm_num only [Rat.cast_zero] at hi
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))

/-- Convexity confines the entire solid, not only the base and apex, to the band. -/
theorem keySolid_subset_normalIntegerBand {d : ℕ} (mu : ℚ) (k : KeyData d)
    (i : Fin d) (n : ℤ) (hr : k.radius i = 0)
    (hc : k.centre i = (n : ℚ)) (ha : |k.apex i - (n : ℚ)| ≤ mu) :
    keySolid k ⊆ normalIntegerBand mu i n := by
  have hcentre : (k.centre i : ℝ) = (n : ℝ) := by
    rw [hc, Rat.cast_intCast]
  have hapex : |(k.apex i : ℝ) - (n : ℝ)| ≤ (mu : ℝ) := by
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_intCast] using
      (Rat.cast_le (K := ℝ)).2 ha
  have hmu : (0 : ℝ) ≤ (mu : ℝ) := (abs_nonneg _).trans hapex
  have hf : IsLinearMap ℝ (fun x : Point d => x i) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hlower : insert (rationalPoint k.apex) (keyBase k) ⊆
      {y : Point d | (n : ℝ) - (mu : ℝ) ≤ y i} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · change (n : ℝ) - (mu : ℝ) ≤ (k.apex i : ℝ)
      have h := (abs_le.mp hapex).1
      linarith
    · change (n : ℝ) - (mu : ℝ) ≤ y i
      rw [cellCore_keyBase_coordinate k i hr hy, hcentre]
      linarith
  have hupper : insert (rationalPoint k.apex) (keyBase k) ⊆
      {y : Point d | y i ≤ (n : ℝ) + (mu : ℝ)} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · change (k.apex i : ℝ) ≤ (n : ℝ) + (mu : ℝ)
      have h := (abs_le.mp hapex).2
      linarith
    · change y i ≤ (n : ℝ) + (mu : ℝ)
      rw [cellCore_keyBase_coordinate k i hr hy, hcentre]
      linarith
  intro x hx
  have hlo := convexHull_min hlower
    (convex_halfSpace_ge hf ((n : ℝ) - (mu : ℝ))) hx
  have hhi := convexHull_min hupper
    (convex_halfSpace_le hf ((n : ℝ) + (mu : ℝ))) hx
  change (n : ℝ) - (mu : ℝ) ≤ x i at hlo
  change x i ≤ (n : ℝ) + (mu : ℝ) at hhi
  change |x i - (n : ℝ)| ≤ (mu : ℝ)
  apply abs_le.mpr
  constructor <;> linarith

/-- The certificate yields a normal band containing the whole key. -/
theorem keySolid_confined_to_integer_band {d : ℕ} (mu : ℚ) (k : KeyData d)
    (h : HasNormalIntegerBand mu k) :
    ∃ i : Fin d, ∃ n : ℤ, keySolid k ⊆ normalIntegerBand mu i n := by
  obtain ⟨i, n, hr, hc, ha⟩ := h
  exact ⟨i, n, keySolid_subset_normalIntegerBand mu k i n hr hc ha⟩

/-- Integer separation excludes every integer normal band from every open core. -/
theorem integerCellCore_disjoint_normalIntegerBand {d : ℕ} (mu : ℚ)
    (c : Fin d → ℤ) (i : Fin d) (n : ℤ) :
    Disjoint (integerCellCore mu c) (normalIntegerBand mu i n) := by
  apply Set.disjoint_left.mpr
  intro x hx hb
  have hcore := hx i
  change |x i - (n : ℝ)| ≤ (mu : ℝ) at hb
  have hband := abs_le.mp hb
  rcases le_or_gt n (c i) with hn | hn
  · have hn' : (n : ℝ) ≤ (c i : ℝ) := Int.cast_le.mpr hn
    linarith
  · have hn' : c i + 1 ≤ n := Int.add_one_le_iff.mpr hn
    have hn'' : (c i : ℝ) + 1 ≤ (n : ℝ) := by
      simpa only [Int.cast_add, Int.cast_one] using
        (Int.cast_le (R := ℝ)).mpr hn'
    linarith

/-- Every certified key misses every integer-cell core. -/
theorem keySolid_disjoint_integerCellCore {d : ℕ} (mu : ℚ) (k : KeyData d)
    (h : HasNormalIntegerBand mu k) (c : Fin d → ℤ) :
    Disjoint (keySolid k) (integerCellCore mu c) := by
  obtain ⟨i, n, hsub⟩ := keySolid_confined_to_integer_band mu k h
  apply Set.disjoint_left.mpr
  intro x hx hc
  exact Set.disjoint_left.mp
    (integerCellCore_disjoint_normalIntegerBand mu c i n) hc (hsub hx)

/-- Cores are open in the Euclidean topology, not merely relative to the carrier. -/
theorem isOpen_integerCellCore {d : ℕ} (mu : ℚ) (c : Fin d → ℤ) :
    IsOpen (integerCellCore mu c) := by
  unfold integerCellCore
  rw [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  have hcoord : Continuous (fun x : Point d => x i) :=
    PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i
  exact (isOpen_lt continuous_const hcoord).inter
    (isOpen_lt hcoord continuous_const)

theorem isOpen_carrierCellCore {d : ℕ} (mu : ℚ) (c : Fin d → Bool) :
    IsOpen (carrierCellCore mu c) :=
  isOpen_integerCellCore mu (fun i => if c i then 1 else 0)

/-- The strict upper bound on `mu` guarantees that each full core is nonempty. -/
theorem integerCellCore_nonempty {d : ℕ} (mu : ℚ) (hmu : mu < 1/2)
    (c : Fin d → ℤ) : (integerCellCore mu c).Nonempty := by
  have hmu' : (mu : ℝ) < 1/2 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hmu
    norm_num at h
    exact h
  refine ⟨(WithLp.equiv 2 (Fin d → ℝ)).symm
    (fun i => (c i : ℝ) + 1/2), ?_⟩
  intro i
  change (c i : ℝ) + (mu : ℝ) < (c i : ℝ) + 1/2 ∧
    (c i : ℝ) + 1/2 < (c i : ℝ) + 1 - (mu : ℝ)
  constructor <;> linarith

theorem carrierCellCore_nonempty {d : ℕ} (mu : ℚ) (hmu : mu < 1/2)
    (c : Fin d → Bool) : (carrierCellCore mu c).Nonempty :=
  integerCellCore_nonempty mu hmu (fun i => if c i then 1 else 0)

/-- Any binary core except the all-one core is in the carrier. -/
theorem carrierCellCore_subset_carrier {d : ℕ} (mu : ℚ) (hmu : 0 ≤ mu)
    (c : Fin d → Bool) (hc : ∃ i, c i = false) :
    carrierCellCore mu c ⊆ carrier d := by
  have hmu' : (0 : ℝ) ≤ (mu : ℝ) := by
    simpa only [Rat.cast_zero] using (Rat.cast_le (K := ℝ)).2 hmu
  intro x hx
  refine ⟨c, hc, ?_⟩
  intro i
  have hi := hx i
  cases hci : c i <;>
    simp [hci] at hi ⊢ <;>
    constructor <;> linarith

/-- Every point of the full open core survives all dents and belongs to the body. -/
theorem carrierCellCore_subset_body {d : ℕ} (mu : ℚ) (hmu : 0 ≤ mu)
    (ks : List (KeyData d)) (hks : ∀ k ∈ ks, HasNormalIntegerBand mu k)
    (c : Fin d → Bool) (hc : ∃ i, c i = false) :
    carrierCellCore mu c ⊆ body ks := by
  intro x hx
  apply subset_closure
  constructor
  · exact Or.inl (carrierCellCore_subset_carrier mu hmu c hc hx)
  · rintro ⟨k, hk, _, hxk⟩
    exact Set.disjoint_left.mp
      (keySolid_disjoint_integerCellCore mu k (hks k hk)
        (fun i => if c i then 1 else 0)) hxk hx

/-- The whole `c + (mu, 1 - mu)^d` is in the ambient interior of the body. -/
theorem carrierCellCore_subset_interior_body {d : ℕ} (mu : ℚ) (hmu : 0 ≤ mu)
    (ks : List (KeyData d)) (hks : ∀ k ∈ ks, HasNormalIntegerBand mu k)
    (c : Fin d → Bool) (hc : ∃ i, c i = false) :
    carrierCellCore mu c ⊆ interior (body ks) :=
  (isOpen_carrierCellCore mu c).subset_interior_iff.mpr
    (carrierCellCore_subset_body mu hmu ks hks c hc)

/-- The same full-core conclusion with the literal exclusion of the all-one cell. -/
theorem carrierCellCore_subset_interior_body_of_ne_allOne {d : ℕ}
    (mu : ℚ) (hmu : 0 ≤ mu) (ks : List (KeyData d))
    (hks : ∀ k ∈ ks, HasNormalIntegerBand mu k)
    (c : Fin d → Bool) (hc : c ≠ fun _ => true) :
    carrierCellCore mu c ⊆ interior (body ks) := by
  classical
  have hc' : ∃ i, c i = false := by
    by_contra h
    apply hc
    funext i
    cases hci : c i with
    | false => exact False.elim (h ⟨i, hci⟩)
    | true => rfl
  exact carrierCellCore_subset_interior_body mu hmu ks hks c hc'

/-- A convenient comparison with the already defined central box. -/
theorem centralBox_subset_zero_carrierCellCore {d : ℕ} (mu : ℚ)
    (hmu : mu ≤ 1/4) :
    centralBox d ⊆ carrierCellCore mu (fun _ => false) := by
  have hmu' : (mu : ℝ) ≤ 1/4 := by
    have h := (Rat.cast_le (K := ℝ)).2 hmu
    norm_num at h
    exact h
  intro x hx i
  have hi := hx i
  simp only [Bool.false_eq_true, if_false, Int.cast_zero, zero_add]
  constructor <;> linarith

/-- At margin `1/100`, the Euclidean radius-`1/4` ball lies in the body's interior. -/
theorem centralBall_subset_interior_of_normalIntegerBands {d : ℕ} (hd : 0 < d)
    (ks : List (KeyData d))
    (hks : ∀ k ∈ ks, HasNormalIntegerBand (1/100) k) :
    Metric.ball (centralPoint d) (1/4 : ℝ) ⊆ interior (body ks) := by
  exact (centralBall_subset_centralBox d).trans
    ((centralBox_subset_zero_carrierCellCore (1/100) (by norm_num)).trans
      (carrierCellCore_subset_interior_body (1/100) (by norm_num) ks hks
        (fun _ => false) ⟨⟨0, hd⟩, rfl⟩))

theorem centralBall_subset_body_of_normalIntegerBands {d : ℕ} (hd : 0 < d)
    (ks : List (KeyData d))
    (hks : ∀ k ∈ ks, HasNormalIntegerBand (1/100) k) :
    Metric.ball (centralPoint d) (1/4 : ℝ) ⊆ body ks :=
  (centralBall_subset_interior_of_normalIntegerBands hd ks hks).trans interior_subset

theorem body_interior_nonempty_of_normalIntegerBands {d : ℕ} (hd : 0 < d)
    (ks : List (KeyData d))
    (hks : ∀ k ∈ ks, HasNormalIntegerBand (1/100) k) :
    (interior (body ks)).Nonempty := by
  exact ⟨centralPoint d, centralBall_subset_interior_of_normalIntegerBands hd ks hks
    (Metric.mem_ball_self (by norm_num))⟩

end SparseMonotiles
