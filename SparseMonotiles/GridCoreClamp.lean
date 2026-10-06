module

public import SparseMonotiles.CellCores
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Every point is near an open integer-cell core

Clamp each coordinate into the closed interval with endpoints two margins from
its integer cell's boundary. For a margin strictly between zero and `1/4`, this
interval lies in the open cell core. The coordinate displacement is at most
twice the margin; the Euclidean distance is at most the sum of the coordinate
distances, giving the deliberately loose bound `2 * d * mu`.

The ball-obstruction theorems retain an explicit hypothesis that the interiors
of the specified family cover **every** integer-cell core. They do not assert
that a key-neighbor component has this property or is closed under adjacency.
-/
namespace SparseMonotiles

open scoped BigOperators

/-- The integer cell chosen by taking floors coordinatewise. -/
noncomputable def integerCellFloor {d : ℕ} (x : Point d) : Fin d → ℤ :=
  fun i => ⌊x i⌋

/-- Clamp into the interval two margins inside the floor-selected integer cell. -/
noncomputable def integerCellClamp {d : ℕ} (mu : ℚ) (x : Point d) : Point d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm fun i =>
    max ((integerCellFloor x i : ℝ) + 2 * (mu : ℝ))
      (min (x i) ((integerCellFloor x i : ℝ) + 1 - 2 * (mu : ℝ)))

private theorem clamp_coordinate_bounds (a e t : ℝ) (he : 0 < e)
    (he' : e < 1/4) (hat : a ≤ t) (hta : t < a + 1) :
    a + e < max (a + 2 * e) (min t (a + 1 - 2 * e)) ∧
    max (a + 2 * e) (min t (a + 1 - 2 * e)) < a + 1 - e ∧
    |t - max (a + 2 * e) (min t (a + 1 - 2 * e))| ≤ 2 * e := by
  have hlo : a + 2 * e ≤ max (a + 2 * e) (min t (a + 1 - 2 * e)) :=
    le_max_left _ _
  have hhi : max (a + 2 * e) (min t (a + 1 - 2 * e)) ≤ a + 1 - 2 * e :=
    max_le (by linarith) (min_le_right _ _)
  have hmovehi : max (a + 2 * e) (min t (a + 1 - 2 * e)) ≤ t + 2 * e :=
    max_le (by linarith) ((min_le_left _ _).trans (by linarith))
  have hmovelo : t - 2 * e ≤ max (a + 2 * e) (min t (a + 1 - 2 * e)) :=
    (le_min (by linarith) (by linarith)).trans (le_max_right _ _)
  refine ⟨by linarith, by linarith, abs_le.mpr ?_⟩
  constructor <;> linarith

/-- The clamped point lies strictly inside the open core of its floor cell. -/
theorem integerCellClamp_mem_integerCellCore {d : ℕ} (mu : ℚ)
    (hmu : 0 < mu) (hmu' : mu < 1/4) (x : Point d) :
    integerCellClamp mu x ∈ integerCellCore mu (integerCellFloor x) := by
  have he : (0 : ℝ) < (mu : ℝ) := by exact_mod_cast hmu
  have he' : (mu : ℝ) < 1/4 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hmu'
    norm_num at h
    exact h
  intro i
  have hi := clamp_coordinate_bounds (⌊x i⌋ : ℝ) (mu : ℝ) (x i) he he'
    (Int.floor_le _) (Int.lt_floor_add_one _)
  exact ⟨hi.1, hi.2.1⟩

/-- Every clamped coordinate moves by at most twice the margin. -/
theorem integerCellClamp_coordinate_dist_le {d : ℕ} (mu : ℚ)
    (hmu : 0 < mu) (hmu' : mu < 1/4) (x : Point d) (i : Fin d) :
    dist (x i) (integerCellClamp mu x i) ≤ 2 * (mu : ℝ) := by
  have he : (0 : ℝ) < (mu : ℝ) := by exact_mod_cast hmu
  have he' : (mu : ℝ) < 1/4 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hmu'
    norm_num at h
    exact h
  have hi := clamp_coordinate_bounds (⌊x i⌋ : ℝ) (mu : ℝ) (x i) he he'
    (Int.floor_le _) (Int.lt_floor_add_one _)
  exact hi.2.2

/-- The Euclidean metric is bounded by the sum of the coordinate metrics. -/
theorem point_dist_le_sum_coordinate_dist {d : ℕ} (x y : Point d) :
    dist x y ≤ ∑ i : Fin d, dist (x i) (y i) := by
  rw [EuclideanSpace.dist_eq]
  apply Real.sqrt_le_iff.mpr
  exact ⟨Finset.sum_nonneg (fun _ _ => dist_nonneg),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => dist_nonneg)⟩

/-- A global Euclidean covering estimate with no square-root constant needed. -/
theorem dist_integerCellClamp_le {d : ℕ} (mu : ℚ)
    (hmu : 0 < mu) (hmu' : mu < 1/4) (x : Point d) :
    dist x (integerCellClamp mu x) ≤ 2 * (d : ℝ) * (mu : ℝ) := by
  calc
    dist x (integerCellClamp mu x) ≤
        ∑ i : Fin d, dist (x i) (integerCellClamp mu x i) :=
      point_dist_le_sum_coordinate_dist x (integerCellClamp mu x)
    _ ≤ ∑ _i : Fin d, 2 * (mu : ℝ) :=
      Finset.sum_le_sum (fun i _ => integerCellClamp_coordinate_dist_le mu hmu hmu' x i)
    _ = 2 * (d : ℝ) * (mu : ℝ) := by simp; ring

/-- Every point is within `2 * d * mu` of some open integer-cell core. -/
theorem exists_mem_integerCellCore_dist_le {d : ℕ} (mu : ℚ)
    (hmu : 0 < mu) (hmu' : mu < 1/4) (x : Point d) :
    ∃ (c : Fin d → ℤ) (y : Point d),
      y ∈ integerCellCore mu c ∧ dist x y ≤ 2 * (d : ℝ) * (mu : ℝ) :=
  ⟨integerCellFloor x, integerCellClamp mu x,
    integerCellClamp_mem_integerCellCore mu hmu hmu' x,
    dist_integerCellClamp_le mu hmu hmu' x⟩

/-- Any set containing all the grid cores meets each ball above the covering radius. -/
theorem exists_mem_ball_of_integerCellCores_subset {d : ℕ} (mu : ℚ)
    (hmu : 0 < mu) (hmu' : mu < 1/4) (S : Set (Point d))
    (hcover : ∀ c : Fin d → ℤ, integerCellCore mu c ⊆ S)
    (x : Point d) (r : ℝ) (hr : 2 * (d : ℝ) * (mu : ℝ) < r) :
    ∃ y, y ∈ Metric.ball x r ∧ y ∈ S := by
  obtain ⟨c, y, hy, hd⟩ := exists_mem_integerCellCore_dist_le mu hmu hmu' x
  refine ⟨y, ?_, hcover c hy⟩
  rw [Metric.mem_ball, dist_comm]
  exact hd.trans_lt hr

/-- Covering every open core rules out a disjoint larger open ball. -/
theorem not_disjoint_ball_of_integerCellCores_subset {d : ℕ} (mu : ℚ)
    (hmu : 0 < mu) (hmu' : mu < 1/4) (S : Set (Point d))
    (hcover : ∀ c : Fin d → ℤ, integerCellCore mu c ⊆ S)
    (x : Point d) (r : ℝ) (hr : 2 * (d : ℝ) * (mu : ℝ) < r) :
    ¬ Disjoint (Metric.ball x r) S := by
  obtain ⟨y, hy, hS⟩ := exists_mem_ball_of_integerCellCores_subset mu hmu hmu' S hcover x r hr
  intro hdisjoint
  exact Set.disjoint_left.mp hdisjoint hy hS

/-- The family version allows different interior owners at different core points. -/
theorem ball_intersects_familyInterior_of_integerCellCores_covered {d : ℕ}
    (mu : ℚ) (hmu : 0 < mu) (hmu' : mu < 1/4)
    (family : Set (Set (Point d)))
    (hcover : ∀ c : Fin d → ℤ, integerCellCore mu c ⊆ ⋃ A ∈ family, interior A)
    (x : Point d) (r : ℝ) (hr : 2 * (d : ℝ) * (mu : ℝ) < r) :
    ∃ A ∈ family, ∃ y ∈ Metric.ball x r, y ∈ interior A := by
  obtain ⟨y, hy, hfamily⟩ := exists_mem_ball_of_integerCellCores_subset mu hmu hmu'
    (⋃ A ∈ family, interior A) hcover x r hr
  obtain ⟨A, hA, hyA⟩ := Set.mem_iUnion₂.mp hfamily
  exact ⟨A, hA, y, hy, hyA⟩

/-- If a ball misses every family interior, its radius cannot exceed the core-cover bound. -/
theorem radius_le_of_ball_disjoint_familyInterior {d : ℕ}
    (mu : ℚ) (hmu : 0 < mu) (hmu' : mu < 1/4)
    (family : Set (Set (Point d)))
    (hcover : ∀ c : Fin d → ℤ, integerCellCore mu c ⊆ ⋃ A ∈ family, interior A)
    (x : Point d) (r : ℝ)
    (hdisjoint : ∀ A ∈ family, Disjoint (Metric.ball x r) (interior A)) :
    r ≤ 2 * (d : ℝ) * (mu : ℝ) := by
  by_contra h
  obtain ⟨A, hA, y, hy, hyA⟩ :=
    ball_intersects_familyInterior_of_integerCellCores_covered mu hmu hmu'
      family hcover x r (lt_of_not_ge h)
  exact Set.disjoint_left.mp (hdisjoint A hA) hy hyA

/-- A convenient form when each entire core has a single interior owner. -/
theorem radius_le_of_ball_disjoint_core_owners {d : ℕ}
    (mu : ℚ) (hmu : 0 < mu) (hmu' : mu < 1/4)
    (family : Set (Set (Point d)))
    (hcover : ∀ c : Fin d → ℤ, ∃ A ∈ family, integerCellCore mu c ⊆ interior A)
    (x : Point d) (r : ℝ)
    (hdisjoint : ∀ A ∈ family, Disjoint (Metric.ball x r) (interior A)) :
    r ≤ 2 * (d : ℝ) * (mu : ℝ) := by
  apply radius_le_of_ball_disjoint_familyInterior mu hmu hmu' family ?_ x r hdisjoint
  intro c y hy
  obtain ⟨A, hA, hcore⟩ := hcover c
  exact Set.mem_iUnion₂.mpr ⟨A, hA, hcore hy⟩

/-- The loose bound is already smaller than the concrete inball in dimensions five and seven. -/
theorem gridCoreRadius_one_hundredth_lt_quarter {d : ℕ} (hd : d = 5 ∨ d = 7) :
    2 * (d : ℝ) * ((1/100 : ℚ) : ℝ) < 1/4 := by
  rcases hd with rfl | rfl <;> norm_num

/-- The explicit global-cover premise excludes a disjoint radius-`1/4` ball for T5/T7. -/
theorem no_disjoint_quarter_ball_of_integerCellCores_covered {d : ℕ}
    (hd : d = 5 ∨ d = 7) (family : Set (Set (Point d)))
    (hcover : ∀ c : Fin d → ℤ, integerCellCore (1/100) c ⊆ ⋃ A ∈ family, interior A)
    (x : Point d) :
    ¬ (∀ A ∈ family, Disjoint (Metric.ball x (1/4 : ℝ)) (interior A)) := by
  intro hdisjoint
  have hle := radius_le_of_ball_disjoint_familyInterior (1/100)
    (by norm_num) (by norm_num) family hcover x (1/4) hdisjoint
  exact not_le_of_gt (gridCoreRadius_one_hundredth_lt_quarter hd) hle

#print axioms exists_mem_integerCellCore_dist_le
#print axioms radius_le_of_ball_disjoint_familyInterior
#print axioms radius_le_of_ball_disjoint_core_owners
#print axioms no_disjoint_quarter_ball_of_integerCellCores_covered

end SparseMonotiles
