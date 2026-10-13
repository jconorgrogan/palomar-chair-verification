module

public import PhysicalRegistration.NativeAssembly

@[expose] public section

/-!
# Literal retained balls in the native keyed chair

Every occupied unit cell retains its open Euclidean ball of radius `1/4`.
The proof uses the ambient Euclidean norm, the actual integral normal
planes of native facets, and the explicit tube width `rho < 1/4`.
No interior-ball certificate is assumed.
-/

namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- The actual center of an occupied unit cell. -/
def cellCenter {m : ℕ} (c : Cell m) : Space m :=
  WithLp.toLp 2 (fun i => bit (c.val i) + 1 / 2)

/-- A Euclidean ball controls each ambient coordinate. -/
theorem abs_coordinate_sub_lt_of_mem_ball {m : ℕ} (x y : Space m) (r : ℝ)
    (hx : x ∈ Metric.ball y r) (i : Fin (m + 1)) :
    |x i - y i| < r := by
  have hi := PiLp.norm_apply_le (x - y) i
  have hx' : ‖x - y‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hi' : |x i - y i| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hi
  exact hi'.trans_lt hx'

/-- The radius-quarter ball lies in the literal occupied closed unit cell. -/
theorem cellCenter_ball_subset_unitCell {m : ℕ} (c : Cell m) :
    Metric.ball (cellCenter c) (1 / 4) ⊆ unitCell c := by
  intro x hx i
  have hi := abs_coordinate_sub_lt_of_mem_ball x (cellCenter c) (1 / 4) hx i
  change |x i - (bit (c.val i) + 1 / 2)| < (1 / 4 : ℝ) at hi
  have hi' := abs_lt.mp hi
  constructor <;> linarith [hi'.1, hi'.2]

/-- Every retained-ball point stays outside every actual native closed tube,
including tubes of other facets or tangent frames. -/
theorem cellCenter_ball_disjoint_closedTube {m J : ℕ} (c : Cell m) (u : Site m) :
    Disjoint (Metric.ball (cellCenter c) (1 / 4)) (closedTube J u) := by
  apply Set.disjoint_left.mpr
  intro x hx htube
  let i := normalIndex u.1
  let b : ℤ := if c.val i then 1 else 0
  have hb : (b : ℝ) = bit (c.val i) := by
    dsimp [b, bit]
    split <;> norm_num
  have hq : |x i - (bit (c.val i) + 1 / 2)| < 1 / 4 := by
    exact
      abs_coordinate_sub_lt_of_mem_ball x (cellCenter c) (1 / 4) hx i
  have hfar := native_tangent_distance_from_integer b (facetPlane u.1)
    (x i - (bit (c.val i) + 1 / 2)) 0 0 hq (by norm_num)
  have heq : (b : ℝ) + 1 / 2 + (x i - (bit (c.val i) + 1 / 2)) + 0 -
      (facetPlane u.1 : ℝ) = x i - siteCenter u i := by
    rw [hb]
    dsimp only [i]
    rw [siteCenter_normal]
    ring
  rw [heq] at hfar
  have hnear : |x i - siteCenter u i| ≤ rho m :=
    (closedTube_mem_coordinateTube u x htube).1
  linarith [rho_lt_quarter m]

/-- The quarter-ball is genuinely retained by the actual tube replacement. -/
theorem cellCenter_ball_subset_body {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (c : Cell m) :
    Metric.ball (cellCenter c) (1 / 4) ⊆ body a := by
  intro x hx
  rw [body_eq_replaceTubes]
  apply replaceTubes_mem_of_untouched
  · exact Set.mem_iUnion.mpr ⟨c, cellCenter_ball_subset_unitCell c hx⟩
  · intro u hu
    exact Set.disjoint_left.mp (cellCenter_ball_disjoint_closedTube c u)
      hx (interior_subset hu)

/-- Every occupied cell retains a literal open Euclidean radius-quarter ball
in the interior of the actual coefficient-dependent native body. -/
theorem cellCenter_ball_subset_interior_body {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (c : Cell m) :
    Metric.ball (cellCenter c) (1 / 4) ⊆ interior (body a) :=
  interior_maximal (cellCenter_ball_subset_body a c) Metric.isOpen_ball

@[simp] theorem cellCenter_zeroCell (m : ℕ) :
    cellCenter (zeroCell m) = halfPoint m := by
  ext i
  norm_num [cellCenter, zeroCell, bit, halfPoint]

/-- The common all-half point supplies a uniform retained ball for packing. -/
theorem halfPoint_ball_subset_interior_body {m J : ℕ} [NeZero m]
    (a : Coefficients m J) :
    Metric.ball (halfPoint m) (1 / 4) ⊆ interior (body a) := by
  simpa only [cellCenter_zeroCell] using
    cellCenter_ball_subset_interior_body a (zeroCell m)

theorem halfPoint_mem_interior_body {m J : ℕ} [NeZero m]
    (a : Coefficients m J) : halfPoint m ∈ interior (body a) :=
  halfPoint_ball_subset_interior_body a (Metric.mem_ball_self (by norm_num))

theorem interior_body_nonempty {m J : ℕ} [NeZero m]
    (a : Coefficients m J) : (interior (body a)).Nonempty :=
  ⟨halfPoint m, halfPoint_mem_interior_body a⟩

#print axioms cellCenter_ball_subset_interior_body
#print axioms halfPoint_ball_subset_interior_body
#print axioms interior_body_nonempty
end
end PhysicalRegistration.NativeChair
