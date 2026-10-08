module

public import SparseMonotiles.CanonicalReferenceKeys
public import SparseMonotiles.BoundaryInventory
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Exact Euclidean clearance from the integer grid skeleton

The codimension-two integer skeleton consists of points with at least two
distinct integer coordinates. The canonical key has all but its normal
coordinate strictly between `1/4` and `3/4`. Convexity propagates these strict
bounds from its exact base and apex to the whole solid. Consequently even the
closed radius-`1/4` ball about any skeleton point misses the solid.

Integer signed poses preserve the skeleton and the Euclidean metric. The final
body/carrier germ theorem explicitly requires a canonical binding for every
key; it does not assume that binding for an unspecified literal list.
-/

namespace SparseMonotiles

open Set Filter
open scoped Topology

/-- The integer grid's codimension-two skeleton, with distinct coordinate axes. -/
def integerSkeleton (d : ℕ) : Set (Point d) :=
  {x | ∃ i j : Fin d, i ≠ j ∧
    (∃ m : ℤ, x i = (m : ℝ)) ∧ (∃ n : ℤ, x j = (n : ℝ))}

/-- Strict coordinate bounds on the base and apex propagate through convexity. -/
theorem keySolid_coordinate_mem_Ioo {d : ℕ} (k : KeyData d) (i : Fin d)
    (a b : ℝ)
    (hlo : a < (k.centre i : ℝ) - (k.radius i : ℝ))
    (hhi : (k.centre i : ℝ) + (k.radius i : ℝ) < b)
    (ha : a < (k.apex i : ℝ) ∧ (k.apex i : ℝ) < b)
    {x : Point d} (hx : x ∈ keySolid k) : a < x i ∧ x i < b := by
  have hf : IsLinearMap ℝ (fun y : Point d => y i) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hsub : insert (rationalPoint k.apex) (keyBase k) ⊆
      {y : Point d | a < y i ∧ y i < b} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ha
    · have hbase := abs_le.mp (hy i)
      constructor <;> linarith [hbase.1, hbase.2]
  exact convexHull_min hsub
    ((convex_halfSpace_gt hf a).inter (convex_halfSpace_lt hf b)) hx

/-- A number in the central open half of a unit interval is more than `1/4`
from every integer, including both adjacent endpoints. -/
theorem quarter_lt_abs_sub_int {x : ℝ} (hlo : 1/4 < x) (hhi : x < 3/4)
    (n : ℤ) : (1/4 : ℝ) < |x - (n : ℝ)| := by
  by_cases hn : n ≤ 0
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    have habs := le_abs_self (x - (n : ℝ))
    linarith
  · have hn' : (1 : ℤ) ≤ n := by omega
    have hn'' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
    have habs := neg_le_abs (x - (n : ℝ))
    linarith

/-- One of the two integer coordinates is tangential to the given normal axis.
Its coordinate distance is bounded above by the genuine Euclidean distance. -/
theorem quarter_lt_dist_integerSkeleton_of_coordinates {d : ℕ}
    (normal : Fin d) {x p : Point d}
    (hx : ∀ i, i ≠ normal → (1/4 : ℝ) < x i ∧ x i < 3/4)
    (hp : p ∈ integerSkeleton d) : (1/4 : ℝ) < dist x p := by
  obtain ⟨i, j, hij, ⟨m, hm⟩, ⟨n, hn⟩⟩ := hp
  have hcoord (a : Fin d) (ha : a ≠ normal) (z : ℤ) (hz : p a = (z : ℝ)) :
      (1/4 : ℝ) < dist x p := by
    have hgap := quarter_lt_abs_sub_int (hx a ha).1 (hx a ha).2 z
    have hmetric := PiLp.dist_apply_le x p a
    rw [Real.dist_eq, hz] at hmetric
    exact hgap.trans_le hmetric
  by_cases hi : i = normal
  · exact hcoord j (by intro hj; exact hij (hi.trans hj.symm)) n hn
  · exact hcoord i hi m hm

namespace Contact

/-- Integral translations and sign changes preserve integrality coordinatewise. -/
theorem Pose.integer_coordinate_iff {d : ℕ} (p : Pose d) (x : Point d) (i : Fin d) :
    (∃ n : ℤ, p.euclidean x i = (n : ℝ)) ↔
      ∃ n : ℤ, x (p.perm i) = (n : ℝ) := by
  rw [p.euclidean_apply]
  cases h : p.negative i <;>
    simp only [Pose.sign, h, Bool.false_eq_true, if_false, if_true,
      Int.cast_neg, Int.cast_one, one_mul, neg_one_mul]
  · constructor
    · rintro ⟨n, hn⟩
      refine ⟨n - p.shift i, ?_⟩
      push_cast
      linarith
    · rintro ⟨n, hn⟩
      refine ⟨n + p.shift i, ?_⟩
      push_cast
      linarith
  · constructor
    · rintro ⟨n, hn⟩
      refine ⟨p.shift i - n, ?_⟩
      push_cast
      linarith
    · rintro ⟨n, hn⟩
      refine ⟨-n + p.shift i, ?_⟩
      push_cast
      linarith

/-- The same two distinct axes are transported by the underlying permutation. -/
theorem Pose.mem_integerSkeleton_iff {d : ℕ} (p : Pose d) (x : Point d) :
    p.euclidean x ∈ integerSkeleton d ↔ x ∈ integerSkeleton d := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨p.perm i, p.perm j, fun h => hij (p.perm.injective h),
      (p.integer_coordinate_iff x i).mp hi, (p.integer_coordinate_iff x j).mp hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨p.perm.symm i, p.perm.symm j,
      fun h => hij (p.perm.symm.injective h), ?_, ?_⟩
    · apply (p.integer_coordinate_iff x _).mpr
      rw [p.perm.apply_symm_apply]
      exact hi
    · apply (p.integer_coordinate_iff x _).mpr
      rw [p.perm.apply_symm_apply]
      exact hj

/-- Euclidean clearance transports without weakening the radius. -/
theorem Pose.quarter_lt_dist_image_of_clearance {d : ℕ} (p : Pose d)
    {S : Set (Point d)}
    (hS : ∀ x ∈ S, ∀ q ∈ integerSkeleton d, (1/4 : ℝ) < dist x q)
    {x q : Point d} (hx : x ∈ p.euclidean '' S)
    (hq : q ∈ integerSkeleton d) : (1/4 : ℝ) < dist x q := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, rfl⟩ := p.euclidean.surjective q
  rw [p.euclidean.dist_map]
  exact hS y hy z ((p.mem_integerSkeleton_iff z).mp hq)

end Contact

namespace Canonical

open Contact

/-- Every tangential coordinate of the actual five-dimensional convex solid
stays strictly in the central half of the reference unit facet. -/
theorem referenceSolid5_tangent_coordinate {x : Point 5}
    (hx : x ∈ referenceSolid5) (i : Fin 5) (hi : i ≠ 4) :
    (1/4 : ℝ) < x i ∧ x i < 3/4 := by
  apply keySolid_coordinate_mem_Ioo ((referenceBox5 true).toKeyData 19200)
    i (1/4) (3/4) (hx := hx)
  all_goals fin_cases i <;>
    norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex] at *
  all_goals exact hi rfl

/-- The exact dimension-seven widths still leave strict quarter clearance. -/
theorem referenceSolid7_tangent_coordinate {x : Point 7}
    (hx : x ∈ referenceSolid7) (i : Fin 7) (hi : i ≠ 6) :
    (1/4 : ℝ) < x i ∧ x i < 3/4 := by
  apply keySolid_coordinate_mem_Ioo ((referenceBox7 true).toKeyData 188160)
    i (1/4) (3/4) (hx := hx)
  all_goals fin_cases i <;>
    norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex] at *
  all_goals exact hi rfl

theorem referenceSolid5_quarter_lt_dist {x p : Point 5}
    (hx : x ∈ referenceSolid5) (hp : p ∈ integerSkeleton 5) :
    (1/4 : ℝ) < dist x p :=
  quarter_lt_dist_integerSkeleton_of_coordinates 4
    (referenceSolid5_tangent_coordinate hx) hp

theorem referenceSolid7_quarter_lt_dist {x p : Point 7}
    (hx : x ∈ referenceSolid7) (hp : p ∈ integerSkeleton 7) :
    (1/4 : ℝ) < dist x p :=
  quarter_lt_dist_integerSkeleton_of_coordinates 6
    (referenceSolid7_tangent_coordinate hx) hp

theorem posed_referenceSolid5_quarter_lt_dist (g : Pose 5) {x p : Point 5}
    (hx : x ∈ g.euclidean '' referenceSolid5) (hp : p ∈ integerSkeleton 5) :
    (1/4 : ℝ) < dist x p :=
  g.quarter_lt_dist_image_of_clearance
    (fun _ hx _ hp => referenceSolid5_quarter_lt_dist hx hp) hx hp

theorem posed_referenceSolid7_quarter_lt_dist (g : Pose 7) {x p : Point 7}
    (hx : x ∈ g.euclidean '' referenceSolid7) (hp : p ∈ integerSkeleton 7) :
    (1/4 : ℝ) < dist x p :=
  g.quarter_lt_dist_image_of_clearance
    (fun _ hx _ hp => referenceSolid7_quarter_lt_dist hx hp) hx hp

end Canonical

/-- A uniform clearance statement gives one common key-free Euclidean ball. -/
theorem quarter_ball_avoids_keys_of_clearance {d : ℕ} {ks : List (KeyData d)}
    {p : Point d}
    (hclear : ∀ k ∈ ks, ∀ x ∈ keySolid k, (1/4 : ℝ) < dist x p) :
    ∀ x ∈ Metric.closedBall p (1/4 : ℝ), ∀ k ∈ ks, x ∉ keySolid k := by
  intro x hx k hk hxk
  exact not_lt_of_ge (Metric.mem_closedBall.mp hx) (hclear k hk x hxk)

/-- The open quarter ball is an explicit common neighborhood for every key. -/
theorem eventually_avoids_keys_of_quarter_clearance {d : ℕ}
    {ks : List (KeyData d)} {p : Point d}
    (hclear : ∀ k ∈ ks, ∀ x ∈ keySolid k, (1/4 : ℝ) < dist x p) :
    ∀ᶠ x in 𝓝 p, ∀ k ∈ ks, x ∉ keySolid k := by
  apply Filter.Eventually.mono (Metric.ball_mem_nhds p (by norm_num : (0 : ℝ) < 1/4))
  intro x hx
  exact quarter_ball_avoids_keys_of_clearance hclear x
    (Metric.ball_subset_closedBall hx)

namespace Canonical

open Contact

/-- The all-key certificate supplies one explicit closed neighborhood in dimension five. -/
theorem canonical5_keys_avoid_quarter_closedBall {ks : List (KeyData 5)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 5,
      keySolid k = g.euclidean '' referenceSolid5)
    {p : Point 5} (hp : p ∈ integerSkeleton 5) :
    ∀ x ∈ Metric.closedBall p (1/4 : ℝ), ∀ k ∈ ks, x ∉ keySolid k := by
  apply quarter_ball_avoids_keys_of_clearance
  intro k hk x hx
  obtain ⟨g, hg⟩ := hcanonical k hk
  rw [hg] at hx
  exact posed_referenceSolid5_quarter_lt_dist g hx hp

/-- The all-key certificate supplies the identical closed radius in dimension seven. -/
theorem canonical7_keys_avoid_quarter_closedBall {ks : List (KeyData 7)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 7,
      keySolid k = g.euclidean '' referenceSolid7)
    {p : Point 7} (hp : p ∈ integerSkeleton 7) :
    ∀ x ∈ Metric.closedBall p (1/4 : ℝ), ∀ k ∈ ks, x ∉ keySolid k := by
  apply quarter_ball_avoids_keys_of_clearance
  intro k hk x hx
  obtain ⟨g, hg⟩ := hcanonical k hk
  rw [hg] at hx
  exact posed_referenceSolid7_quarter_lt_dist g hx hp

/-- K1 for any five-dimensional literal list whose every key has been bound to
a canonical reference solid by an integer signed pose. -/
theorem localSetEq_body_carrier_of_canonical5 {ks : List (KeyData 5)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 5,
      keySolid k = g.euclidean '' referenceSolid5)
    {p : Point 5} (hp : p ∈ integerSkeleton 5) :
    LocalSetEq p (body ks) (carrier 5) := by
  apply localSetEq_body_carrier_away_keys
  apply eventually_avoids_keys_of_quarter_clearance
  intro k hk x hx
  obtain ⟨g, hg⟩ := hcanonical k hk
  rw [hg] at hx
  exact posed_referenceSolid5_quarter_lt_dist g hx hp

/-- The dimension-seven K1 interface has exactly the same all-key obligation. -/
theorem localSetEq_body_carrier_of_canonical7 {ks : List (KeyData 7)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 7,
      keySolid k = g.euclidean '' referenceSolid7)
    {p : Point 7} (hp : p ∈ integerSkeleton 7) :
    LocalSetEq p (body ks) (carrier 7) := by
  apply localSetEq_body_carrier_away_keys
  apply eventually_avoids_keys_of_quarter_clearance
  intro k hk x hx
  obtain ⟨g, hg⟩ := hcanonical k hk
  rw [hg] at hx
  exact posed_referenceSolid7_quarter_lt_dist g hx hp

#print axioms referenceSolid5_tangent_coordinate
#print axioms referenceSolid7_tangent_coordinate
#print axioms referenceSolid5_quarter_lt_dist
#print axioms referenceSolid7_quarter_lt_dist
#print axioms posed_referenceSolid5_quarter_lt_dist
#print axioms posed_referenceSolid7_quarter_lt_dist
#print axioms localSetEq_body_carrier_of_canonical5
#print axioms localSetEq_body_carrier_of_canonical7

end Canonical

end SparseMonotiles
