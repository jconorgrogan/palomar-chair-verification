module

public import SparseMonotiles.CanonicalReferenceKeys
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# Exact Euclidean diameter bounds for canonical key solids

Closed coordinate intervals propagate from the base and apex through the
convex hull. In dimension five every interval has width at most `7/160`; in
dimension seven the uniform bound is `11/336`. The Euclidean norm is bounded
by the sum of absolute coordinates, giving the respective diameter bounds
`7/32` and `11/48`, both strictly below `1/4`.

The statements about a list of keys explicitly require a canonical binding
for every member. This module does not discharge the literal-data certificates.
-/

namespace SparseMonotiles

open Set

/-- Closed coordinate bounds on the base and apex hold on the whole pyramid. -/
theorem keySolid_coordinate_mem_Icc {d : ℕ} (k : KeyData d) (i : Fin d)
    (a b : ℝ)
    (hlo : a ≤ (k.centre i : ℝ) - (k.radius i : ℝ))
    (hhi : (k.centre i : ℝ) + (k.radius i : ℝ) ≤ b)
    (ha : a ≤ (k.apex i : ℝ) ∧ (k.apex i : ℝ) ≤ b)
    {x : Point d} (hx : x ∈ keySolid k) : a ≤ x i ∧ x i ≤ b := by
  have hf : IsLinearMap ℝ (fun y : Point d => y i) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hsub : insert (rationalPoint k.apex) (keyBase k) ⊆
      {y : Point d | a ≤ y i ∧ y i ≤ b} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ha
    · have hbase := abs_le.mp (hy i)
      constructor <;> linarith [hbase.1, hbase.2]
  exact convexHull_min hsub
    ((convex_halfSpace_ge hf a).inter (convex_halfSpace_le hf b)) hx

/-- The genuine Euclidean norm is at most the sum of absolute coordinates. -/
theorem point_norm_le_sum_abs {d : ℕ} (v : Point d) :
    ‖v‖ ≤ ∑ i : Fin d, |v i| := by
  have hv : v = ∑ i : Fin d, EuclideanSpace.single i (v i) := by
    ext j
    simp [WithLp.ofLp_sum]
  calc
    ‖v‖ = ‖∑ i : Fin d, EuclideanSpace.single i (v i)‖ := congrArg norm hv
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, |v i| := by simp

/-- Coordinate-width bounds imply an L1 upper bound on Euclidean distance. -/
theorem point_dist_le_of_coordinate_bounds {d : ℕ} (x y : Point d) (w : ℝ)
    (h : ∀ i, |x i - y i| ≤ w) : dist x y ≤ (d : ℝ) * w := by
  rw [dist_eq_norm]
  calc
    ‖x - y‖ ≤ ∑ i : Fin d, |(x - y) i| := point_norm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, w := Finset.sum_le_sum (fun i _ => h i)
    _ = (d : ℝ) * w := by simp

namespace Contact

/-- Isometric transport preserves a pairwise distance bound exactly. -/
theorem Pose.dist_le_image_of_bound {d : ℕ} (p : Pose d)
    {S : Set (Point d)} {C : ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ C)
    {x y : Point d} (hx : x ∈ p.euclidean '' S)
    (hy : y ∈ p.euclidean '' S) : dist x y ≤ C := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [p.euclidean.dist_map]
  exact hS u hu v hv

end Contact

namespace Canonical

open Contact

/-- A fixed width-`7/160` interval contains every reference-key coordinate. -/
theorem referenceSolid5_coordinate_interval {x : Point 5}
    (hx : x ∈ referenceSolid5) (i : Fin 5) :
    let k := (referenceBox5 true).toKeyData 19200
    (k.centre i : ℝ) - (k.radius i : ℝ) ≤ x i ∧
      x i ≤ (k.centre i : ℝ) - (k.radius i : ℝ) + 7/160 := by
  apply keySolid_coordinate_mem_Icc ((referenceBox5 true).toKeyData 19200)
    i _ _ (hx := hx)
  · exact le_rfl
  all_goals fin_cases i <;>
    norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex]

/-- The dimension-seven coordinate enclosure has width `11/336`. -/
theorem referenceSolid7_coordinate_interval {x : Point 7}
    (hx : x ∈ referenceSolid7) (i : Fin 7) :
    let k := (referenceBox7 true).toKeyData 188160
    (k.centre i : ℝ) - (k.radius i : ℝ) ≤ x i ∧
      x i ≤ (k.centre i : ℝ) - (k.radius i : ℝ) + 11/336 := by
  apply keySolid_coordinate_mem_Icc ((referenceBox7 true).toKeyData 188160)
    i _ _ (hx := hx)
  · exact le_rfl
  all_goals fin_cases i <;>
    norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex]

theorem referenceSolid5_coordinate_dist_le {x y : Point 5}
    (hx : x ∈ referenceSolid5) (hy : y ∈ referenceSolid5) (i : Fin 5) :
    |x i - y i| ≤ (7/160 : ℝ) := by
  have hxi := referenceSolid5_coordinate_interval hx i
  have hyi := referenceSolid5_coordinate_interval hy i
  apply abs_le.mpr
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

theorem referenceSolid7_coordinate_dist_le {x y : Point 7}
    (hx : x ∈ referenceSolid7) (hy : y ∈ referenceSolid7) (i : Fin 7) :
    |x i - y i| ≤ (11/336 : ℝ) := by
  have hxi := referenceSolid7_coordinate_interval hx i
  have hyi := referenceSolid7_coordinate_interval hy i
  apply abs_le.mpr
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- Exact rational L1 bound for the Euclidean diameter in dimension five. -/
theorem referenceSolid5_dist_le {x y : Point 5}
    (hx : x ∈ referenceSolid5) (hy : y ∈ referenceSolid5) :
    dist x y ≤ (7/32 : ℝ) := by
  have h := point_dist_le_of_coordinate_bounds x y (7/160)
    (referenceSolid5_coordinate_dist_le hx hy)
  norm_num at h ⊢
  exact h

/-- Exact rational L1 bound for the Euclidean diameter in dimension seven. -/
theorem referenceSolid7_dist_le {x y : Point 7}
    (hx : x ∈ referenceSolid7) (hy : y ∈ referenceSolid7) :
    dist x y ≤ (11/48 : ℝ) := by
  have h := point_dist_le_of_coordinate_bounds x y (11/336)
    (referenceSolid7_coordinate_dist_le hx hy)
  norm_num at h ⊢
  exact h

theorem referenceSolid5_dist_lt_quarter {x y : Point 5}
    (hx : x ∈ referenceSolid5) (hy : y ∈ referenceSolid5) :
    dist x y < (1/4 : ℝ) :=
  (referenceSolid5_dist_le hx hy).trans_lt (by norm_num)

theorem referenceSolid7_dist_lt_quarter {x y : Point 7}
    (hx : x ∈ referenceSolid7) (hy : y ∈ referenceSolid7) :
    dist x y < (1/4 : ℝ) :=
  (referenceSolid7_dist_le hx hy).trans_lt (by norm_num)

theorem referenceSolid5_diam_le : Metric.diam referenceSolid5 ≤ (7/32 : ℝ) :=
  Metric.diam_le_of_forall_dist_le (by norm_num)
    (fun _ hx _ hy => referenceSolid5_dist_le hx hy)

theorem referenceSolid7_diam_le : Metric.diam referenceSolid7 ≤ (11/48 : ℝ) :=
  Metric.diam_le_of_forall_dist_le (by norm_num)
    (fun _ hx _ hy => referenceSolid7_dist_le hx hy)

theorem referenceSolid5_diam_lt_quarter :
    Metric.diam referenceSolid5 < (1/4 : ℝ) :=
  referenceSolid5_diam_le.trans_lt (by norm_num)

theorem referenceSolid7_diam_lt_quarter :
    Metric.diam referenceSolid7 < (1/4 : ℝ) :=
  referenceSolid7_diam_le.trans_lt (by norm_num)

/-- Integer signed poses retain the five-dimensional metric bound. -/
theorem posed_referenceSolid5_dist_le (g : Pose 5) {x y : Point 5}
    (hx : x ∈ g.euclidean '' referenceSolid5)
    (hy : y ∈ g.euclidean '' referenceSolid5) : dist x y ≤ (7/32 : ℝ) :=
  g.dist_le_image_of_bound (fun _ hx _ hy => referenceSolid5_dist_le hx hy) hx hy

/-- Integer signed poses retain the seven-dimensional metric bound. -/
theorem posed_referenceSolid7_dist_le (g : Pose 7) {x y : Point 7}
    (hx : x ∈ g.euclidean '' referenceSolid7)
    (hy : y ∈ g.euclidean '' referenceSolid7) : dist x y ≤ (11/48 : ℝ) :=
  g.dist_le_image_of_bound (fun _ hx _ hy => referenceSolid7_dist_le hx hy) hx hy

/-- The all-key binding gives the five-dimensional bound for every actual key. -/
theorem canonical5_keys_dist_le {ks : List (KeyData 5)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 5,
      keySolid k = g.euclidean '' referenceSolid5)
    {k : KeyData 5} (hk : k ∈ ks) {x y : Point 5}
    (hx : x ∈ keySolid k) (hy : y ∈ keySolid k) : dist x y ≤ (7/32 : ℝ) := by
  obtain ⟨g, hg⟩ := hcanonical k hk
  rw [hg] at hx hy
  exact posed_referenceSolid5_dist_le g hx hy

/-- The corresponding seven-dimensional statement keeps its binding explicit. -/
theorem canonical7_keys_dist_le {ks : List (KeyData 7)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 7,
      keySolid k = g.euclidean '' referenceSolid7)
    {k : KeyData 7} (hk : k ∈ ks) {x y : Point 7}
    (hx : x ∈ keySolid k) (hy : y ∈ keySolid k) : dist x y ≤ (11/48 : ℝ) := by
  obtain ⟨g, hg⟩ := hcanonical k hk
  rw [hg] at hx hy
  exact posed_referenceSolid7_dist_le g hx hy

theorem canonical5_keys_dist_lt_quarter {ks : List (KeyData 5)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 5,
      keySolid k = g.euclidean '' referenceSolid5)
    {k : KeyData 5} (hk : k ∈ ks) {x y : Point 5}
    (hx : x ∈ keySolid k) (hy : y ∈ keySolid k) : dist x y < (1/4 : ℝ) :=
  (canonical5_keys_dist_le hcanonical hk hx hy).trans_lt (by norm_num)

theorem canonical7_keys_dist_lt_quarter {ks : List (KeyData 7)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 7,
      keySolid k = g.euclidean '' referenceSolid7)
    {k : KeyData 7} (hk : k ∈ ks) {x y : Point 7}
    (hx : x ∈ keySolid k) (hy : y ∈ keySolid k) : dist x y < (1/4 : ℝ) :=
  (canonical7_keys_dist_le hcanonical hk hx hy).trans_lt (by norm_num)

theorem canonical5_keys_diam_le {ks : List (KeyData 5)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 5,
      keySolid k = g.euclidean '' referenceSolid5)
    {k : KeyData 5} (hk : k ∈ ks) : Metric.diam (keySolid k) ≤ (7/32 : ℝ) :=
  Metric.diam_le_of_forall_dist_le (by norm_num)
    (fun _ hx _ hy => canonical5_keys_dist_le hcanonical hk hx hy)

theorem canonical7_keys_diam_le {ks : List (KeyData 7)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 7,
      keySolid k = g.euclidean '' referenceSolid7)
    {k : KeyData 7} (hk : k ∈ ks) : Metric.diam (keySolid k) ≤ (11/48 : ℝ) :=
  Metric.diam_le_of_forall_dist_le (by norm_num)
    (fun _ hx _ hy => canonical7_keys_dist_le hcanonical hk hx hy)

theorem canonical5_keys_diam_lt_quarter {ks : List (KeyData 5)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 5,
      keySolid k = g.euclidean '' referenceSolid5)
    {k : KeyData 5} (hk : k ∈ ks) : Metric.diam (keySolid k) < (1/4 : ℝ) :=
  (canonical5_keys_diam_le hcanonical hk).trans_lt (by norm_num)

theorem canonical7_keys_diam_lt_quarter {ks : List (KeyData 7)}
    (hcanonical : ∀ k ∈ ks, ∃ g : Pose 7,
      keySolid k = g.euclidean '' referenceSolid7)
    {k : KeyData 7} (hk : k ∈ ks) : Metric.diam (keySolid k) < (1/4 : ℝ) :=
  (canonical7_keys_diam_le hcanonical hk).trans_lt (by norm_num)

#print axioms keySolid_coordinate_mem_Icc
#print axioms point_norm_le_sum_abs
#print axioms point_dist_le_of_coordinate_bounds
#print axioms Pose.dist_le_image_of_bound
#print axioms referenceSolid5_coordinate_interval
#print axioms referenceSolid7_coordinate_interval
#print axioms referenceSolid5_dist_le
#print axioms referenceSolid7_dist_le
#print axioms referenceSolid5_diam_lt_quarter
#print axioms referenceSolid7_diam_lt_quarter
#print axioms posed_referenceSolid5_dist_le
#print axioms posed_referenceSolid7_dist_le
#print axioms canonical5_keys_dist_lt_quarter
#print axioms canonical7_keys_dist_lt_quarter
#print axioms canonical5_keys_diam_lt_quarter
#print axioms canonical7_keys_diam_lt_quarter

end Canonical

end SparseMonotiles
