module

public import SparseMonotiles.Model
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMonotiles

def centralBox (d : ℕ) : Set (Point d) :=
  {x | ∀ i, (1/4 : ℝ) < x i ∧ x i < 3/4}

def avoidsCentralBox {d : ℕ} (k : KeyData d) : Bool :=
  (List.finRange d).any fun i => decide (k.radius i = 0 ∧
    ((k.centre i ≤ 1/4 ∧ k.apex i ≤ 1/4) ∨
     (3/4 ≤ k.centre i ∧ 3/4 ≤ k.apex i)))

theorem avoidsCentralBox_of_witness {d : ℕ} (k : KeyData d) (i : Fin d)
    (h : k.radius i = 0 ∧
      ((k.centre i ≤ 1/4 ∧ k.apex i ≤ 1/4) ∨
       (3/4 ≤ k.centre i ∧ 3/4 ≤ k.apex i))) :
    avoidsCentralBox k = true := by
  apply List.any_eq_true.mpr
  exact ⟨i, List.mem_finRange i, decide_eq_true h⟩

theorem avoidsCentralBox_sound {d : ℕ} (k : KeyData d)
    (h : avoidsCentralBox k = true) :
    ∃ i, k.radius i = 0 ∧
      ((k.centre i ≤ 1/4 ∧ k.apex i ≤ 1/4) ∨
       (3/4 ≤ k.centre i ∧ 3/4 ≤ k.apex i)) := by
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp h
  exact ⟨i, of_decide_eq_true hi⟩

private theorem keyBase_coordinate_of_zero_radius {d : ℕ}
    (k : KeyData d) (i : Fin d) (hr : k.radius i = 0)
    {x : Point d} (hx : x ∈ keyBase k) : x i = (k.centre i : ℝ) := by
  have hi := hx i
  rw [hr] at hi
  norm_num only [Rat.cast_zero] at hi
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))

theorem keySolid_avoids_centralBox {d : ℕ} (k : KeyData d)
    (h : avoidsCentralBox k = true) : Disjoint (keySolid k) (centralBox d) := by
  obtain ⟨i, hr, hi⟩ := avoidsCentralBox_sound k h
  have hf : IsLinearMap ℝ (fun x : Point d => x i) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  apply Set.disjoint_left.mpr
  intro x hx hc
  rcases hi with ⟨hcentre, hapex⟩ | ⟨hcentre, hapex⟩
  · have hsub : insert (rationalPoint k.apex) (keyBase k) ⊆
        {y : Point d | y i ≤ 1/4} := by
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · change (k.apex i : ℝ) ≤ 1/4
        have hc := (Rat.cast_le (K := ℝ)).2 hapex
        norm_num at hc
        exact hc
      · change y i ≤ 1/4
        rw [keyBase_coordinate_of_zero_radius k i hr hy]
        have hc := (Rat.cast_le (K := ℝ)).2 hcentre
        norm_num at hc
        exact hc
    have hbound := convexHull_min hsub (convex_halfSpace_le hf (1/4 : ℝ)) hx
    exact not_le_of_gt (hc i).1 hbound
  · have hsub : insert (rationalPoint k.apex) (keyBase k) ⊆
        {y : Point d | 3/4 ≤ y i} := by
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · change (3/4 : ℝ) ≤ (k.apex i : ℝ)
        have hc := (Rat.cast_le (K := ℝ)).2 hapex
        norm_num at hc
        exact hc
      · change (3/4 : ℝ) ≤ y i
        rw [keyBase_coordinate_of_zero_radius k i hr hy]
        have hc := (Rat.cast_le (K := ℝ)).2 hcentre
        norm_num at hc
        exact hc
    have hbound := convexHull_min hsub (convex_halfSpace_ge hf (3/4 : ℝ)) hx
    exact not_le_of_gt (hc i).2 hbound

theorem centralBox_subset_body {d : ℕ} (hd : 0 < d) (ks : List (KeyData d))
    (h : ks.all avoidsCentralBox = true) : centralBox d ⊆ body ks := by
  intro x hx
  apply subset_closure
  constructor
  · left
    refine ⟨fun _ => false, ⟨⟨0, hd⟩, rfl⟩, ?_⟩
    intro i
    have hi := hx i
    change (0 : ℝ) ≤ x i ∧ x i ≤ 0 + 1
    constructor <;> linarith
  · rintro ⟨k, hk, _, hxk⟩
    have hkavoid := List.all_eq_true.mp h k hk
    exact Set.disjoint_left.mp (keySolid_avoids_centralBox k hkavoid) hxk hx

noncomputable def centralPoint (d : ℕ) : Point d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun _ => 1/2)

theorem centralBall_subset_centralBox (d : ℕ) :
    Metric.ball (centralPoint d) (1/4 : ℝ) ⊆ centralBox d := by
  intro x hx i
  have hi := (PiLp.dist_apply_le x (centralPoint d) i).trans_lt hx
  change dist (x i) (1/2 : ℝ) < 1/4 at hi
  rw [Real.dist_eq, abs_lt] at hi
  constructor <;> linarith

theorem centralBall_subset_body {d : ℕ} (hd : 0 < d) (ks : List (KeyData d))
    (h : ks.all avoidsCentralBox = true) :
    Metric.ball (centralPoint d) (1/4 : ℝ) ⊆ body ks :=
  (centralBall_subset_centralBox d).trans (centralBox_subset_body hd ks h)

theorem body_interior_nonempty {d : ℕ} (hd : 0 < d) (ks : List (KeyData d))
    (h : ks.all avoidsCentralBox = true) : (interior (body ks)).Nonempty := by
  have hsub := Metric.isOpen_ball.subset_interior_iff.mpr (centralBall_subset_body hd ks h)
  exact ⟨centralPoint d, hsub (Metric.mem_ball_self (by norm_num))⟩

end SparseMonotiles
