module

public import SpectreGeometry.PolygonBody
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

@[expose] public section


/-! Elementary affine half-plane geometry for the actual real triangles. -/
namespace SpectreGeometry
noncomputable section
open Set
open scoped Topology

def side (a b x : RealPoint) : ℝ := RealPoint.det (RealPoint.sub b a) (RealPoint.sub x a)

@[simp] theorem side_self_left (a b : RealPoint) : side a b a = 0 := by
  simp [side,RealPoint.det,RealPoint.sub]
@[simp] theorem side_self_right (a b : RealPoint) : side a b b = 0 := by
  simp [side,RealPoint.det,RealPoint.sub]; ring
theorem side_cyclic (a b c : RealPoint) : side a b c = side b c a := by
  simp only [side,RealPoint.det,RealPoint.sub]; ring
theorem side_reverse (a b x : RealPoint) : side b a x = -side a b x := by
  simp only [side,RealPoint.det,RealPoint.sub]; ring

theorem side_continuous (a b : RealPoint) : Continuous (side a b) := by
  unfold side RealPoint.det RealPoint.sub
  fun_prop

theorem side_combo (a b x y : RealPoint) (t u : ℝ) (htu : t+u=1) :
    side a b (t • x + u • y) = t*side a b x + u*side a b y := by
  have hu : u = 1-t := by linarith
  subst u
  simp only [side,RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem side_interpolate (a b x y : RealPoint) (t : ℝ) :
    side a b (interpolate x y t) = (1-t)*side a b x + t*side a b y :=
  det_interpolate _ _ _ _ _

theorem side_nonneg_hull (a b : RealPoint) (s : Set RealPoint)
    (hs : ∀ x ∈ s, 0 ≤ side a b x) : ∀ x ∈ convexHull ℝ s, 0 ≤ side a b x := by
  apply convexHull_min hs
  intro x hx y hy t u ht hu htu
  change 0 ≤ side a b (t • x + u • y)
  rw [side_combo _ _ _ _ _ _ htu]
  exact add_nonneg (mul_nonneg ht hx) (mul_nonneg hu hy)

theorem side_nonpos_hull (a b : RealPoint) (s : Set RealPoint)
    (hs : ∀ x ∈ s, side a b x ≤ 0) : ∀ x ∈ convexHull ℝ s, side a b x ≤ 0 := by
  have hh := side_nonneg_hull b a s (by intro x hx; rw [side_reverse]; linarith [hs x hx])
  intro x hx
  have h := hh x hx
  rw [side_reverse] at h
  linarith

theorem triangle_mem_iff (a b c x : RealPoint) (hD : 0 < side a b c) :
    x ∈ convexHull ℝ {a,b,c} ↔
      0 ≤ side a b x ∧ 0 ≤ side b c x ∧ 0 ≤ side c a x := by
  constructor
  · intro hx
    have hbc : 0 ≤ side b c a := by rw [←side_cyclic]; exact hD.le
    have hca : 0 ≤ side c a b := by rw [side_cyclic]; exact hD.le
    have h1 : 0 ≤ side a b x := side_nonneg_hull a b {a,b,c}
      (by intro y hy; simp only [mem_insert_iff,mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl <;> simp [le_of_lt hD]) x hx
    have h2 : 0 ≤ side b c x := side_nonneg_hull b c {a,b,c}
      (by intro y hy; simp only [mem_insert_iff,mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl <;> simp_all) x hx
    have h3 : 0 ≤ side c a x := side_nonneg_hull c a {a,b,c}
      (by intro y hy; simp only [mem_insert_iff,mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl <;> simp_all) x hx
    exact ⟨h1,h2,h3⟩
  · rintro ⟨h1,h2,h3⟩
    have hsum : side b c x / side a b c + side c a x / side a b c +
        side a b x / side a b c = 1 := by
      field_simp
      simp only [side,RealPoint.det,RealPoint.sub]
      ring
    have heq : (side b c x / side a b c) • a +
        (side c a x / side a b c) • b + (side a b x / side a b c) • c = x := by
      apply Prod.ext <;>
        simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;>
        field_simp <;> simp only [side,RealPoint.det,RealPoint.sub] <;> ring
    rw [←heq]
    exact three_point_convex_combo a b c _ _ _
      (div_nonneg h2 hD.le) (div_nonneg h3 hD.le) (div_nonneg h1 hD.le) hsum

theorem strict_sides_mem_interior (a b c x : RealPoint) (hD : 0 < side a b c)
    (hx : 0 < side a b x ∧ 0 < side b c x ∧ 0 < side c a x) :
    x ∈ interior (convexHull ℝ {a,b,c}) := by
  let U : Set RealPoint := {y | 0 < side a b y ∧ 0 < side b c y ∧ 0 < side c a y}
  have hopen : IsOpen U := (isOpen_lt continuous_const (side_continuous a b)).inter
    ((isOpen_lt continuous_const (side_continuous b c)).inter
    (isOpen_lt continuous_const (side_continuous c a)))
  have hsub : U ⊆ convexHull ℝ {a,b,c} := by
    intro y hy
    exact (triangle_mem_iff a b c y hD).2 ⟨hy.1.le,hy.2.1.le,hy.2.2.le⟩
  exact (interior_maximal hsub hopen) hx

theorem interior_side_pos (a b c : RealPoint) (hD : 0 < side a b c)
    (s : Set RealPoint) (hs : ∀ x ∈ s, 0 ≤ side a b x)
    (x : RealPoint) (hx : x ∈ interior s) : 0 < side a b x := by
  have hnonneg := hs x (interior_subset hx)
  by_contra hn
  have hz : side a b x = 0 := by linarith
  let f : ℝ → RealPoint := fun t => x - t • (c-a)
  have hf : Continuous f := by unfold f; fun_prop
  have hf0 : f 0 = x := by simp [f]
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ s := by
    have hx0 : f 0 ∈ interior s := hf0.symm ▸ hx
    exact hf.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.1 hx0)
  obtain ⟨t,ht,hft⟩ := hevent.exists_gt
  have hh := hs (f t) hft
  have hid : side a b (f t) = side a b x - t*side a b c := by
    simp only [f,side,RealPoint.det,RealPoint.sub,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [hid,hz] at hh
  nlinarith

theorem triangle_interior_iff (a b c x : RealPoint) (hD : 0 < side a b c) :
    x ∈ interior (convexHull ℝ {a,b,c}) ↔
      0 < side a b x ∧ 0 < side b c x ∧ 0 < side c a x := by
  constructor
  · intro hx
    exact ⟨interior_side_pos a b c hD _
        (fun y hy => ((triangle_mem_iff a b c y hD).1 hy).1) x hx,
      interior_side_pos b c a (by rwa [←side_cyclic a b c]) _
        (fun y hy => ((triangle_mem_iff a b c y hD).1 hy).2.1) x hx,
      interior_side_pos c a b (by rwa [side_cyclic c a b]) _
        (fun y hy => ((triangle_mem_iff a b c y hD).1 hy).2.2) x hx⟩
  · exact strict_sides_mem_interior a b c x hD


theorem triangle_interior_nonempty (a b c : RealPoint) (hD : 0 < side a b c) :
    (interior (convexHull ℝ {a,b,c})).Nonempty := by
  let x : RealPoint := (1/3 : ℝ) • a + (1/3 : ℝ) • b + (1/3 : ℝ) • c
  have h1 : side a b x = side a b c / 3 := by
    simp only [x,side,RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]; ring
  have h2 : side b c x = side a b c / 3 := by
    simp only [x,side,RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]; ring
  have h3 : side c a x = side a b c / 3 := by
    simp only [x,side,RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]; ring
  exact ⟨x,strict_sides_mem_interior a b c x hD (by rw [h1,h2,h3]; exact ⟨by positivity,by positivity,by positivity⟩)⟩

theorem triangle_side_zero_segment (a b c x : RealPoint) (hD : 0 < side a b c)
    (hx : x ∈ convexHull ℝ {a,b,c}) (hz : side a b x = 0) : x ∈ closedSegmentR a b := by
  obtain ⟨h1,h2,h3⟩ := (triangle_mem_iff a b c x hD).1 hx
  have hsum : side b c x + side c a x = side a b c := by
    have hi : side a b x + side b c x + side c a x = side a b c := by
      simp only [side,RealPoint.det,RealPoint.sub]; ring
    linarith
  refine ⟨side c a x / side a b c, div_nonneg h3 hD.le, ?_, ?_⟩
  · apply (div_le_one hD).2
    linarith
  · apply Prod.ext <;> simp only [interpolate] <;> field_simp
    all_goals
      have hz' := hz
      simp only [side,RealPoint.det,RealPoint.sub] at hz' ⊢
    · linear_combination (c.1-a.1) * hz'
    · linear_combination (c.2-a.2) * hz'

end
end SpectreGeometry
