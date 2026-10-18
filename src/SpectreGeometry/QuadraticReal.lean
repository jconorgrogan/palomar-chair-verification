module

public import SpectreGeometry.PolygonData
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! The exact integer-pair certificates embed into actual real arithmetic.
This file proves the algebra and strict-order soundness of that embedding. -/
namespace SpectreGeometry
namespace Quad3
noncomputable def eval (x : Quad3) : ℝ := (x.1 : ℝ) + (x.2 : ℝ)*Real.sqrt 3

theorem eval_add (x y : Quad3) : eval (add x y) = eval x + eval y := by
  simp only [eval,add,Int.cast_add]
  ring

theorem eval_sub (x y : Quad3) : eval (sub x y) = eval x - eval y := by
  simp only [eval,sub,Int.cast_sub]
  ring

theorem eval_mul (x y : Quad3) : eval (mul x y) = eval x * eval y := by
  simp only [eval,mul,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem positive_sound (x : Quad3) (h : positive x) : 0 < eval x := by
  have hs : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hsp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb,hab⟩ | ⟨ha,hb,hab⟩
  · exact add_pos_of_pos_of_nonneg (Int.cast_pos.mpr ha)
      (mul_nonneg (by exact_mod_cast hb) hs)
  · exact add_pos_of_nonneg_of_pos (by exact_mod_cast ha)
      (mul_pos (Int.cast_pos.mpr hb) hsp)
  · have ha' : (0 : ℝ) < x.1 := Int.cast_pos.mpr ha
    have hb' : (x.2 : ℝ) < 0 := Int.cast_lt_zero.mpr hb
    have hab' : (3 : ℝ)*(x.2 : ℝ)*(x.2 : ℝ) < (x.1 : ℝ)*(x.1 : ℝ) := by
      exact_mod_cast hab
    have hsq : (-(x.2 : ℝ)*Real.sqrt 3)^2 < (x.1 : ℝ)^2 := by
      rw [mul_pow,neg_sq,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      nlinarith
    have hh := (sq_lt_sq₀ (mul_nonneg (by linarith : 0 ≤ -(x.2 : ℝ)) hs)
      (le_of_lt ha')).mp hsq
    unfold eval
    nlinarith
  · have ha' : (x.1 : ℝ) < 0 := Int.cast_lt_zero.mpr ha
    have hb' : (0 : ℝ) < x.2 := Int.cast_pos.mpr hb
    have hab' : (x.1 : ℝ)*(x.1 : ℝ) < (3 : ℝ)*(x.2 : ℝ)*(x.2 : ℝ) := by
      exact_mod_cast hab
    have hsq : (-(x.1 : ℝ))^2 < ((x.2 : ℝ)*Real.sqrt 3)^2 := by
      rw [mul_pow,neg_sq,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      nlinarith
    have hh := (sq_lt_sq₀ (by linarith : 0 ≤ -(x.1 : ℝ))
      (mul_nonneg (le_of_lt hb') hs)).mp hsq
    unfold eval
    linarith

end Quad3

abbrev RealPoint := ℝ × ℝ
namespace RealPoint
def sub (x y : RealPoint) : RealPoint := (x.1-y.1,x.2-y.2)
def dot (x y : RealPoint) : ℝ := x.1*y.1+x.2*y.2
def det (x y : RealPoint) : ℝ := x.1*y.2-x.2*y.1
end RealPoint

namespace ExactPoint
noncomputable def eval (x : ExactPoint) : RealPoint := (Quad3.eval x.1,Quad3.eval x.2)

theorem eval_sub (x y : ExactPoint) : eval (sub x y) = RealPoint.sub (eval x) (eval y) := by
  simp [eval,sub,RealPoint.sub,Quad3.eval_sub]

theorem eval_dot (x y : ExactPoint) : Quad3.eval (dot x y) = RealPoint.dot (eval x) (eval y) := by
  simp [dot,eval,RealPoint.dot,Quad3.eval_add,Quad3.eval_mul]

theorem eval_det (x y : ExactPoint) : Quad3.eval (det x y) = RealPoint.det (eval x) (eval y) := by
  simp [det,eval,RealPoint.det,Quad3.eval_sub,Quad3.eval_mul]

end ExactPoint
end SpectreGeometry
