module

public import SpectreGeometry.QuadraticReal
public import Mathlib.Data.Int.Sqrt
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat

@[expose] public section


/-! Rational sqrt(3) coordinates and their faithful real interpretation.
The small rational-square-root argument below adapts Rat.sqrt_eq and
Rat.exists_mul_self from mathlib Mathlib/Data/Rat/Sqrt.lean, copyright2019
Johannes Hölzl, authors Johannes Hölzl and Mario Carneiro, Apache2.0.
The project retains MATHLIB_LICENSE. No irrationality theorem is assumed. -/
namespace SpectreGeometry.QuadraticCoordinates
noncomputable section

def rationalSqrt (q : ℚ) : ℚ := mkRat (Int.sqrt q.num) (Nat.sqrt q.den)

theorem rationalSqrt_mul_self (q : ℚ) : rationalSqrt (q*q) = |q| := by
  rw [rationalSqrt,Rat.mul_self_num,Rat.mul_self_den,Int.sqrt_eq,Nat.sqrt_eq,Rat.abs_def,Rat.divInt_ofNat]

theorem rationalSqrt_square_witness (x : ℚ) (h : ∃ q : ℚ, q*q=x) :
    rationalSqrt x * rationalSqrt x = x := by
  obtain ⟨q,hq⟩ := h
  rw [←hq,rationalSqrt_mul_self,abs_mul_abs_self]

theorem rational_ne_sqrt_three (q : ℚ) : (q : ℝ) ≠ Real.sqrt 3 := by
  intro hq
  have hsq : q*q = 3 := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [hq,Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hbad := rationalSqrt_square_witness 3 ⟨q,hsq⟩
  have h3 : Nat.sqrt 3 = 1 := (Nat.eq_sqrt.mpr (by norm_num)).symm
  norm_num [rationalSqrt,h3] at hbad

abbrev Coordinate := ℚ × ℚ

def eval (x : Coordinate) : ℝ := (x.1 : ℝ)+(x.2 : ℝ)*Real.sqrt 3

theorem eval_zero_iff (x : Coordinate) : eval x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hb : x.2 = 0 := by
      by_contra hb
      have hb' : (x.2 : ℝ) ≠ 0 := by exact_mod_cast hb
      have he : ((-x.1/x.2 : ℚ) : ℝ) = Real.sqrt 3 := by
        rw [Rat.cast_div,Rat.cast_neg]
        apply (div_eq_iff hb').2
        dsimp only [eval] at h
        nlinarith
      exact rational_ne_sqrt_three _ he
    have ha : x.1 = 0 := by
      simp only [eval,hb,Rat.cast_zero,zero_mul,add_zero] at h
      exact_mod_cast h
    exact Prod.ext ha hb
  · rintro rfl
    simp [eval]

theorem eval_sub (x y : Coordinate) : eval (x-y) = eval x-eval y := by
  simp only [eval,Prod.fst_sub,Prod.snd_sub,Rat.cast_sub]
  ring

theorem eval_injective : Function.Injective eval := by
  intro x y h
  have hh : eval (x-y) = 0 := by rw [eval_sub,h,sub_self]
  exact sub_eq_zero.mp ((eval_zero_iff _).1 hh)

end
end SpectreGeometry.QuadraticCoordinates
