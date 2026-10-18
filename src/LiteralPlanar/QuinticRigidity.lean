module

public import LiteralPlanar.QuinticArc
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


/-! Rigidity of the quintic graph under Euclidean affine maps. This is an
algebraic contact lemma, not whole-boundary registration or a tiling theorem. -/
namespace LiteralPlanar.Quintic
noncomputable section
open Polynomial

def graphPolynomial (ε : ℝ) : ℝ[X] :=
  C ε * (X ^ 5 - C (1 / 2) * X ^ 3 + C (1 / 16) * X)

@[simp] theorem graphPolynomial_eval (ε t : ℝ) :
    (graphPolynomial ε).eval t = height ε t := by
  rw [height_expanded]
  simp [graphPolynomial]

theorem graphPolynomial_degree (ε : ℝ) (hε : ε ≠ 0) :
    (graphPolynomial ε).natDegree = 5 := by
  unfold graphPolynomial
  compute_degree!

/-- Coefficients of an orthogonal affine transformation, with both signs of
its determinant permitted. The row equations are ordinary Euclidean data. -/
structure RigidCoefficients where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  u : ℝ
  v : ℝ
  row_one : a ^ 2 + b ^ 2 = 1
  row_two : c ^ 2 + d ^ 2 = 1
  row_dot : a * c + b * d = 0

def horizontalPolynomial (ε : ℝ) (M : RigidCoefficients) : ℝ[X] :=
  C M.a * X + C M.b * graphPolynomial ε + C M.u

def verticalPolynomial (ε : ℝ) (M : RigidCoefficients) : ℝ[X] :=
  C M.c * X + C M.d * graphPolynomial ε + C M.v

def coincidenceParameters (ε : ℝ) (M : RigidCoefficients) : Set ℝ :=
  {t | height ε (M.a * t + M.b * height ε t + M.u) =
    M.c * t + M.d * height ε t + M.v}

def IsGraphSymmetry (M : RigidCoefficients) : Prop :=
  M.b = 0 ∧ M.c = 0 ∧ M.u = 0 ∧ M.v = 0 ∧
    ((M.a = 1 ∧ M.d = 1) ∨ (M.a = -1 ∧ M.d = -1))

theorem infinite_coincidence_polynomial_identity (ε : ℝ) (M : RigidCoefficients)
    (h : (coincidenceParameters ε M).Infinite) :
    (graphPolynomial ε).comp (horizontalPolynomial ε M) = verticalPolynomial ε M := by
  apply Polynomial.eq_of_infinite_eval_eq
  simpa [coincidenceParameters, horizontalPolynomial, verticalPolynomial,
    Polynomial.eval_comp] using h

theorem polynomial_identity_no_mixing (ε : ℝ) (hε : ε ≠ 0)
    (M : RigidCoefficients)
    (h : (graphPolynomial ε).comp (horizontalPolynomial ε M) = verticalPolynomial ε M) :
    M.b = 0 := by
  by_contra hb
  have hx : (horizontalPolynomial ε M).natDegree = 5 := by
    unfold horizontalPolynomial graphPolynomial
    compute_degree!
  have hy : (verticalPolynomial ε M).natDegree ≤ 5 := by
    unfold verticalPolynomial graphPolynomial
    compute_degree!
  have hd := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_comp, graphPolynomial_degree ε hε, hx] at hd
  omega

/-- Exact expanded coefficient calculation for the remaining horizontal affine
substitution. The displayed formula avoids a degree25 symbolic expansion. -/
theorem graphPolynomial_affine_expansion (ε a u : ℝ) :
    (graphPolynomial ε).comp (C a * X + C u) =
      C (ε * a ^ 5) * X ^ 5 +
      C (5 * ε * a ^ 4 * u) * X ^ 4 +
      C (ε * (10 * a ^ 3 * u ^ 2 - 1 / 2 * a ^ 3)) * X ^ 3 +
      C (ε * (10 * a ^ 2 * u ^ 3 - 3 / 2 * a ^ 2 * u)) * X ^ 2 +
      C (ε * (5 * a * u ^ 4 - 3 / 2 * a * u ^ 2 + 1 / 16 * a)) * X +
      C (height ε u) := by
  simp only [graphPolynomial, Polynomial.mul_comp, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp]
  rw [show (3 / 2 : ℝ) = 3 * (1 / 2) by ring]
  simp only [height_expanded, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem polynomial_identity_rigidity (ε : ℝ) (hε : ε ≠ 0)
    (M : RigidCoefficients)
    (h : (graphPolynomial ε).comp (horizontalPolynomial ε M) = verticalPolynomial ε M) :
    IsGraphSymmetry M := by
  have hb := polynomial_identity_no_mixing ε hε M h
  have ha2 : M.a ^ 2 = 1 := by simpa [hb] using M.row_one
  have ha : M.a ≠ 0 := by intro hz; rw [hz] at ha2; norm_num at ha2
  have hc : M.c = 0 := by
    have he : M.a * M.c = 0 := by simpa [hb] using M.row_dot
    exact (mul_eq_zero.mp he).resolve_left ha
  have hp : (graphPolynomial ε).comp (C M.a * X + C M.u) =
      C M.d * graphPolynomial ε + C M.v := by
    simpa [horizontalPolynomial, verticalPolynomial, hb, hc] using h
  have h4 := congrArg (fun p : ℝ[X] => p.coeff 4) hp
  rw [graphPolynomial_affine_expansion] at h4
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h4
  norm_num [graphPolynomial, Polynomial.coeff_C_mul] at h4
  have hu : M.u = 0 := by
    exact h4.resolve_left (not_or.mpr ⟨hε, ha⟩)
  have h5 := congrArg (fun p : ℝ[X] => p.coeff 5) hp
  rw [graphPolynomial_affine_expansion] at h5
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h5
  norm_num [graphPolynomial, Polynomial.coeff_C_mul] at h5
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hp
  rw [graphPolynomial_affine_expansion] at h0
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h0
  norm_num [graphPolynomial, hu, height, Polynomial.coeff_C_mul] at h0
  have hv : M.v = 0 := by linarith
  have has : M.a = 1 ∨ M.a = -1 := by
    have hz : (M.a - 1) * (M.a + 1) = 0 := by nlinarith [ha2]
    rcases mul_eq_zero.mp hz with hl | hr
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hd : M.d = M.a ^ 5 := by
    apply mul_left_cancel₀ hε
    nlinarith [h5]
  refine ⟨hb, hc, hu, hv, ?_⟩
  rcases has with hapos | haneg
  · left
    refine ⟨hapos, ?_⟩
    simpa [hapos] using hd
  · right
    refine ⟨haneg, ?_⟩
    norm_num [haneg] at hd
    exact hd

theorem infinite_coincidence_rigidity (ε : ℝ) (hε : ε ≠ 0)
    (M : RigidCoefficients) (h : (coincidenceParameters ε M).Infinite) :
    IsGraphSymmetry M :=
  polynomial_identity_rigidity ε hε M (infinite_coincidence_polynomial_identity ε M h)

/-- A non-stabilizing Euclidean image has only finitely many contacts with the
entire graph, hence also with the closed unit arc. No open-overlap premise. -/
theorem finite_coincidence_of_not_symmetry (ε : ℝ) (hε : ε ≠ 0)
    (M : RigidCoefficients) (hM : ¬ IsGraphSymmetry M) :
    (coincidenceParameters ε M).Finite := by
  by_contra h
  exact hM (infinite_coincidence_rigidity ε hε M h)

/-- In particular, improper Euclidean maps cannot have infinitely many contacts. -/
theorem graphSymmetry_determinant (M : RigidCoefficients) (h : IsGraphSymmetry M) :
    M.a * M.d - M.b * M.c = 1 := by
  rcases h with ⟨hb, hc, hu, hv, hsign⟩
  rcases hsign with ⟨ha, hd⟩ | ⟨ha, hd⟩ <;> simp [hb, hc, ha, hd]

theorem improper_coincidence_finite (ε : ℝ) (hε : ε ≠ 0)
    (M : RigidCoefficients) (hM : M.a * M.d - M.b * M.c = -1) :
    (coincidenceParameters ε M).Finite := by
  apply finite_coincidence_of_not_symmetry ε hε M
  intro h
  have hd := graphSymmetry_determinant M h
  linarith

end
end LiteralPlanar.Quintic
