module

public import PhysicalRegistration.NativeChair
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Orthogonal

@[expose] public section

/-! Determinant orientation of the literal full native key frame, with the
normal column last. Properness of a candidate relative map is a conclusion. -/
namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
noncomputable section

/-- Ordered tangent columns followed by the native outward normal. -/
def fullFrame {m : ℕ} (u : Site m) (j : Fin (m+1)) : Space m :=
  Fin.lastCases (outward u.1) (siteAxis u) j

@[simp] theorem fullFrame_last {m : ℕ} (u : Site m) :
    fullFrame u (Fin.last m) = outward u.1 := by simp [fullFrame]
@[simp] theorem fullFrame_castSucc {m : ℕ} (u : Site m) (j : Fin m) :
    fullFrame u j.castSucc = siteAxis u j := by simp [fullFrame]

theorem fullFrame_inner {m : ℕ} (u : Site m) (i j : Fin (m+1)) :
    ⟪fullFrame u i, fullFrame u j⟫_ℝ = if i = j then 1 else 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j =>
      simp only [fullFrame_last, fullFrame_castSucc]
      rw [real_inner_comm, siteAxis_outward_inner]
      simp [Ne.symm (Fin.castSucc_ne_last j)]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [siteAxis_inner]

/-- The matrix [I_f A_q,n_f] in the standard ambient coordinates. -/
def frameMatrix {m : ℕ} (u : Site m) : Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  fun i j => fullFrame u j i

theorem frameMatrix_transpose_mul {m : ℕ} (u : Site m) :
    (frameMatrix u).transpose * frameMatrix u = 1 := by
  ext i j
  have h := fullFrame_inner u j i
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [Matrix.mul_apply, frameMatrix, dotProduct, Matrix.one_apply, eq_comm] using h

theorem frameMatrix_det_sq {m : ℕ} (u : Site m) : (frameMatrix u).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (frameMatrix_transpose_mul u)
  simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using h

theorem frameMatrix_det_sign {m : ℕ} (u : Site m) :
    (frameMatrix u).det = 1 ∨ (frameMatrix u).det = -1 := by
  have h := frameMatrix_det_sq u
  rcases eq_or_ne (frameMatrix u).det 1 with he | hn
  · exact Or.inl he
  · right
    have hf : ((frameMatrix u).det - 1) * ((frameMatrix u).det + 1) = 0 := by nlinarith
    have := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hn)
    linarith

def orientation {m : ℕ} (u : Site m) : ℤ := if (frameMatrix u).det = 1 then 1 else -1

theorem orientation_sign {m : ℕ} (u : Site m) : orientation u = 1 ∨ orientation u = -1 := by
  unfold orientation
  split_ifs <;> simp

theorem orientation_cast {m : ℕ} (u : Site m) :
    (orientation u : ℝ) = (frameMatrix u).det := by
  rcases frameMatrix_det_sign u with h | h <;> norm_num [orientation, h]

theorem orientation_nonzero {m : ℕ} (u : Site m) : orientation u ≠ 0 := by
  rcases orientation_sign u with h | h <;> simp [h]

/-- Standard-coordinate matrix of an actual ambient linear map. -/
def ambientMatrix {m : ℕ} (L : Space m →ₗ[ℝ] Space m) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℝ :=
  LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin (m+1)))
    (PiLp.basisFun 2 ℝ (Fin (m+1))) L

theorem ambientMatrix_mul_frame {m : ℕ} (L : Space m →ₗ[ℝ] Space m) (u : Site m) :
    ambientMatrix L * frameMatrix u = fun i j => L (fullFrame u j) i := by
  ext i j
  have h := LinearMap.toMatrix_mulVec_repr (PiLp.basisFun 2 ℝ (Fin (m+1)))
    (PiLp.basisFun 2 ℝ (Fin (m+1))) L (fullFrame u j)
  have hh := congrFun h i
  simpa [ambientMatrix, frameMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    PiLp.basisFun_repr] using hh

/-- Exact orientation transport from tangent agreement and reversed normals.
No sign of det L is assumed; L need not even be supplied as an isometry. -/
theorem frame_matching_determinant {m : ℕ} (L : Space m →ₗ[ℝ] Space m)
    (u v : Site m) (ht : ∀ j, L (siteAxis v j) = siteAxis u j)
    (hn : L (outward v.1) = -outward u.1) :
    LinearMap.det L * (orientation v : ℝ) = -(orientation u : ℝ) := by
  let M := frameMatrix u
  have hm : ambientMatrix L * frameMatrix v =
      M.updateCol (Fin.last m) ((-1 : ℝ) • fun i => M i (Fin.last m)) := by
    rw [ambientMatrix_mul_frame]
    ext i j
    induction j using Fin.lastCases with
    | last => simp [M, frameMatrix, hn]
    | cast j => simp [M, frameMatrix, ht]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_updateCol_smul, Matrix.updateCol_eq_self] at hd
  rw [orientation_cast, orientation_cast]
  simpa [ambientMatrix, M, LinearMap.det_toMatrix] using hd

/-- Opposite coefficient orientation makes a geometrically matched relative
map proper. Properness is not an input certificate. -/
theorem proper_of_frame_matching {m : ℕ} (L : Space m →ₗ[ℝ] Space m)
    (u v : Site m) (ht : ∀ j, L (siteAxis v j) = siteAxis u j)
    (hn : L (outward v.1) = -outward u.1)
    (hχ : orientation v = -orientation u) : LinearMap.det L = 1 := by
  have hd := frame_matching_determinant L u v ht hn
  have hv : (orientation v : ℝ) ≠ 0 := by exact_mod_cast orientation_nonzero v
  have he : (orientation v : ℝ) = -(orientation u : ℝ) := by exact_mod_cast hχ
  rw [← he] at hd
  exact (mul_eq_right₀ hv).mp hd

end
end PhysicalRegistration.NativeChair
