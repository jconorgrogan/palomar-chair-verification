module

public import PhysicalRegistration.PoseRealization
public import RegisteredPrime.FrameBridge
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section

/-! The historical inversion-count properness condition agrees exactly with
properness of the literal Euclidean realization. -/
namespace PhysicalRegistration.NativeChair
noncomputable section

/-- Mathlib's permutation sign is its finite inversion product. -/
theorem permutation_sign_eq_signAux {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.sign = σ.signAux := by
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq ↦ ?_
  rw [Equiv.Perm.signAux_mul, Equiv.Perm.sign_mul, h_eq, Equiv.Perm.sign_swap hne,
    Equiv.Perm.signAux_swap hne]

/-- Exact comparison with the recovered source's list of inversion pairs. -/
theorem registered_permSign_eq {m : ℕ}
    (F : RegisteredPrime.RegisteredFrame (m+1)) :
    Uniform.permSign (m+1) F.toUniform.perm = ((rowPermutation F).sign : ℤ) := by
  rw [permutation_sign_eq_signAux]
  unfold Equiv.Perm.signAux
  rw [Units.coe_prod]
  rw [Uniform.permSign, Uniform.invCount, ← Uniform.prod_signs]
  rw [← List.prod_toFinset _ (Uniform.nodup_pairs (m+1))]
  symm
  refine Finset.prod_bij (fun q _ => (q.2.val, q.1.val)) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [List.mem_toFinset, Uniform.mem_pairs]
    exact ⟨Equiv.Perm.mem_finPairsLT.mp hq, q.1.isLt⟩
  · intro q hq r hr h
    have h1 : q.1 = r.1 := Fin.ext (congrArg Prod.snd h)
    have h2 : q.2 = r.2 := Fin.ext (congrArg Prod.fst h)
    cases q; cases r
    simp_all
  · intro q hq
    have h := Uniform.mem_pairs.mp (List.mem_toFinset.mp hq)
    refine ⟨⟨⟨q.2, h.2⟩, ⟨q.1, lt_trans h.1 h.2⟩⟩, ?_, rfl⟩
    exact Equiv.Perm.mem_finPairsLT.mpr h.1
  · intro q hq
    have hne : F.perm q.1 ≠ F.perm q.2 := by
      intro he
      have hx := congrArg F.inverse he
      simp only [F.left_inverse] at hx
      exact (ne_of_gt (Equiv.Perm.mem_finPairsLT.mp hq)) hx
    simp only [RegisteredPrime.RegisteredFrame.toUniform, q.1.isLt, q.2.isLt,
      dite_true, rowPermutation, Equiv.coe_fn_mk, decide_eq_true_eq, Fin.eta]
    rcases lt_or_gt_of_ne hne with h | h
    · have hv : (F.perm q.1).val < (F.perm q.2).val := h
      simp [le_of_lt h, hv]
    · have hv : ¬ (F.perm q.1).val < (F.perm q.2).val := not_lt_of_gt h
      simp [not_le_of_gt h, hv]


/-- The historical list product is exactly the product of row signs. -/
theorem registered_signProd_eq {m : ℕ}
    (F : RegisteredPrime.RegisteredFrame (m+1)) :
    Uniform.signProd (m+1) F.toUniform.neg = ∏ i, F.sign i := by
  unfold Uniform.signProd
  rw [← List.prod_toFinset _ (List.nodup_range), List.toFinset_range,
    ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  simp only [RegisteredPrime.RegisteredFrame.toUniform, RegisteredPrime.extendMask,
    i.isLt, dite_true, Fin.eta, RegisteredPrime.RegisteredFrame.sign]

/-- The recovered total natural-number map is indeed a permutation on its bound. -/
theorem registered_toUniform_isPermOn {m : ℕ}
    (F : RegisteredPrime.RegisteredFrame (m+1)) :
    Uniform.IsPermOn (m+1) F.toUniform.perm := by
  constructor
  · intro i hi
    simpa only [RegisteredPrime.RegisteredFrame.toUniform, hi, dite_true]
      using (F.perm ⟨i, hi⟩).isLt
  · intro i j hi hj hij
    simp only [RegisteredPrime.RegisteredFrame.toUniform, hi, hj, dite_true] at hij
    have h := congrArg F.inverse (Fin.ext hij)
    simpa only [F.left_inverse, Fin.mk.injEq] using h

/-- Literal standard-coordinate matrix of the signed row action. -/
theorem registeredFrameIsometry_matrix {m : ℕ}
    (F : RegisteredPrime.RegisteredFrame (m+1)) :
    ambientMatrix (registeredFrameIsometry F).toLinearMap =
      Matrix.of (fun i j => (F.sign i : ℝ) *
        ((1 : Matrix (Fin (m+1)) (Fin (m+1)) ℝ).submatrix (rowPermutation F) id) i j) := by
  ext i j
  simp [ambientMatrix, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    registeredFrameIsometry_apply, Matrix.one_apply, rowPermutation, eq_comm]

/-- The actual Euclidean determinant is the exact historical integer sign. -/
theorem registeredFrameIsometry_det {m : ℕ}
    (F : RegisteredPrime.RegisteredFrame (m+1)) :
    LinearMap.det (registeredFrameIsometry F).toLinearMap =
      ((Uniform.permSign (m+1) F.toUniform.perm *
        Uniform.signProd (m+1) F.toUniform.neg : ℤ) : ℝ) := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin (m+1)))]
  change (ambientMatrix (registeredFrameIsometry F).toLinearMap).det = _
  rw [registeredFrameIsometry_matrix, Matrix.det_mul_column, Matrix.det_permute,
    Matrix.det_one, mul_one, registered_permSign_eq, registered_signProd_eq]
  push_cast
  ring

/-- Affine translation has no effect on the realized linear part. -/
theorem poseIsometry_linear {m : ℕ} (q : RegisteredPrime.Pose (m+1)) :
    (poseIsometry q).toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap =
      (registeredFrameIsometry q.frame).toLinearMap := by
  apply LinearMap.ext
  intro x
  ext i
  have h := congrArg (fun y : Space m => y i) (placedNormal_eq_sub_zero (poseIsometry q) x)
  change placedNormal (poseIsometry q) x i = registeredFrameIsometry q.frame x i
  simpa [poseIsometry_apply, registeredFrameIsometry_apply] using h

/-- Historical combinatorial properness and actual positive determinant agree. -/
theorem poseIsometry_isProper_iff {m : ℕ} (q : RegisteredPrime.Pose (m+1)) :
    IsProperPlacement (poseIsometry q) ↔ q.frame.IsProper := by
  rw [IsProperPlacement, poseIsometry_linear, registeredFrameIsometry_det]
  unfold RegisteredPrime.RegisteredFrame.IsProper Uniform.IsRotation
  have hp := registered_toUniform_isPermOn q.frame
  constructor
  · intro h
    exact ⟨hp, by exact_mod_cast h⟩
  · rintro ⟨_, h⟩
    exact_mod_cast h

/-- Any actual realization inherits the same exact properness equivalence. -/
theorem RegisteredPoseRealizes.isProper_iff {m : ℕ}
    {q : RegisteredPrime.Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (h : RegisteredPoseRealizes q e) : IsProperPlacement e ↔ q.frame.IsProper := by
  rw [h.eq_poseIsometry]
  exact poseIsometry_isProper_iff q

end
end PhysicalRegistration.NativeChair
