module

public import ProductClosure.ProductGraphOrbit
public import ProductClosure.NativeOrientation

@[expose] public section

/-!
# The passive orientation twist is constructed, not supplied

The passive label determines an explicit signed column permutation. Multiplying
an active native frame (with its normal last) by this fixed matrix reconstructs
the full mixed-label product frame. Its determinant is a fixed unit sign on
that passive orbit copy, independent of the active frame and facet.
-/
namespace ProductClosure.ProductGraphOrientation
noncomputable section
open ProductGraphOrbit PhysicalRegistration.NativeChair

/-- Active tangent, passive tangent, and normal columns rearranged into the
active ambient block followed by the passive block. -/
def blockColumnEquiv (a b : ℕ) :
    ((Fin a ⊕ Fin b) ⊕ Fin 1) ≃ (Fin (a+1) ⊕ Fin b) where
  toFun
    | .inl (.inl i) => .inl (Fin.castSucc i)
    | .inl (.inr j) => .inr j
    | .inr _ => .inl (Fin.last a)
  invFun
    | .inl i => Fin.lastCases (.inr 0) (fun j => .inl (.inl j)) i
    | .inr j => .inl (.inr j)
  left_inv := by
    rintro ((i | j) | k)
    · simp
    · rfl
    · have hk : k = 0 := Subsingleton.elim _ _
      subst k
      simp
  right_inv := by
    rintro (i | j)
    · induction i using Fin.lastCases <;> simp
    · rfl

/-- Native full column order, with the full normal column last. -/
def nativeColumnEquiv (a b : ℕ) :
    (Fin (a+1) ⊕ Fin b) ≃ (Fin (a+b) ⊕ Fin 1) :=
  finSumFinEquiv.trans ((finCongr (by omega : (a+1)+b = (a+b)+1)).trans
    finSumFinEquiv.symm)

/-- The fixed column shuffle dictated by the actual passive magnitude tuple. -/
def passiveColumnPerm {a b : ℕ} (p : Passive a b) :
    Equiv.Perm (Fin (a+1) ⊕ Fin b) :=
  (nativeColumnEquiv a b).trans
    (((assembledLabels p (Equiv.refl _, fun _ => true)).symm.sumCongr (Equiv.refl _)).trans
      (blockColumnEquiv a b))

def passiveColumnSign {a b : ℕ} (p : Passive a b) (j : Fin (a+1) ⊕ Fin b) : ℝ :=
  match passiveColumnPerm p j with
  | .inl _ => 1
  | .inr k => sign (p.2 k)

@[simp] theorem passiveColumnSign_sq {a b : ℕ} (p : Passive a b)
    (j : Fin (a+1) ⊕ Fin b) : passiveColumnSign p j * passiveColumnSign p j = 1 := by
  unfold passiveColumnSign
  split
  · norm_num
  · exact sign_mul_self _

/-- Concrete signed permutation matrix, containing no active geometry. -/
def passiveMatrix {a b : ℕ} (p : Passive a b) :
    Matrix (Fin (a+1) ⊕ Fin b) (Fin (a+1) ⊕ Fin b) ℝ :=
  fun i j => if i = passiveColumnPerm p j then passiveColumnSign p j else 0

theorem passiveMatrix_orthogonal {a b : ℕ} (p : Passive a b) :
    (passiveMatrix p).transpose * passiveMatrix p = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, passiveMatrix]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hij : i = j
  · subst j
    simp [Matrix.one_apply]
  · have hp : passiveColumnPerm p i ≠ passiveColumnPerm p j :=
      fun h => hij ((passiveColumnPerm p).injective h)
    simp [hp, Matrix.one_apply, hij]

theorem passiveMatrix_det_sign {a b : ℕ} (p : Passive a b) :
    (passiveMatrix p).det = 1 ∨ (passiveMatrix p).det = -1 := by
  have hd := congrArg Matrix.det (passiveMatrix_orthogonal p)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  rcases eq_or_ne (passiveMatrix p).det 1 with h | h
  · exact Or.inl h
  · right
    have hf : ((passiveMatrix p).det - 1) * ((passiveMatrix p).det + 1) = 0 := by nlinarith
    have := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr h)
    linarith

/-- Product-frame columns described directly: active columns come from the
whole active frame, while passive columns are signed passive coordinate axes. -/
def assembledNativeMatrix {a b : ℕ} (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)
    (p : Passive a b) : Matrix (Fin (a+1) ⊕ Fin b) (Fin (a+1) ⊕ Fin b) ℝ :=
  fun i j => match passiveColumnPerm p j with
  | .inl k => match i with | .inl l => U l k | .inr _ => 0
  | .inr k => match i with | .inl _ => 0 | .inr l => if l = k then passiveColumnSign p j else 0

theorem assembledNativeMatrix_factorization {a b : ℕ}
    (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) (p : Passive a b) :
    assembledNativeMatrix U p = Matrix.fromBlocks U 0 0 1 * passiveMatrix p := by
  ext i j
  simp only [Matrix.mul_apply, passiveMatrix, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold assembledNativeMatrix passiveColumnSign
  split <;> cases i <;> simp_all [Matrix.fromBlocks, Matrix.one_apply]

theorem assembledNativeMatrix_det {a b : ℕ}
    (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) (p : Passive a b) :
    (assembledNativeMatrix U p).det = U.det * (passiveMatrix p).det := by
  rw [assembledNativeMatrix_factorization, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- The actual integer orientation sign for a real unit determinant. -/
def detOrientation {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : ℤ :=
  if M.det = 1 then 1 else -1

theorem detOrientation_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.det = 1 ∨ M.det = -1) :
    (detOrientation M : ℝ) = M.det := by
  rcases hM with h | h <;> norm_num [detOrientation, h]

def passiveOrientation {a b : ℕ} (p : Passive a b) : ℤ := detOrientation (passiveMatrix p)

theorem passiveOrientation_sign {a b : ℕ} (p : Passive a b) :
    passiveOrientation p = 1 ∨ passiveOrientation p = -1 := by
  unfold passiveOrientation detOrientation
  split_ifs <;> simp

/-- The passive sign is derived from its explicit signed column permutation.
No orientation-pullback certificate is supplied. -/
theorem assembledNativeMatrix_orientation {a b : ℕ}
    (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) (p : Passive a b)
    (hU : U.det = 1 ∨ U.det = -1) :
    detOrientation (assembledNativeMatrix U p) = passiveOrientation p * detOrientation U := by
  rcases hU with hU | hU <;>
    rcases passiveMatrix_det_sign p with hp | hp <;>
    norm_num [detOrientation, passiveOrientation, assembledNativeMatrix_det, hU, hp]

/-- Specialization to the literal active native frame determinant. -/
theorem native_active_orientation {a b : ℕ}
    {S : Finset (Polycube.LatticeIndex (a+1))} (u : NativeCompiler.Site S) (p : Passive a b) :
    detOrientation (assembledNativeMatrix (NativeCompiler.frameMatrix u) p) =
      passiveOrientation p * NativeCompiler.orientation u := by
  exact assembledNativeMatrix_orientation _ p (NativeCompiler.frameMatrix_det_sign u)

#print axioms passiveMatrix_det_sign
#print axioms assembledNativeMatrix_orientation
#print axioms native_active_orientation
end
end ProductClosure.ProductGraphOrientation
