module

public import ProductClosure.ProductGraphSites

@[expose] public section

/-! Literal left-type product sites and their complete active/passive axes. -/
namespace ProductClosure.ProductGraphRightSites
noncomputable section
open ProductGraphOrbit ProductGraphOrientation NativeCompiler
variable {a b : ℕ}

abbrev rightProductDim (a b : ℕ) : b+(a+1) = (a+b)+1 := by omega

def nativeRightProduct (S : Finset (Polycube.LatticeIndex (a+1)))
    (T : Finset (Polycube.LatticeIndex b)) : Finset (Polycube.LatticeIndex ((a+b)+1)) :=
  Polycube.castCells (rightProductDim a b) (Polycube.productCells T S)

def rightFacet {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (f : Polycube.Facet S) (c : Polycube.Cell T) :
    Polycube.Facet (nativeRightProduct S T) :=
  Polycube.castFacetEquiv (rightProductDim a b) _ (Polycube.productFacetRight c f)

def rightTangentEquiv (a b : ℕ) : (Fin a ⊕ Fin b) ≃ Fin (a+b) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (Nat.add_comm b a)))

def rightBlockToFrame (o : BlockOrbit a b) : Frame (a+b) :=
  ((rightTangentEquiv a b).symm.trans o.1).symm |> fun p =>
    (p, fun j => o.2 (o.1.symm j))

def rightSite {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) : Site (nativeRightProduct S T) :=
  (rightFacet u.1 c, rightBlockToFrame (assemble p u.2))

def appendRightNative (x : Space a) (y : Polycube.Space b) : Space (a+b) :=
  Polycube.castPoint (rightProductDim a b) (Polycube.appendPoint y x)

def rightAmbientEquiv (a b : ℕ) : (Fin (a+1) ⊕ Fin b) ≃ Fin ((a+b)+1) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (rightProductDim a b)))

@[simp] theorem appendRightNative_left (x : Space a) (y : Polycube.Space b) (i : Fin (a+1)) :
    appendRightNative x y (rightAmbientEquiv a b (.inl i)) = x i := by
  simp [appendRightNative, rightAmbientEquiv, Polycube.appendPoint]

@[simp] theorem appendRightNative_right (x : Space a) (y : Polycube.Space b) (j : Fin b) :
    appendRightNative x y (rightAmbientEquiv a b (.inr j)) = y j := by
  simp [appendRightNative, rightAmbientEquiv, Polycube.appendPoint]

theorem rightSuccAbove_active (i : Fin (a+1)) (j : Fin a) :
    (rightAmbientEquiv a b (.inl i)).succAbove (rightTangentEquiv a b (.inl j)) =
      rightAmbientEquiv a b (.inl (i.succAbove j)) := by
  apply Fin.ext
  simp only [Fin.succAbove]
  split_ifs with h1 h2 h2
  all_goals simp_all [rightAmbientEquiv, rightTangentEquiv, Fin.lt_def] <;> omega

theorem rightSuccAbove_passive (i : Fin (a+1)) (j : Fin b) :
    (rightAmbientEquiv a b (.inl i)).succAbove (rightTangentEquiv a b (.inr j)) =
      rightAmbientEquiv a b (.inr j) := by
  rw [Fin.succAbove_of_castSucc_lt]
  · apply Fin.ext
    simp [rightAmbientEquiv, rightTangentEquiv]
  · simp [rightAmbientEquiv, rightTangentEquiv, Fin.lt_def]
    omega

@[simp] theorem rightFacet_axis {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (f : Polycube.Facet S) (c : Polycube.Cell T) :
    (rightFacet f c).axis = rightAmbientEquiv a b (.inl f.axis) := by
  simp [rightFacet, rightAmbientEquiv, Polycube.productFacetRight]

@[simp] theorem rightFacet_positive {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (f : Polycube.Facet S) (c : Polycube.Cell T) :
    (rightFacet f c).positive = f.positive := by
  simp [rightFacet, Polycube.productFacetRight]

theorem appendRightNative_single_active (i : Fin (a+1)) (r : ℝ) :
    appendRightNative (EuclideanSpace.single i r) 0 =
      EuclideanSpace.single (rightAmbientEquiv a b (.inl i)) r := by
  ext k
  obtain ⟨j,rfl⟩ := (rightAmbientEquiv a b).surjective k
  cases j with
  | inl j => simp
  | inr j => simp

theorem appendRightNative_single_passive (j : Fin b) (r : ℝ) :
    appendRightNative 0 (EuclideanSpace.single j r) =
      EuclideanSpace.single (rightAmbientEquiv a b (.inr j)) r := by
  ext k
  obtain ⟨i,rfl⟩ := (rightAmbientEquiv a b).surjective k
  cases i with
  | inl i => simp
  | inr i => simp

theorem appendRightNative_smul (r : ℝ) (x : Space a) (y : Polycube.Space b) :
    appendRightNative (r • x) (r • y) = r • appendRightNative x y := by
  ext k
  obtain ⟨i,rfl⟩ := (rightAmbientEquiv a b).surjective k
  cases i <;> simp [PiLp.smul_apply]

theorem rightSite_normal {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    outward (rightSite u c p).1 = appendRightNative (outward u.1) 0 := by
  simp only [rightSite, outward, normalSign, normalIndex, rightFacet_axis, rightFacet_positive]
  rw [← appendRightNative_single_active]
  simpa only [smul_zero] using (appendRightNative_smul (sign u.1.positive)
    (EuclideanSpace.single u.1.axis 1) 0).symm

/-- Active full-orbit magnitude `rankLabels p k` really has the factor's kth
complete signed tangent column, regardless of interleaving with passive labels. -/
theorem rightSite_axis_active {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) (k : Fin a) :
    siteAxis (rightSite u c p) (rankLabels p k).val = appendRightNative (siteAxis u k) 0 := by
  have he : (assembledLabels p u.2).symm (rankLabels p k).val = .inl (u.2.1 k) := by
    apply (assembledLabels p u.2).injective
    simp
  simp only [siteAxis, rightSite, rightBlockToFrame, assemble, Equiv.symm_trans,
    Equiv.symm_symm, Equiv.trans_apply, he]
  simp only [Sum.elim_inl, Equiv.symm_apply_apply, tangentAxis, normalIndex,
    rightFacet_axis]
  rw [rightSuccAbove_active, ← appendRightNative_single_active]
  simpa only [smul_zero] using (appendRightNative_smul (sign (u.2.2 k))
    (EuclideanSpace.single (u.1.axis.succAbove (u.2.1 k)) 1) 0).symm

/-- Every passive tangent column is the literal signed passive coordinate
axis, and is independent of the active factor frame. -/
theorem rightSite_axis_passive {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) (j : Fin b) :
    siteAxis (rightSite u c p) (p.1 j) =
      appendRightNative 0 (sign (p.2 j) • EuclideanSpace.single j 1) := by
  have he : (assembledLabels p u.2).symm (p.1 j) = .inr j := by
    apply (assembledLabels p u.2).injective
    simp
  simp only [siteAxis, rightSite, rightBlockToFrame, assemble, Equiv.symm_trans,
    Equiv.symm_symm, Equiv.trans_apply, he]
  simp only [Sum.elim_inr, tangentAxis, normalIndex, rightFacet_axis]
  rw [rightSuccAbove_passive, ← appendRightNative_single_passive]
  simpa only [smul_zero] using (appendRightNative_smul (sign (p.2 j)) 0
    (EuclideanSpace.single j 1)).symm

def rightNativeColumnEquiv (a b : ℕ) :
    (Fin (a+1) ⊕ Fin b) ≃ (Fin (a+b) ⊕ Fin 1) :=
  (rightAmbientEquiv a b).trans finSumFinEquiv.symm

/-- The fixed column shuffle dictated by the actual passive magnitude tuple. -/
def rightPassiveColumnPerm {a b : ℕ} (p : Passive a b) :
    Equiv.Perm (Fin (a+1) ⊕ Fin b) :=
  (rightNativeColumnEquiv a b).trans
    (((assembledLabels p (Equiv.refl _, fun _ => true)).symm.sumCongr (Equiv.refl _)).trans
      (blockColumnEquiv a b))

def rightPassiveColumnSign {a b : ℕ} (p : Passive a b) (j : Fin (a+1) ⊕ Fin b) : ℝ :=
  match rightPassiveColumnPerm p j with
  | .inl _ => 1
  | .inr k => sign (p.2 k)

@[simp] theorem rightPassiveColumnSign_sq {a b : ℕ} (p : Passive a b)
    (j : Fin (a+1) ⊕ Fin b) : rightPassiveColumnSign p j * rightPassiveColumnSign p j = 1 := by
  unfold rightPassiveColumnSign
  split
  · norm_num
  · exact sign_mul_self _

/-- Concrete signed permutation matrix, containing no active geometry. -/
def rightPassiveMatrix {a b : ℕ} (p : Passive a b) :
    Matrix (Fin (a+1) ⊕ Fin b) (Fin (a+1) ⊕ Fin b) ℝ :=
  fun i j => if i = rightPassiveColumnPerm p j then rightPassiveColumnSign p j else 0

theorem rightPassiveMatrix_orthogonal {a b : ℕ} (p : Passive a b) :
    (rightPassiveMatrix p).transpose * rightPassiveMatrix p = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rightPassiveMatrix]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hij : i = j
  · subst j
    simp [Matrix.one_apply]
  · have hp : rightPassiveColumnPerm p i ≠ rightPassiveColumnPerm p j :=
      fun h => hij ((rightPassiveColumnPerm p).injective h)
    simp [hp, Matrix.one_apply, hij]

theorem rightPassiveMatrix_det_sign {a b : ℕ} (p : Passive a b) :
    (rightPassiveMatrix p).det = 1 ∨ (rightPassiveMatrix p).det = -1 := by
  have hd := congrArg Matrix.det (rightPassiveMatrix_orthogonal p)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  rcases eq_or_ne (rightPassiveMatrix p).det 1 with h | h
  · exact Or.inl h
  · right
    have hf : ((rightPassiveMatrix p).det - 1) * ((rightPassiveMatrix p).det + 1) = 0 := by nlinarith
    have := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr h)
    linarith

/-- Product-frame columns described directly: active columns come from the
whole active frame, while passive columns are signed passive coordinate axes. -/
def rightAssembledNativeMatrix {a b : ℕ} (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)
    (p : Passive a b) : Matrix (Fin (a+1) ⊕ Fin b) (Fin (a+1) ⊕ Fin b) ℝ :=
  fun i j => match rightPassiveColumnPerm p j with
  | .inl k => match i with | .inl l => U l k | .inr _ => 0
  | .inr k => match i with | .inl _ => 0 | .inr l => if l = k then rightPassiveColumnSign p j else 0

theorem rightAssembledNativeMatrix_factorization {a b : ℕ}
    (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) (p : Passive a b) :
    rightAssembledNativeMatrix U p = Matrix.fromBlocks U 0 0 1 * rightPassiveMatrix p := by
  ext i j
  simp only [Matrix.mul_apply, rightPassiveMatrix, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold rightAssembledNativeMatrix rightPassiveColumnSign
  split <;> cases i <;> simp_all [Matrix.fromBlocks, Matrix.one_apply]

theorem rightAssembledNativeMatrix_det {a b : ℕ}
    (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) (p : Passive a b) :
    (rightAssembledNativeMatrix U p).det = U.det * (rightPassiveMatrix p).det := by
  rw [rightAssembledNativeMatrix_factorization, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

def rightPassiveOrientation {a b : ℕ} (p : Passive a b) : ℤ := detOrientation (rightPassiveMatrix p)

theorem rightPassiveOrientation_sign {a b : ℕ} (p : Passive a b) :
    rightPassiveOrientation p = 1 ∨ rightPassiveOrientation p = -1 := by
  unfold rightPassiveOrientation detOrientation
  split_ifs <;> simp

/-- The passive sign is derived from its explicit signed column permutation.
No orientation-pullback certificate is supplied. -/
theorem rightAssembledNativeMatrix_orientation {a b : ℕ}
    (U : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) (p : Passive a b)
    (hU : U.det = 1 ∨ U.det = -1) :
    detOrientation (rightAssembledNativeMatrix U p) = rightPassiveOrientation p * detOrientation U := by
  rcases hU with hU | hU <;>
    rcases rightPassiveMatrix_det_sign p with hp | hp <;>
    norm_num [detOrientation, rightPassiveOrientation, rightAssembledNativeMatrix_det, hU, hp]

/-- Specialization to the literal active native frame determinant. -/
theorem right_native_active_orientation {a b : ℕ}
    {S : Finset (Polycube.LatticeIndex (a+1))} (u : NativeCompiler.Site S) (p : Passive a b) :
    detOrientation (rightAssembledNativeMatrix (NativeCompiler.frameMatrix u) p) =
      rightPassiveOrientation p * NativeCompiler.orientation u := by
  exact rightAssembledNativeMatrix_orientation _ p (NativeCompiler.frameMatrix_det_sign u)


@[simp] theorem rightPassiveColumnPerm_active (p : Passive a b) (k : Fin a) :
    rightPassiveColumnPerm p ((rightAmbientEquiv a b).symm (rankLabels p k).val.castSucc) =
      .inl k.castSucc := by
  have he : (assembledLabels p (Equiv.refl _, fun _ => true)).symm (rankLabels p k).val =
      .inl k := by
    apply (assembledLabels p (Equiv.refl _, fun _ => true)).injective
    simp
  simp [rightPassiveColumnPerm, rightNativeColumnEquiv, rightAmbientEquiv, he, blockColumnEquiv]

@[simp] theorem rightPassiveColumnPerm_passive (p : Passive a b) (j : Fin b) :
    rightPassiveColumnPerm p ((rightAmbientEquiv a b).symm (p.1 j).castSucc) = .inr j := by
  have he : (assembledLabels p (Equiv.refl _, fun _ => true)).symm (p.1 j) = .inr j := by
    apply (assembledLabels p (Equiv.refl _, fun _ => true)).injective
    simp
  simp [rightPassiveColumnPerm, rightNativeColumnEquiv, rightAmbientEquiv, he, blockColumnEquiv]

@[simp] theorem rightPassiveColumnPerm_normal (p : Passive a b) :
    rightPassiveColumnPerm p ((rightAmbientEquiv a b).symm (Fin.last (a+b))) = .inl (Fin.last a) := by
  simp [rightPassiveColumnPerm, rightNativeColumnEquiv, blockColumnEquiv]

/-- The determinant matrix used for the passive twist is literally the full
native product-site frame matrix, after the standard block coordinate reindex.
This closes the geometric binding; no orientation equivalence is assumed. -/
theorem rightSite_frameMatrix {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    (frameMatrix (rightSite u c p)).submatrix (rightAmbientEquiv a b) (rightAmbientEquiv a b) =
      rightAssembledNativeMatrix (frameMatrix u) p := by
  ext row col
  obtain ⟨j,rfl⟩ := (rightAmbientEquiv a b).symm.surjective col
  induction j using Fin.lastCases with
  | last =>
    cases row <;>
      simp [Matrix.submatrix, frameMatrix, rightSite_normal, rightAssembledNativeMatrix]
  | cast j =>
    obtain ⟨i,hi⟩ := (assembledLabels p (Equiv.refl _, fun _ => true)).surjective j
    rw [← hi]
    cases i with
    | inl i =>
      simp only [assembledLabels_inl, Equiv.refl_symm, Equiv.refl_apply]
      cases row <;>
        simp [Matrix.submatrix, frameMatrix, rightSite_axis_active, rightAssembledNativeMatrix]
    | inr k =>
      simp only [assembledLabels_inr]
      cases row <;>
        simp [Matrix.submatrix, frameMatrix, rightSite_axis_passive, rightAssembledNativeMatrix,
          rightPassiveColumnSign, PiLp.smul_apply]

/-- Actual determinant orientation of every literal left product site is the
factor orientation times the explicitly constructed passive-orbit sign. -/
theorem rightSite_orientation {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    orientation (rightSite u c p) = rightPassiveOrientation p * orientation u := by
  have hd := congrArg Matrix.det (rightSite_frameMatrix u c p)
  rw [Matrix.det_submatrix_equiv_self] at hd
  change detOrientation (frameMatrix (rightSite u c p)) = _
  unfold detOrientation
  rw [hd]
  exact right_native_active_orientation u p

#print axioms rightSite_frameMatrix
#print axioms rightSite_orientation
#print axioms rightSite_axis_active
#print axioms rightSite_axis_passive
#print axioms rightSite_normal
end
end ProductClosure.ProductGraphRightSites
