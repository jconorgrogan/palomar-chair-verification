module

public import ProductClosure.PolycubeDimensionCast
public import ProductClosure.ProductGraphOrientation

@[expose] public section

/-! Literal left-type product sites and their complete active/passive axes. -/
namespace ProductClosure.ProductGraphSites
noncomputable section
open ProductGraphOrbit ProductGraphOrientation NativeCompiler
variable {a b : ℕ}

abbrev productDim (a b : ℕ) : (a+1)+b = (a+b)+1 := by omega

def nativeProduct (S : Finset (Polycube.LatticeIndex (a+1)))
    (T : Finset (Polycube.LatticeIndex b)) : Finset (Polycube.LatticeIndex ((a+b)+1)) :=
  Polycube.castCells (productDim a b) (Polycube.productCells S T)

def leftFacet {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (f : Polycube.Facet S) (c : Polycube.Cell T) :
    Polycube.Facet (nativeProduct S T) :=
  Polycube.castFacetEquiv (productDim a b) _ (Polycube.productFacetLeft f c)

def leftSite {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) : Site (nativeProduct S T) :=
  (leftFacet u.1 c, blockToFrame (assemble p u.2))

def appendNative (x : Space a) (y : Polycube.Space b) : Space (a+b) :=
  Polycube.castPoint (productDim a b) (Polycube.appendPoint x y)

def ambientEquiv (a b : ℕ) : (Fin (a+1) ⊕ Fin b) ≃ Fin ((a+b)+1) :=
  finSumFinEquiv.trans (finCongr (productDim a b))

@[simp] theorem appendNative_left (x : Space a) (y : Polycube.Space b) (i : Fin (a+1)) :
    appendNative x y (ambientEquiv a b (.inl i)) = x i := by
  simp [appendNative, ambientEquiv, Polycube.appendPoint]

@[simp] theorem appendNative_right (x : Space a) (y : Polycube.Space b) (j : Fin b) :
    appendNative x y (ambientEquiv a b (.inr j)) = y j := by
  simp [appendNative, ambientEquiv, Polycube.appendPoint]

theorem succAbove_active (i : Fin (a+1)) (j : Fin a) :
    (ambientEquiv a b (.inl i)).succAbove (Fin.castAdd b j) =
      ambientEquiv a b (.inl (i.succAbove j)) := by
  apply Fin.ext
  simp only [Fin.succAbove]
  split_ifs with h1 h2 h2
  all_goals simp_all [ambientEquiv, Fin.lt_def] <;> omega

theorem succAbove_passive (i : Fin (a+1)) (j : Fin b) :
    (ambientEquiv a b (.inl i)).succAbove (Fin.natAdd a j) =
      ambientEquiv a b (.inr j) := by
  rw [Fin.succAbove_of_le_castSucc]
  · apply Fin.ext
    simp [ambientEquiv]
    omega
  · simp [ambientEquiv, Fin.le_def]
    omega

@[simp] theorem leftFacet_axis {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (f : Polycube.Facet S) (c : Polycube.Cell T) :
    (leftFacet f c).axis = ambientEquiv a b (.inl f.axis) := by
  simp [leftFacet, ambientEquiv, Polycube.productFacetLeft]

@[simp] theorem leftFacet_positive {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (f : Polycube.Facet S) (c : Polycube.Cell T) :
    (leftFacet f c).positive = f.positive := by
  simp [leftFacet, Polycube.productFacetLeft]

theorem appendNative_single_active (i : Fin (a+1)) (r : ℝ) :
    appendNative (EuclideanSpace.single i r) 0 =
      EuclideanSpace.single (ambientEquiv a b (.inl i)) r := by
  ext k
  obtain ⟨j,rfl⟩ := (ambientEquiv a b).surjective k
  cases j with
  | inl j => simp
  | inr j => simp

theorem appendNative_single_passive (j : Fin b) (r : ℝ) :
    appendNative 0 (EuclideanSpace.single j r) =
      EuclideanSpace.single (ambientEquiv a b (.inr j)) r := by
  ext k
  obtain ⟨i,rfl⟩ := (ambientEquiv a b).surjective k
  cases i with
  | inl i => simp
  | inr i => simp

theorem appendNative_smul (r : ℝ) (x : Space a) (y : Polycube.Space b) :
    appendNative (r • x) (r • y) = r • appendNative x y := by
  ext k
  obtain ⟨i,rfl⟩ := (ambientEquiv a b).surjective k
  cases i <;> simp [PiLp.smul_apply]

theorem leftSite_normal {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    outward (leftSite u c p).1 = appendNative (outward u.1) 0 := by
  simp only [leftSite, outward, normalSign, normalIndex, leftFacet_axis, leftFacet_positive]
  rw [← appendNative_single_active]
  simpa only [smul_zero] using (appendNative_smul (sign u.1.positive)
    (EuclideanSpace.single u.1.axis 1) 0).symm

/-- Active full-orbit magnitude `rankLabels p k` really has the factor's kth
complete signed tangent column, regardless of interleaving with passive labels. -/
theorem leftSite_axis_active {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) (k : Fin a) :
    siteAxis (leftSite u c p) (rankLabels p k).val = appendNative (siteAxis u k) 0 := by
  have he : (assembledLabels p u.2).symm (rankLabels p k).val = .inl (u.2.1 k) := by
    apply (assembledLabels p u.2).injective
    simp
  simp only [siteAxis, leftSite, blockToFrame, assemble, Equiv.symm_trans,
    Equiv.symm_symm, Equiv.trans_apply, he]
  simp only [Sum.elim_inl, Equiv.symm_apply_apply, tangentAxis, normalIndex,
    leftFacet_axis, finSumFinEquiv_apply_left]
  rw [succAbove_active, ← appendNative_single_active]
  simpa only [smul_zero] using (appendNative_smul (sign (u.2.2 k))
    (EuclideanSpace.single (u.1.axis.succAbove (u.2.1 k)) 1) 0).symm

/-- Every passive tangent column is the literal signed passive coordinate
axis, and is independent of the active factor frame. -/
theorem leftSite_axis_passive {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) (j : Fin b) :
    siteAxis (leftSite u c p) (p.1 j) =
      appendNative 0 (sign (p.2 j) • EuclideanSpace.single j 1) := by
  have he : (assembledLabels p u.2).symm (p.1 j) = .inr j := by
    apply (assembledLabels p u.2).injective
    simp
  simp only [siteAxis, leftSite, blockToFrame, assemble, Equiv.symm_trans,
    Equiv.symm_symm, Equiv.trans_apply, he]
  simp only [Sum.elim_inr, tangentAxis, normalIndex, leftFacet_axis, finSumFinEquiv_apply_right]
  rw [succAbove_passive, ← appendNative_single_passive]
  simpa only [smul_zero] using (appendNative_smul (sign (p.2 j)) 0
    (EuclideanSpace.single j 1)).symm

@[simp] theorem passiveColumnPerm_active (p : Passive a b) (k : Fin a) :
    passiveColumnPerm p ((ambientEquiv a b).symm (rankLabels p k).val.castSucc) =
      .inl k.castSucc := by
  have he : (assembledLabels p (Equiv.refl _, fun _ => true)).symm (rankLabels p k).val =
      .inl k := by
    apply (assembledLabels p (Equiv.refl _, fun _ => true)).injective
    simp
  simp [passiveColumnPerm, nativeColumnEquiv, ambientEquiv, he, blockColumnEquiv]

@[simp] theorem passiveColumnPerm_passive (p : Passive a b) (j : Fin b) :
    passiveColumnPerm p ((ambientEquiv a b).symm (p.1 j).castSucc) = .inr j := by
  have he : (assembledLabels p (Equiv.refl _, fun _ => true)).symm (p.1 j) = .inr j := by
    apply (assembledLabels p (Equiv.refl _, fun _ => true)).injective
    simp
  simp [passiveColumnPerm, nativeColumnEquiv, ambientEquiv, he, blockColumnEquiv]

@[simp] theorem passiveColumnPerm_normal (p : Passive a b) :
    passiveColumnPerm p ((ambientEquiv a b).symm (Fin.last (a+b))) = .inl (Fin.last a) := by
  simp [passiveColumnPerm, nativeColumnEquiv, ambientEquiv, blockColumnEquiv]

/-- The determinant matrix used for the passive twist is literally the full
native product-site frame matrix, after the standard block coordinate reindex.
This closes the geometric binding; no orientation equivalence is assumed. -/
theorem leftSite_frameMatrix {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    (frameMatrix (leftSite u c p)).submatrix (ambientEquiv a b) (ambientEquiv a b) =
      assembledNativeMatrix (frameMatrix u) p := by
  ext row col
  obtain ⟨j,rfl⟩ := (ambientEquiv a b).symm.surjective col
  induction j using Fin.lastCases with
  | last =>
    cases row <;>
      simp [Matrix.submatrix, frameMatrix, leftSite_normal, assembledNativeMatrix]
  | cast j =>
    obtain ⟨i,hi⟩ := (assembledLabels p (Equiv.refl _, fun _ => true)).surjective j
    rw [← hi]
    cases i with
    | inl i =>
      simp only [assembledLabels_inl, Equiv.refl_symm, Equiv.refl_apply]
      cases row <;>
        simp [Matrix.submatrix, frameMatrix, leftSite_axis_active, assembledNativeMatrix]
    | inr k =>
      simp only [assembledLabels_inr]
      cases row <;>
        simp [Matrix.submatrix, frameMatrix, leftSite_axis_passive, assembledNativeMatrix,
          passiveColumnSign, PiLp.smul_apply]
      rfl

/-- Actual determinant orientation of every literal left product site is the
factor orientation times the explicitly constructed passive-orbit sign. -/
theorem leftSite_orientation {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    orientation (leftSite u c p) = passiveOrientation p * orientation u := by
  have hd := congrArg Matrix.det (leftSite_frameMatrix u c p)
  rw [Matrix.det_submatrix_equiv_self] at hd
  change detOrientation (frameMatrix (leftSite u c p)) = _
  unfold detOrientation
  rw [hd]
  exact native_active_orientation u p

#print axioms leftSite_frameMatrix
#print axioms leftSite_orientation
#print axioms leftSite_axis_active
#print axioms leftSite_axis_passive
#print axioms leftSite_normal
end
end ProductClosure.ProductGraphSites
