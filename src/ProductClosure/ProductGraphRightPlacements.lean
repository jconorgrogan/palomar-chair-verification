module

public import ProductClosure.ProductGraphRightSites
public import ProductClosure.ProductGraphPlacements

@[expose] public section

/-! Actual Euclidean product placements and their complete native transports. -/
namespace ProductClosure.ProductGraphRightPlacements
noncomputable section
open ProductGraphRightSites ProductGraphOrbit NativeCompiler ProductGraphPlacements
variable {a b : ℕ}

/-- Euclidean (L², not supremum-norm) splitting of actual product coordinates. -/
def splitRightNative (a b : ℕ) :
    Space (a+b) ≃ₗᵢ[ℝ] WithLp 2 (Space a × Polycube.Space b) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (rightAmbientEquiv a b).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin (a+1) ⊕ Fin b => ℝ))

@[simp] theorem splitRightNative_append (x : Space a) (y : Polycube.Space b) :
    splitRightNative a b (appendRightNative x y) = WithLp.toLp 2 (x,y) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext i
    exact appendRightNative_left x y i
  · ext j
    exact appendRightNative_right x y j

@[simp] theorem splitRightNative_symm_pair (x : Space a) (y : Polycube.Space b) :
    (splitRightNative a b).symm (WithLp.toLp 2 (x,y)) = appendRightNative x y := by
  apply (splitRightNative a b).injective
  simp

/-- An unrestricted active isometry extended by the identity on the passive
Euclidean block, including its full affine translation. -/
def liftRight (g : Space a ≃ᵢ Space a) : Space (a+b) ≃ᵢ Space (a+b) :=
  (splitRightNative a b).toIsometryEquiv.trans
    ((IsometryEquiv.withLpProdCongr 2 g (IsometryEquiv.refl (Polycube.Space b))).trans
      (splitRightNative a b).symm.toIsometryEquiv)

@[simp] theorem liftRight_append (g : Space a ≃ᵢ Space a)
    (x : Space a) (y : Polycube.Space b) :
    liftRight (b := b) g (appendRightNative x y) = appendRightNative (g x) y := by
  simp [liftRight, IsometryEquiv.trans_apply]
  rfl

@[simp] theorem appendRightNative_zero : appendRightNative (0 : Space a) (0 : Polycube.Space b) = 0 := by
  ext k
  obtain ⟨j,rfl⟩ := (rightAmbientEquiv a b).surjective k
  cases j <;> simp

theorem appendRightNative_sub (x x' : Space a) (y y' : Polycube.Space b) :
    appendRightNative x y - appendRightNative x' y' = appendRightNative (x-x') (y-y') := by
  ext k
  obtain ⟨j,rfl⟩ := (rightAmbientEquiv a b).surjective k
  cases j <;> simp

@[simp] theorem placedNormal_liftRight (g : Space a ≃ᵢ Space a)
    (x : Space a) (y : Polycube.Space b) :
    placedNormal (liftRight g) (appendRightNative x y) = appendRightNative (placedNormal g x) y := by
  rw [placedNormal_eq_sub, ← appendRightNative_zero (a := a) (b := b), liftRight_append,
    liftRight_append, appendRightNative_sub, sub_zero, placedNormal_eq_sub]

theorem appendRightNative_injective : Function.Injective
    (fun z : Space a × Polycube.Space b => appendRightNative z.1 z.2) := by
  intro x y h
  apply Prod.ext
  · ext i
    simpa using congrArg (fun z => z (rightAmbientEquiv a b (.inl i))) h
  · ext j
    simpa using congrArg (fun z => z (rightAmbientEquiv a b (.inr j))) h

@[simp] theorem appendRightNative_eq_iff (x x' : Space a) (y y' : Polycube.Space b) :
    appendRightNative x y = appendRightNative x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    exact Prod.mk.inj (appendRightNative_injective h)
  · rintro ⟨rfl,rfl⟩
    rfl

@[simp] theorem appendRightNative_neg (x : Space a) (y : Polycube.Space b) :
    -appendRightNative x y = appendRightNative (-x) (-y) := by
  simpa using appendRightNative_sub (0 : Space a) x (0 : Polycube.Space b) y

@[simp] theorem rightSite_facetCenter {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    facetCenter (rightSite u c p).1 = appendRightNative (facetCenter u.1) (Polycube.latticeCenter c.val) := by
  change Polycube.facetCenter (Polycube.castFacetEquiv (rightProductDim a b) _ _) = _
  rw [Polycube.castFacetEquiv_center, Polycube.productFacetRight_center]
  rfl

/-- Every factor generator transports every full native orbit coset, rather
than just a convenient ordering of active and passive site labels. -/
theorem SiteTransport_liftRight {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c : Polycube.Cell T) (p : Passive a b)
    (h : SiteTransport g u v) :
    SiteTransport (liftRight g) (rightSite u c p) (rightSite v c p) := by
  have ht : ∀ j, placedNormal (liftRight g) (siteAxis (rightSite v c p) j) =
      siteAxis (rightSite u c p) j := by
    intro j
    obtain ⟨i,hi⟩ := (assembledLabels p (Equiv.refl _, fun _ => true)).surjective j
    rw [← hi]
    cases i with
    | inl k => simp only [assembledLabels_inl, Equiv.refl_symm, Equiv.refl_apply,
        rightSite_axis_active, placedNormal_liftRight, h.1]
    | inr k =>
      rw [assembledLabels_inr, rightSite_axis_passive, rightSite_axis_passive, placedNormal_liftRight]
      simp [placedNormal]
  refine ⟨ht, ?_, siteCenter_transport_of_facet (liftRight g) _ _ ht ?_⟩
  · rw [rightSite_normal, rightSite_normal, placedNormal_liftRight, h.2.1, appendRightNative_neg, neg_zero]
  · rw [rightSite_facetCenter, rightSite_facetCenter, liftRight_append, transport_facetCenter h]

/-- Full product native equations in any one fixed passive copy recover the
factor's complete native equations, including the site-center placement. -/
theorem SiteTransport_of_liftRight {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c d : Polycube.Cell T) (p : Passive a b)
    (h : SiteTransport (liftRight g) (rightSite u c p) (rightSite v d p)) :
    SiteTransport g u v ∧ c = d := by
  have ht : ∀ k, placedNormal g (siteAxis v k) = siteAxis u k := by
    intro k
    have hh := h.1 (rankLabels p k).val
    rw [rightSite_axis_active, rightSite_axis_active, placedNormal_liftRight] at hh
    exact (appendRightNative_eq_iff _ _ _ _).mp hh |>.1
  have hn : placedNormal g (outward v.1) = -outward u.1 := by
    have hh := h.2.1
    rw [rightSite_normal, rightSite_normal, placedNormal_liftRight, appendRightNative_neg, neg_zero] at hh
    exact (appendRightNative_eq_iff _ _ _ _).mp hh |>.1
  have hh := transport_facetCenter h
  rw [rightSite_facetCenter, rightSite_facetCenter, liftRight_append] at hh
  obtain ⟨hc,hd⟩ := (appendRightNative_eq_iff _ _ _ _).mp hh
  refine ⟨⟨ht,hn,siteCenter_transport_of_facet g u v ht hc⟩, ?_⟩
  apply Subtype.ext
  funext j
  have hj := congrArg (fun x : Polycube.Space b => x j) hd
  simp only [Polycube.latticeCenter] at hj
  exact_mod_cast (by linarith : (c.val j : ℝ) = d.val j)

/-- Full tangent-frame transport by a block placement recovers the passive
signed magnitude tuple. Even interleaved global labels cannot change copy. -/
theorem passive_eq_of_liftRight_tangents
    {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c d : Polycube.Cell T) (p q : Passive a b)
    (ht : ∀ k, placedNormal (liftRight g) (siteAxis (rightSite v d q) k) =
      siteAxis (rightSite u c p) k) : p = q := by
  have hj : ∀ j, p.1 j = q.1 j ∧ p.2 j = q.2 j := by
    intro j
    have hs := ht (q.1 j)
    rw [rightSite_axis_passive, placedNormal_liftRight] at hs
    have hz : placedNormal g 0 = 0 := by simp [placedNormal]
    rw [hz] at hs
    obtain ⟨i,hi⟩ := (assembledLabels p (Equiv.refl _, fun _ => true)).surjective (q.1 j)
    rw [← hi] at hs
    cases i with
    | inl k =>
      simp only [assembledLabels_inl, Equiv.refl_symm, Equiv.refl_apply,
        rightSite_axis_active] at hs
      have he := congrArg (fun x => x (rightAmbientEquiv a b (.inr j))) hs
      simp only [appendRightNative_right, PiLp.smul_apply, EuclideanSpace.single_apply,
        ite_true, mul_one, PiLp.zero_apply] at he
      cases hq : q.2 j <;> simp [sign,hq] at he
    | inr k =>
      simp only [assembledLabels_inr, rightSite_axis_passive] at hs
      have he := (appendRightNative_eq_iff _ _ _ _).mp hs |>.2
      have hk : k = j := by
        by_contra hne
        have hh := congrArg (fun x : Polycube.Space b => x j) he
        simp [PiLp.smul_apply, Ne.symm hne] at hh
        cases hq : q.2 j <;> simp [sign,hq] at hh
      subst k
      refine ⟨hi, ?_⟩
      have hh := congrArg (fun x : Polycube.Space b => x j) he
      simp only [PiLp.smul_apply, EuclideanSpace.single_apply, ite_true, mul_one] at hh
      cases hp : p.2 j <;> cases hq : q.2 j <;> simp [sign,hp,hq] at hh ⊢ <;> norm_num at hh
  apply Prod.ext
  · apply Function.Embedding.ext
    intro j
    exact (hj j).1
  · funext j
    exact (hj j).2

/-- Exact physical native transport pullback, including necessity of the
same occupied passive cell and the same full-orbit passive signed tuple. -/
theorem SiteTransport_liftRight_iff
    {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c d : Polycube.Cell T) (p q : Passive a b) :
    SiteTransport (liftRight g) (rightSite u c p) (rightSite v d q) ↔
      SiteTransport g u v ∧ c = d ∧ p = q := by
  constructor
  · intro h
    have hp := passive_eq_of_liftRight_tangents g u v c d p q h.1
    subst q
    have hh := SiteTransport_of_liftRight g u v c d p h
    exact ⟨hh.1,hh.2,rfl⟩
  · rintro ⟨h,rfl,rfl⟩
    exact SiteTransport_liftRight g u v c p h

/-- The lifted isometry's actual linear matrix is block diagonal in product
coordinates. This also derives properness rather than postulating it. -/
theorem liftRight_ambientMatrix (g : Space a ≃ᵢ Space a) :
    (ambientMatrix (liftRight (b := b) g).toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap).submatrix
      (rightAmbientEquiv a b) (rightAmbientEquiv a b) =
    Matrix.fromBlocks (ambientMatrix g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap) 0 0 1 := by
  ext i j
  simp only [Matrix.submatrix_apply, ambientMatrix_placed_apply]
  cases j with
  | inl j =>
    rw [← appendRightNative_single_active, placedNormal_liftRight]
    cases i <;> simp [Matrix.fromBlocks, ambientMatrix_placed_apply]
  | inr j =>
    rw [← appendRightNative_single_passive, placedNormal_liftRight]
    have hz : placedNormal g 0 = 0 := by simp [placedNormal]
    rw [hz]
    cases i <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem liftRight_determinant (g : Space a ≃ᵢ Space a) :
    LinearMap.det (liftRight (b := b) g).toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap =
      LinearMap.det g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap := by
  have hd := congrArg Matrix.det (liftRight_ambientMatrix (b := b) g)
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one] at hd
  simpa only [ambientMatrix, LinearMap.det_toMatrix] using hd

theorem liftRight_proper (g : Space a ≃ᵢ Space a) (hg : IsProperPlacement g) :
    IsProperPlacement (liftRight (b := b) g) := by
  change LinearMap.det _ = 1
  rw [liftRight_determinant]
  exact hg

#print axioms liftRight_determinant
#print axioms liftRight_proper
#print axioms passive_eq_of_liftRight_tangents
#print axioms SiteTransport_liftRight_iff
#print axioms SiteTransport_liftRight
#print axioms SiteTransport_of_liftRight
#print axioms liftRight_append
#print axioms placedNormal_liftRight
end
end ProductClosure.ProductGraphRightPlacements
