module

public import ProductClosure.ProductGraphSites
public import ProductClosure.NativeGraphCoefficients

@[expose] public section

/-! Actual Euclidean product placements and their complete native transports. -/
namespace ProductClosure.ProductGraphPlacements
noncomputable section
open ProductGraphSites ProductGraphOrbit NativeCompiler
variable {a b : ℕ}

/-- Euclidean (L², not supremum-norm) splitting of actual product coordinates. -/
def splitNative (a b : ℕ) :
    Space (a+b) ≃ₗᵢ[ℝ] WithLp 2 (Space a × Polycube.Space b) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (ambientEquiv a b).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin (a+1) ⊕ Fin b => ℝ))

@[simp] theorem splitNative_append (x : Space a) (y : Polycube.Space b) :
    splitNative a b (appendNative x y) = WithLp.toLp 2 (x,y) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext i
    exact appendNative_left x y i
  · ext j
    exact appendNative_right x y j

@[simp] theorem splitNative_symm_pair (x : Space a) (y : Polycube.Space b) :
    (splitNative a b).symm (WithLp.toLp 2 (x,y)) = appendNative x y := by
  apply (splitNative a b).injective
  simp

/-- An unrestricted active isometry extended by the identity on the passive
Euclidean block, including its full affine translation. -/
def liftLeft (g : Space a ≃ᵢ Space a) : Space (a+b) ≃ᵢ Space (a+b) :=
  (splitNative a b).toIsometryEquiv.trans
    ((IsometryEquiv.withLpProdCongr 2 g (IsometryEquiv.refl (Polycube.Space b))).trans
      (splitNative a b).symm.toIsometryEquiv)

@[simp] theorem liftLeft_append (g : Space a ≃ᵢ Space a)
    (x : Space a) (y : Polycube.Space b) :
    liftLeft (b := b) g (appendNative x y) = appendNative (g x) y := by
  simp [liftLeft, IsometryEquiv.trans_apply]
  rfl

@[simp] theorem appendNative_zero : appendNative (0 : Space a) (0 : Polycube.Space b) = 0 := by
  ext k
  obtain ⟨j,rfl⟩ := (ambientEquiv a b).surjective k
  cases j <;> simp

theorem appendNative_sub (x x' : Space a) (y y' : Polycube.Space b) :
    appendNative x y - appendNative x' y' = appendNative (x-x') (y-y') := by
  ext k
  obtain ⟨j,rfl⟩ := (ambientEquiv a b).surjective k
  cases j <;> simp

/-- The linear part supplied by Mazur--Ulam is the literal affine difference. -/
theorem placedNormal_eq_sub {m : ℕ} (g : Space m ≃ᵢ Space m) (x : Space m) :
    placedNormal g x = g x - g 0 := by
  have h := g.toRealAffineIsometryEquiv.map_vadd (0 : Space m) x
  change g (x + 0) = placedNormal g x + g 0 at h
  rw [add_zero] at h
  exact eq_sub_iff_add_eq.mpr h.symm

@[simp] theorem placedNormal_liftLeft (g : Space a ≃ᵢ Space a)
    (x : Space a) (y : Polycube.Space b) :
    placedNormal (liftLeft g) (appendNative x y) = appendNative (placedNormal g x) y := by
  rw [placedNormal_eq_sub, ← appendNative_zero (a := a) (b := b), liftLeft_append,
    liftLeft_append, appendNative_sub, sub_zero, placedNormal_eq_sub]

/-- Matching all tangent columns transports the entire native site offset. -/
theorem transport_siteOffset {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} {g : Space m ≃ᵢ Space m}
    {u v : Site S} (h : NativeCompiler.SiteTransport g u v) :
    placedNormal g (siteOffset v) = siteOffset u := by
  unfold siteOffset placedNormal
  simp only [map_sum, map_smul]
  congr 1
  funext j
  exact congrArg (fun x => q0 j • x) (h.1 j)

/-- The facet center is recovered, not imposed on the dense site equation. -/
theorem transport_facetCenter {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} {g : Space m ≃ᵢ Space m}
    {u v : Site S} (h : NativeCompiler.SiteTransport g u v) :
    g (facetCenter v.1) = facetCenter u.1 := by
  have hm := g.toRealAffineIsometryEquiv.map_vadd (facetCenter v.1) (siteOffset v)
  change g (siteOffset v + facetCenter v.1) = placedNormal g (siteOffset v) + g (facetCenter v.1) at hm
  rw [transport_siteOffset h, add_comm (siteOffset v), ← siteCenter, h.2.2, siteCenter] at hm
  exact add_left_cancel (hm.symm.trans (add_comm _ _))

/-- Conversely center and all tangent equations imply the site-center equation
for the literal full native orbit, whatever its ambient denominator. -/
theorem siteCenter_transport_of_facet {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} (g : Space m ≃ᵢ Space m)
    (u v : Site S) (ht : ∀ j, placedNormal g (siteAxis v j) = siteAxis u j)
    (hc : g (facetCenter v.1) = facetCenter u.1) : g (siteCenter v) = siteCenter u := by
  have ho : placedNormal g (siteOffset v) = siteOffset u := by
    unfold siteOffset placedNormal
    simp only [map_sum, map_smul]
    congr 1
    funext j
    exact congrArg (fun x => q0 j • x) (ht j)
  have hm := g.toRealAffineIsometryEquiv.map_vadd (facetCenter v.1) (siteOffset v)
  change g (siteOffset v + facetCenter v.1) = placedNormal g (siteOffset v) + g (facetCenter v.1) at hm
  simpa [siteCenter, add_comm, ho, hc] using hm

theorem appendNative_injective : Function.Injective
    (fun z : Space a × Polycube.Space b => appendNative z.1 z.2) := by
  intro x y h
  apply Prod.ext
  · ext i
    simpa using congrArg (fun z => z (ambientEquiv a b (.inl i))) h
  · ext j
    simpa using congrArg (fun z => z (ambientEquiv a b (.inr j))) h

@[simp] theorem appendNative_eq_iff (x x' : Space a) (y y' : Polycube.Space b) :
    appendNative x y = appendNative x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    exact Prod.mk.inj (appendNative_injective h)
  · rintro ⟨rfl,rfl⟩
    rfl

@[simp] theorem appendNative_neg (x : Space a) (y : Polycube.Space b) :
    -appendNative x y = appendNative (-x) (-y) := by
  simpa using appendNative_sub (0 : Space a) x (0 : Polycube.Space b) y

@[simp] theorem leftSite_facetCenter {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (u : Site S) (c : Polycube.Cell T)
    (p : Passive a b) :
    facetCenter (leftSite u c p).1 = appendNative (facetCenter u.1) (Polycube.latticeCenter c.val) := by
  change Polycube.facetCenter (Polycube.castFacetEquiv (productDim a b) _ _) = _
  rw [Polycube.castFacetEquiv_center, Polycube.productFacetLeft_center]
  rfl

/-- Every factor generator transports every full native orbit coset, rather
than just a convenient ordering of active and passive site labels. -/
theorem SiteTransport_liftLeft {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c : Polycube.Cell T) (p : Passive a b)
    (h : SiteTransport g u v) :
    SiteTransport (liftLeft g) (leftSite u c p) (leftSite v c p) := by
  have ht : ∀ j, placedNormal (liftLeft g) (siteAxis (leftSite v c p) j) =
      siteAxis (leftSite u c p) j := by
    intro j
    obtain ⟨i,hi⟩ := (assembledLabels p (Equiv.refl _, fun _ => true)).surjective j
    rw [← hi]
    cases i with
    | inl k => simp only [assembledLabels_inl, Equiv.refl_symm, Equiv.refl_apply,
        leftSite_axis_active, placedNormal_liftLeft, h.1]
    | inr k =>
      rw [assembledLabels_inr, leftSite_axis_passive, leftSite_axis_passive, placedNormal_liftLeft]
      simp [placedNormal]
  refine ⟨ht, ?_, siteCenter_transport_of_facet (liftLeft g) _ _ ht ?_⟩
  · rw [leftSite_normal, leftSite_normal, placedNormal_liftLeft, h.2.1, appendNative_neg, neg_zero]
  · rw [leftSite_facetCenter, leftSite_facetCenter, liftLeft_append, transport_facetCenter h]

/-- Full product native equations in any one fixed passive copy recover the
factor's complete native equations, including the site-center placement. -/
theorem SiteTransport_of_liftLeft {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c d : Polycube.Cell T) (p : Passive a b)
    (h : SiteTransport (liftLeft g) (leftSite u c p) (leftSite v d p)) :
    SiteTransport g u v ∧ c = d := by
  have ht : ∀ k, placedNormal g (siteAxis v k) = siteAxis u k := by
    intro k
    have hh := h.1 (rankLabels p k).val
    rw [leftSite_axis_active, leftSite_axis_active, placedNormal_liftLeft] at hh
    exact (appendNative_eq_iff _ _ _ _).mp hh |>.1
  have hn : placedNormal g (outward v.1) = -outward u.1 := by
    have hh := h.2.1
    rw [leftSite_normal, leftSite_normal, placedNormal_liftLeft, appendNative_neg, neg_zero] at hh
    exact (appendNative_eq_iff _ _ _ _).mp hh |>.1
  have hh := transport_facetCenter h
  rw [leftSite_facetCenter, leftSite_facetCenter, liftLeft_append] at hh
  obtain ⟨hc,hd⟩ := (appendNative_eq_iff _ _ _ _).mp hh
  refine ⟨⟨ht,hn,siteCenter_transport_of_facet g u v ht hc⟩, ?_⟩
  apply Subtype.ext
  funext j
  have hj := congrArg (fun x : Polycube.Space b => x j) hd
  simp only [Polycube.latticeCenter] at hj
  exact_mod_cast (by linarith : (c.val j : ℝ) = d.val j)

/-- Full tangent-frame transport by a block placement recovers the passive
signed magnitude tuple. Even interleaved global labels cannot change copy. -/
theorem passive_eq_of_liftLeft_tangents
    {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c d : Polycube.Cell T) (p q : Passive a b)
    (ht : ∀ k, placedNormal (liftLeft g) (siteAxis (leftSite v d q) k) =
      siteAxis (leftSite u c p) k) : p = q := by
  have hj : ∀ j, p.1 j = q.1 j ∧ p.2 j = q.2 j := by
    intro j
    have hs := ht (q.1 j)
    rw [leftSite_axis_passive, placedNormal_liftLeft] at hs
    have hz : placedNormal g 0 = 0 := by simp [placedNormal]
    rw [hz] at hs
    obtain ⟨i,hi⟩ := (assembledLabels p (Equiv.refl _, fun _ => true)).surjective (q.1 j)
    rw [← hi] at hs
    cases i with
    | inl k =>
      simp only [assembledLabels_inl, Equiv.refl_symm, Equiv.refl_apply,
        leftSite_axis_active] at hs
      have he := congrArg (fun x => x (ambientEquiv a b (.inr j))) hs
      simp only [appendNative_right, PiLp.smul_apply, EuclideanSpace.single_apply,
        ite_true, mul_one, PiLp.zero_apply] at he
      cases hq : q.2 j <;> simp [sign,hq] at he
    | inr k =>
      simp only [assembledLabels_inr, leftSite_axis_passive] at hs
      have he := (appendNative_eq_iff _ _ _ _).mp hs |>.2
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
theorem SiteTransport_liftLeft_iff
    {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)} (g : Space a ≃ᵢ Space a)
    (u v : Site S) (c d : Polycube.Cell T) (p q : Passive a b) :
    SiteTransport (liftLeft g) (leftSite u c p) (leftSite v d q) ↔
      SiteTransport g u v ∧ c = d ∧ p = q := by
  constructor
  · intro h
    have hp := passive_eq_of_liftLeft_tangents g u v c d p q h.1
    subst q
    have hh := SiteTransport_of_liftLeft g u v c d p h
    exact ⟨hh.1,hh.2,rfl⟩
  · rintro ⟨h,rfl,rfl⟩
    exact SiteTransport_liftLeft g u v c p h

theorem ambientMatrix_placed_apply {m : ℕ} (g : Space m ≃ᵢ Space m)
    (i j : Fin (m+1)) :
    ambientMatrix g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap i j =
      placedNormal g (EuclideanSpace.single j 1) i := by
  simp [ambientMatrix, LinearMap.toMatrix_apply, PiLp.basisFun_apply,
    PiLp.basisFun_repr, placedNormal]

/-- The lifted isometry's actual linear matrix is block diagonal in product
coordinates. This also derives properness rather than postulating it. -/
theorem liftLeft_ambientMatrix (g : Space a ≃ᵢ Space a) :
    (ambientMatrix (liftLeft (b := b) g).toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap).submatrix
      (ambientEquiv a b) (ambientEquiv a b) =
    Matrix.fromBlocks (ambientMatrix g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap) 0 0 1 := by
  ext i j
  simp only [Matrix.submatrix_apply, ambientMatrix_placed_apply]
  cases j with
  | inl j =>
    rw [← appendNative_single_active, placedNormal_liftLeft]
    cases i <;> simp [Matrix.fromBlocks, ambientMatrix_placed_apply]
  | inr j =>
    rw [← appendNative_single_passive, placedNormal_liftLeft]
    have hz : placedNormal g 0 = 0 := by simp [placedNormal]
    rw [hz]
    cases i <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem liftLeft_determinant (g : Space a ≃ᵢ Space a) :
    LinearMap.det (liftLeft (b := b) g).toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap =
      LinearMap.det g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap := by
  have hd := congrArg Matrix.det (liftLeft_ambientMatrix (b := b) g)
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one] at hd
  simpa only [ambientMatrix, LinearMap.det_toMatrix] using hd

theorem liftLeft_proper (g : Space a ≃ᵢ Space a) (hg : IsProperPlacement g) :
    IsProperPlacement (liftLeft (b := b) g) := by
  change LinearMap.det _ = 1
  rw [liftLeft_determinant]
  exact hg

#print axioms liftLeft_determinant
#print axioms liftLeft_proper
#print axioms passive_eq_of_liftLeft_tangents
#print axioms SiteTransport_liftLeft_iff
#print axioms SiteTransport_liftLeft
#print axioms SiteTransport_of_liftLeft
#print axioms liftLeft_append
#print axioms placedNormal_liftLeft
#print axioms transport_facetCenter
end
end ProductClosure.ProductGraphPlacements
