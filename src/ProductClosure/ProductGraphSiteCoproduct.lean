module

public import ProductClosure.ProductGraphRightPlacements

@[expose] public section

/-! Every literal native product site is in exactly one complete factor-orbit copy. -/
namespace ProductClosure.ProductGraphSiteCoproduct
noncomputable section
open NativeCompiler ProductGraphOrbit ProductGraphSites ProductGraphRightSites
open ProductGraphPlacements ProductGraphRightPlacements

variable {m n : ℕ}

def tangentCast (h : m = n) : Frame m ≃ Frame n := by subst n; exact Equiv.refl _

def facetCast (h : m = n) {S : Finset (Polycube.LatticeIndex (m+1))}
    {T : Finset (Polycube.LatticeIndex (n+1))}
    (hc : Polycube.castCells (congrArg (fun k => k+1) h) S = T) : Facet S ≃ Facet T := by
  subst n
  change S = T at hc
  subst T
  exact Equiv.refl _

def siteCast (h : m = n) {S : Finset (Polycube.LatticeIndex (m+1))}
    {T : Finset (Polycube.LatticeIndex (n+1))}
    (hc : Polycube.castCells (congrArg (fun k => k+1) h) S = T) : Site S ≃ Site T :=
  (facetCast h hc).prodCongr (tangentCast h)

def poseCast (h : m = n) (g : Space m ≃ᵢ Space m) : Space n ≃ᵢ Space n := by
  subst n
  exact g

@[simp] theorem siteCast_orientation (h : m = n) {S : Finset (Polycube.LatticeIndex (m+1))}
    {T : Finset (Polycube.LatticeIndex (n+1))}
    (hc : Polycube.castCells (congrArg (fun k => k+1) h) S = T) (u : Site S) :
    orientation (siteCast h hc u) = orientation u := by
  subst n
  change S = T at hc
  subst T
  rfl

@[simp] theorem SiteTransport_cast_iff (h : m = n) {S : Finset (Polycube.LatticeIndex (m+1))}
    {T : Finset (Polycube.LatticeIndex (n+1))}
    (hc : Polycube.castCells (congrArg (fun k => k+1) h) S = T)
    (g : Space m ≃ᵢ Space m) (u v : Site S) :
    SiteTransport (poseCast h g) (siteCast h hc u) (siteCast h hc v) ↔ SiteTransport g u v := by
  subst n
  change S = T at hc
  subst T
  rfl

@[simp] theorem poseCast_proper_iff (h : m = n) (g : Space m ≃ᵢ Space m) :
    IsProperPlacement (poseCast h g) ↔ IsProperPlacement g := by subst n; rfl

theorem facetCast_chain {d : ℕ} (h0 : d = m+1) (h : m = n) (h2 : d = n+1)
    (S : Finset (Polycube.LatticeIndex d))
    (hc : Polycube.castCells (congrArg (fun k => k+1) h) (Polycube.castCells h0 S) =
      Polycube.castCells h2 S) (f : Polycube.Facet S) :
    facetCast h hc (Polycube.castFacetEquiv h0 S f) = Polycube.castFacetEquiv h2 S f := by
  subst n
  subst d
  rfl

variable {a b : ℕ}

def rightFrameToBlock (F : Frame (a+b)) : BlockOrbit a b :=
  ((rightTangentEquiv a b).trans F.1.symm,
    fun i => F.2 (F.1.symm (rightTangentEquiv a b i)))

def rightFullFrameBlockEquiv (a b : ℕ) : Frame (a+b) ≃ BlockOrbit a b where
  toFun := rightFrameToBlock
  invFun := rightBlockToFrame
  left_inv F := by
    apply Prod.ext
    · ext j
      simp [rightFrameToBlock, rightBlockToFrame]
    · funext j
      simp [rightFrameToBlock, rightBlockToFrame]
  right_inv o := by
    apply Prod.ext
    · ext j
      simp [rightFrameToBlock, rightBlockToFrame]
    · funext j
      simp [rightFrameToBlock, rightBlockToFrame]

def leftFactorFrameEquiv (a b : ℕ) : (Frame a × Passive a b) ≃ Frame (a+b) :=
  (Equiv.prodComm _ _).trans (nativeFullOrbitCosetEquiv a b).symm

def rightFactorFrameEquiv (a b : ℕ) : (Frame a × Passive a b) ≃ Frame (a+b) :=
  (Equiv.prodComm _ _).trans ((rightFullFrameBlockEquiv a b).trans (blockOrbitCosetEquiv a b)).symm

@[simp] theorem leftFactorFrameEquiv_apply (F : Frame a) (p : Passive a b) :
    leftFactorFrameEquiv a b (F,p) = blockToFrame (assemble p F) := rfl
@[simp] theorem rightFactorFrameEquiv_apply (F : Frame a) (p : Passive a b) :
    rightFactorFrameEquiv a b (F,p) = rightBlockToFrame (assemble p F) := rfl

abbrev tangentSwap (a b : ℕ) : b+(a+1) = a+(b+1) := by omega

theorem castCells_trans {d e f : ℕ} (h : d = e) (k : e = f)
    (S : Finset (Polycube.LatticeIndex d)) :
    Polycube.castCells k (Polycube.castCells h S) = Polycube.castCells (h.trans k) S := by
  subst e
  subst f
  rfl

theorem nativeRightProduct_cast_eq (SA : Finset (Polycube.LatticeIndex (a+1)))
    (SB : Finset (Polycube.LatticeIndex (b+1))) :
    Polycube.castCells (congrArg (fun k => k+1) (tangentSwap a b)) (nativeRightProduct SB SA) =
      nativeProduct SA SB := by
  unfold nativeRightProduct nativeProduct
  rw [castCells_trans]

def commonRightSite {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}
    (u : Site SB) (c : Polycube.Cell SA) (p : Passive b (a+1)) : Site (nativeProduct SA SB) :=
  siteCast (tangentSwap a b) (nativeRightProduct_cast_eq SA SB) (rightSite u c p)

def commonLiftRight (g : Space b ≃ᵢ Space b) : Space (a+(b+1)) ≃ᵢ Space (a+(b+1)) :=
  poseCast (tangentSwap a b) (liftRight (b := a+1) g)

@[simp] theorem commonRightSite_orientation {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}
    (u : Site SB) (c : Polycube.Cell SA) (p : Passive b (a+1)) :
    orientation (commonRightSite u c p) = rightPassiveOrientation p * orientation u := by
  rw [commonRightSite, siteCast_orientation, rightSite_orientation]

theorem SiteTransport_commonLiftRight_iff {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))} (g : Space b ≃ᵢ Space b)
    (u v : Site SB) (c d : Polycube.Cell SA) (p q : Passive b (a+1)) :
    SiteTransport (commonLiftRight g) (commonRightSite u c p) (commonRightSite v d q) ↔
      SiteTransport g u v ∧ c = d ∧ p = q := by
  rw [commonLiftRight, commonRightSite, commonRightSite, SiteTransport_cast_iff,
    SiteTransport_liftRight_iff]

theorem castPoint_trans {d e f : ℕ} (h : d = e) (k : e = f)
    (x : Polycube.Space d) :
    Polycube.castPoint k (Polycube.castPoint h x) = Polycube.castPoint (h.trans k) x := by
  subst e
  subst f
  rfl

@[simp] theorem poseCast_apply (h : m = n) (g : Space m ≃ᵢ Space m) (x : Space m) :
    poseCast h g (Polycube.castPoint (congrArg (fun k => k+1) h) x) =
      Polycube.castPoint (congrArg (fun k => k+1) h) (g x) := by subst n; rfl

@[simp] theorem siteCast_facetCenter (h : m = n) {S : Finset (Polycube.LatticeIndex (m+1))}
    {T : Finset (Polycube.LatticeIndex (n+1))}
    (hc : Polycube.castCells (congrArg (fun k => k+1) h) S = T) (u : Site S) :
    facetCenter (siteCast h hc u).1 =
      Polycube.castPoint (congrArg (fun k => k+1) h) (facetCenter u.1) := by
  subst n
  change S = T at hc
  subst T
  rfl

@[simp] theorem siteCast_outward (h : m = n) {S : Finset (Polycube.LatticeIndex (m+1))}
    {T : Finset (Polycube.LatticeIndex (n+1))}
    (hc : Polycube.castCells (congrArg (fun k => k+1) h) S = T) (u : Site S) :
    outward (siteCast h hc u).1 =
      Polycube.castPoint (congrArg (fun k => k+1) h) (outward u.1) := by
  subst n
  change S = T at hc
  subst T
  rfl

/-- Both factor conventions describe the same literal ordered Euclidean
product coordinates after the harmless dimension reassociation. -/
@[simp] theorem cast_appendRightNative (x : Space a) (y : Space b) :
    Polycube.castPoint (congrArg (fun k => k+1) (tangentSwap a b))
      (appendRightNative y x) = appendNative x y := by
  unfold appendRightNative appendNative
  rw [castPoint_trans]

@[simp] theorem commonLiftRight_append (g : Space b ≃ᵢ Space b)
    (x : Space a) (y : Space b) : commonLiftRight g (appendNative x y) = appendNative x (g y) := by
  rw [commonLiftRight, ← cast_appendRightNative x y, poseCast_apply, liftRight_append,
    cast_appendRightNative]

@[simp] theorem commonRightSite_facetCenter {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}
    (u : Site SB) (c : Polycube.Cell SA) (p : Passive b (a+1)) :
    facetCenter (commonRightSite u c p).1 =
      appendNative (Polycube.latticeCenter c.val) (facetCenter u.1) := by
  rw [commonRightSite, siteCast_facetCenter, rightSite_facetCenter, cast_appendRightNative]

@[simp] theorem commonRightSite_normal {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}
    (u : Site SB) (c : Polycube.Cell SA) (p : Passive b (a+1)) :
    outward (commonRightSite u c p).1 = appendNative 0 (outward u.1) := by
  rw [commonRightSite, siteCast_outward, rightSite_normal, cast_appendRightNative]

variable (SA : Finset (Polycube.LatticeIndex (a+1))) (SB : Finset (Polycube.LatticeIndex (b+1)))

def leftPackedEquiv : (Site SA × (Polycube.Cell SB × Passive a (b+1))) ≃
    (Facet SA × Polycube.Cell SB) × Frame (a+(b+1)) where
  toFun p := ((p.1.1,p.2.1), leftFactorFrameEquiv a (b+1) (p.1.2,p.2.2))
  invFun q := ((q.1.1, ((leftFactorFrameEquiv a (b+1)).symm q.2).1),
    (q.1.2, ((leftFactorFrameEquiv a (b+1)).symm q.2).2))
  left_inv p := by
    rcases p with ⟨⟨f,F⟩,c,p⟩
    simp only [Equiv.symm_apply_apply]
  right_inv q := by
    rcases q with ⟨⟨f,c⟩,F⟩
    simp

def rightCommonFrameEquiv : (Frame b × Passive b (a+1)) ≃ Frame (a+(b+1)) :=
  (rightFactorFrameEquiv b (a+1)).trans (tangentCast (tangentSwap a b))

def rightPackedEquiv : (Site SB × (Polycube.Cell SA × Passive b (a+1))) ≃
    (Polycube.Cell SA × Facet SB) × Frame (a+(b+1)) where
  toFun p := ((p.2.1,p.1.1), rightCommonFrameEquiv (p.1.2,p.2.2))
  invFun q := ((q.1.2, (rightCommonFrameEquiv.symm q.2).1),
    (q.1.1, (rightCommonFrameEquiv.symm q.2).2))
  left_inv p := by
    rcases p with ⟨⟨f,F⟩,c,p⟩
    simp only [Equiv.symm_apply_apply]
  right_inv q := by
    rcases q with ⟨⟨c,f⟩,F⟩
    simp

/-- Every facet type and every interleaved full tangent-orbit frame occurs. -/
def siteCoproductEquiv :
    (Site SA × (Polycube.Cell SB × Passive a (b+1))) ⊕
      (Site SB × (Polycube.Cell SA × Passive b (a+1))) ≃ Site (nativeProduct SA SB) :=
  ((leftPackedEquiv SA SB).sumCongr (rightPackedEquiv SA SB)).trans
    ((Equiv.sumProdDistrib _ _ _).symm.trans
      (((Polycube.productFacetEquiv SA SB).trans
        (Polycube.castFacetEquiv (productDim a (b+1)) _)).prodCongr (Equiv.refl _)))

@[simp] theorem siteCoproductEquiv_left (u : Site SA) (c : Polycube.Cell SB)
    (p : Passive a (b+1)) : siteCoproductEquiv SA SB (.inl (u,c,p)) = leftSite u c p := rfl

@[simp] theorem siteCoproductEquiv_right (u : Site SB) (c : Polycube.Cell SA)
    (p : Passive b (a+1)) : siteCoproductEquiv SA SB (.inr (u,c,p)) = commonRightSite u c p := by
  apply Prod.ext
  · exact (facetCast_chain (rightProductDim b (a+1)) (tangentSwap a b) (productDim a (b+1))
      (Polycube.productCells SA SB) (nativeRightProduct_cast_eq SA SB)
      (Polycube.productFacetRight c u.1)).symm
  · rfl

#print axioms siteCoproductEquiv
#print axioms siteCoproductEquiv_right
#print axioms SiteTransport_commonLiftRight_iff
end
end ProductClosure.ProductGraphSiteCoproduct
