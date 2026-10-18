module

public import SpectreGeometry.PolygonProductKeyFactorTransition
public import SpectreGeometry.PolygonProductKeyPairing
public import Mathlib.Logic.Relation

@[expose] public section


/-! Active-edge components with actual proper planar placements and a fixed
passive factor pointwise. These constructions do not assert that a component
covers its plane; that is a subsequent geometric completeness obligation. -/
namespace SpectreGeometry
noncomputable section
open Set

private theorem component_coordinateAction_apply (f : EPlane ≃ᵢ EPlane) (x : RealPoint) :
    coordinateAction f x = euclideanCoordinates.symm (f (euclideanCoordinates x)) -
      euclideanCoordinates.symm (f 0) := by
  change coordinateLinearEquiv.symm (f.toRealLinearIsometryEquiv (coordinateLinearEquiv x)) = _
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply,map_sub]
  rfl

private theorem component_coordinateAction_trans (f g : EPlane ≃ᵢ EPlane) (x : RealPoint) :
    coordinateAction (f.trans g) x = coordinateAction g (coordinateAction f x) := by
  rw [component_coordinateAction_apply f x,coordinateAction_sub,
    component_coordinateAction_apply]
  simp only [Homeomorph.apply_symm_apply,IsometryEquiv.trans_apply]

private theorem component_direct_det (f : EPlane ≃ᵢ EPlane) (hf : DirectPlacement f)
    (x y : RealPoint) :
    RealPoint.det (coordinateAction f x) (coordinateAction f y) = RealPoint.det x y := by
  rw [direct_coordinateAction f hf,direct_coordinateAction f hf]
  have hn := frame_unit_first f
  calc
    _ = RealPoint.dot (frameFirst f) (frameFirst f)*RealPoint.det x y := by
      simp only [complexMulReal,RealPoint.det,RealPoint.dot]; ring
    _ = _ := by rw [hn,one_mul]

private theorem component_direct_refl : DirectPlacement (IsometryEquiv.refl EPlane) := by
  change 0 < RealPoint.det (coordinateAction (IsometryEquiv.refl EPlane) (1,0))
    (coordinateAction (IsometryEquiv.refl EPlane) (0,1))
  rw [component_coordinateAction_apply,component_coordinateAction_apply]
  change 0 < RealPoint.det (((1,0):RealPoint)-(0,0)) (((0,1):RealPoint)-(0,0))
  norm_num [RealPoint.det]

private theorem component_direct_trans (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) : DirectPlacement (f.trans g) := by
  change 0 < RealPoint.det (coordinateAction (f.trans g) (1,0))
    (coordinateAction (f.trans g) (0,1))
  rw [component_coordinateAction_trans,component_coordinateAction_trans,component_direct_det g hg]
  exact hf

private theorem component_direct_symm (f : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) : DirectPlacement f.symm := by
  have hd := component_direct_det f hf (coordinateAction f.symm (1,0))
    (coordinateAction f.symm (0,1))
  rw [← component_coordinateAction_trans,← component_coordinateAction_trans] at hd
  have he : f.symm.trans f = IsometryEquiv.refl EPlane := by
    apply DFunLike.ext
    intro x
    change f (f.symm x) = x
    exact f.apply_symm_apply x
  rw [he] at hd
  change 0 < RealPoint.det (coordinateAction f.symm (1,0)) (coordinateAction f.symm (0,1))
  rw [← hd]
  exact component_direct_refl

/-- A proper active transition together with pointwise passive identity. -/
def ProductActiveBlockRelation (b : Fin 2) (f g : EFour ≃ᵢ EFour) : Prop :=
  ∃ A : EPlane ≃ᵢ EPlane, DirectPlacement A ∧ ∀ a p : RealPoint,
    f (productFactorPoint b a p) = g (productFactorPoint b
      (euclideanCoordinates.symm (A (euclideanCoordinates a))) p)

theorem ProductActiveBlockRelation.refl (b : Fin 2) (f : EFour ≃ᵢ EFour) :
    ProductActiveBlockRelation b f f := by
  refine ⟨IsometryEquiv.refl EPlane,component_direct_refl,?_⟩
  intro a p
  change f (productFactorPoint b a p) = f (productFactorPoint b (euclideanCoordinates.symm (euclideanCoordinates a)) p)
  rw [Homeomorph.symm_apply_apply]

theorem ProductActiveBlockRelation.symm {b : Fin 2} {f g : EFour ≃ᵢ EFour}
    (h : ProductActiveBlockRelation b f g) : ProductActiveBlockRelation b g f := by
  obtain ⟨A,hA,h⟩ := h
  refine ⟨A.symm,component_direct_symm A hA,?_⟩
  intro a p
  have he := h (euclideanCoordinates.symm (A.symm (euclideanCoordinates a))) p
  simpa only [Homeomorph.apply_symm_apply,IsometryEquiv.apply_symm_apply,
    Homeomorph.symm_apply_apply] using he.symm

theorem ProductActiveBlockRelation.trans {b : Fin 2} {f g k : EFour ≃ᵢ EFour}
    (hfg : ProductActiveBlockRelation b f g) (hgk : ProductActiveBlockRelation b g k) :
    ProductActiveBlockRelation b f k := by
  obtain ⟨A,hA,ha⟩ := hfg
  obtain ⟨B,hB,hb⟩ := hgk
  refine ⟨A.trans B,component_direct_trans A B hA hB,?_⟩
  intro a p
  rw [ha,hb]
  simp only [Homeomorph.apply_symm_apply,IsometryEquiv.trans_apply]

def ProductActiveStep {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (i j : ι) : Prop :=
  ∃ u : ProductKeySite, u.1 = b ∧ (P.partner i u).1 = j

theorem product_active_step_block_relation {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) {i j : ι} (h : ProductActiveStep P b i j) :
    ProductActiveBlockRelation b (f i) (f j) := by
  obtain ⟨u,hu,rfl⟩ := h
  refine ⟨productActiveEdgeTransition u.2.1 (P.partner i u).2.2.1,
    product_active_edge_transition_direct _ _,?_⟩
  intro a p
  have ht : (P.partner i u).2.1 = b := (P.sameLabel i u).symm.trans hu
  simpa only [hu,ht] using registered_product_factor_transition u (P.partner i u).2
    (f i) (f (P.partner i u).1) (P.oppositeSigns i u) (P.samePose i u) a p

theorem product_active_component_block_relation {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) {i j : ι}
    (h : Relation.EqvGen (ProductActiveStep P b) i j) :
    ProductActiveBlockRelation b (f i) (f j) := by
  induction h with
  | rel i j h => exact product_active_step_block_relation P b h
  | refl i => exact ProductActiveBlockRelation.refl b (f i)
  | symm i j h ih => exact ih.symm
  | trans i j k h h' ih ih' => exact ih.trans ih'

def ProductActiveComponent {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) :=
  {i : ι // Relation.EqvGen (ProductActiveStep P b) root i}

def productActiveComponentPlacement {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root) :
    EPlane ≃ᵢ EPlane :=
  (product_active_component_block_relation P b i.property).symm.choose

theorem product_active_component_placement_direct {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root) :
    DirectPlacement (productActiveComponentPlacement P b root i) :=
  (product_active_component_block_relation P b i.property).symm.choose_spec.1

theorem product_active_component_placement_spec {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root)
    (a p : RealPoint) :
    f i.val (productFactorPoint b a p) = f root (productFactorPoint b
      (euclideanCoordinates.symm (productActiveComponentPlacement P b root i (euclideanCoordinates a))) p) :=
  (product_active_component_block_relation P b i.property).symm.choose_spec.2 a p

def productActiveComponentPartner {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (P : ProductKeyPairing f) (b : Fin 2) (root : ι) (i : ProductActiveComponent P b root)
    (u : ProductKeySite) (hu : u.1 = b) : ProductActiveComponent P b root :=
  ⟨(P.partner i.val u).1,Relation.EqvGen.trans _ _ _ i.property
    (Relation.EqvGen.rel _ _ ⟨u,hu,rfl⟩)⟩

end
end SpectreGeometry
