module

public import SpectreGeometry.EdgeNeighborhood
public import SpectreGeometry.EuclideanCarrier
public import Mathlib.Analysis.Normed.Affine.MazurUlam

@[expose] public section


/-! Exact affine half-plane forms for arbitrary Euclidean isometric copies
of the polygon. The affine structure is derived by Mazur-Ulam. -/
namespace SpectreGeometry
noncomputable section
open Set
abbrev EPlane := EuclideanSpace ℝ (Fin 2)

def coordinateLinearEquiv : RealPoint ≃ₗ[ℝ] EPlane where
  toEquiv := euclideanCoordinates.toEquiv
  map_add' := by intro x y; ext k; fin_cases k <;> rfl
  map_smul' := by intro a x; ext k; fin_cases k <;> rfl

def detLinearForm (a : RealPoint) : RealPoint →ₗ[ℝ] ℝ where
  toFun := RealPoint.det a
  map_add' := by intro x y; simp only [RealPoint.det,Prod.fst_add,Prod.snd_add]; ring
  map_smul' := by intro t x; simp only [RealPoint.det,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply]; ring

def displacementPullback (f : EPlane ≃ᵢ EPlane) : EPlane →ₗ[ℝ] RealPoint :=
  coordinateLinearEquiv.symm.toLinearMap.comp f.symm.toRealLinearIsometryEquiv.toLinearMap

def edgeLinearForm (f : EPlane ≃ᵢ EPlane) (i : Fin 14) : EPlane →ₗ[ℝ] ℝ :=
  (detLinearForm (realEdge i)).comp (displacementPullback f)

def placedSide (f : EPlane ≃ᵢ EPlane) (i : Fin 14) (y : EPlane) : ℝ :=
  side (realVertex i) (realVertex (next i)) (euclideanCoordinates.symm (f.symm y))

theorem displacementPullback_sub (f : EPlane ≃ᵢ EPlane) (x y : EPlane) :
    displacementPullback f (y-x) =
      euclideanCoordinates.symm (f.symm y)-euclideanCoordinates.symm (f.symm x) := by
  have he : f.symm.toRealLinearIsometryEquiv (y-x) = f.symm y-f.symm x := by
    rw [map_sub,IsometryEquiv.toRealLinearIsometryEquiv_apply,
      IsometryEquiv.toRealLinearIsometryEquiv_apply]
    abel
  change coordinateLinearEquiv.symm (f.symm.toRealLinearIsometryEquiv (y-x)) = _
  rw [he,map_sub]
  rfl

theorem edgeLinearForm_sub (f : EPlane ≃ᵢ EPlane) (i : Fin 14) (x y : EPlane) :
    edgeLinearForm f i (y-x) = placedSide f i y-placedSide f i x := by
  change RealPoint.det (realEdge i) (displacementPullback f (y-x)) = _
  rw [displacementPullback_sub]
  simp only [placedSide,side,realEdge,RealPoint.det,RealPoint.sub,Prod.fst_sub,Prod.snd_sub]
  ring

theorem displacementPullback_surjective (f : EPlane ≃ᵢ EPlane) :
    Function.Surjective (displacementPullback f) :=
  coordinateLinearEquiv.symm.surjective.comp f.symm.toRealLinearIsometryEquiv.surjective

theorem edgeLinearForm_nonzero (f : EPlane ≃ᵢ EPlane) (i : Fin 14) :
    edgeLinearForm f i ≠ 0 := by
  intro hz
  let p : RealPoint := (-(realEdge i).2,(realEdge i).1)
  obtain ⟨v,hv⟩ := displacementPullback_surjective f p
  have he : edgeLinearForm f i v = 1 := by
    change RealPoint.det (realEdge i) (displacementPullback f v) = 1
    rw [hv]
    have hd := real_edges_unit_squared i
    simpa only [p,RealPoint.det,RealPoint.dot,mul_neg,sub_neg_eq_add] using hd
  rw [hz] at he
  norm_num at he

/-- Pullback side forms vanish at the corresponding actual placed edge. -/
theorem placedSide_edge_zero (f : EPlane ≃ᵢ EPlane) (i : Fin 14) (t : ℝ) :
    placedSide f i (f (euclideanCoordinates
      (interpolate (realVertex i) (realVertex (next i)) t))) = 0 := by
  unfold placedSide
  rw [f.symm_apply_apply,euclideanCoordinates.symm_apply_apply,side_interpolate]
  simp

/-- The actual tile interior is the positive side of this nonzero affine
form throughout a proved open neighborhood of any strict edge point. -/
theorem placed_open_edge_local_interior (f : EPlane ≃ᵢ EPlane) (i : Fin 14)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    ∃ U : Set EPlane, IsOpen U ∧
      f (euclideanCoordinates (interpolate (realVertex i) (realVertex (next i)) t)) ∈ U ∧
      ∀ y ∈ U, (y ∈ interior (f '' euclideanBody) ↔ 0 < placedSide f i y) := by
  obtain ⟨U,hU,hx,hl⟩ := outer_open_edge_local_halfplane i t ht ht'
  let H : RealPoint ≃ₜ EPlane := euclideanCoordinates.trans f.toHomeomorph
  refine ⟨H '' U,H.isOpenMap _ hU,⟨_,hx,rfl⟩,?_⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩ := hy
  have hid : f '' euclideanBody = H '' polygonBody := by
    rw [euclideanBody,Set.image_image]
    rfl
  rw [hid,←H.image_interior]
  simp only [Set.mem_image,H.injective.eq_iff,exists_eq_right]
  have hs : placedSide f i (H z) = side (realVertex i) (realVertex (next i)) z := by
    unfold placedSide H
    simp only [Homeomorph.trans_apply,IsometryEquiv.coe_toHomeomorph,
      f.symm_apply_apply,euclideanCoordinates.symm_apply_apply]
  rw [hs]
  exact (hl z hz).2.1

end
end SpectreGeometry
