module

public import SpectreGeometry.DeformationHomeomorphismTransport
public import SpectreGeometry.DevelopmentTranslation
public import SpectreGeometry.QuadraticFrameUniqueness

@[expose] public section


/-! Full translation-equivariance for slot-preserving placement translations.
Passing from unlabelled carrier-set symmetries to this hypothesis requires
separate intrinsic rigidity of the source polygon and is not assumed here. -/
namespace SpectreGeometry.Deformation
noncomputable section

private theorem coordinateAction_translation (f g : EPlane ≃ᵢ EPlane) (v : EPlane)
    (h : ∀ p, g p = f p+v) (q : RealPoint) : coordinateAction g q = coordinateAction f q := by
  change coordinateLinearEquiv.symm (g.toRealLinearIsometryEquiv (coordinateLinearEquiv q)) =
    coordinateLinearEquiv.symm (f.toRealLinearIsometryEquiv (coordinateLinearEquiv q))
  congr 1
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply,IsometryEquiv.toRealLinearIsometryEquiv_apply,h,h]
  abel

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

theorem tilingFrame_translation (i j : ι) (v : EPlane) (h : ∀ p, f j p = f i p+v) :
    tilingFrame f hdirect hdisjoint hcover root i = tilingFrame f hdirect hdisjoint hcover root j := by
  apply relative_frame_unique (f root) (f i) _ _ (tilingFrame_spec f hdirect hdisjoint hcover root i)
  intro q
  rw [←coordinateAction_translation (f i) (f j) v h q]
  exact tilingFrame_spec f hdirect hdisjoint hcover root j q

theorem tilingTargetOrigin_registered (i : ι) :
    tilingTargetOrigin f hdirect hdisjoint hcover root i =
      physicalVertexDevelopment (f root) (f i 0) :=
  (physicalVertexDevelopment_registered (f root) (f i 0)
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i)).symm

theorem tilingTargetOrigin_translation_difference (i j r : ι) (v : EPlane)
    (hij : f j 0 = f i 0+v) (hr : f r 0 = f root 0+v) :
    tilingTargetOrigin f hdirect hdisjoint hcover root j-
      tilingTargetOrigin f hdirect hdisjoint hcover root i =
    tilingTargetOrigin f hdirect hdisjoint hcover root r-
      tilingTargetOrigin f hdirect hdisjoint hcover root root := by
  simp only [tilingTargetOrigin_registered]
  apply registered_development_displacement (f root) (f i 0) (f j 0) (f root 0) (f r 0)
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i)
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root j)
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root root)
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root r)
  rw [hij,hr]
  simp only [add_sub_cancel_left]

/-- The actual plane homeomorphism conjugates every slot-preserving physical
translation symmetry to a translation. -/
theorem physicalHomeomorph_translation (v : EPlane)
    (hperiod : ∀ i, ∃ j, ∀ p : EPlane, f j p = f i p+v) :
    ∃ w : EPlane, ∀ x : EPlane,
      physicalHomeomorph f hdirect hdisjoint hcover root (x+v) =
        physicalHomeomorph f hdirect hdisjoint hcover root x+w := by
  obtain ⟨r,hr⟩ := hperiod root
  let w := euclideanCoordinates (tilingTargetOrigin f hdirect hdisjoint hcover root r-
    tilingTargetOrigin f hdirect hdisjoint hcover root root)
  refine ⟨w,?_⟩
  intro x
  obtain ⟨i,u,⟨p,hp,rfl⟩,hpx⟩ := hcover x
  obtain ⟨j,hj⟩ := hperiod i
  have hk := tilingFrame_translation f hdirect hdisjoint hcover root i j v hj
  have ho := tilingTargetOrigin_translation_difference f hdirect hdisjoint hcover root i j r v
    (hj 0) (hr 0)
  rw [←hpx,←hj,physicalHomeomorph_on_tile f hdirect hdisjoint hcover root j p hp,
    physicalHomeomorph_on_tile f hdirect hdisjoint hcover root i p hp,←hk]
  change coordinateLinearEquiv _ = coordinateLinearEquiv _ + coordinateLinearEquiv _
  rw [←map_add]
  congr 1
  rw [←ho]
  abel

theorem physicalHomeomorph_nonzero_translation (v : EPlane) (hv : v ≠ 0)
    (hperiod : ∀ i, ∃ j, ∀ p : EPlane, f j p = f i p+v) :
    ∃ w : EPlane, w ≠ 0 ∧ ∀ x : EPlane,
      physicalHomeomorph f hdirect hdisjoint hcover root (x+v) =
        physicalHomeomorph f hdirect hdisjoint hcover root x+w := by
  obtain ⟨w,hw⟩ := physicalHomeomorph_translation f hdirect hdisjoint hcover root v hperiod
  refine ⟨w,?_,hw⟩
  intro hz
  have he := hw 0
  rw [hz,add_zero,zero_add] at he
  exact hv ((physicalHomeomorph f hdirect hdisjoint hcover root).injective he)

end Tiling
end
end SpectreGeometry.Deformation
