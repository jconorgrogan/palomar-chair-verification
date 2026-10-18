module

public import SpectreGeometry.ReverseFinitePLScaling
public import SpectreGeometry.ReverseSourceHexRotation
public import SpectreGeometry.ReverseSourceHexLocalFinite
public import SpectreGeometry.ReverseClusterTriangulationScaleReal

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreFinite.HexSearch ReverseClusterTriangulation

/-- A genuine plane motion in the axial coordinate model. -/
def axialMotionHomeomorph (r : Fin 6) (a : RealPoint) : RealPoint ≃ₜ RealPoint where
  toFun p := a+gridRotation r p
  invFun p := gridRotation (inverseTurn r) (p-a)
  left_inv p := by
    change gridRotation (inverseTurn r) (a+gridRotation r p-a)=p
    rw [_root_.add_sub_cancel_left]
    have h := gridRotation_inverse_cancel (inverseTurn r) p
    simpa only [inverseTurn_involutive] using h
  right_inv p := by
    change a+gridRotation r (gridRotation (inverseTurn r) (p-a))=p
    rw [gridRotation_inverse_cancel]
    abel
  continuous_toFun := continuous_const.add (gridRotationLinear r).continuous_of_finiteDimensional
  continuous_invFun := (gridRotationLinear (inverseTurn r)).continuous_of_finiteDimensional.comp
    (continuous_id.sub continuous_const)

@[simp] theorem axialMotionHomeomorph_apply (r : Fin 6) (a p : RealPoint) :
    axialMotionHomeomorph r a p = a+gridRotation r p := rfl

theorem axialMotion_sourceHex_image (r : Fin 6) (c : ℤ×ℤ) :
    axialMotionHomeomorph r (integerPoint c) '' sourceHexCarrier (0,0) = sourceHexCarrier c := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    have h := (sourceHexCarrier_gridRotation_iff r q).mpr hq
    simpa only [axialMotionHomeomorph_apply,sourceHexCarrier,mem_ofPred_eq,integerPoint,
      Prod.fst_add,Prod.snd_add,add_sub_cancel_left,Int.cast_zero,sub_zero] using h
  · intro hp
    have hq : p-integerPoint c ∈ sourceHexCarrier (0,0) := by
      simpa only [sourceHexCarrier,mem_ofPred_eq,integerPoint,Prod.fst_sub,Prod.snd_sub,
        Int.cast_zero,sub_zero] using hp
    refine ⟨gridRotation (inverseTurn r) (p-integerPoint c),
      (sourceHexCarrier_gridRotation_iff (inverseTurn r) _).mpr hq,?_⟩
    change integerPoint c+gridRotation r (gridRotation (inverseTurn r) (p-integerPoint c))=p
    rw [gridRotation_inverse_cancel]
    abel

def sourceHexMotionHomeomorph (r : Fin 6) (c : ℤ×ℤ) :
    sourceHexCarrier (0,0) ≃ₜ sourceHexCarrier c :=
  ((axialMotionHomeomorph r (integerPoint c)).image (sourceHexCarrier (0,0))).trans
    (Homeomorph.setCongr (axialMotion_sourceHex_image r c))

@[simp] theorem sourceHexMotionHomeomorph_apply (r : Fin 6) (c : ℤ×ℤ)
    (x : sourceHexCarrier (0,0)) :
    (sourceHexMotionHomeomorph r c x).val = integerPoint c+gridRotation r x.val := rfl

def placedClusterCarrier (r : Fin 6) (a : RealPoint) (kind : ClusterKind) : Set RealPoint :=
  axialMotionHomeomorph r a '' rawClusterBody kind

theorem integerHull_isCompact (vs : List Point) : IsCompact (integerHull vs) :=
  ((List.finite_toSet vs).image integerPoint).isCompact_convexHull ℝ

theorem rawClusterBody_isCompact (kind : ClusterKind) : IsCompact (rawClusterBody kind) :=
  (List.finite_toSet (clusterCells kind)).isCompact_biUnion
    (fun c _ => integerHull_isCompact (cellVertices c))

theorem placedClusterCarrier_isClosed (r : Fin 6) (a : RealPoint) (kind : ClusterKind) :
    IsClosed (placedClusterCarrier r a kind) :=
  ((rawClusterBody_isCompact kind).image (axialMotionHomeomorph r a).continuous).isClosed

/-- The local closed-carrier chart is transported using the identical direct
turn in its regular source hexagon and literal cluster target. -/
def placedClusterChart {kind : ClusterKind}
    (h : sourceHexCarrier (0,0) ≃ₜ rawClusterBody kind)
    (r : Fin 6) (c : ℤ×ℤ) (a : RealPoint) :
    sourceHexCarrier c ≃ₜ placedClusterCarrier r a kind :=
  (sourceHexMotionHomeomorph r c).symm.trans
    (h.trans ((axialMotionHomeomorph r a).image (rawClusterBody kind)))

theorem placedClusterChart_on {kind : ClusterKind}
    (h : sourceHexCarrier (0,0) ≃ₜ rawClusterBody kind)
    (r : Fin 6) (c : ℤ×ℤ) (a : RealPoint) (x : sourceHexCarrier (0,0)) :
    (placedClusterChart h r c a (sourceHexMotionHomeomorph r c x)).val =
      a+gridRotation r (h x).val := by
  change a+gridRotation r (h ((sourceHexMotionHomeomorph r c).symm
    (sourceHexMotionHomeomorph r c x))).val = _
  rw [Homeomorph.symm_apply_apply]

end
end SpectreGeometry.ReverseExistence
