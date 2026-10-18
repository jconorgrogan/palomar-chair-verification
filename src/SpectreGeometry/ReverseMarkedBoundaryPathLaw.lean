module

public import SpectreGeometry.ReverseMarkedBoundaryParameters
public import SpectreGeometry.ReversePolygonalPathAffine

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence ReverseClusterTriangulation ReverseFinitePL

def normalizedTargetBoundary (k : Fin 9) (d : Fin 6) : List RealPoint :=
  (boundaryIndices k d).map (fun n => (1/6:ℝ) • integerPoint (targetVertex k n))

theorem normalizedTargetBoundary_eq_markedPath (k : Fin 9) (d : Fin 6) :
    normalizedTargetBoundary k d = ((markedPaths k).getD d.val []).map integerPoint := by
  have he : normalizedTargetBoundary k d =
      ((boundaryIndices k d).map (targetVertex k)).map
        (fun p => (1/6:ℝ) • integerPoint p) := by
    rw [List.map_map]
    rfl
  rw [he,target_boundary_path_bound,List.map_map]
  apply List.map_congr_left
  intro p hp
  dsimp only [Function.comp_apply]
  rw [integerPoint_scale]
  simp only [Int.cast_ofNat,smul_smul,show (1/6:ℝ)*6=1 by norm_num,one_smul]

def MarkedBoundarySubintervalLaw (k : Fin 9) (F : sourceHexCarrier (0,0) → RealPoint) : Prop :=
  ∀ (d : Fin 6) (j : Nat), j < (boundaryIndices k d).length-1 →
    ∀ u ∈ Icc (0:ℝ) 1, ∀ x : sourceHexCarrier (0,0),
      x.val = AffineMap.lineMap (sourceHexCorner d) (sourceHexCorner (d+1))
        (((j:ℝ)+u)/((boundaryIndices k d).length-1)) →
      F x = AffineMap.lineMap
        ((1/6:ℝ) • integerPoint (targetVertex k ((boundaryIndices k d).getD j 0)))
        ((1/6:ℝ) • integerPoint (targetVertex k ((boundaryIndices k d).getD (j+1) 0))) u

theorem markedBoundary_pathParameter (k : Fin 9) (F : sourceHexCarrier (0,0) → RealPoint)
    (hF : MarkedBoundarySubintervalLaw k F) (d : Fin 6) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (x : sourceHexCarrier (0,0))
    (hx : x.val = AffineMap.lineMap (sourceHexCorner d) (sourceHexCorner (d+1)) t) :
    PathParameter (((markedPaths k).getD d.val []).map integerPoint) t (F x) := by
  rw [←normalizedTargetBoundary_eq_markedPath]
  obtain ⟨j,u,hu,hparam⟩ := unit_subdivision ((boundaryIndices k d).length-1)
    (boundary_subdivision_pos k d) t ht
  have hget (i : Nat) (hi : i < (boundaryIndices k d).length) :
      (normalizedTargetBoundary k d).getD i 0 =
        (1/6:ℝ) • integerPoint (targetVertex k ((boundaryIndices k d).getD i 0)) := by
    simp [normalizedTargetBoundary,List.getD_eq_getElem?_getD,hi]
  refine ⟨j.val,by simpa only [normalizedTargetBoundary,List.length_map] using j.isLt,
    u,hu,by simpa only [normalizedTargetBoundary,List.length_map] using hparam,?_⟩
  rw [hget j.val (by omega),hget (j.val+1) (by omega)]
  have hlen : 1 ≤ (boundaryIndices k d).length := by
    have hp := boundary_subdivision_pos k d
    omega
  have hparamR : t = ((j.val:ℝ)+u)/((boundaryIndices k d).length-1) := by
    simpa only [Nat.cast_sub hlen,Nat.cast_one] using hparam
  exact hF d j.val j.isLt u hu x (hx.trans (congrArg _ hparamR))

end
end SpectreGeometry.ReverseExistence
