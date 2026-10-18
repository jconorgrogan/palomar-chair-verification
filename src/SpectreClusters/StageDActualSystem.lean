module

public import SpectreClusters.StageDActualRows
public import SpectreClusters.ClusterOrbitPeriod

@[expose] public section


/-! The final finite certificates give inverse and triangle laws on actual
owned clusters, hence a genuine labelled axial action without a chart axiom. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch

theorem clusterStep_opposite (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (d : Fin 6) (p : ActualCluster f) :
    clusterStep checks hc hf (opposite d) (clusterStep checks hc hf d p) = p := by
  let i := chosenRow hc hf p
  let e := turnDiff d p.val.turn
  let q := rowPort i e
  let j := chosenRow hc hf (clusterStep checks hc hf d p)
  have h := actual_pair_laws checks hc hf p d
  change pairLawsB i e j = true at h
  simp only [pairLawsB,Bool.and_eq_true,clusterPoseEqB_iff,decide_eq_true_eq] at h
  have hi : moveClusterPlacement q.turn q.center (rowPort j (turnDiff (opposite e) q.turn)) =
      canonical (rowKind i) := h.1.1
  apply Subtype.ext
  change moveClusterPlacement (turnAdd p.val.turn q.turn) (add p.val.center (rotate p.val.turn q.center))
    (rowPort j (turnDiff (opposite d) (turnAdd p.val.turn q.turn))) = p.val
  rw [turnDiff_compose,turnDiff_opposite,←moveClusterPlacement_compose,hi]
  rw [(chosenRow_spec hc hf p).1,moveClusterPlacement_canonical]

theorem clusterStep_triangle (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (d : Fin 6) (p : ActualCluster f) :
    clusterStep checks hc hf (rotateTurn 2 d) (clusterStep checks hc hf d p) =
      clusterStep checks hc hf (rotateTurn 1 d) p := by
  let i := chosenRow hc hf p
  let e := turnDiff d p.val.turn
  let q := rowPort i e
  let j := chosenRow hc hf (clusterStep checks hc hf d p)
  have h := actual_pair_laws checks hc hf p d
  change pairLawsB i e j = true at h
  simp only [pairLawsB,Bool.and_eq_true,clusterPoseEqB_iff,decide_eq_true_eq] at h
  have hi : moveClusterPlacement q.turn q.center (rowPort j (turnDiff (rotateTurn 2 e) q.turn)) =
      rowPort i (rotateTurn 1 e) := h.1.2
  apply Subtype.ext
  change moveClusterPlacement (turnAdd p.val.turn q.turn) (add p.val.center (rotate p.val.turn q.center))
    (rowPort j (turnDiff (rotateTurn 2 d) (turnAdd p.val.turn q.turn))) =
      moveClusterPlacement p.val.turn p.val.center (rowPort i (turnDiff (rotateTurn 1 d) p.val.turn))
  rw [turnDiff_compose,turnDiff_rotate 2 d p.val.turn,
    turnDiff_rotate 1 d p.val.turn,←moveClusterPlacement_compose,hi]

theorem clusterStep_match (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (d : Fin 6) (p : ActualCluster f) :
    ReverseExistence.sideMatch (clusterLabel hc hf p) (clusterLabel hc hf (clusterStep checks hc hf d p)) d := by
  have h := actual_pair_laws checks hc hf p d
  simp only [pairLawsB,Bool.and_eq_true,clusterPoseEqB_iff,decide_eq_true_eq] at h
  exact sideMatch_in_frame _ _ p.val.turn _ d h.2

noncomputable def actualHexSystem (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) : HexStepSystem (ActualCluster f) where
  step := clusterStep checks hc hf
  opposite_inverse := clusterStep_opposite checks hc hf
  triangle := clusterStep_triangle checks hc hf

/-- The marked field is the pullback of the actual cluster labels along the
proved axial action. No injective coarse-coordinate chart is assumed. -/
noncomputable def actualMarkedField (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f) : Position → State :=
  (actualHexSystem checks hc hf).labelField (clusterLabel hc hf) p

theorem actualMarkedField_globallyLegal (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f) :
    GloballyLegal (actualMarkedField checks hc hf p) :=
  (actualHexSystem checks hc hf).labelField_globallyLegal (clusterLabel hc hf) (clusterStep_match checks hc hf) p

end SpectreClusters.StageD
