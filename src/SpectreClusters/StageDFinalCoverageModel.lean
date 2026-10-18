module

public import SpectreClusters.StageDFinalChecksModel

@[expose] public section


/-! Positive halo witnesses replace repeated full six-pose searches. -/
namespace SpectreClusters.StageD

def rowCoverageWitnessB (i : Row) (ws : List (Cell × Nat)) : Bool :=
  ws.all fun w => decide (w.2 < (rowNeighbors i).length) &&
    (clusterPlacementCells ((rowNeighbors i).getD w.2 (canonical .t7h))).any (cellEqB w.1)

theorem rowCoverage_of_witness (i : Row) (ws : List (Cell × Nat))
    (he : ws.map Prod.fst = haloOrder (rowKind i)) (hw : rowCoverageWitnessB i ws = true) :
    (haloOrder (rowKind i)).all (fun c => (rowNeighbors i).any
      (fun p => (clusterPlacementCells p).any (cellEqB c))) = true := by
  apply List.all_eq_true.mpr
  intro c hc
  rw [← he] at hc
  obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hc
  have ht := List.all_eq_true.mp hw w hm
  simp only [Bool.and_eq_true,decide_eq_true_eq] at ht
  apply List.any_eq_true.mpr
  refine ⟨(rowNeighbors i).getD w.2 (canonical .t7h),?_,ht.2⟩
  simpa [List.getD_eq_getElem?_getD,ht.1] using (List.getElem_mem ht.1)

theorem rowBasics_of_witness (i : Row) (ws : List (Cell × Nat))
    (ht : (decide (LegalClusterKind (rowKind i)) && ((rowNeighbors i).length == 6) &&
      (rowNeighbors i).all (fun p => decide (LegalClusterKind p.kind) &&
        !(clusterPoseEqB p (canonical (rowKind i))))) = true)
    (he : ws.map Prod.fst = haloOrder (rowKind i)) (hw : rowCoverageWitnessB i ws = true) :
    rowBasicsB i = true := by
  unfold rowBasicsB
  rw [ht]
  exact rowCoverage_of_witness i ws he hw
end SpectreClusters.StageD
