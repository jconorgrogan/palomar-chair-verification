module

public import SpectreClusters.StageDReductionRawBindingT7H
public import SpectreClusters.StageDReductionRawBindingT8H

@[expose] public section

namespace SpectreClusters.StageD.Reduction

theorem raw_rows_binding (k : ClusterKind) :
    (compactRowIDs k).map (List.map (originalID k)) = Raw.rawNeighborIDs k := by
  cases k
  · rfl
  · exact raw_rows_T7H_binding
  · exact raw_rows_T8H_binding

theorem raw_row_count_binding (k : ClusterKind) :
    (compactRowIDs k).length = (Raw.rawNeighborIDs k).length := by
  have h := congrArg List.length (raw_rows_binding k)
  simpa only [List.length_map] using h

theorem compact_raw_patch_binding (k : ClusterKind) (i : Nat)
    (hi : i < (compactRowIDs k).length) : compactPatch k i = Raw.rawPatch k i := by
  have hrows := raw_rows_binding k
  have hget : (Raw.rawNeighborIDs k).getD i [] =
      ((compactRowIDs k).getD i []).map (originalID k) := by
    rw [←hrows]
    simp [List.getD_eq_getElem?_getD,hi]
  unfold compactPatch compactIDs Raw.rawPatch
  rw [hget,List.map_map]
  congr 1
  apply List.map_congr_left
  intro n hn
  have hrow : (compactRowIDs k).getD i [] ∈ compactRowIDs k := by
    simp [List.getD_eq_getElem?_getD,hi]
  have hb := List.all_eq_true.mp (row_bounds_checked k) _ hrow
  have hnlt : n < (originalCandidateIDs k).length := by
    simpa using (List.all_eq_true.mp hb n hn)
  have hc := List.all_eq_true.mp (candidate_binding_checked k) n (List.mem_range.mpr hnlt)
  exact (Raw.poseEqB_iff _ _).mp hc
end SpectreClusters.StageD.Reduction
