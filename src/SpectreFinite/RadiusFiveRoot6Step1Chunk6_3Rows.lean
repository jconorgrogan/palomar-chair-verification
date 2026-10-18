module

public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root6Node0Step1Chunk6_3_project_eq_self_of_length (row : List State) (hlen : row.length = 61) :
    table35Project row = row := by
  have hproject : table35Project row =
      List.ofFn (fun i : Fin 61 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root6Node0Step1Chunk6_3_rows0_binding :
    RadiusFourPruning.stateRows6_3_0.map table35Project = RadiusFourPruning.stateRows6_3_0 := by
  have hlengths : RadiusFourPruning.stateRows6_3_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows6_3_0.map table35Project = RadiusFourPruning.stateRows6_3_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root6Node0Step1Chunk6_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows6_3_0 := List.map_id' _

theorem root6Node0Step1Chunk6_3_rows1_binding :
    RadiusFourPruning.stateRows6_3_1.map table35Project = RadiusFourPruning.stateRows6_3_1 := by
  have hlengths : RadiusFourPruning.stateRows6_3_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows6_3_1.map table35Project = RadiusFourPruning.stateRows6_3_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root6Node0Step1Chunk6_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows6_3_1 := List.map_id' _

theorem root6Node0Step1Chunk6_3_rows2_binding :
    RadiusFourPruning.stateRows6_3_2.map table35Project = RadiusFourPruning.stateRows6_3_2 := by
  have hlengths : RadiusFourPruning.stateRows6_3_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows6_3_2.map table35Project = RadiusFourPruning.stateRows6_3_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root6Node0Step1Chunk6_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows6_3_2 := List.map_id' _

theorem root6Node0Step1Chunk6_3_rows3_binding :
    RadiusFourPruning.stateRows6_3_3.map table35Project = RadiusFourPruning.stateRows6_3_3 := by
  have hlengths : RadiusFourPruning.stateRows6_3_3.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows6_3_3.map table35Project = RadiusFourPruning.stateRows6_3_3.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root6Node0Step1Chunk6_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows6_3_3 := List.map_id' _

theorem root6Node0Step1Chunk6_3_rows_exact :
    table35Rows6_3 = [RadiusFourPruning.stateRows6_3_0, RadiusFourPruning.stateRows6_3_1, RadiusFourPruning.stateRows6_3_2, RadiusFourPruning.stateRows6_3_3].flatten := by
  change ([RadiusFourPruning.stateRows6_3_0, RadiusFourPruning.stateRows6_3_1, RadiusFourPruning.stateRows6_3_2, RadiusFourPruning.stateRows6_3_3].flatten).map table35Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows6_3_0.map table35Project, RadiusFourPruning.stateRows6_3_1.map table35Project, RadiusFourPruning.stateRows6_3_2.map table35Project, RadiusFourPruning.stateRows6_3_3.map table35Project].flatten = _
  rw [root6Node0Step1Chunk6_3_rows0_binding, root6Node0Step1Chunk6_3_rows1_binding, root6Node0Step1Chunk6_3_rows2_binding, root6Node0Step1Chunk6_3_rows3_binding]

#print axioms root6Node0Step1Chunk6_3_project_eq_self_of_length
#print axioms root6Node0Step1Chunk6_3_rows_exact
end SpectreFinite.HexSearch.RadiusFive
