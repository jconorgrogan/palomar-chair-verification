module

public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root8Node0Step1Chunk8_0_project_eq_self_of_length (row : List State) (hlen : row.length = 61) :
    table56Project row = row := by
  have hproject : table56Project row =
      List.ofFn (fun i : Fin 61 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root8Node0Step1Chunk8_0_rows0_binding :
    RadiusFourPruning.stateRows8_0_0.map table56Project = RadiusFourPruning.stateRows8_0_0 := by
  have hlengths : RadiusFourPruning.stateRows8_0_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows8_0_0.map table56Project = RadiusFourPruning.stateRows8_0_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows8_0_0 := List.map_id' _

theorem root8Node0Step1Chunk8_0_rows1_binding :
    RadiusFourPruning.stateRows8_0_1.map table56Project = RadiusFourPruning.stateRows8_0_1 := by
  have hlengths : RadiusFourPruning.stateRows8_0_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows8_0_1.map table56Project = RadiusFourPruning.stateRows8_0_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows8_0_1 := List.map_id' _

theorem root8Node0Step1Chunk8_0_rows2_binding :
    RadiusFourPruning.stateRows8_0_2.map table56Project = RadiusFourPruning.stateRows8_0_2 := by
  have hlengths : RadiusFourPruning.stateRows8_0_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows8_0_2.map table56Project = RadiusFourPruning.stateRows8_0_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows8_0_2 := List.map_id' _

theorem root8Node0Step1Chunk8_0_rows3_binding :
    RadiusFourPruning.stateRows8_0_3.map table56Project = RadiusFourPruning.stateRows8_0_3 := by
  have hlengths : RadiusFourPruning.stateRows8_0_3.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows8_0_3.map table56Project = RadiusFourPruning.stateRows8_0_3.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows8_0_3 := List.map_id' _

theorem root8Node0Step1Chunk8_0_rows4_binding :
    RadiusFourPruning.stateRows8_0_4.map table56Project = RadiusFourPruning.stateRows8_0_4 := by
  have hlengths : RadiusFourPruning.stateRows8_0_4.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows8_0_4.map table56Project = RadiusFourPruning.stateRows8_0_4.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows8_0_4 := List.map_id' _

theorem root8Node0Step1Chunk8_0_rows_exact :
    table56Rows8_0 = [RadiusFourPruning.stateRows8_0_0, RadiusFourPruning.stateRows8_0_1, RadiusFourPruning.stateRows8_0_2, RadiusFourPruning.stateRows8_0_3, RadiusFourPruning.stateRows8_0_4].flatten := by
  change ([RadiusFourPruning.stateRows8_0_0, RadiusFourPruning.stateRows8_0_1, RadiusFourPruning.stateRows8_0_2, RadiusFourPruning.stateRows8_0_3, RadiusFourPruning.stateRows8_0_4].flatten).map table56Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows8_0_0.map table56Project, RadiusFourPruning.stateRows8_0_1.map table56Project, RadiusFourPruning.stateRows8_0_2.map table56Project, RadiusFourPruning.stateRows8_0_3.map table56Project, RadiusFourPruning.stateRows8_0_4.map table56Project].flatten = _
  rw [root8Node0Step1Chunk8_0_rows0_binding, root8Node0Step1Chunk8_0_rows1_binding, root8Node0Step1Chunk8_0_rows2_binding, root8Node0Step1Chunk8_0_rows3_binding, root8Node0Step1Chunk8_0_rows4_binding]

#print axioms root8Node0Step1Chunk8_0_project_eq_self_of_length
#print axioms root8Node0Step1Chunk8_0_rows_exact
end SpectreFinite.HexSearch.RadiusFive
