module

public import SpectreFinite.RadiusFourTable30
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root8Node0Step1Chunk8_5_project_eq_self_of_length (row : List State) (hlen : row.length = 37) :
    table30Project row = row := by
  have hproject : table30Project row =
      List.ofFn (fun i : Fin 37 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root8Node0Step1Chunk8_5_rows0_binding :
    RadiusThreePruning.stateRows8_5_0.map table30Project = RadiusThreePruning.stateRows8_5_0 := by
  have hlengths : RadiusThreePruning.stateRows8_5_0.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows8_5_0.map table30Project = RadiusThreePruning.stateRows8_5_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_5_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows8_5_0 := List.map_id' _

theorem root8Node0Step1Chunk8_5_rows1_binding :
    RadiusThreePruning.stateRows8_5_1.map table30Project = RadiusThreePruning.stateRows8_5_1 := by
  have hlengths : RadiusThreePruning.stateRows8_5_1.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows8_5_1.map table30Project = RadiusThreePruning.stateRows8_5_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_5_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows8_5_1 := List.map_id' _

theorem root8Node0Step1Chunk8_5_rows2_binding :
    RadiusThreePruning.stateRows8_5_2.map table30Project = RadiusThreePruning.stateRows8_5_2 := by
  have hlengths : RadiusThreePruning.stateRows8_5_2.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows8_5_2.map table30Project = RadiusThreePruning.stateRows8_5_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_5_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows8_5_2 := List.map_id' _

theorem root8Node0Step1Chunk8_5_rows3_binding :
    RadiusThreePruning.stateRows8_5_3.map table30Project = RadiusThreePruning.stateRows8_5_3 := by
  have hlengths : RadiusThreePruning.stateRows8_5_3.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows8_5_3.map table30Project = RadiusThreePruning.stateRows8_5_3.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root8Node0Step1Chunk8_5_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows8_5_3 := List.map_id' _

theorem root8Node0Step1Chunk8_5_rows_exact :
    table30Rows8_5 = [RadiusThreePruning.stateRows8_5_0, RadiusThreePruning.stateRows8_5_1, RadiusThreePruning.stateRows8_5_2, RadiusThreePruning.stateRows8_5_3].flatten := by
  change ([RadiusThreePruning.stateRows8_5_0, RadiusThreePruning.stateRows8_5_1, RadiusThreePruning.stateRows8_5_2, RadiusThreePruning.stateRows8_5_3].flatten).map table30Project = _
  rw [List.map_flatten]
  change [RadiusThreePruning.stateRows8_5_0.map table30Project, RadiusThreePruning.stateRows8_5_1.map table30Project, RadiusThreePruning.stateRows8_5_2.map table30Project, RadiusThreePruning.stateRows8_5_3.map table30Project].flatten = _
  rw [root8Node0Step1Chunk8_5_rows0_binding, root8Node0Step1Chunk8_5_rows1_binding, root8Node0Step1Chunk8_5_rows2_binding, root8Node0Step1Chunk8_5_rows3_binding]

#print axioms root8Node0Step1Chunk8_5_project_eq_self_of_length
#print axioms root8Node0Step1Chunk8_5_rows_exact
end SpectreFinite.HexSearch.RadiusFour
