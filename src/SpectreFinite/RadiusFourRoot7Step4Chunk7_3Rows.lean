module

public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node0Step4Chunk7_3_project_eq_self_of_length (row : List State) (hlen : row.length = 37) :
    table39Project row = row := by
  have hproject : table39Project row =
      List.ofFn (fun i : Fin 37 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root7Node0Step4Chunk7_3_rows0_binding :
    RadiusThreePruning.stateRows7_3_0.map table39Project = RadiusThreePruning.stateRows7_3_0 := by
  have hlengths : RadiusThreePruning.stateRows7_3_0.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows7_3_0.map table39Project = RadiusThreePruning.stateRows7_3_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step4Chunk7_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows7_3_0 := List.map_id' _

theorem root7Node0Step4Chunk7_3_rows1_binding :
    RadiusThreePruning.stateRows7_3_1.map table39Project = RadiusThreePruning.stateRows7_3_1 := by
  have hlengths : RadiusThreePruning.stateRows7_3_1.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows7_3_1.map table39Project = RadiusThreePruning.stateRows7_3_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step4Chunk7_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows7_3_1 := List.map_id' _

theorem root7Node0Step4Chunk7_3_rows2_binding :
    RadiusThreePruning.stateRows7_3_2.map table39Project = RadiusThreePruning.stateRows7_3_2 := by
  have hlengths : RadiusThreePruning.stateRows7_3_2.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows7_3_2.map table39Project = RadiusThreePruning.stateRows7_3_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step4Chunk7_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows7_3_2 := List.map_id' _

theorem root7Node0Step4Chunk7_3_rows3_binding :
    RadiusThreePruning.stateRows7_3_3.map table39Project = RadiusThreePruning.stateRows7_3_3 := by
  have hlengths : RadiusThreePruning.stateRows7_3_3.all (fun row => decide (row.length = 37)) = true := by
    decide
  calc
    RadiusThreePruning.stateRows7_3_3.map table39Project = RadiusThreePruning.stateRows7_3_3.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step4Chunk7_3_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusThreePruning.stateRows7_3_3 := List.map_id' _

theorem root7Node0Step4Chunk7_3_rows_exact :
    table39Rows7_3 = [RadiusThreePruning.stateRows7_3_0, RadiusThreePruning.stateRows7_3_1, RadiusThreePruning.stateRows7_3_2, RadiusThreePruning.stateRows7_3_3].flatten := by
  change ([RadiusThreePruning.stateRows7_3_0, RadiusThreePruning.stateRows7_3_1, RadiusThreePruning.stateRows7_3_2, RadiusThreePruning.stateRows7_3_3].flatten).map table39Project = _
  rw [List.map_flatten]
  change [RadiusThreePruning.stateRows7_3_0.map table39Project, RadiusThreePruning.stateRows7_3_1.map table39Project, RadiusThreePruning.stateRows7_3_2.map table39Project, RadiusThreePruning.stateRows7_3_3.map table39Project].flatten = _
  rw [root7Node0Step4Chunk7_3_rows0_binding, root7Node0Step4Chunk7_3_rows1_binding, root7Node0Step4Chunk7_3_rows2_binding, root7Node0Step4Chunk7_3_rows3_binding]

#print axioms root7Node0Step4Chunk7_3_project_eq_self_of_length
#print axioms root7Node0Step4Chunk7_3_rows_exact
end SpectreFinite.HexSearch.RadiusFour
