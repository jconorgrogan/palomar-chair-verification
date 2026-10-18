module

public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root7Node0Step1Chunk7_0_project_eq_self_of_length (row : List State) (hlen : row.length = 61) :
    table34Project row = row := by
  have hproject : table34Project row =
      List.ofFn (fun i : Fin 61 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root7Node0Step1Chunk7_0_rows0_binding :
    RadiusFourPruning.stateRows7_0_0.map table34Project = RadiusFourPruning.stateRows7_0_0 := by
  have hlengths : RadiusFourPruning.stateRows7_0_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows7_0_0.map table34Project = RadiusFourPruning.stateRows7_0_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step1Chunk7_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows7_0_0 := List.map_id' _

theorem root7Node0Step1Chunk7_0_rows1_binding :
    RadiusFourPruning.stateRows7_0_1.map table34Project = RadiusFourPruning.stateRows7_0_1 := by
  have hlengths : RadiusFourPruning.stateRows7_0_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows7_0_1.map table34Project = RadiusFourPruning.stateRows7_0_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step1Chunk7_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows7_0_1 := List.map_id' _

theorem root7Node0Step1Chunk7_0_rows2_binding :
    RadiusFourPruning.stateRows7_0_2.map table34Project = RadiusFourPruning.stateRows7_0_2 := by
  have hlengths : RadiusFourPruning.stateRows7_0_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows7_0_2.map table34Project = RadiusFourPruning.stateRows7_0_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step1Chunk7_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows7_0_2 := List.map_id' _

theorem root7Node0Step1Chunk7_0_rows3_binding :
    RadiusFourPruning.stateRows7_0_3.map table34Project = RadiusFourPruning.stateRows7_0_3 := by
  have hlengths : RadiusFourPruning.stateRows7_0_3.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows7_0_3.map table34Project = RadiusFourPruning.stateRows7_0_3.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step1Chunk7_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows7_0_3 := List.map_id' _

theorem root7Node0Step1Chunk7_0_rows4_binding :
    RadiusFourPruning.stateRows7_0_4.map table34Project = RadiusFourPruning.stateRows7_0_4 := by
  have hlengths : RadiusFourPruning.stateRows7_0_4.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows7_0_4.map table34Project = RadiusFourPruning.stateRows7_0_4.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step1Chunk7_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows7_0_4 := List.map_id' _

theorem root7Node0Step1Chunk7_0_rows5_binding :
    RadiusFourPruning.stateRows7_0_5.map table34Project = RadiusFourPruning.stateRows7_0_5 := by
  have hlengths : RadiusFourPruning.stateRows7_0_5.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows7_0_5.map table34Project = RadiusFourPruning.stateRows7_0_5.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step1Chunk7_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows7_0_5 := List.map_id' _

theorem root7Node0Step1Chunk7_0_rows6_binding :
    RadiusFourPruning.stateRows7_0_6.map table34Project = RadiusFourPruning.stateRows7_0_6 := by
  have hlengths : RadiusFourPruning.stateRows7_0_6.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows7_0_6.map table34Project = RadiusFourPruning.stateRows7_0_6.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root7Node0Step1Chunk7_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows7_0_6 := List.map_id' _

theorem root7Node0Step1Chunk7_0_rows_exact :
    table34Rows7_0 = [RadiusFourPruning.stateRows7_0_0, RadiusFourPruning.stateRows7_0_1, RadiusFourPruning.stateRows7_0_2, RadiusFourPruning.stateRows7_0_3, RadiusFourPruning.stateRows7_0_4, RadiusFourPruning.stateRows7_0_5, RadiusFourPruning.stateRows7_0_6].flatten := by
  change ([RadiusFourPruning.stateRows7_0_0, RadiusFourPruning.stateRows7_0_1, RadiusFourPruning.stateRows7_0_2, RadiusFourPruning.stateRows7_0_3, RadiusFourPruning.stateRows7_0_4, RadiusFourPruning.stateRows7_0_5, RadiusFourPruning.stateRows7_0_6].flatten).map table34Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows7_0_0.map table34Project, RadiusFourPruning.stateRows7_0_1.map table34Project, RadiusFourPruning.stateRows7_0_2.map table34Project, RadiusFourPruning.stateRows7_0_3.map table34Project, RadiusFourPruning.stateRows7_0_4.map table34Project, RadiusFourPruning.stateRows7_0_5.map table34Project, RadiusFourPruning.stateRows7_0_6.map table34Project].flatten = _
  rw [root7Node0Step1Chunk7_0_rows0_binding, root7Node0Step1Chunk7_0_rows1_binding, root7Node0Step1Chunk7_0_rows2_binding, root7Node0Step1Chunk7_0_rows3_binding, root7Node0Step1Chunk7_0_rows4_binding, root7Node0Step1Chunk7_0_rows5_binding, root7Node0Step1Chunk7_0_rows6_binding]

#print axioms root7Node0Step1Chunk7_0_project_eq_self_of_length
#print axioms root7Node0Step1Chunk7_0_rows_exact
end SpectreFinite.HexSearch.RadiusFive
