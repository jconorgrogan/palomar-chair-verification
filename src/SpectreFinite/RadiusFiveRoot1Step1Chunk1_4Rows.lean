module

public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root1Node0Step1Chunk1_4_project_eq_self_of_length (row : List State) (hlen : row.length = 61) :
    table34Project row = row := by
  have hproject : table34Project row =
      List.ofFn (fun i : Fin 61 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root1Node0Step1Chunk1_4_rows0_binding :
    RadiusFourPruning.stateRows1_4_0.map table34Project = RadiusFourPruning.stateRows1_4_0 := by
  have hlengths : RadiusFourPruning.stateRows1_4_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows1_4_0.map table34Project = RadiusFourPruning.stateRows1_4_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root1Node0Step1Chunk1_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows1_4_0 := List.map_id' _

theorem root1Node0Step1Chunk1_4_rows1_binding :
    RadiusFourPruning.stateRows1_4_1.map table34Project = RadiusFourPruning.stateRows1_4_1 := by
  have hlengths : RadiusFourPruning.stateRows1_4_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows1_4_1.map table34Project = RadiusFourPruning.stateRows1_4_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root1Node0Step1Chunk1_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows1_4_1 := List.map_id' _

theorem root1Node0Step1Chunk1_4_rows2_binding :
    RadiusFourPruning.stateRows1_4_2.map table34Project = RadiusFourPruning.stateRows1_4_2 := by
  have hlengths : RadiusFourPruning.stateRows1_4_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows1_4_2.map table34Project = RadiusFourPruning.stateRows1_4_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root1Node0Step1Chunk1_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows1_4_2 := List.map_id' _

theorem root1Node0Step1Chunk1_4_rows_exact :
    table34Rows1_4 = [RadiusFourPruning.stateRows1_4_0, RadiusFourPruning.stateRows1_4_1, RadiusFourPruning.stateRows1_4_2].flatten := by
  change ([RadiusFourPruning.stateRows1_4_0, RadiusFourPruning.stateRows1_4_1, RadiusFourPruning.stateRows1_4_2].flatten).map table34Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows1_4_0.map table34Project, RadiusFourPruning.stateRows1_4_1.map table34Project, RadiusFourPruning.stateRows1_4_2.map table34Project].flatten = _
  rw [root1Node0Step1Chunk1_4_rows0_binding, root1Node0Step1Chunk1_4_rows1_binding, root1Node0Step1Chunk1_4_rows2_binding]

#print axioms root1Node0Step1Chunk1_4_project_eq_self_of_length
#print axioms root1Node0Step1Chunk1_4_rows_exact
end SpectreFinite.HexSearch.RadiusFive
