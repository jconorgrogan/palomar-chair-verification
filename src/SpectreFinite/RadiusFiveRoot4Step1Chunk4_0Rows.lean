module

public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root4Node0Step1Chunk4_0_project_eq_self_of_length (row : List State) (hlen : row.length = 61) :
    table56Project row = row := by
  have hproject : table56Project row =
      List.ofFn (fun i : Fin 61 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root4Node0Step1Chunk4_0_rows0_binding :
    RadiusFourPruning.stateRows4_0_0.map table56Project = RadiusFourPruning.stateRows4_0_0 := by
  have hlengths : RadiusFourPruning.stateRows4_0_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows4_0_0.map table56Project = RadiusFourPruning.stateRows4_0_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root4Node0Step1Chunk4_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows4_0_0 := List.map_id' _

theorem root4Node0Step1Chunk4_0_rows1_binding :
    RadiusFourPruning.stateRows4_0_1.map table56Project = RadiusFourPruning.stateRows4_0_1 := by
  have hlengths : RadiusFourPruning.stateRows4_0_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows4_0_1.map table56Project = RadiusFourPruning.stateRows4_0_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root4Node0Step1Chunk4_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows4_0_1 := List.map_id' _

theorem root4Node0Step1Chunk4_0_rows2_binding :
    RadiusFourPruning.stateRows4_0_2.map table56Project = RadiusFourPruning.stateRows4_0_2 := by
  have hlengths : RadiusFourPruning.stateRows4_0_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows4_0_2.map table56Project = RadiusFourPruning.stateRows4_0_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root4Node0Step1Chunk4_0_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows4_0_2 := List.map_id' _

theorem root4Node0Step1Chunk4_0_rows_exact :
    table56Rows4_0 = [RadiusFourPruning.stateRows4_0_0, RadiusFourPruning.stateRows4_0_1, RadiusFourPruning.stateRows4_0_2].flatten := by
  change ([RadiusFourPruning.stateRows4_0_0, RadiusFourPruning.stateRows4_0_1, RadiusFourPruning.stateRows4_0_2].flatten).map table56Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows4_0_0.map table56Project, RadiusFourPruning.stateRows4_0_1.map table56Project, RadiusFourPruning.stateRows4_0_2.map table56Project].flatten = _
  rw [root4Node0Step1Chunk4_0_rows0_binding, root4Node0Step1Chunk4_0_rows1_binding, root4Node0Step1Chunk4_0_rows2_binding]

#print axioms root4Node0Step1Chunk4_0_project_eq_self_of_length
#print axioms root4Node0Step1Chunk4_0_rows_exact
end SpectreFinite.HexSearch.RadiusFive
