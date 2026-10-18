module

public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root5Node0Step1Chunk5_4_project_eq_self_of_length (row : List State) (hlen : row.length = 61) :
    table56Project row = row := by
  have hproject : table56Project row =
      List.ofFn (fun i : Fin 61 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root5Node0Step1Chunk5_4_rows0_binding :
    RadiusFourPruning.stateRows5_4_0.map table56Project = RadiusFourPruning.stateRows5_4_0 := by
  have hlengths : RadiusFourPruning.stateRows5_4_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows5_4_0.map table56Project = RadiusFourPruning.stateRows5_4_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root5Node0Step1Chunk5_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows5_4_0 := List.map_id' _

theorem root5Node0Step1Chunk5_4_rows1_binding :
    RadiusFourPruning.stateRows5_4_1.map table56Project = RadiusFourPruning.stateRows5_4_1 := by
  have hlengths : RadiusFourPruning.stateRows5_4_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows5_4_1.map table56Project = RadiusFourPruning.stateRows5_4_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root5Node0Step1Chunk5_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows5_4_1 := List.map_id' _

theorem root5Node0Step1Chunk5_4_rows2_binding :
    RadiusFourPruning.stateRows5_4_2.map table56Project = RadiusFourPruning.stateRows5_4_2 := by
  have hlengths : RadiusFourPruning.stateRows5_4_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows5_4_2.map table56Project = RadiusFourPruning.stateRows5_4_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root5Node0Step1Chunk5_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows5_4_2 := List.map_id' _

theorem root5Node0Step1Chunk5_4_rows_exact :
    table56Rows5_4 = [RadiusFourPruning.stateRows5_4_0, RadiusFourPruning.stateRows5_4_1, RadiusFourPruning.stateRows5_4_2].flatten := by
  change ([RadiusFourPruning.stateRows5_4_0, RadiusFourPruning.stateRows5_4_1, RadiusFourPruning.stateRows5_4_2].flatten).map table56Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows5_4_0.map table56Project, RadiusFourPruning.stateRows5_4_1.map table56Project, RadiusFourPruning.stateRows5_4_2.map table56Project].flatten = _
  rw [root5Node0Step1Chunk5_4_rows0_binding, root5Node0Step1Chunk5_4_rows1_binding, root5Node0Step1Chunk5_4_rows2_binding]

#print axioms root5Node0Step1Chunk5_4_project_eq_self_of_length
#print axioms root5Node0Step1Chunk5_4_rows_exact
end SpectreFinite.HexSearch.RadiusFive
