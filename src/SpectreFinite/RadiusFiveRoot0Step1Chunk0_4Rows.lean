module

public import SpectreFinite.RadiusFiveTable45
public import SpectreFinite.RadiusFiveListProjectionIdentity

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem root0Node0Step1Chunk0_4_project_eq_self_of_length (row : List State) (hlen : row.length = 61) :
    table45Project row = row := by
  have hproject : table45Project row =
      List.ofFn (fun i : Fin 61 => row[i.val]?.getD (0,0)) := by
    rfl
  exact hproject.trans (list_ofFn_getD_eq_self_of_length row (0,0) hlen)

theorem root0Node0Step1Chunk0_4_rows0_binding :
    RadiusFourPruning.stateRows0_4_0.map table45Project = RadiusFourPruning.stateRows0_4_0 := by
  have hlengths : RadiusFourPruning.stateRows0_4_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows0_4_0.map table45Project = RadiusFourPruning.stateRows0_4_0.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root0Node0Step1Chunk0_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows0_4_0 := List.map_id' _

theorem root0Node0Step1Chunk0_4_rows1_binding :
    RadiusFourPruning.stateRows0_4_1.map table45Project = RadiusFourPruning.stateRows0_4_1 := by
  have hlengths : RadiusFourPruning.stateRows0_4_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows0_4_1.map table45Project = RadiusFourPruning.stateRows0_4_1.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root0Node0Step1Chunk0_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows0_4_1 := List.map_id' _

theorem root0Node0Step1Chunk0_4_rows2_binding :
    RadiusFourPruning.stateRows0_4_2.map table45Project = RadiusFourPruning.stateRows0_4_2 := by
  have hlengths : RadiusFourPruning.stateRows0_4_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  calc
    RadiusFourPruning.stateRows0_4_2.map table45Project = RadiusFourPruning.stateRows0_4_2.map (fun row => row) := by
      apply List.map_congr_left
      intro row hrow
      apply root0Node0Step1Chunk0_4_project_eq_self_of_length
      exact of_decide_eq_true (List.all_eq_true.mp hlengths row hrow)
    _ = RadiusFourPruning.stateRows0_4_2 := List.map_id' _

theorem root0Node0Step1Chunk0_4_rows_exact :
    table45Rows0_4 = [RadiusFourPruning.stateRows0_4_0, RadiusFourPruning.stateRows0_4_1, RadiusFourPruning.stateRows0_4_2].flatten := by
  change ([RadiusFourPruning.stateRows0_4_0, RadiusFourPruning.stateRows0_4_1, RadiusFourPruning.stateRows0_4_2].flatten).map table45Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows0_4_0.map table45Project, RadiusFourPruning.stateRows0_4_1.map table45Project, RadiusFourPruning.stateRows0_4_2.map table45Project].flatten = _
  rw [root0Node0Step1Chunk0_4_rows0_binding, root0Node0Step1Chunk0_4_rows1_binding, root0Node0Step1Chunk0_4_rows2_binding]

#print axioms root0Node0Step1Chunk0_4_project_eq_self_of_length
#print axioms root0Node0Step1Chunk0_4_rows_exact
end SpectreFinite.HexSearch.RadiusFive
