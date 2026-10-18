module

public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveListProjectionRuns

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def root0Node0Step3Chunk6_3_runProjection (row : List State) : List State :=
  (row.drop 1).take 4 ++ (row.drop 6).take 5 ++ (row.drop 12).take 6 ++ (row.drop 19).take 7 ++ (row.drop 27).take 34

theorem root0Node0Step3Chunk6_3_project_runs_eq (row : List State) (hlen : row.length = 61) :
    table33Project row = root0Node0Step3Chunk6_3_runProjection row := by
  have hexpansion : table33Project row =
      List.ofFn (fun i : Fin 4 => row[1 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 5 => row[6 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 6 => row[12 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 7 => row[19 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 34 => row[27 + i.val]?.getD (0,0)) := by
    rfl
  rw [hexpansion]
  unfold root0Node0Step3Chunk6_3_runProjection
  rw [list_ofFn_getD_drop_take row (0,0) 1 4 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 6 5 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 12 6 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 19 7 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 27 34 (by rw [List.length_drop, hlen]; decide)]

def root0Node0Step3Chunk6_3_projectedRows0 : List (List State) :=
  RadiusFourPruning.stateRows6_3_0.map root0Node0Step3Chunk6_3_runProjection

theorem root0Node0Step3Chunk6_3_projected_rows0_binding :
    RadiusFourPruning.stateRows6_3_0.map table33Project = root0Node0Step3Chunk6_3_projectedRows0 := by
  have hlengths : RadiusFourPruning.stateRows6_3_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows6_3_0.map table33Project = RadiusFourPruning.stateRows6_3_0.map root0Node0Step3Chunk6_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step3Chunk6_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step3Chunk6_3_projectedRows1 : List (List State) :=
  RadiusFourPruning.stateRows6_3_1.map root0Node0Step3Chunk6_3_runProjection

theorem root0Node0Step3Chunk6_3_projected_rows1_binding :
    RadiusFourPruning.stateRows6_3_1.map table33Project = root0Node0Step3Chunk6_3_projectedRows1 := by
  have hlengths : RadiusFourPruning.stateRows6_3_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows6_3_1.map table33Project = RadiusFourPruning.stateRows6_3_1.map root0Node0Step3Chunk6_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step3Chunk6_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step3Chunk6_3_projectedRows2 : List (List State) :=
  RadiusFourPruning.stateRows6_3_2.map root0Node0Step3Chunk6_3_runProjection

theorem root0Node0Step3Chunk6_3_projected_rows2_binding :
    RadiusFourPruning.stateRows6_3_2.map table33Project = root0Node0Step3Chunk6_3_projectedRows2 := by
  have hlengths : RadiusFourPruning.stateRows6_3_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows6_3_2.map table33Project = RadiusFourPruning.stateRows6_3_2.map root0Node0Step3Chunk6_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step3Chunk6_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step3Chunk6_3_projectedRows3 : List (List State) :=
  RadiusFourPruning.stateRows6_3_3.map root0Node0Step3Chunk6_3_runProjection

theorem root0Node0Step3Chunk6_3_projected_rows3_binding :
    RadiusFourPruning.stateRows6_3_3.map table33Project = root0Node0Step3Chunk6_3_projectedRows3 := by
  have hlengths : RadiusFourPruning.stateRows6_3_3.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows6_3_3.map table33Project = RadiusFourPruning.stateRows6_3_3.map root0Node0Step3Chunk6_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step3Chunk6_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

theorem root0Node0Step3Chunk6_3_projected_rows_exact :
    table33Rows6_3 = [root0Node0Step3Chunk6_3_projectedRows0, root0Node0Step3Chunk6_3_projectedRows1, root0Node0Step3Chunk6_3_projectedRows2, root0Node0Step3Chunk6_3_projectedRows3].flatten := by
  change ([RadiusFourPruning.stateRows6_3_0, RadiusFourPruning.stateRows6_3_1, RadiusFourPruning.stateRows6_3_2, RadiusFourPruning.stateRows6_3_3].flatten).map table33Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows6_3_0.map table33Project, RadiusFourPruning.stateRows6_3_1.map table33Project, RadiusFourPruning.stateRows6_3_2.map table33Project, RadiusFourPruning.stateRows6_3_3.map table33Project].flatten = _
  rw [root0Node0Step3Chunk6_3_projected_rows0_binding, root0Node0Step3Chunk6_3_projected_rows1_binding, root0Node0Step3Chunk6_3_projected_rows2_binding, root0Node0Step3Chunk6_3_projected_rows3_binding]

#print axioms root0Node0Step3Chunk6_3_project_runs_eq
#print axioms root0Node0Step3Chunk6_3_projected_rows_exact
end SpectreFinite.HexSearch.RadiusFive
