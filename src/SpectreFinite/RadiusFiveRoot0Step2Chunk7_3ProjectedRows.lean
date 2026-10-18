module

public import SpectreFinite.RadiusFiveTable57
public import SpectreFinite.RadiusFiveListProjectionRuns

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
open HigherFastChecking
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def root0Node0Step2Chunk7_3_runProjection (row : List State) : List State :=
  (row.drop 0).take 34 ++ (row.drop 35).take 7 ++ (row.drop 43).take 6 ++ (row.drop 50).take 5 ++ (row.drop 56).take 4

theorem root0Node0Step2Chunk7_3_project_runs_eq (row : List State) (hlen : row.length = 61) :
    table57Project row = root0Node0Step2Chunk7_3_runProjection row := by
  have hexpansion : table57Project row =
      List.ofFn (fun i : Fin 34 => row[0 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 7 => row[35 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 6 => row[43 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 5 => row[50 + i.val]?.getD (0,0)) ++ List.ofFn (fun i : Fin 4 => row[56 + i.val]?.getD (0,0)) := by
    rfl
  rw [hexpansion]
  unfold root0Node0Step2Chunk7_3_runProjection
  rw [list_ofFn_getD_drop_take row (0,0) 0 34 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 35 7 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 43 6 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 50 5 (by rw [List.length_drop, hlen]; decide), list_ofFn_getD_drop_take row (0,0) 56 4 (by rw [List.length_drop, hlen]; decide)]

def root0Node0Step2Chunk7_3_projectedRows0 : List (List State) :=
  RadiusFourPruning.stateRows7_3_0.map root0Node0Step2Chunk7_3_runProjection

theorem root0Node0Step2Chunk7_3_projected_rows0_binding :
    RadiusFourPruning.stateRows7_3_0.map table57Project = root0Node0Step2Chunk7_3_projectedRows0 := by
  have hlengths : RadiusFourPruning.stateRows7_3_0.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows7_3_0.map table57Project = RadiusFourPruning.stateRows7_3_0.map root0Node0Step2Chunk7_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step2Chunk7_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step2Chunk7_3_projectedRows1 : List (List State) :=
  RadiusFourPruning.stateRows7_3_1.map root0Node0Step2Chunk7_3_runProjection

theorem root0Node0Step2Chunk7_3_projected_rows1_binding :
    RadiusFourPruning.stateRows7_3_1.map table57Project = root0Node0Step2Chunk7_3_projectedRows1 := by
  have hlengths : RadiusFourPruning.stateRows7_3_1.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows7_3_1.map table57Project = RadiusFourPruning.stateRows7_3_1.map root0Node0Step2Chunk7_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step2Chunk7_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step2Chunk7_3_projectedRows2 : List (List State) :=
  RadiusFourPruning.stateRows7_3_2.map root0Node0Step2Chunk7_3_runProjection

theorem root0Node0Step2Chunk7_3_projected_rows2_binding :
    RadiusFourPruning.stateRows7_3_2.map table57Project = root0Node0Step2Chunk7_3_projectedRows2 := by
  have hlengths : RadiusFourPruning.stateRows7_3_2.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows7_3_2.map table57Project = RadiusFourPruning.stateRows7_3_2.map root0Node0Step2Chunk7_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step2Chunk7_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step2Chunk7_3_projectedRows3 : List (List State) :=
  RadiusFourPruning.stateRows7_3_3.map root0Node0Step2Chunk7_3_runProjection

theorem root0Node0Step2Chunk7_3_projected_rows3_binding :
    RadiusFourPruning.stateRows7_3_3.map table57Project = root0Node0Step2Chunk7_3_projectedRows3 := by
  have hlengths : RadiusFourPruning.stateRows7_3_3.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows7_3_3.map table57Project = RadiusFourPruning.stateRows7_3_3.map root0Node0Step2Chunk7_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step2Chunk7_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step2Chunk7_3_projectedRows4 : List (List State) :=
  RadiusFourPruning.stateRows7_3_4.map root0Node0Step2Chunk7_3_runProjection

theorem root0Node0Step2Chunk7_3_projected_rows4_binding :
    RadiusFourPruning.stateRows7_3_4.map table57Project = root0Node0Step2Chunk7_3_projectedRows4 := by
  have hlengths : RadiusFourPruning.stateRows7_3_4.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows7_3_4.map table57Project = RadiusFourPruning.stateRows7_3_4.map root0Node0Step2Chunk7_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step2Chunk7_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step2Chunk7_3_projectedRows5 : List (List State) :=
  RadiusFourPruning.stateRows7_3_5.map root0Node0Step2Chunk7_3_runProjection

theorem root0Node0Step2Chunk7_3_projected_rows5_binding :
    RadiusFourPruning.stateRows7_3_5.map table57Project = root0Node0Step2Chunk7_3_projectedRows5 := by
  have hlengths : RadiusFourPruning.stateRows7_3_5.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows7_3_5.map table57Project = RadiusFourPruning.stateRows7_3_5.map root0Node0Step2Chunk7_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step2Chunk7_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

def root0Node0Step2Chunk7_3_projectedRows6 : List (List State) :=
  RadiusFourPruning.stateRows7_3_6.map root0Node0Step2Chunk7_3_runProjection

theorem root0Node0Step2Chunk7_3_projected_rows6_binding :
    RadiusFourPruning.stateRows7_3_6.map table57Project = root0Node0Step2Chunk7_3_projectedRows6 := by
  have hlengths : RadiusFourPruning.stateRows7_3_6.all (fun row => decide (row.length = 61)) = true := by
    decide
  change RadiusFourPruning.stateRows7_3_6.map table57Project = RadiusFourPruning.stateRows7_3_6.map root0Node0Step2Chunk7_3_runProjection
  apply List.map_congr_left
  intro row hrow
  exact root0Node0Step2Chunk7_3_project_runs_eq row
    (of_decide_eq_true (List.all_eq_true.mp hlengths row hrow))

theorem root0Node0Step2Chunk7_3_projected_rows_exact :
    table57Rows7_3 = [root0Node0Step2Chunk7_3_projectedRows0, root0Node0Step2Chunk7_3_projectedRows1, root0Node0Step2Chunk7_3_projectedRows2, root0Node0Step2Chunk7_3_projectedRows3, root0Node0Step2Chunk7_3_projectedRows4, root0Node0Step2Chunk7_3_projectedRows5, root0Node0Step2Chunk7_3_projectedRows6].flatten := by
  change ([RadiusFourPruning.stateRows7_3_0, RadiusFourPruning.stateRows7_3_1, RadiusFourPruning.stateRows7_3_2, RadiusFourPruning.stateRows7_3_3, RadiusFourPruning.stateRows7_3_4, RadiusFourPruning.stateRows7_3_5, RadiusFourPruning.stateRows7_3_6].flatten).map table57Project = _
  rw [List.map_flatten]
  change [RadiusFourPruning.stateRows7_3_0.map table57Project, RadiusFourPruning.stateRows7_3_1.map table57Project, RadiusFourPruning.stateRows7_3_2.map table57Project, RadiusFourPruning.stateRows7_3_3.map table57Project, RadiusFourPruning.stateRows7_3_4.map table57Project, RadiusFourPruning.stateRows7_3_5.map table57Project, RadiusFourPruning.stateRows7_3_6.map table57Project].flatten = _
  rw [root0Node0Step2Chunk7_3_projected_rows0_binding, root0Node0Step2Chunk7_3_projected_rows1_binding, root0Node0Step2Chunk7_3_projected_rows2_binding, root0Node0Step2Chunk7_3_projected_rows3_binding, root0Node0Step2Chunk7_3_projected_rows4_binding, root0Node0Step2Chunk7_3_projected_rows5_binding, root0Node0Step2Chunk7_3_projected_rows6_binding]

#print axioms root0Node0Step2Chunk7_3_project_runs_eq
#print axioms root0Node0Step2Chunk7_3_projected_rows_exact
end SpectreFinite.HexSearch.RadiusFive
