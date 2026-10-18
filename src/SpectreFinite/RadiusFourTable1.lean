module

public import SpectreFinite.RadiusFourSourceCanonical

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def table1Scope : List (Fin 61) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 19, 20, 21, 22]
theorem table1Scope_eq : table1Scope = windowScope positions (hexRegion 3) (-4,1) := by rfl
def table1Project (row : List State) : List State := [row[17]?.getD (0,0),row[18]?.getD (0,0),row[19]?.getD (0,0),row[20]?.getD (0,0),row[21]?.getD (0,0),row[23]?.getD (0,0),row[24]?.getD (0,0),row[25]?.getD (0,0),row[26]?.getD (0,0),row[27]?.getD (0,0),row[28]?.getD (0,0),row[29]?.getD (0,0),row[30]?.getD (0,0),row[31]?.getD (0,0),row[32]?.getD (0,0),row[33]?.getD (0,0),row[34]?.getD (0,0),row[35]?.getD (0,0),row[36]?.getD (0,0)]
theorem table1Project_eq (row : List State) : table1Project row =
    table1Scope.map (fun v => patchState ((hexRegion 3).zip row)
      (subPos (positions v) (-4,1))) := by
  change [row[17]?.getD (0,0),row[18]?.getD (0,0),row[19]?.getD (0,0),row[20]?.getD (0,0),row[21]?.getD (0,0),row[23]?.getD (0,0),row[24]?.getD (0,0),row[25]?.getD (0,0),row[26]?.getD (0,0),row[27]?.getD (0,0),row[28]?.getD (0,0),row[29]?.getD (0,0),row[30]?.getD (0,0),row[31]?.getD (0,0),row[32]?.getD (0,0),row[33]?.getD (0,0),row[34]?.getD (0,0),row[35]?.getD (0,0),row[36]?.getD (0,0)] = [patchState ((hexRegion 3).zip row) (0,-1),patchState ((hexRegion 3).zip row) (0,0),patchState ((hexRegion 3).zip row) (0,1),patchState ((hexRegion 3).zip row) (0,2),patchState ((hexRegion 3).zip row) (0,3),patchState ((hexRegion 3).zip row) (1,-2),patchState ((hexRegion 3).zip row) (1,-1),patchState ((hexRegion 3).zip row) (1,0),patchState ((hexRegion 3).zip row) (1,1),patchState ((hexRegion 3).zip row) (1,2),patchState ((hexRegion 3).zip row) (2,-3),patchState ((hexRegion 3).zip row) (2,-2),patchState ((hexRegion 3).zip row) (2,-1),patchState ((hexRegion 3).zip row) (2,0),patchState ((hexRegion 3).zip row) (2,1),patchState ((hexRegion 3).zip row) (3,-3),patchState ((hexRegion 3).zip row) (3,-2),patchState ((hexRegion 3).zip row) (3,-1),patchState ((hexRegion 3).zip row) (3,0)]
  rw [patchState_zip_index (hexRegion 3) row (0,-1) 17 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,0) 18 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,1) 19 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,2) 20 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,3) 21 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,-2) 23 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,-1) 24 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,0) 25 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,1) 26 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,2) 27 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (2,-3) 28 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (2,-2) 29 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (2,-1) 30 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (2,0) 31 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (2,1) 32 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (3,-3) 33 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (3,-2) 34 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (3,-1) 35 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (3,0) 36 (by decide) (by decide)]
def table1Rows0_0 : List (List State) := sourceRows0_0.map table1Project
theorem table1Rows0_0_eq : table1Rows0_0 = RadiusThreePruning.final0_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical0_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows0_1 : List (List State) := sourceRows0_1.map table1Project
theorem table1Rows0_1_eq : table1Rows0_1 = RadiusThreePruning.final0_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical0_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows0_2 : List (List State) := sourceRows0_2.map table1Project
theorem table1Rows0_2_eq : table1Rows0_2 = RadiusThreePruning.final0_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical0_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows0_3 : List (List State) := sourceRows0_3.map table1Project
theorem table1Rows0_3_eq : table1Rows0_3 = RadiusThreePruning.final0_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical0_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows0_4 : List (List State) := sourceRows0_4.map table1Project
theorem table1Rows0_4_eq : table1Rows0_4 = RadiusThreePruning.final0_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical0_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows0_5 : List (List State) := sourceRows0_5.map table1Project
theorem table1Rows0_5_eq : table1Rows0_5 = RadiusThreePruning.final0_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical0_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows1_0 : List (List State) := sourceRows1_0.map table1Project
theorem table1Rows1_0_eq : table1Rows1_0 = RadiusThreePruning.final1_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical1_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows1_1 : List (List State) := sourceRows1_1.map table1Project
theorem table1Rows1_1_eq : table1Rows1_1 = RadiusThreePruning.final1_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical1_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows1_2 : List (List State) := sourceRows1_2.map table1Project
theorem table1Rows1_2_eq : table1Rows1_2 = RadiusThreePruning.final1_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical1_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows1_3 : List (List State) := sourceRows1_3.map table1Project
theorem table1Rows1_3_eq : table1Rows1_3 = RadiusThreePruning.final1_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical1_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows1_4 : List (List State) := sourceRows1_4.map table1Project
theorem table1Rows1_4_eq : table1Rows1_4 = RadiusThreePruning.final1_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical1_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows1_5 : List (List State) := sourceRows1_5.map table1Project
theorem table1Rows1_5_eq : table1Rows1_5 = RadiusThreePruning.final1_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical1_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows2_0 : List (List State) := sourceRows2_0.map table1Project
theorem table1Rows2_0_eq : table1Rows2_0 = RadiusThreePruning.final2_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical2_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows2_1 : List (List State) := sourceRows2_1.map table1Project
theorem table1Rows2_1_eq : table1Rows2_1 = RadiusThreePruning.final2_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical2_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows2_2 : List (List State) := sourceRows2_2.map table1Project
theorem table1Rows2_2_eq : table1Rows2_2 = RadiusThreePruning.final2_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical2_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows2_3 : List (List State) := sourceRows2_3.map table1Project
theorem table1Rows2_3_eq : table1Rows2_3 = RadiusThreePruning.final2_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical2_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows2_4 : List (List State) := sourceRows2_4.map table1Project
theorem table1Rows2_4_eq : table1Rows2_4 = RadiusThreePruning.final2_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical2_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows2_5 : List (List State) := sourceRows2_5.map table1Project
theorem table1Rows2_5_eq : table1Rows2_5 = RadiusThreePruning.final2_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical2_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows3_0 : List (List State) := sourceRows3_0.map table1Project
theorem table1Rows3_0_eq : table1Rows3_0 = RadiusThreePruning.final3_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical3_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows3_1 : List (List State) := sourceRows3_1.map table1Project
theorem table1Rows3_1_eq : table1Rows3_1 = RadiusThreePruning.final3_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical3_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows3_2 : List (List State) := sourceRows3_2.map table1Project
theorem table1Rows3_2_eq : table1Rows3_2 = RadiusThreePruning.final3_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical3_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows3_3 : List (List State) := sourceRows3_3.map table1Project
theorem table1Rows3_3_eq : table1Rows3_3 = RadiusThreePruning.final3_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical3_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows3_4 : List (List State) := sourceRows3_4.map table1Project
theorem table1Rows3_4_eq : table1Rows3_4 = RadiusThreePruning.final3_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical3_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows3_5 : List (List State) := sourceRows3_5.map table1Project
theorem table1Rows3_5_eq : table1Rows3_5 = RadiusThreePruning.final3_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical3_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows4_0 : List (List State) := sourceRows4_0.map table1Project
theorem table1Rows4_0_eq : table1Rows4_0 = RadiusThreePruning.final4_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical4_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows4_1 : List (List State) := sourceRows4_1.map table1Project
theorem table1Rows4_1_eq : table1Rows4_1 = RadiusThreePruning.final4_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical4_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows4_2 : List (List State) := sourceRows4_2.map table1Project
theorem table1Rows4_2_eq : table1Rows4_2 = RadiusThreePruning.final4_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical4_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows4_3 : List (List State) := sourceRows4_3.map table1Project
theorem table1Rows4_3_eq : table1Rows4_3 = RadiusThreePruning.final4_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical4_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows4_4 : List (List State) := sourceRows4_4.map table1Project
theorem table1Rows4_4_eq : table1Rows4_4 = RadiusThreePruning.final4_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical4_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows4_5 : List (List State) := sourceRows4_5.map table1Project
theorem table1Rows4_5_eq : table1Rows4_5 = RadiusThreePruning.final4_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical4_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows5_0 : List (List State) := sourceRows5_0.map table1Project
theorem table1Rows5_0_eq : table1Rows5_0 = RadiusThreePruning.final5_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical5_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows5_1 : List (List State) := sourceRows5_1.map table1Project
theorem table1Rows5_1_eq : table1Rows5_1 = RadiusThreePruning.final5_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical5_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows5_2 : List (List State) := sourceRows5_2.map table1Project
theorem table1Rows5_2_eq : table1Rows5_2 = RadiusThreePruning.final5_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical5_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows5_3 : List (List State) := sourceRows5_3.map table1Project
theorem table1Rows5_3_eq : table1Rows5_3 = RadiusThreePruning.final5_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical5_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows5_4 : List (List State) := sourceRows5_4.map table1Project
theorem table1Rows5_4_eq : table1Rows5_4 = RadiusThreePruning.final5_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical5_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows5_5 : List (List State) := sourceRows5_5.map table1Project
theorem table1Rows5_5_eq : table1Rows5_5 = RadiusThreePruning.final5_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical5_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows6_0 : List (List State) := sourceRows6_0.map table1Project
theorem table1Rows6_0_eq : table1Rows6_0 = RadiusThreePruning.final6_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical6_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows6_1 : List (List State) := sourceRows6_1.map table1Project
theorem table1Rows6_1_eq : table1Rows6_1 = RadiusThreePruning.final6_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical6_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows6_2 : List (List State) := sourceRows6_2.map table1Project
theorem table1Rows6_2_eq : table1Rows6_2 = RadiusThreePruning.final6_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical6_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows6_3 : List (List State) := sourceRows6_3.map table1Project
theorem table1Rows6_3_eq : table1Rows6_3 = RadiusThreePruning.final6_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical6_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows6_4 : List (List State) := sourceRows6_4.map table1Project
theorem table1Rows6_4_eq : table1Rows6_4 = RadiusThreePruning.final6_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical6_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows6_5 : List (List State) := sourceRows6_5.map table1Project
theorem table1Rows6_5_eq : table1Rows6_5 = RadiusThreePruning.final6_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical6_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows7_0 : List (List State) := sourceRows7_0.map table1Project
theorem table1Rows7_0_eq : table1Rows7_0 = RadiusThreePruning.final7_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical7_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows7_1 : List (List State) := sourceRows7_1.map table1Project
theorem table1Rows7_1_eq : table1Rows7_1 = RadiusThreePruning.final7_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical7_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows7_2 : List (List State) := sourceRows7_2.map table1Project
theorem table1Rows7_2_eq : table1Rows7_2 = RadiusThreePruning.final7_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical7_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows7_3 : List (List State) := sourceRows7_3.map table1Project
theorem table1Rows7_3_eq : table1Rows7_3 = RadiusThreePruning.final7_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical7_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows7_4 : List (List State) := sourceRows7_4.map table1Project
theorem table1Rows7_4_eq : table1Rows7_4 = RadiusThreePruning.final7_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical7_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows7_5 : List (List State) := sourceRows7_5.map table1Project
theorem table1Rows7_5_eq : table1Rows7_5 = RadiusThreePruning.final7_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical7_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows8_0 : List (List State) := sourceRows8_0.map table1Project
theorem table1Rows8_0_eq : table1Rows8_0 = RadiusThreePruning.final8_0.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical8_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows8_1 : List (List State) := sourceRows8_1.map table1Project
theorem table1Rows8_1_eq : table1Rows8_1 = RadiusThreePruning.final8_1.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical8_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows8_2 : List (List State) := sourceRows8_2.map table1Project
theorem table1Rows8_2_eq : table1Rows8_2 = RadiusThreePruning.final8_2.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical8_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows8_3 : List (List State) := sourceRows8_3.map table1Project
theorem table1Rows8_3_eq : table1Rows8_3 = RadiusThreePruning.final8_3.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical8_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows8_4 : List (List State) := sourceRows8_4.map table1Project
theorem table1Rows8_4_eq : table1Rows8_4 = RadiusThreePruning.final8_4.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical8_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1Rows8_5 : List (List State) := sourceRows8_5.map table1Project
theorem table1Rows8_5_eq : table1Rows8_5 = RadiusThreePruning.final8_5.map (fun p =>
    table1Scope.map (fun v => patchState p (subPos (positions v) (-4,1)))) := by
  rw [sourceRowsCanonical8_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table1Project_eq row
def table1 : Constraint 61 State := ⟨table1Scope, [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5].flatten⟩
theorem table1_eq : table1 = windowConstraint positions (hexRegion 3)
    RadiusThreePruning.certifiedFamily (-4,1) := by
  unfold table1 windowConstraint
  rw [← table1Scope_eq]
  simp only [RadiusThreePruning.certifiedFamily, RadiusThreePruning.finalChunks, List.map_flatten,
    List.map_cons, List.map_nil, ← table1Rows0_0_eq, ← table1Rows0_1_eq, ← table1Rows0_2_eq, ← table1Rows0_3_eq, ← table1Rows0_4_eq, ← table1Rows0_5_eq, ← table1Rows1_0_eq, ← table1Rows1_1_eq, ← table1Rows1_2_eq, ← table1Rows1_3_eq, ← table1Rows1_4_eq, ← table1Rows1_5_eq, ← table1Rows2_0_eq, ← table1Rows2_1_eq, ← table1Rows2_2_eq, ← table1Rows2_3_eq, ← table1Rows2_4_eq, ← table1Rows2_5_eq, ← table1Rows3_0_eq, ← table1Rows3_1_eq, ← table1Rows3_2_eq, ← table1Rows3_3_eq, ← table1Rows3_4_eq, ← table1Rows3_5_eq, ← table1Rows4_0_eq, ← table1Rows4_1_eq, ← table1Rows4_2_eq, ← table1Rows4_3_eq, ← table1Rows4_4_eq, ← table1Rows4_5_eq, ← table1Rows5_0_eq, ← table1Rows5_1_eq, ← table1Rows5_2_eq, ← table1Rows5_3_eq, ← table1Rows5_4_eq, ← table1Rows5_5_eq, ← table1Rows6_0_eq, ← table1Rows6_1_eq, ← table1Rows6_2_eq, ← table1Rows6_3_eq, ← table1Rows6_4_eq, ← table1Rows6_5_eq, ← table1Rows7_0_eq, ← table1Rows7_1_eq, ← table1Rows7_2_eq, ← table1Rows7_3_eq, ← table1Rows7_4_eq, ← table1Rows7_5_eq, ← table1Rows8_0_eq, ← table1Rows8_1_eq, ← table1Rows8_2_eq, ← table1Rows8_3_eq, ← table1Rows8_4_eq, ← table1Rows8_5_eq]
theorem table1_member : table1 ∈ constraints := by
  rw [table1_eq]
  exact List.mem_map.mpr ⟨(-4,1), by decide, rfl⟩
end SpectreFinite.HexSearch.RadiusFour
