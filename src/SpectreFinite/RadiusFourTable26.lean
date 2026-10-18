module

public import SpectreFinite.RadiusFourSourceCanonical

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def table26Scope : List (Fin 61) := [5, 11, 12, 18, 19, 20, 26, 27, 28, 29, 35, 36, 37, 43, 44, 50]
theorem table26Scope_eq : table26Scope = windowScope positions (hexRegion 3) (0,-4) := by rfl
def table26Project (row : List State) : List State := [row[3]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[18]?.getD (0,0),row[19]?.getD (0,0),row[20]?.getD (0,0),row[21]?.getD (0,0),row[25]?.getD (0,0),row[26]?.getD (0,0),row[27]?.getD (0,0),row[31]?.getD (0,0),row[32]?.getD (0,0),row[36]?.getD (0,0)]
theorem table26Project_eq (row : List State) : table26Project row =
    table26Scope.map (fun v => patchState ((hexRegion 3).zip row)
      (subPos (positions v) (0,-4))) := by
  change [row[3]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[18]?.getD (0,0),row[19]?.getD (0,0),row[20]?.getD (0,0),row[21]?.getD (0,0),row[25]?.getD (0,0),row[26]?.getD (0,0),row[27]?.getD (0,0),row[31]?.getD (0,0),row[32]?.getD (0,0),row[36]?.getD (0,0)] = [patchState ((hexRegion 3).zip row) (-3,3),patchState ((hexRegion 3).zip row) (-2,2),patchState ((hexRegion 3).zip row) (-2,3),patchState ((hexRegion 3).zip row) (-1,1),patchState ((hexRegion 3).zip row) (-1,2),patchState ((hexRegion 3).zip row) (-1,3),patchState ((hexRegion 3).zip row) (0,0),patchState ((hexRegion 3).zip row) (0,1),patchState ((hexRegion 3).zip row) (0,2),patchState ((hexRegion 3).zip row) (0,3),patchState ((hexRegion 3).zip row) (1,0),patchState ((hexRegion 3).zip row) (1,1),patchState ((hexRegion 3).zip row) (1,2),patchState ((hexRegion 3).zip row) (2,0),patchState ((hexRegion 3).zip row) (2,1),patchState ((hexRegion 3).zip row) (3,0)]
  rw [patchState_zip_index (hexRegion 3) row (-3,3) 3 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (-2,2) 7 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (-2,3) 8 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (-1,1) 12 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (-1,2) 13 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (-1,3) 14 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,0) 18 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,1) 19 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,2) 20 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (0,3) 21 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,0) 25 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,1) 26 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (1,2) 27 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (2,0) 31 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (2,1) 32 (by decide) (by decide),
    patchState_zip_index (hexRegion 3) row (3,0) 36 (by decide) (by decide)]
def table26Rows0_0 : List (List State) := sourceRows0_0.map table26Project
theorem table26Rows0_0_eq : table26Rows0_0 = RadiusThreePruning.final0_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical0_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows0_1 : List (List State) := sourceRows0_1.map table26Project
theorem table26Rows0_1_eq : table26Rows0_1 = RadiusThreePruning.final0_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical0_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows0_2 : List (List State) := sourceRows0_2.map table26Project
theorem table26Rows0_2_eq : table26Rows0_2 = RadiusThreePruning.final0_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical0_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows0_3 : List (List State) := sourceRows0_3.map table26Project
theorem table26Rows0_3_eq : table26Rows0_3 = RadiusThreePruning.final0_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical0_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows0_4 : List (List State) := sourceRows0_4.map table26Project
theorem table26Rows0_4_eq : table26Rows0_4 = RadiusThreePruning.final0_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical0_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows0_5 : List (List State) := sourceRows0_5.map table26Project
theorem table26Rows0_5_eq : table26Rows0_5 = RadiusThreePruning.final0_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical0_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows1_0 : List (List State) := sourceRows1_0.map table26Project
theorem table26Rows1_0_eq : table26Rows1_0 = RadiusThreePruning.final1_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical1_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows1_1 : List (List State) := sourceRows1_1.map table26Project
theorem table26Rows1_1_eq : table26Rows1_1 = RadiusThreePruning.final1_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical1_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows1_2 : List (List State) := sourceRows1_2.map table26Project
theorem table26Rows1_2_eq : table26Rows1_2 = RadiusThreePruning.final1_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical1_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows1_3 : List (List State) := sourceRows1_3.map table26Project
theorem table26Rows1_3_eq : table26Rows1_3 = RadiusThreePruning.final1_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical1_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows1_4 : List (List State) := sourceRows1_4.map table26Project
theorem table26Rows1_4_eq : table26Rows1_4 = RadiusThreePruning.final1_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical1_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows1_5 : List (List State) := sourceRows1_5.map table26Project
theorem table26Rows1_5_eq : table26Rows1_5 = RadiusThreePruning.final1_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical1_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows2_0 : List (List State) := sourceRows2_0.map table26Project
theorem table26Rows2_0_eq : table26Rows2_0 = RadiusThreePruning.final2_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical2_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows2_1 : List (List State) := sourceRows2_1.map table26Project
theorem table26Rows2_1_eq : table26Rows2_1 = RadiusThreePruning.final2_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical2_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows2_2 : List (List State) := sourceRows2_2.map table26Project
theorem table26Rows2_2_eq : table26Rows2_2 = RadiusThreePruning.final2_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical2_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows2_3 : List (List State) := sourceRows2_3.map table26Project
theorem table26Rows2_3_eq : table26Rows2_3 = RadiusThreePruning.final2_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical2_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows2_4 : List (List State) := sourceRows2_4.map table26Project
theorem table26Rows2_4_eq : table26Rows2_4 = RadiusThreePruning.final2_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical2_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows2_5 : List (List State) := sourceRows2_5.map table26Project
theorem table26Rows2_5_eq : table26Rows2_5 = RadiusThreePruning.final2_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical2_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows3_0 : List (List State) := sourceRows3_0.map table26Project
theorem table26Rows3_0_eq : table26Rows3_0 = RadiusThreePruning.final3_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical3_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows3_1 : List (List State) := sourceRows3_1.map table26Project
theorem table26Rows3_1_eq : table26Rows3_1 = RadiusThreePruning.final3_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical3_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows3_2 : List (List State) := sourceRows3_2.map table26Project
theorem table26Rows3_2_eq : table26Rows3_2 = RadiusThreePruning.final3_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical3_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows3_3 : List (List State) := sourceRows3_3.map table26Project
theorem table26Rows3_3_eq : table26Rows3_3 = RadiusThreePruning.final3_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical3_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows3_4 : List (List State) := sourceRows3_4.map table26Project
theorem table26Rows3_4_eq : table26Rows3_4 = RadiusThreePruning.final3_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical3_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows3_5 : List (List State) := sourceRows3_5.map table26Project
theorem table26Rows3_5_eq : table26Rows3_5 = RadiusThreePruning.final3_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical3_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows4_0 : List (List State) := sourceRows4_0.map table26Project
theorem table26Rows4_0_eq : table26Rows4_0 = RadiusThreePruning.final4_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical4_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows4_1 : List (List State) := sourceRows4_1.map table26Project
theorem table26Rows4_1_eq : table26Rows4_1 = RadiusThreePruning.final4_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical4_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows4_2 : List (List State) := sourceRows4_2.map table26Project
theorem table26Rows4_2_eq : table26Rows4_2 = RadiusThreePruning.final4_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical4_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows4_3 : List (List State) := sourceRows4_3.map table26Project
theorem table26Rows4_3_eq : table26Rows4_3 = RadiusThreePruning.final4_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical4_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows4_4 : List (List State) := sourceRows4_4.map table26Project
theorem table26Rows4_4_eq : table26Rows4_4 = RadiusThreePruning.final4_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical4_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows4_5 : List (List State) := sourceRows4_5.map table26Project
theorem table26Rows4_5_eq : table26Rows4_5 = RadiusThreePruning.final4_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical4_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows5_0 : List (List State) := sourceRows5_0.map table26Project
theorem table26Rows5_0_eq : table26Rows5_0 = RadiusThreePruning.final5_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical5_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows5_1 : List (List State) := sourceRows5_1.map table26Project
theorem table26Rows5_1_eq : table26Rows5_1 = RadiusThreePruning.final5_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical5_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows5_2 : List (List State) := sourceRows5_2.map table26Project
theorem table26Rows5_2_eq : table26Rows5_2 = RadiusThreePruning.final5_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical5_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows5_3 : List (List State) := sourceRows5_3.map table26Project
theorem table26Rows5_3_eq : table26Rows5_3 = RadiusThreePruning.final5_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical5_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows5_4 : List (List State) := sourceRows5_4.map table26Project
theorem table26Rows5_4_eq : table26Rows5_4 = RadiusThreePruning.final5_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical5_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows5_5 : List (List State) := sourceRows5_5.map table26Project
theorem table26Rows5_5_eq : table26Rows5_5 = RadiusThreePruning.final5_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical5_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows6_0 : List (List State) := sourceRows6_0.map table26Project
theorem table26Rows6_0_eq : table26Rows6_0 = RadiusThreePruning.final6_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical6_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows6_1 : List (List State) := sourceRows6_1.map table26Project
theorem table26Rows6_1_eq : table26Rows6_1 = RadiusThreePruning.final6_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical6_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows6_2 : List (List State) := sourceRows6_2.map table26Project
theorem table26Rows6_2_eq : table26Rows6_2 = RadiusThreePruning.final6_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical6_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows6_3 : List (List State) := sourceRows6_3.map table26Project
theorem table26Rows6_3_eq : table26Rows6_3 = RadiusThreePruning.final6_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical6_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows6_4 : List (List State) := sourceRows6_4.map table26Project
theorem table26Rows6_4_eq : table26Rows6_4 = RadiusThreePruning.final6_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical6_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows6_5 : List (List State) := sourceRows6_5.map table26Project
theorem table26Rows6_5_eq : table26Rows6_5 = RadiusThreePruning.final6_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical6_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows7_0 : List (List State) := sourceRows7_0.map table26Project
theorem table26Rows7_0_eq : table26Rows7_0 = RadiusThreePruning.final7_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical7_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows7_1 : List (List State) := sourceRows7_1.map table26Project
theorem table26Rows7_1_eq : table26Rows7_1 = RadiusThreePruning.final7_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical7_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows7_2 : List (List State) := sourceRows7_2.map table26Project
theorem table26Rows7_2_eq : table26Rows7_2 = RadiusThreePruning.final7_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical7_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows7_3 : List (List State) := sourceRows7_3.map table26Project
theorem table26Rows7_3_eq : table26Rows7_3 = RadiusThreePruning.final7_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical7_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows7_4 : List (List State) := sourceRows7_4.map table26Project
theorem table26Rows7_4_eq : table26Rows7_4 = RadiusThreePruning.final7_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical7_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows7_5 : List (List State) := sourceRows7_5.map table26Project
theorem table26Rows7_5_eq : table26Rows7_5 = RadiusThreePruning.final7_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical7_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows8_0 : List (List State) := sourceRows8_0.map table26Project
theorem table26Rows8_0_eq : table26Rows8_0 = RadiusThreePruning.final8_0.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical8_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows8_1 : List (List State) := sourceRows8_1.map table26Project
theorem table26Rows8_1_eq : table26Rows8_1 = RadiusThreePruning.final8_1.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical8_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows8_2 : List (List State) := sourceRows8_2.map table26Project
theorem table26Rows8_2_eq : table26Rows8_2 = RadiusThreePruning.final8_2.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical8_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows8_3 : List (List State) := sourceRows8_3.map table26Project
theorem table26Rows8_3_eq : table26Rows8_3 = RadiusThreePruning.final8_3.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical8_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows8_4 : List (List State) := sourceRows8_4.map table26Project
theorem table26Rows8_4_eq : table26Rows8_4 = RadiusThreePruning.final8_4.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical8_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26Rows8_5 : List (List State) := sourceRows8_5.map table26Project
theorem table26Rows8_5_eq : table26Rows8_5 = RadiusThreePruning.final8_5.map (fun p =>
    table26Scope.map (fun v => patchState p (subPos (positions v) (0,-4)))) := by
  rw [sourceRowsCanonical8_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table26Project_eq row
def table26 : Constraint 61 State := ⟨table26Scope, [table26Rows0_0,table26Rows0_1,table26Rows0_2,table26Rows0_3,table26Rows0_4,table26Rows0_5,table26Rows1_0,table26Rows1_1,table26Rows1_2,table26Rows1_3,table26Rows1_4,table26Rows1_5,table26Rows2_0,table26Rows2_1,table26Rows2_2,table26Rows2_3,table26Rows2_4,table26Rows2_5,table26Rows3_0,table26Rows3_1,table26Rows3_2,table26Rows3_3,table26Rows3_4,table26Rows3_5,table26Rows4_0,table26Rows4_1,table26Rows4_2,table26Rows4_3,table26Rows4_4,table26Rows4_5,table26Rows5_0,table26Rows5_1,table26Rows5_2,table26Rows5_3,table26Rows5_4,table26Rows5_5,table26Rows6_0,table26Rows6_1,table26Rows6_2,table26Rows6_3,table26Rows6_4,table26Rows6_5,table26Rows7_0,table26Rows7_1,table26Rows7_2,table26Rows7_3,table26Rows7_4,table26Rows7_5,table26Rows8_0,table26Rows8_1,table26Rows8_2,table26Rows8_3,table26Rows8_4,table26Rows8_5].flatten⟩
theorem table26_eq : table26 = windowConstraint positions (hexRegion 3)
    RadiusThreePruning.certifiedFamily (0,-4) := by
  unfold table26 windowConstraint
  rw [← table26Scope_eq]
  simp only [RadiusThreePruning.certifiedFamily, RadiusThreePruning.finalChunks, List.map_flatten,
    List.map_cons, List.map_nil, ← table26Rows0_0_eq, ← table26Rows0_1_eq, ← table26Rows0_2_eq, ← table26Rows0_3_eq, ← table26Rows0_4_eq, ← table26Rows0_5_eq, ← table26Rows1_0_eq, ← table26Rows1_1_eq, ← table26Rows1_2_eq, ← table26Rows1_3_eq, ← table26Rows1_4_eq, ← table26Rows1_5_eq, ← table26Rows2_0_eq, ← table26Rows2_1_eq, ← table26Rows2_2_eq, ← table26Rows2_3_eq, ← table26Rows2_4_eq, ← table26Rows2_5_eq, ← table26Rows3_0_eq, ← table26Rows3_1_eq, ← table26Rows3_2_eq, ← table26Rows3_3_eq, ← table26Rows3_4_eq, ← table26Rows3_5_eq, ← table26Rows4_0_eq, ← table26Rows4_1_eq, ← table26Rows4_2_eq, ← table26Rows4_3_eq, ← table26Rows4_4_eq, ← table26Rows4_5_eq, ← table26Rows5_0_eq, ← table26Rows5_1_eq, ← table26Rows5_2_eq, ← table26Rows5_3_eq, ← table26Rows5_4_eq, ← table26Rows5_5_eq, ← table26Rows6_0_eq, ← table26Rows6_1_eq, ← table26Rows6_2_eq, ← table26Rows6_3_eq, ← table26Rows6_4_eq, ← table26Rows6_5_eq, ← table26Rows7_0_eq, ← table26Rows7_1_eq, ← table26Rows7_2_eq, ← table26Rows7_3_eq, ← table26Rows7_4_eq, ← table26Rows7_5_eq, ← table26Rows8_0_eq, ← table26Rows8_1_eq, ← table26Rows8_2_eq, ← table26Rows8_3_eq, ← table26Rows8_4_eq, ← table26Rows8_5_eq]
theorem table26_member : table26 ∈ constraints := by
  rw [table26_eq]
  exact List.mem_map.mpr ⟨(0,-4), by decide, rfl⟩
end SpectreFinite.HexSearch.RadiusFour
