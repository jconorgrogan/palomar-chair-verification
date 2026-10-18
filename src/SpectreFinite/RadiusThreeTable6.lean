module

public import SpectreFinite.RadiusThreeSourceCanonical

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def table6Scope : List (Fin 37) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 17, 18, 19]
theorem table6Scope_eq : table6Scope = windowScope positions (hexRegion 2) (-2,1) := by rfl
def table6Project (row : List State) : List State := [row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[6]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[11]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)]
theorem table6Project_eq (row : List State) : table6Project row =
    table6Scope.map (fun v => patchState ((hexRegion 2).zip row)
      (subPos (positions v) (-2,1))) := by
  change [row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[6]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[11]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)] = [patchState ((hexRegion 2).zip row) (-1,-1),patchState ((hexRegion 2).zip row) (-1,0),patchState ((hexRegion 2).zip row) (-1,1),patchState ((hexRegion 2).zip row) (-1,2),patchState ((hexRegion 2).zip row) (0,-2),patchState ((hexRegion 2).zip row) (0,-1),patchState ((hexRegion 2).zip row) (0,0),patchState ((hexRegion 2).zip row) (0,1),patchState ((hexRegion 2).zip row) (0,2),patchState ((hexRegion 2).zip row) (1,-2),patchState ((hexRegion 2).zip row) (1,-1),patchState ((hexRegion 2).zip row) (1,0),patchState ((hexRegion 2).zip row) (1,1),patchState ((hexRegion 2).zip row) (2,-2),patchState ((hexRegion 2).zip row) (2,-1),patchState ((hexRegion 2).zip row) (2,0)]
  rw [patchState_zip_index (hexRegion 2) row (-1,-1) 3 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (-1,0) 4 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (-1,1) 5 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (-1,2) 6 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (0,-2) 7 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (0,-1) 8 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (0,0) 9 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (0,1) 10 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (0,2) 11 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (1,-2) 12 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (1,-1) 13 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (1,0) 14 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (1,1) 15 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (2,-2) 16 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (2,-1) 17 (by decide) (by decide),
    patchState_zip_index (hexRegion 2) row (2,0) 18 (by decide) (by decide)]
def table6Rows0_0 : List (List State) := sourceRows0_0.map table6Project
theorem table6Rows0_0_eq : table6Rows0_0 = RadiusTwoPruning.final0_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical0_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows0_1 : List (List State) := sourceRows0_1.map table6Project
theorem table6Rows0_1_eq : table6Rows0_1 = RadiusTwoPruning.final0_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical0_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows0_2 : List (List State) := sourceRows0_2.map table6Project
theorem table6Rows0_2_eq : table6Rows0_2 = RadiusTwoPruning.final0_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical0_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows0_3 : List (List State) := sourceRows0_3.map table6Project
theorem table6Rows0_3_eq : table6Rows0_3 = RadiusTwoPruning.final0_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical0_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows0_4 : List (List State) := sourceRows0_4.map table6Project
theorem table6Rows0_4_eq : table6Rows0_4 = RadiusTwoPruning.final0_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical0_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows0_5 : List (List State) := sourceRows0_5.map table6Project
theorem table6Rows0_5_eq : table6Rows0_5 = RadiusTwoPruning.final0_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical0_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows1_0 : List (List State) := sourceRows1_0.map table6Project
theorem table6Rows1_0_eq : table6Rows1_0 = RadiusTwoPruning.final1_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical1_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows1_1 : List (List State) := sourceRows1_1.map table6Project
theorem table6Rows1_1_eq : table6Rows1_1 = RadiusTwoPruning.final1_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical1_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows1_2 : List (List State) := sourceRows1_2.map table6Project
theorem table6Rows1_2_eq : table6Rows1_2 = RadiusTwoPruning.final1_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical1_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows1_3 : List (List State) := sourceRows1_3.map table6Project
theorem table6Rows1_3_eq : table6Rows1_3 = RadiusTwoPruning.final1_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical1_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows1_4 : List (List State) := sourceRows1_4.map table6Project
theorem table6Rows1_4_eq : table6Rows1_4 = RadiusTwoPruning.final1_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical1_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows1_5 : List (List State) := sourceRows1_5.map table6Project
theorem table6Rows1_5_eq : table6Rows1_5 = RadiusTwoPruning.final1_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical1_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows2_0 : List (List State) := sourceRows2_0.map table6Project
theorem table6Rows2_0_eq : table6Rows2_0 = RadiusTwoPruning.final2_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical2_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows2_1 : List (List State) := sourceRows2_1.map table6Project
theorem table6Rows2_1_eq : table6Rows2_1 = RadiusTwoPruning.final2_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical2_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows2_2 : List (List State) := sourceRows2_2.map table6Project
theorem table6Rows2_2_eq : table6Rows2_2 = RadiusTwoPruning.final2_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical2_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows2_3 : List (List State) := sourceRows2_3.map table6Project
theorem table6Rows2_3_eq : table6Rows2_3 = RadiusTwoPruning.final2_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical2_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows2_4 : List (List State) := sourceRows2_4.map table6Project
theorem table6Rows2_4_eq : table6Rows2_4 = RadiusTwoPruning.final2_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical2_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows2_5 : List (List State) := sourceRows2_5.map table6Project
theorem table6Rows2_5_eq : table6Rows2_5 = RadiusTwoPruning.final2_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical2_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows3_0 : List (List State) := sourceRows3_0.map table6Project
theorem table6Rows3_0_eq : table6Rows3_0 = RadiusTwoPruning.final3_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical3_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows3_1 : List (List State) := sourceRows3_1.map table6Project
theorem table6Rows3_1_eq : table6Rows3_1 = RadiusTwoPruning.final3_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical3_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows3_2 : List (List State) := sourceRows3_2.map table6Project
theorem table6Rows3_2_eq : table6Rows3_2 = RadiusTwoPruning.final3_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical3_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows3_3 : List (List State) := sourceRows3_3.map table6Project
theorem table6Rows3_3_eq : table6Rows3_3 = RadiusTwoPruning.final3_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical3_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows3_4 : List (List State) := sourceRows3_4.map table6Project
theorem table6Rows3_4_eq : table6Rows3_4 = RadiusTwoPruning.final3_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical3_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows3_5 : List (List State) := sourceRows3_5.map table6Project
theorem table6Rows3_5_eq : table6Rows3_5 = RadiusTwoPruning.final3_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical3_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows4_0 : List (List State) := sourceRows4_0.map table6Project
theorem table6Rows4_0_eq : table6Rows4_0 = RadiusTwoPruning.final4_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical4_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows4_1 : List (List State) := sourceRows4_1.map table6Project
theorem table6Rows4_1_eq : table6Rows4_1 = RadiusTwoPruning.final4_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical4_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows4_2 : List (List State) := sourceRows4_2.map table6Project
theorem table6Rows4_2_eq : table6Rows4_2 = RadiusTwoPruning.final4_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical4_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows4_3 : List (List State) := sourceRows4_3.map table6Project
theorem table6Rows4_3_eq : table6Rows4_3 = RadiusTwoPruning.final4_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical4_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows4_4 : List (List State) := sourceRows4_4.map table6Project
theorem table6Rows4_4_eq : table6Rows4_4 = RadiusTwoPruning.final4_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical4_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows4_5 : List (List State) := sourceRows4_5.map table6Project
theorem table6Rows4_5_eq : table6Rows4_5 = RadiusTwoPruning.final4_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical4_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows5_0 : List (List State) := sourceRows5_0.map table6Project
theorem table6Rows5_0_eq : table6Rows5_0 = RadiusTwoPruning.final5_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical5_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows5_1 : List (List State) := sourceRows5_1.map table6Project
theorem table6Rows5_1_eq : table6Rows5_1 = RadiusTwoPruning.final5_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical5_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows5_2 : List (List State) := sourceRows5_2.map table6Project
theorem table6Rows5_2_eq : table6Rows5_2 = RadiusTwoPruning.final5_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical5_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows5_3 : List (List State) := sourceRows5_3.map table6Project
theorem table6Rows5_3_eq : table6Rows5_3 = RadiusTwoPruning.final5_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical5_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows5_4 : List (List State) := sourceRows5_4.map table6Project
theorem table6Rows5_4_eq : table6Rows5_4 = RadiusTwoPruning.final5_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical5_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows5_5 : List (List State) := sourceRows5_5.map table6Project
theorem table6Rows5_5_eq : table6Rows5_5 = RadiusTwoPruning.final5_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical5_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows6_0 : List (List State) := sourceRows6_0.map table6Project
theorem table6Rows6_0_eq : table6Rows6_0 = RadiusTwoPruning.final6_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical6_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows6_1 : List (List State) := sourceRows6_1.map table6Project
theorem table6Rows6_1_eq : table6Rows6_1 = RadiusTwoPruning.final6_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical6_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows6_2 : List (List State) := sourceRows6_2.map table6Project
theorem table6Rows6_2_eq : table6Rows6_2 = RadiusTwoPruning.final6_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical6_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows6_3 : List (List State) := sourceRows6_3.map table6Project
theorem table6Rows6_3_eq : table6Rows6_3 = RadiusTwoPruning.final6_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical6_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows6_4 : List (List State) := sourceRows6_4.map table6Project
theorem table6Rows6_4_eq : table6Rows6_4 = RadiusTwoPruning.final6_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical6_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows6_5 : List (List State) := sourceRows6_5.map table6Project
theorem table6Rows6_5_eq : table6Rows6_5 = RadiusTwoPruning.final6_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical6_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows7_0 : List (List State) := sourceRows7_0.map table6Project
theorem table6Rows7_0_eq : table6Rows7_0 = RadiusTwoPruning.final7_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical7_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows7_1 : List (List State) := sourceRows7_1.map table6Project
theorem table6Rows7_1_eq : table6Rows7_1 = RadiusTwoPruning.final7_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical7_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows7_2 : List (List State) := sourceRows7_2.map table6Project
theorem table6Rows7_2_eq : table6Rows7_2 = RadiusTwoPruning.final7_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical7_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows7_3 : List (List State) := sourceRows7_3.map table6Project
theorem table6Rows7_3_eq : table6Rows7_3 = RadiusTwoPruning.final7_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical7_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows7_4 : List (List State) := sourceRows7_4.map table6Project
theorem table6Rows7_4_eq : table6Rows7_4 = RadiusTwoPruning.final7_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical7_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows7_5 : List (List State) := sourceRows7_5.map table6Project
theorem table6Rows7_5_eq : table6Rows7_5 = RadiusTwoPruning.final7_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical7_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows8_0 : List (List State) := sourceRows8_0.map table6Project
theorem table6Rows8_0_eq : table6Rows8_0 = RadiusTwoPruning.final8_0.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical8_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows8_1 : List (List State) := sourceRows8_1.map table6Project
theorem table6Rows8_1_eq : table6Rows8_1 = RadiusTwoPruning.final8_1.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical8_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows8_2 : List (List State) := sourceRows8_2.map table6Project
theorem table6Rows8_2_eq : table6Rows8_2 = RadiusTwoPruning.final8_2.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical8_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows8_3 : List (List State) := sourceRows8_3.map table6Project
theorem table6Rows8_3_eq : table6Rows8_3 = RadiusTwoPruning.final8_3.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical8_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows8_4 : List (List State) := sourceRows8_4.map table6Project
theorem table6Rows8_4_eq : table6Rows8_4 = RadiusTwoPruning.final8_4.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical8_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6Rows8_5 : List (List State) := sourceRows8_5.map table6Project
theorem table6Rows8_5_eq : table6Rows8_5 = RadiusTwoPruning.final8_5.map (fun p =>
    table6Scope.map (fun v => patchState p (subPos (positions v) (-2,1)))) := by
  rw [sourceRowsCanonical8_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table6Project_eq row
def table6 : Constraint 37 State := ⟨table6Scope, [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5].flatten⟩
theorem table6_eq : table6 = windowConstraint positions (hexRegion 2)
    RadiusTwoPruning.certifiedFamily (-2,1) := by
  unfold table6 windowConstraint
  rw [← table6Scope_eq]
  simp only [RadiusTwoPruning.certifiedFamily, RadiusTwoPruning.finalChunks, List.map_flatten,
    List.map_cons, List.map_nil, ← table6Rows0_0_eq, ← table6Rows0_1_eq, ← table6Rows0_2_eq, ← table6Rows0_3_eq, ← table6Rows0_4_eq, ← table6Rows0_5_eq, ← table6Rows1_0_eq, ← table6Rows1_1_eq, ← table6Rows1_2_eq, ← table6Rows1_3_eq, ← table6Rows1_4_eq, ← table6Rows1_5_eq, ← table6Rows2_0_eq, ← table6Rows2_1_eq, ← table6Rows2_2_eq, ← table6Rows2_3_eq, ← table6Rows2_4_eq, ← table6Rows2_5_eq, ← table6Rows3_0_eq, ← table6Rows3_1_eq, ← table6Rows3_2_eq, ← table6Rows3_3_eq, ← table6Rows3_4_eq, ← table6Rows3_5_eq, ← table6Rows4_0_eq, ← table6Rows4_1_eq, ← table6Rows4_2_eq, ← table6Rows4_3_eq, ← table6Rows4_4_eq, ← table6Rows4_5_eq, ← table6Rows5_0_eq, ← table6Rows5_1_eq, ← table6Rows5_2_eq, ← table6Rows5_3_eq, ← table6Rows5_4_eq, ← table6Rows5_5_eq, ← table6Rows6_0_eq, ← table6Rows6_1_eq, ← table6Rows6_2_eq, ← table6Rows6_3_eq, ← table6Rows6_4_eq, ← table6Rows6_5_eq, ← table6Rows7_0_eq, ← table6Rows7_1_eq, ← table6Rows7_2_eq, ← table6Rows7_3_eq, ← table6Rows7_4_eq, ← table6Rows7_5_eq, ← table6Rows8_0_eq, ← table6Rows8_1_eq, ← table6Rows8_2_eq, ← table6Rows8_3_eq, ← table6Rows8_4_eq, ← table6Rows8_5_eq]
theorem table6_member : table6 ∈ constraints := by
  rw [table6_eq]
  exact List.mem_map.mpr ⟨(-2,1), by decide, rfl⟩
end SpectreFinite.HexSearch.RadiusThree
