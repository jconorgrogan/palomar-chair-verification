module

public import SpectreFinite.RadiusFiveSourceCanonical

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def table30Scope : List (Fin 91) := [0, 6, 7, 13, 14, 15, 21, 22, 23, 24, 30, 31, 32, 33, 34, 40, 41, 42, 43, 44, 51, 52, 53, 54, 61, 62, 63, 70, 71]
theorem table30Scope_eq : table30Scope = windowScope positions (hexRegion 4) (-1,-4) := by rfl
def table30Project (row : List State) : List State := [row[4]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[22]?.getD (0,0),row[23]?.getD (0,0),row[24]?.getD (0,0),row[25]?.getD (0,0),row[30]?.getD (0,0),row[31]?.getD (0,0),row[32]?.getD (0,0),row[33]?.getD (0,0),row[34]?.getD (0,0),row[38]?.getD (0,0),row[39]?.getD (0,0),row[40]?.getD (0,0),row[41]?.getD (0,0),row[42]?.getD (0,0),row[46]?.getD (0,0),row[47]?.getD (0,0),row[48]?.getD (0,0),row[49]?.getD (0,0),row[53]?.getD (0,0),row[54]?.getD (0,0),row[55]?.getD (0,0),row[59]?.getD (0,0),row[60]?.getD (0,0)]
theorem table30Project_eq (row : List State) : table30Project row =
    table30Scope.map (fun v => patchState ((hexRegion 4).zip row)
      (subPos (positions v) (-1,-4))) := by
  change [row[4]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[22]?.getD (0,0),row[23]?.getD (0,0),row[24]?.getD (0,0),row[25]?.getD (0,0),row[30]?.getD (0,0),row[31]?.getD (0,0),row[32]?.getD (0,0),row[33]?.getD (0,0),row[34]?.getD (0,0),row[38]?.getD (0,0),row[39]?.getD (0,0),row[40]?.getD (0,0),row[41]?.getD (0,0),row[42]?.getD (0,0),row[46]?.getD (0,0),row[47]?.getD (0,0),row[48]?.getD (0,0),row[49]?.getD (0,0),row[53]?.getD (0,0),row[54]?.getD (0,0),row[55]?.getD (0,0),row[59]?.getD (0,0),row[60]?.getD (0,0)] = [patchState ((hexRegion 4).zip row) (-4,4),patchState ((hexRegion 4).zip row) (-3,3),patchState ((hexRegion 4).zip row) (-3,4),patchState ((hexRegion 4).zip row) (-2,2),patchState ((hexRegion 4).zip row) (-2,3),patchState ((hexRegion 4).zip row) (-2,4),patchState ((hexRegion 4).zip row) (-1,1),patchState ((hexRegion 4).zip row) (-1,2),patchState ((hexRegion 4).zip row) (-1,3),patchState ((hexRegion 4).zip row) (-1,4),patchState ((hexRegion 4).zip row) (0,0),patchState ((hexRegion 4).zip row) (0,1),patchState ((hexRegion 4).zip row) (0,2),patchState ((hexRegion 4).zip row) (0,3),patchState ((hexRegion 4).zip row) (0,4),patchState ((hexRegion 4).zip row) (1,-1),patchState ((hexRegion 4).zip row) (1,0),patchState ((hexRegion 4).zip row) (1,1),patchState ((hexRegion 4).zip row) (1,2),patchState ((hexRegion 4).zip row) (1,3),patchState ((hexRegion 4).zip row) (2,-1),patchState ((hexRegion 4).zip row) (2,0),patchState ((hexRegion 4).zip row) (2,1),patchState ((hexRegion 4).zip row) (2,2),patchState ((hexRegion 4).zip row) (3,-1),patchState ((hexRegion 4).zip row) (3,0),patchState ((hexRegion 4).zip row) (3,1),patchState ((hexRegion 4).zip row) (4,-1),patchState ((hexRegion 4).zip row) (4,0)]
  rw [patchState_zip_index (hexRegion 4) row (-4,4) 4 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-3,3) 9 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-3,4) 10 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-2,2) 15 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-2,3) 16 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-2,4) 17 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-1,1) 22 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-1,2) 23 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-1,3) 24 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-1,4) 25 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,0) 30 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,1) 31 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,2) 32 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,3) 33 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,4) 34 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,-1) 38 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,0) 39 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,1) 40 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,2) 41 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,3) 42 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,-1) 46 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,0) 47 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,1) 48 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,2) 49 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,-1) 53 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,0) 54 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,1) 55 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (4,-1) 59 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (4,0) 60 (by decide) (by decide)]
def table30Rows0_0 : List (List State) := sourceRows0_0.map table30Project
theorem table30Rows0_0_eq : table30Rows0_0 = RadiusFourPruning.final0_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical0_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows0_1 : List (List State) := sourceRows0_1.map table30Project
theorem table30Rows0_1_eq : table30Rows0_1 = RadiusFourPruning.final0_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical0_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows0_2 : List (List State) := sourceRows0_2.map table30Project
theorem table30Rows0_2_eq : table30Rows0_2 = RadiusFourPruning.final0_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical0_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows0_3 : List (List State) := sourceRows0_3.map table30Project
theorem table30Rows0_3_eq : table30Rows0_3 = RadiusFourPruning.final0_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical0_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows0_4 : List (List State) := sourceRows0_4.map table30Project
theorem table30Rows0_4_eq : table30Rows0_4 = RadiusFourPruning.final0_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical0_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows0_5 : List (List State) := sourceRows0_5.map table30Project
theorem table30Rows0_5_eq : table30Rows0_5 = RadiusFourPruning.final0_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical0_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows1_0 : List (List State) := sourceRows1_0.map table30Project
theorem table30Rows1_0_eq : table30Rows1_0 = RadiusFourPruning.final1_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical1_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows1_1 : List (List State) := sourceRows1_1.map table30Project
theorem table30Rows1_1_eq : table30Rows1_1 = RadiusFourPruning.final1_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical1_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows1_2 : List (List State) := sourceRows1_2.map table30Project
theorem table30Rows1_2_eq : table30Rows1_2 = RadiusFourPruning.final1_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical1_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows1_3 : List (List State) := sourceRows1_3.map table30Project
theorem table30Rows1_3_eq : table30Rows1_3 = RadiusFourPruning.final1_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical1_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows1_4 : List (List State) := sourceRows1_4.map table30Project
theorem table30Rows1_4_eq : table30Rows1_4 = RadiusFourPruning.final1_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical1_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows1_5 : List (List State) := sourceRows1_5.map table30Project
theorem table30Rows1_5_eq : table30Rows1_5 = RadiusFourPruning.final1_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical1_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows2_0 : List (List State) := sourceRows2_0.map table30Project
theorem table30Rows2_0_eq : table30Rows2_0 = RadiusFourPruning.final2_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical2_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows2_1 : List (List State) := sourceRows2_1.map table30Project
theorem table30Rows2_1_eq : table30Rows2_1 = RadiusFourPruning.final2_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical2_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows2_2 : List (List State) := sourceRows2_2.map table30Project
theorem table30Rows2_2_eq : table30Rows2_2 = RadiusFourPruning.final2_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical2_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows2_3 : List (List State) := sourceRows2_3.map table30Project
theorem table30Rows2_3_eq : table30Rows2_3 = RadiusFourPruning.final2_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical2_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows2_4 : List (List State) := sourceRows2_4.map table30Project
theorem table30Rows2_4_eq : table30Rows2_4 = RadiusFourPruning.final2_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical2_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows2_5 : List (List State) := sourceRows2_5.map table30Project
theorem table30Rows2_5_eq : table30Rows2_5 = RadiusFourPruning.final2_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical2_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows3_0 : List (List State) := sourceRows3_0.map table30Project
theorem table30Rows3_0_eq : table30Rows3_0 = RadiusFourPruning.final3_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical3_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows3_1 : List (List State) := sourceRows3_1.map table30Project
theorem table30Rows3_1_eq : table30Rows3_1 = RadiusFourPruning.final3_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical3_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows3_2 : List (List State) := sourceRows3_2.map table30Project
theorem table30Rows3_2_eq : table30Rows3_2 = RadiusFourPruning.final3_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical3_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows3_3 : List (List State) := sourceRows3_3.map table30Project
theorem table30Rows3_3_eq : table30Rows3_3 = RadiusFourPruning.final3_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical3_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows3_4 : List (List State) := sourceRows3_4.map table30Project
theorem table30Rows3_4_eq : table30Rows3_4 = RadiusFourPruning.final3_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical3_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows3_5 : List (List State) := sourceRows3_5.map table30Project
theorem table30Rows3_5_eq : table30Rows3_5 = RadiusFourPruning.final3_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical3_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows4_0 : List (List State) := sourceRows4_0.map table30Project
theorem table30Rows4_0_eq : table30Rows4_0 = RadiusFourPruning.final4_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical4_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows4_1 : List (List State) := sourceRows4_1.map table30Project
theorem table30Rows4_1_eq : table30Rows4_1 = RadiusFourPruning.final4_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical4_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows4_2 : List (List State) := sourceRows4_2.map table30Project
theorem table30Rows4_2_eq : table30Rows4_2 = RadiusFourPruning.final4_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical4_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows4_3 : List (List State) := sourceRows4_3.map table30Project
theorem table30Rows4_3_eq : table30Rows4_3 = RadiusFourPruning.final4_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical4_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows4_4 : List (List State) := sourceRows4_4.map table30Project
theorem table30Rows4_4_eq : table30Rows4_4 = RadiusFourPruning.final4_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical4_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows4_5 : List (List State) := sourceRows4_5.map table30Project
theorem table30Rows4_5_eq : table30Rows4_5 = RadiusFourPruning.final4_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical4_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows5_0 : List (List State) := sourceRows5_0.map table30Project
theorem table30Rows5_0_eq : table30Rows5_0 = RadiusFourPruning.final5_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical5_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows5_1 : List (List State) := sourceRows5_1.map table30Project
theorem table30Rows5_1_eq : table30Rows5_1 = RadiusFourPruning.final5_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical5_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows5_2 : List (List State) := sourceRows5_2.map table30Project
theorem table30Rows5_2_eq : table30Rows5_2 = RadiusFourPruning.final5_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical5_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows5_3 : List (List State) := sourceRows5_3.map table30Project
theorem table30Rows5_3_eq : table30Rows5_3 = RadiusFourPruning.final5_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical5_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows5_4 : List (List State) := sourceRows5_4.map table30Project
theorem table30Rows5_4_eq : table30Rows5_4 = RadiusFourPruning.final5_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical5_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows5_5 : List (List State) := sourceRows5_5.map table30Project
theorem table30Rows5_5_eq : table30Rows5_5 = RadiusFourPruning.final5_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical5_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows6_0 : List (List State) := sourceRows6_0.map table30Project
theorem table30Rows6_0_eq : table30Rows6_0 = RadiusFourPruning.final6_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical6_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows6_1 : List (List State) := sourceRows6_1.map table30Project
theorem table30Rows6_1_eq : table30Rows6_1 = RadiusFourPruning.final6_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical6_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows6_2 : List (List State) := sourceRows6_2.map table30Project
theorem table30Rows6_2_eq : table30Rows6_2 = RadiusFourPruning.final6_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical6_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows6_3 : List (List State) := sourceRows6_3.map table30Project
theorem table30Rows6_3_eq : table30Rows6_3 = RadiusFourPruning.final6_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical6_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows6_4 : List (List State) := sourceRows6_4.map table30Project
theorem table30Rows6_4_eq : table30Rows6_4 = RadiusFourPruning.final6_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical6_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows6_5 : List (List State) := sourceRows6_5.map table30Project
theorem table30Rows6_5_eq : table30Rows6_5 = RadiusFourPruning.final6_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical6_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows7_0 : List (List State) := sourceRows7_0.map table30Project
theorem table30Rows7_0_eq : table30Rows7_0 = RadiusFourPruning.final7_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical7_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows7_1 : List (List State) := sourceRows7_1.map table30Project
theorem table30Rows7_1_eq : table30Rows7_1 = RadiusFourPruning.final7_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical7_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows7_2 : List (List State) := sourceRows7_2.map table30Project
theorem table30Rows7_2_eq : table30Rows7_2 = RadiusFourPruning.final7_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical7_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows7_3 : List (List State) := sourceRows7_3.map table30Project
theorem table30Rows7_3_eq : table30Rows7_3 = RadiusFourPruning.final7_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical7_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows7_4 : List (List State) := sourceRows7_4.map table30Project
theorem table30Rows7_4_eq : table30Rows7_4 = RadiusFourPruning.final7_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical7_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows7_5 : List (List State) := sourceRows7_5.map table30Project
theorem table30Rows7_5_eq : table30Rows7_5 = RadiusFourPruning.final7_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical7_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows8_0 : List (List State) := sourceRows8_0.map table30Project
theorem table30Rows8_0_eq : table30Rows8_0 = RadiusFourPruning.final8_0.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical8_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows8_1 : List (List State) := sourceRows8_1.map table30Project
theorem table30Rows8_1_eq : table30Rows8_1 = RadiusFourPruning.final8_1.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical8_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows8_2 : List (List State) := sourceRows8_2.map table30Project
theorem table30Rows8_2_eq : table30Rows8_2 = RadiusFourPruning.final8_2.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical8_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows8_3 : List (List State) := sourceRows8_3.map table30Project
theorem table30Rows8_3_eq : table30Rows8_3 = RadiusFourPruning.final8_3.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical8_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows8_4 : List (List State) := sourceRows8_4.map table30Project
theorem table30Rows8_4_eq : table30Rows8_4 = RadiusFourPruning.final8_4.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical8_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30Rows8_5 : List (List State) := sourceRows8_5.map table30Project
theorem table30Rows8_5_eq : table30Rows8_5 = RadiusFourPruning.final8_5.map (fun p =>
    table30Scope.map (fun v => patchState p (subPos (positions v) (-1,-4)))) := by
  rw [sourceRowsCanonical8_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table30Project_eq row
def table30 : Constraint 91 State := ⟨table30Scope, [table30Rows0_0,table30Rows0_1,table30Rows0_2,table30Rows0_3,table30Rows0_4,table30Rows0_5,table30Rows1_0,table30Rows1_1,table30Rows1_2,table30Rows1_3,table30Rows1_4,table30Rows1_5,table30Rows2_0,table30Rows2_1,table30Rows2_2,table30Rows2_3,table30Rows2_4,table30Rows2_5,table30Rows3_0,table30Rows3_1,table30Rows3_2,table30Rows3_3,table30Rows3_4,table30Rows3_5,table30Rows4_0,table30Rows4_1,table30Rows4_2,table30Rows4_3,table30Rows4_4,table30Rows4_5,table30Rows5_0,table30Rows5_1,table30Rows5_2,table30Rows5_3,table30Rows5_4,table30Rows5_5,table30Rows6_0,table30Rows6_1,table30Rows6_2,table30Rows6_3,table30Rows6_4,table30Rows6_5,table30Rows7_0,table30Rows7_1,table30Rows7_2,table30Rows7_3,table30Rows7_4,table30Rows7_5,table30Rows8_0,table30Rows8_1,table30Rows8_2,table30Rows8_3,table30Rows8_4,table30Rows8_5].flatten⟩
theorem table30_eq : table30 = windowConstraint positions (hexRegion 4)
    RadiusFourPruning.certifiedFamily (-1,-4) := by
  unfold table30 windowConstraint
  rw [← table30Scope_eq]
  simp only [RadiusFourPruning.certifiedFamily, RadiusFourPruning.finalChunks, List.map_flatten,
    List.map_cons, List.map_nil, ← table30Rows0_0_eq, ← table30Rows0_1_eq, ← table30Rows0_2_eq, ← table30Rows0_3_eq, ← table30Rows0_4_eq, ← table30Rows0_5_eq, ← table30Rows1_0_eq, ← table30Rows1_1_eq, ← table30Rows1_2_eq, ← table30Rows1_3_eq, ← table30Rows1_4_eq, ← table30Rows1_5_eq, ← table30Rows2_0_eq, ← table30Rows2_1_eq, ← table30Rows2_2_eq, ← table30Rows2_3_eq, ← table30Rows2_4_eq, ← table30Rows2_5_eq, ← table30Rows3_0_eq, ← table30Rows3_1_eq, ← table30Rows3_2_eq, ← table30Rows3_3_eq, ← table30Rows3_4_eq, ← table30Rows3_5_eq, ← table30Rows4_0_eq, ← table30Rows4_1_eq, ← table30Rows4_2_eq, ← table30Rows4_3_eq, ← table30Rows4_4_eq, ← table30Rows4_5_eq, ← table30Rows5_0_eq, ← table30Rows5_1_eq, ← table30Rows5_2_eq, ← table30Rows5_3_eq, ← table30Rows5_4_eq, ← table30Rows5_5_eq, ← table30Rows6_0_eq, ← table30Rows6_1_eq, ← table30Rows6_2_eq, ← table30Rows6_3_eq, ← table30Rows6_4_eq, ← table30Rows6_5_eq, ← table30Rows7_0_eq, ← table30Rows7_1_eq, ← table30Rows7_2_eq, ← table30Rows7_3_eq, ← table30Rows7_4_eq, ← table30Rows7_5_eq, ← table30Rows8_0_eq, ← table30Rows8_1_eq, ← table30Rows8_2_eq, ← table30Rows8_3_eq, ← table30Rows8_4_eq, ← table30Rows8_5_eq]
theorem table30_member : table30 ∈ constraints := by
  rw [table30_eq]
  exact List.mem_map.mpr ⟨(-1,-4), by decide, rfl⟩
end SpectreFinite.HexSearch.RadiusFive
