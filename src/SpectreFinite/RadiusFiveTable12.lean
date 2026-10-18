module

public import SpectreFinite.RadiusFiveSourceCanonical

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def table12Scope : List (Fin 91) := [2, 3, 4, 5, 8, 9, 10, 11, 12, 16, 17, 18, 19, 20, 25, 26, 27, 28, 29, 35, 36, 37, 38, 39, 46, 47, 48, 49, 50]
theorem table12Scope_eq : table12Scope = windowScope positions (hexRegion 4) (-4,5) := by rfl
def table12Project (row : List State) : List State := [row[18]?.getD (0,0),row[19]?.getD (0,0),row[20]?.getD (0,0),row[21]?.getD (0,0),row[26]?.getD (0,0),row[27]?.getD (0,0),row[28]?.getD (0,0),row[29]?.getD (0,0),row[30]?.getD (0,0),row[35]?.getD (0,0),row[36]?.getD (0,0),row[37]?.getD (0,0),row[38]?.getD (0,0),row[39]?.getD (0,0),row[43]?.getD (0,0),row[44]?.getD (0,0),row[45]?.getD (0,0),row[46]?.getD (0,0),row[47]?.getD (0,0),row[50]?.getD (0,0),row[51]?.getD (0,0),row[52]?.getD (0,0),row[53]?.getD (0,0),row[54]?.getD (0,0),row[56]?.getD (0,0),row[57]?.getD (0,0),row[58]?.getD (0,0),row[59]?.getD (0,0),row[60]?.getD (0,0)]
theorem table12Project_eq (row : List State) : table12Project row =
    table12Scope.map (fun v => patchState ((hexRegion 4).zip row)
      (subPos (positions v) (-4,5))) := by
  change [row[18]?.getD (0,0),row[19]?.getD (0,0),row[20]?.getD (0,0),row[21]?.getD (0,0),row[26]?.getD (0,0),row[27]?.getD (0,0),row[28]?.getD (0,0),row[29]?.getD (0,0),row[30]?.getD (0,0),row[35]?.getD (0,0),row[36]?.getD (0,0),row[37]?.getD (0,0),row[38]?.getD (0,0),row[39]?.getD (0,0),row[43]?.getD (0,0),row[44]?.getD (0,0),row[45]?.getD (0,0),row[46]?.getD (0,0),row[47]?.getD (0,0),row[50]?.getD (0,0),row[51]?.getD (0,0),row[52]?.getD (0,0),row[53]?.getD (0,0),row[54]?.getD (0,0),row[56]?.getD (0,0),row[57]?.getD (0,0),row[58]?.getD (0,0),row[59]?.getD (0,0),row[60]?.getD (0,0)] = [patchState ((hexRegion 4).zip row) (-1,-3),patchState ((hexRegion 4).zip row) (-1,-2),patchState ((hexRegion 4).zip row) (-1,-1),patchState ((hexRegion 4).zip row) (-1,0),patchState ((hexRegion 4).zip row) (0,-4),patchState ((hexRegion 4).zip row) (0,-3),patchState ((hexRegion 4).zip row) (0,-2),patchState ((hexRegion 4).zip row) (0,-1),patchState ((hexRegion 4).zip row) (0,0),patchState ((hexRegion 4).zip row) (1,-4),patchState ((hexRegion 4).zip row) (1,-3),patchState ((hexRegion 4).zip row) (1,-2),patchState ((hexRegion 4).zip row) (1,-1),patchState ((hexRegion 4).zip row) (1,0),patchState ((hexRegion 4).zip row) (2,-4),patchState ((hexRegion 4).zip row) (2,-3),patchState ((hexRegion 4).zip row) (2,-2),patchState ((hexRegion 4).zip row) (2,-1),patchState ((hexRegion 4).zip row) (2,0),patchState ((hexRegion 4).zip row) (3,-4),patchState ((hexRegion 4).zip row) (3,-3),patchState ((hexRegion 4).zip row) (3,-2),patchState ((hexRegion 4).zip row) (3,-1),patchState ((hexRegion 4).zip row) (3,0),patchState ((hexRegion 4).zip row) (4,-4),patchState ((hexRegion 4).zip row) (4,-3),patchState ((hexRegion 4).zip row) (4,-2),patchState ((hexRegion 4).zip row) (4,-1),patchState ((hexRegion 4).zip row) (4,0)]
  rw [patchState_zip_index (hexRegion 4) row (-1,-3) 18 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-1,-2) 19 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-1,-1) 20 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (-1,0) 21 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,-4) 26 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,-3) 27 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,-2) 28 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,-1) 29 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (0,0) 30 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,-4) 35 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,-3) 36 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,-2) 37 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,-1) 38 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (1,0) 39 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,-4) 43 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,-3) 44 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,-2) 45 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,-1) 46 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (2,0) 47 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,-4) 50 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,-3) 51 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,-2) 52 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,-1) 53 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (3,0) 54 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (4,-4) 56 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (4,-3) 57 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (4,-2) 58 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (4,-1) 59 (by decide) (by decide),
    patchState_zip_index (hexRegion 4) row (4,0) 60 (by decide) (by decide)]
def table12Rows0_0 : List (List State) := sourceRows0_0.map table12Project
theorem table12Rows0_0_eq : table12Rows0_0 = RadiusFourPruning.final0_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical0_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows0_1 : List (List State) := sourceRows0_1.map table12Project
theorem table12Rows0_1_eq : table12Rows0_1 = RadiusFourPruning.final0_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical0_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows0_2 : List (List State) := sourceRows0_2.map table12Project
theorem table12Rows0_2_eq : table12Rows0_2 = RadiusFourPruning.final0_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical0_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows0_3 : List (List State) := sourceRows0_3.map table12Project
theorem table12Rows0_3_eq : table12Rows0_3 = RadiusFourPruning.final0_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical0_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows0_4 : List (List State) := sourceRows0_4.map table12Project
theorem table12Rows0_4_eq : table12Rows0_4 = RadiusFourPruning.final0_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical0_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows0_5 : List (List State) := sourceRows0_5.map table12Project
theorem table12Rows0_5_eq : table12Rows0_5 = RadiusFourPruning.final0_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical0_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows1_0 : List (List State) := sourceRows1_0.map table12Project
theorem table12Rows1_0_eq : table12Rows1_0 = RadiusFourPruning.final1_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical1_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows1_1 : List (List State) := sourceRows1_1.map table12Project
theorem table12Rows1_1_eq : table12Rows1_1 = RadiusFourPruning.final1_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical1_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows1_2 : List (List State) := sourceRows1_2.map table12Project
theorem table12Rows1_2_eq : table12Rows1_2 = RadiusFourPruning.final1_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical1_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows1_3 : List (List State) := sourceRows1_3.map table12Project
theorem table12Rows1_3_eq : table12Rows1_3 = RadiusFourPruning.final1_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical1_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows1_4 : List (List State) := sourceRows1_4.map table12Project
theorem table12Rows1_4_eq : table12Rows1_4 = RadiusFourPruning.final1_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical1_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows1_5 : List (List State) := sourceRows1_5.map table12Project
theorem table12Rows1_5_eq : table12Rows1_5 = RadiusFourPruning.final1_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical1_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows2_0 : List (List State) := sourceRows2_0.map table12Project
theorem table12Rows2_0_eq : table12Rows2_0 = RadiusFourPruning.final2_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical2_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows2_1 : List (List State) := sourceRows2_1.map table12Project
theorem table12Rows2_1_eq : table12Rows2_1 = RadiusFourPruning.final2_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical2_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows2_2 : List (List State) := sourceRows2_2.map table12Project
theorem table12Rows2_2_eq : table12Rows2_2 = RadiusFourPruning.final2_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical2_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows2_3 : List (List State) := sourceRows2_3.map table12Project
theorem table12Rows2_3_eq : table12Rows2_3 = RadiusFourPruning.final2_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical2_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows2_4 : List (List State) := sourceRows2_4.map table12Project
theorem table12Rows2_4_eq : table12Rows2_4 = RadiusFourPruning.final2_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical2_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows2_5 : List (List State) := sourceRows2_5.map table12Project
theorem table12Rows2_5_eq : table12Rows2_5 = RadiusFourPruning.final2_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical2_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows3_0 : List (List State) := sourceRows3_0.map table12Project
theorem table12Rows3_0_eq : table12Rows3_0 = RadiusFourPruning.final3_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical3_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows3_1 : List (List State) := sourceRows3_1.map table12Project
theorem table12Rows3_1_eq : table12Rows3_1 = RadiusFourPruning.final3_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical3_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows3_2 : List (List State) := sourceRows3_2.map table12Project
theorem table12Rows3_2_eq : table12Rows3_2 = RadiusFourPruning.final3_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical3_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows3_3 : List (List State) := sourceRows3_3.map table12Project
theorem table12Rows3_3_eq : table12Rows3_3 = RadiusFourPruning.final3_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical3_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows3_4 : List (List State) := sourceRows3_4.map table12Project
theorem table12Rows3_4_eq : table12Rows3_4 = RadiusFourPruning.final3_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical3_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows3_5 : List (List State) := sourceRows3_5.map table12Project
theorem table12Rows3_5_eq : table12Rows3_5 = RadiusFourPruning.final3_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical3_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows4_0 : List (List State) := sourceRows4_0.map table12Project
theorem table12Rows4_0_eq : table12Rows4_0 = RadiusFourPruning.final4_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical4_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows4_1 : List (List State) := sourceRows4_1.map table12Project
theorem table12Rows4_1_eq : table12Rows4_1 = RadiusFourPruning.final4_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical4_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows4_2 : List (List State) := sourceRows4_2.map table12Project
theorem table12Rows4_2_eq : table12Rows4_2 = RadiusFourPruning.final4_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical4_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows4_3 : List (List State) := sourceRows4_3.map table12Project
theorem table12Rows4_3_eq : table12Rows4_3 = RadiusFourPruning.final4_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical4_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows4_4 : List (List State) := sourceRows4_4.map table12Project
theorem table12Rows4_4_eq : table12Rows4_4 = RadiusFourPruning.final4_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical4_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows4_5 : List (List State) := sourceRows4_5.map table12Project
theorem table12Rows4_5_eq : table12Rows4_5 = RadiusFourPruning.final4_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical4_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows5_0 : List (List State) := sourceRows5_0.map table12Project
theorem table12Rows5_0_eq : table12Rows5_0 = RadiusFourPruning.final5_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical5_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows5_1 : List (List State) := sourceRows5_1.map table12Project
theorem table12Rows5_1_eq : table12Rows5_1 = RadiusFourPruning.final5_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical5_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows5_2 : List (List State) := sourceRows5_2.map table12Project
theorem table12Rows5_2_eq : table12Rows5_2 = RadiusFourPruning.final5_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical5_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows5_3 : List (List State) := sourceRows5_3.map table12Project
theorem table12Rows5_3_eq : table12Rows5_3 = RadiusFourPruning.final5_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical5_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows5_4 : List (List State) := sourceRows5_4.map table12Project
theorem table12Rows5_4_eq : table12Rows5_4 = RadiusFourPruning.final5_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical5_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows5_5 : List (List State) := sourceRows5_5.map table12Project
theorem table12Rows5_5_eq : table12Rows5_5 = RadiusFourPruning.final5_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical5_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows6_0 : List (List State) := sourceRows6_0.map table12Project
theorem table12Rows6_0_eq : table12Rows6_0 = RadiusFourPruning.final6_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical6_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows6_1 : List (List State) := sourceRows6_1.map table12Project
theorem table12Rows6_1_eq : table12Rows6_1 = RadiusFourPruning.final6_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical6_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows6_2 : List (List State) := sourceRows6_2.map table12Project
theorem table12Rows6_2_eq : table12Rows6_2 = RadiusFourPruning.final6_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical6_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows6_3 : List (List State) := sourceRows6_3.map table12Project
theorem table12Rows6_3_eq : table12Rows6_3 = RadiusFourPruning.final6_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical6_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows6_4 : List (List State) := sourceRows6_4.map table12Project
theorem table12Rows6_4_eq : table12Rows6_4 = RadiusFourPruning.final6_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical6_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows6_5 : List (List State) := sourceRows6_5.map table12Project
theorem table12Rows6_5_eq : table12Rows6_5 = RadiusFourPruning.final6_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical6_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows7_0 : List (List State) := sourceRows7_0.map table12Project
theorem table12Rows7_0_eq : table12Rows7_0 = RadiusFourPruning.final7_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical7_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows7_1 : List (List State) := sourceRows7_1.map table12Project
theorem table12Rows7_1_eq : table12Rows7_1 = RadiusFourPruning.final7_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical7_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows7_2 : List (List State) := sourceRows7_2.map table12Project
theorem table12Rows7_2_eq : table12Rows7_2 = RadiusFourPruning.final7_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical7_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows7_3 : List (List State) := sourceRows7_3.map table12Project
theorem table12Rows7_3_eq : table12Rows7_3 = RadiusFourPruning.final7_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical7_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows7_4 : List (List State) := sourceRows7_4.map table12Project
theorem table12Rows7_4_eq : table12Rows7_4 = RadiusFourPruning.final7_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical7_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows7_5 : List (List State) := sourceRows7_5.map table12Project
theorem table12Rows7_5_eq : table12Rows7_5 = RadiusFourPruning.final7_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical7_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows8_0 : List (List State) := sourceRows8_0.map table12Project
theorem table12Rows8_0_eq : table12Rows8_0 = RadiusFourPruning.final8_0.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical8_0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows8_1 : List (List State) := sourceRows8_1.map table12Project
theorem table12Rows8_1_eq : table12Rows8_1 = RadiusFourPruning.final8_1.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical8_1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows8_2 : List (List State) := sourceRows8_2.map table12Project
theorem table12Rows8_2_eq : table12Rows8_2 = RadiusFourPruning.final8_2.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical8_2]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows8_3 : List (List State) := sourceRows8_3.map table12Project
theorem table12Rows8_3_eq : table12Rows8_3 = RadiusFourPruning.final8_3.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical8_3]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows8_4 : List (List State) := sourceRows8_4.map table12Project
theorem table12Rows8_4_eq : table12Rows8_4 = RadiusFourPruning.final8_4.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical8_4]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12Rows8_5 : List (List State) := sourceRows8_5.map table12Project
theorem table12Rows8_5_eq : table12Rows8_5 = RadiusFourPruning.final8_5.map (fun p =>
    table12Scope.map (fun v => patchState p (subPos (positions v) (-4,5)))) := by
  rw [sourceRowsCanonical8_5]
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  exact table12Project_eq row
def table12 : Constraint 91 State := ⟨table12Scope, [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5].flatten⟩
theorem table12_eq : table12 = windowConstraint positions (hexRegion 4)
    RadiusFourPruning.certifiedFamily (-4,5) := by
  unfold table12 windowConstraint
  rw [← table12Scope_eq]
  simp only [RadiusFourPruning.certifiedFamily, RadiusFourPruning.finalChunks, List.map_flatten,
    List.map_cons, List.map_nil, ← table12Rows0_0_eq, ← table12Rows0_1_eq, ← table12Rows0_2_eq, ← table12Rows0_3_eq, ← table12Rows0_4_eq, ← table12Rows0_5_eq, ← table12Rows1_0_eq, ← table12Rows1_1_eq, ← table12Rows1_2_eq, ← table12Rows1_3_eq, ← table12Rows1_4_eq, ← table12Rows1_5_eq, ← table12Rows2_0_eq, ← table12Rows2_1_eq, ← table12Rows2_2_eq, ← table12Rows2_3_eq, ← table12Rows2_4_eq, ← table12Rows2_5_eq, ← table12Rows3_0_eq, ← table12Rows3_1_eq, ← table12Rows3_2_eq, ← table12Rows3_3_eq, ← table12Rows3_4_eq, ← table12Rows3_5_eq, ← table12Rows4_0_eq, ← table12Rows4_1_eq, ← table12Rows4_2_eq, ← table12Rows4_3_eq, ← table12Rows4_4_eq, ← table12Rows4_5_eq, ← table12Rows5_0_eq, ← table12Rows5_1_eq, ← table12Rows5_2_eq, ← table12Rows5_3_eq, ← table12Rows5_4_eq, ← table12Rows5_5_eq, ← table12Rows6_0_eq, ← table12Rows6_1_eq, ← table12Rows6_2_eq, ← table12Rows6_3_eq, ← table12Rows6_4_eq, ← table12Rows6_5_eq, ← table12Rows7_0_eq, ← table12Rows7_1_eq, ← table12Rows7_2_eq, ← table12Rows7_3_eq, ← table12Rows7_4_eq, ← table12Rows7_5_eq, ← table12Rows8_0_eq, ← table12Rows8_1_eq, ← table12Rows8_2_eq, ← table12Rows8_3_eq, ← table12Rows8_4_eq, ← table12Rows8_5_eq]
theorem table12_member : table12 ∈ constraints := by
  rw [table12_eq]
  exact List.mem_map.mpr ⟨(-4,5), by decide, rfl⟩
end SpectreFinite.HexSearch.RadiusFive
