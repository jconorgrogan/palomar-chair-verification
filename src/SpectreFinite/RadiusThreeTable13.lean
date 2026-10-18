module

public import SpectreFinite.RadiusThreeSourceRows

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def table13Scope : List (Fin 37) := [2, 3, 6, 7, 8, 11, 12, 13, 14, 18, 19, 20, 21, 25, 26, 27]
theorem table13Scope_eq : table13Scope = windowScope positions (hexRegion 2) (-1,2) := by rfl
def table13Rows0_0 : List (List State) := sourceRows0_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows0_0_eq : table13Rows0_0 = RadiusTwoPruning.final0_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows0_1 : List (List State) := sourceRows0_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows0_1_eq : table13Rows0_1 = RadiusTwoPruning.final0_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows0_2 : List (List State) := sourceRows0_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows0_2_eq : table13Rows0_2 = RadiusTwoPruning.final0_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows0_3 : List (List State) := sourceRows0_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows0_3_eq : table13Rows0_3 = RadiusTwoPruning.final0_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows0_4 : List (List State) := sourceRows0_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows0_4_eq : table13Rows0_4 = RadiusTwoPruning.final0_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows0_5 : List (List State) := sourceRows0_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows0_5_eq : table13Rows0_5 = RadiusTwoPruning.final0_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows1_0 : List (List State) := sourceRows1_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows1_0_eq : table13Rows1_0 = RadiusTwoPruning.final1_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows1_1 : List (List State) := sourceRows1_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows1_1_eq : table13Rows1_1 = RadiusTwoPruning.final1_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows1_2 : List (List State) := sourceRows1_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows1_2_eq : table13Rows1_2 = RadiusTwoPruning.final1_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows1_3 : List (List State) := sourceRows1_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows1_3_eq : table13Rows1_3 = RadiusTwoPruning.final1_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows1_4 : List (List State) := sourceRows1_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows1_4_eq : table13Rows1_4 = RadiusTwoPruning.final1_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows1_5 : List (List State) := sourceRows1_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows1_5_eq : table13Rows1_5 = RadiusTwoPruning.final1_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows2_0 : List (List State) := sourceRows2_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows2_0_eq : table13Rows2_0 = RadiusTwoPruning.final2_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows2_1 : List (List State) := sourceRows2_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows2_1_eq : table13Rows2_1 = RadiusTwoPruning.final2_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows2_2 : List (List State) := sourceRows2_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows2_2_eq : table13Rows2_2 = RadiusTwoPruning.final2_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows2_3 : List (List State) := sourceRows2_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows2_3_eq : table13Rows2_3 = RadiusTwoPruning.final2_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows2_4 : List (List State) := sourceRows2_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows2_4_eq : table13Rows2_4 = RadiusTwoPruning.final2_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows2_5 : List (List State) := sourceRows2_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows2_5_eq : table13Rows2_5 = RadiusTwoPruning.final2_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows3_0 : List (List State) := sourceRows3_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows3_0_eq : table13Rows3_0 = RadiusTwoPruning.final3_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows3_1 : List (List State) := sourceRows3_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows3_1_eq : table13Rows3_1 = RadiusTwoPruning.final3_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows3_2 : List (List State) := sourceRows3_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows3_2_eq : table13Rows3_2 = RadiusTwoPruning.final3_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows3_3 : List (List State) := sourceRows3_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows3_3_eq : table13Rows3_3 = RadiusTwoPruning.final3_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows3_4 : List (List State) := sourceRows3_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows3_4_eq : table13Rows3_4 = RadiusTwoPruning.final3_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows3_5 : List (List State) := sourceRows3_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows3_5_eq : table13Rows3_5 = RadiusTwoPruning.final3_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows4_0 : List (List State) := sourceRows4_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows4_0_eq : table13Rows4_0 = RadiusTwoPruning.final4_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows4_1 : List (List State) := sourceRows4_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows4_1_eq : table13Rows4_1 = RadiusTwoPruning.final4_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows4_2 : List (List State) := sourceRows4_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows4_2_eq : table13Rows4_2 = RadiusTwoPruning.final4_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows4_3 : List (List State) := sourceRows4_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows4_3_eq : table13Rows4_3 = RadiusTwoPruning.final4_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows4_4 : List (List State) := sourceRows4_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows4_4_eq : table13Rows4_4 = RadiusTwoPruning.final4_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows4_5 : List (List State) := sourceRows4_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows4_5_eq : table13Rows4_5 = RadiusTwoPruning.final4_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows5_0 : List (List State) := sourceRows5_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows5_0_eq : table13Rows5_0 = RadiusTwoPruning.final5_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows5_1 : List (List State) := sourceRows5_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows5_1_eq : table13Rows5_1 = RadiusTwoPruning.final5_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows5_2 : List (List State) := sourceRows5_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows5_2_eq : table13Rows5_2 = RadiusTwoPruning.final5_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows5_3 : List (List State) := sourceRows5_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows5_3_eq : table13Rows5_3 = RadiusTwoPruning.final5_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows5_4 : List (List State) := sourceRows5_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows5_4_eq : table13Rows5_4 = RadiusTwoPruning.final5_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows5_5 : List (List State) := sourceRows5_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows5_5_eq : table13Rows5_5 = RadiusTwoPruning.final5_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows6_0 : List (List State) := sourceRows6_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows6_0_eq : table13Rows6_0 = RadiusTwoPruning.final6_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows6_1 : List (List State) := sourceRows6_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows6_1_eq : table13Rows6_1 = RadiusTwoPruning.final6_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows6_2 : List (List State) := sourceRows6_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows6_2_eq : table13Rows6_2 = RadiusTwoPruning.final6_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows6_3 : List (List State) := sourceRows6_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows6_3_eq : table13Rows6_3 = RadiusTwoPruning.final6_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows6_4 : List (List State) := sourceRows6_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows6_4_eq : table13Rows6_4 = RadiusTwoPruning.final6_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows6_5 : List (List State) := sourceRows6_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows6_5_eq : table13Rows6_5 = RadiusTwoPruning.final6_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows7_0 : List (List State) := sourceRows7_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows7_0_eq : table13Rows7_0 = RadiusTwoPruning.final7_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows7_1 : List (List State) := sourceRows7_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows7_1_eq : table13Rows7_1 = RadiusTwoPruning.final7_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows7_2 : List (List State) := sourceRows7_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows7_2_eq : table13Rows7_2 = RadiusTwoPruning.final7_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows7_3 : List (List State) := sourceRows7_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows7_3_eq : table13Rows7_3 = RadiusTwoPruning.final7_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows7_4 : List (List State) := sourceRows7_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows7_4_eq : table13Rows7_4 = RadiusTwoPruning.final7_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows7_5 : List (List State) := sourceRows7_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows7_5_eq : table13Rows7_5 = RadiusTwoPruning.final7_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows8_0 : List (List State) := sourceRows8_0.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows8_0_eq : table13Rows8_0 = RadiusTwoPruning.final8_0.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows8_1 : List (List State) := sourceRows8_1.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows8_1_eq : table13Rows8_1 = RadiusTwoPruning.final8_1.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows8_2 : List (List State) := sourceRows8_2.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows8_2_eq : table13Rows8_2 = RadiusTwoPruning.final8_2.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows8_3 : List (List State) := sourceRows8_3.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows8_3_eq : table13Rows8_3 = RadiusTwoPruning.final8_3.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows8_4 : List (List State) := sourceRows8_4.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows8_4_eq : table13Rows8_4 = RadiusTwoPruning.final8_4.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13Rows8_5 : List (List State) := sourceRows8_5.map (fun row =>
  [row[0]?.getD (0,0),row[1]?.getD (0,0),row[3]?.getD (0,0),row[4]?.getD (0,0),row[5]?.getD (0,0),row[7]?.getD (0,0),row[8]?.getD (0,0),row[9]?.getD (0,0),row[10]?.getD (0,0),row[12]?.getD (0,0),row[13]?.getD (0,0),row[14]?.getD (0,0),row[15]?.getD (0,0),row[16]?.getD (0,0),row[17]?.getD (0,0),row[18]?.getD (0,0)])
theorem table13Rows8_5_eq : table13Rows8_5 = RadiusTwoPruning.final8_5.map (fun p =>
    table13Scope.map (fun v => patchState p (subPos (positions v) (-1,2)))) := by rfl
def table13 : Constraint 37 State := ⟨table13Scope, [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5].flatten⟩
theorem table13_eq : table13 = windowConstraint positions (hexRegion 2)
    RadiusTwoPruning.certifiedFamily (-1,2) := by
  unfold table13 windowConstraint
  rw [← table13Scope_eq]
  simp only [RadiusTwoPruning.certifiedFamily, RadiusTwoPruning.finalChunks, List.map_flatten,
    List.map_cons, List.map_nil, ← table13Rows0_0_eq, ← table13Rows0_1_eq, ← table13Rows0_2_eq, ← table13Rows0_3_eq, ← table13Rows0_4_eq, ← table13Rows0_5_eq, ← table13Rows1_0_eq, ← table13Rows1_1_eq, ← table13Rows1_2_eq, ← table13Rows1_3_eq, ← table13Rows1_4_eq, ← table13Rows1_5_eq, ← table13Rows2_0_eq, ← table13Rows2_1_eq, ← table13Rows2_2_eq, ← table13Rows2_3_eq, ← table13Rows2_4_eq, ← table13Rows2_5_eq, ← table13Rows3_0_eq, ← table13Rows3_1_eq, ← table13Rows3_2_eq, ← table13Rows3_3_eq, ← table13Rows3_4_eq, ← table13Rows3_5_eq, ← table13Rows4_0_eq, ← table13Rows4_1_eq, ← table13Rows4_2_eq, ← table13Rows4_3_eq, ← table13Rows4_4_eq, ← table13Rows4_5_eq, ← table13Rows5_0_eq, ← table13Rows5_1_eq, ← table13Rows5_2_eq, ← table13Rows5_3_eq, ← table13Rows5_4_eq, ← table13Rows5_5_eq, ← table13Rows6_0_eq, ← table13Rows6_1_eq, ← table13Rows6_2_eq, ← table13Rows6_3_eq, ← table13Rows6_4_eq, ← table13Rows6_5_eq, ← table13Rows7_0_eq, ← table13Rows7_1_eq, ← table13Rows7_2_eq, ← table13Rows7_3_eq, ← table13Rows7_4_eq, ← table13Rows7_5_eq, ← table13Rows8_0_eq, ← table13Rows8_1_eq, ← table13Rows8_2_eq, ← table13Rows8_3_eq, ← table13Rows8_4_eq, ← table13Rows8_5_eq]
theorem table13_member : table13 ∈ constraints := by
  rw [table13_eq]
  exact List.mem_map.mpr ⟨(-1,2), by decide, rfl⟩
end SpectreFinite.HexSearch.RadiusThree
