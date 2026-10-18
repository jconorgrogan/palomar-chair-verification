module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration22RootChunk0 : List Cell := (rootCells configuration22).drop 0 |>.take 8
theorem configuration22RootChunk0_checked : configuration22RootChunk0.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk1 : List Cell := (rootCells configuration22).drop 8 |>.take 8
theorem configuration22RootChunk1_checked : configuration22RootChunk1.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk2 : List Cell := (rootCells configuration22).drop 16 |>.take 8
theorem configuration22RootChunk2_checked : configuration22RootChunk2.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk3 : List Cell := (rootCells configuration22).drop 24 |>.take 8
theorem configuration22RootChunk3_checked : configuration22RootChunk3.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk4 : List Cell := (rootCells configuration22).drop 32 |>.take 8
theorem configuration22RootChunk4_checked : configuration22RootChunk4.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk5 : List Cell := (rootCells configuration22).drop 40 |>.take 8
theorem configuration22RootChunk5_checked : configuration22RootChunk5.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk6 : List Cell := (rootCells configuration22).drop 48 |>.take 8
theorem configuration22RootChunk6_checked : configuration22RootChunk6.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk7 : List Cell := (rootCells configuration22).drop 56 |>.take 8
theorem configuration22RootChunk7_checked : configuration22RootChunk7.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk8 : List Cell := (rootCells configuration22).drop 64 |>.take 8
theorem configuration22RootChunk8_checked : configuration22RootChunk8.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

def configuration22RootChunk9 : List Cell := (rootCells configuration22).drop 72 |>.take 8
theorem configuration22RootChunk9_checked : configuration22RootChunk9.all (fun a =>
    (neighborCells configuration22).all (cellPairFastB configuration22.sharedPath a)) = true := by decide

theorem placement22_checked : configurationCheckedB configuration22 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration22.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration22 = configuration22RootChunk0 ++ configuration22RootChunk1 ++ configuration22RootChunk2 ++ configuration22RootChunk3 ++ configuration22RootChunk4 ++ configuration22RootChunk5 ++ configuration22RootChunk6 ++ configuration22RootChunk7 ++ configuration22RootChunk8 ++ configuration22RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration22RootChunk0_checked,configuration22RootChunk1_checked,configuration22RootChunk2_checked,configuration22RootChunk3_checked,configuration22RootChunk4_checked,configuration22RootChunk5_checked,configuration22RootChunk6_checked,configuration22RootChunk7_checked,configuration22RootChunk8_checked,configuration22RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
