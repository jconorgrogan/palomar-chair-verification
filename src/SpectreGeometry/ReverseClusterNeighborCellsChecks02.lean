module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration2RootChunk0 : List Cell := (rootCells configuration2).drop 0 |>.take 8
theorem configuration2RootChunk0_checked : configuration2RootChunk0.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk1 : List Cell := (rootCells configuration2).drop 8 |>.take 8
theorem configuration2RootChunk1_checked : configuration2RootChunk1.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk2 : List Cell := (rootCells configuration2).drop 16 |>.take 8
theorem configuration2RootChunk2_checked : configuration2RootChunk2.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk3 : List Cell := (rootCells configuration2).drop 24 |>.take 8
theorem configuration2RootChunk3_checked : configuration2RootChunk3.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk4 : List Cell := (rootCells configuration2).drop 32 |>.take 8
theorem configuration2RootChunk4_checked : configuration2RootChunk4.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk5 : List Cell := (rootCells configuration2).drop 40 |>.take 8
theorem configuration2RootChunk5_checked : configuration2RootChunk5.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk6 : List Cell := (rootCells configuration2).drop 48 |>.take 8
theorem configuration2RootChunk6_checked : configuration2RootChunk6.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk7 : List Cell := (rootCells configuration2).drop 56 |>.take 8
theorem configuration2RootChunk7_checked : configuration2RootChunk7.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

def configuration2RootChunk8 : List Cell := (rootCells configuration2).drop 64 |>.take 8
theorem configuration2RootChunk8_checked : configuration2RootChunk8.all (fun a =>
    (neighborCells configuration2).all (cellPairFastB configuration2.sharedPath a)) = true := by decide

theorem placement2_checked : configurationCheckedB configuration2 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration2.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration2 = configuration2RootChunk0 ++ configuration2RootChunk1 ++ configuration2RootChunk2 ++ configuration2RootChunk3 ++ configuration2RootChunk4 ++ configuration2RootChunk5 ++ configuration2RootChunk6 ++ configuration2RootChunk7 ++ configuration2RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration2RootChunk0_checked,configuration2RootChunk1_checked,configuration2RootChunk2_checked,configuration2RootChunk3_checked,configuration2RootChunk4_checked,configuration2RootChunk5_checked,configuration2RootChunk6_checked,configuration2RootChunk7_checked,configuration2RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
