module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration10RootChunk0 : List Cell := (rootCells configuration10).drop 0 |>.take 8
theorem configuration10RootChunk0_checked : configuration10RootChunk0.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk1 : List Cell := (rootCells configuration10).drop 8 |>.take 8
theorem configuration10RootChunk1_checked : configuration10RootChunk1.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk2 : List Cell := (rootCells configuration10).drop 16 |>.take 8
theorem configuration10RootChunk2_checked : configuration10RootChunk2.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk3 : List Cell := (rootCells configuration10).drop 24 |>.take 8
theorem configuration10RootChunk3_checked : configuration10RootChunk3.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk4 : List Cell := (rootCells configuration10).drop 32 |>.take 8
theorem configuration10RootChunk4_checked : configuration10RootChunk4.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk5 : List Cell := (rootCells configuration10).drop 40 |>.take 8
theorem configuration10RootChunk5_checked : configuration10RootChunk5.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk6 : List Cell := (rootCells configuration10).drop 48 |>.take 8
theorem configuration10RootChunk6_checked : configuration10RootChunk6.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk7 : List Cell := (rootCells configuration10).drop 56 |>.take 8
theorem configuration10RootChunk7_checked : configuration10RootChunk7.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

def configuration10RootChunk8 : List Cell := (rootCells configuration10).drop 64 |>.take 8
theorem configuration10RootChunk8_checked : configuration10RootChunk8.all (fun a =>
    (neighborCells configuration10).all (cellPairFastB configuration10.sharedPath a)) = true := by decide

theorem placement10_checked : configurationCheckedB configuration10 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration10.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration10 = configuration10RootChunk0 ++ configuration10RootChunk1 ++ configuration10RootChunk2 ++ configuration10RootChunk3 ++ configuration10RootChunk4 ++ configuration10RootChunk5 ++ configuration10RootChunk6 ++ configuration10RootChunk7 ++ configuration10RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration10RootChunk0_checked,configuration10RootChunk1_checked,configuration10RootChunk2_checked,configuration10RootChunk3_checked,configuration10RootChunk4_checked,configuration10RootChunk5_checked,configuration10RootChunk6_checked,configuration10RootChunk7_checked,configuration10RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
