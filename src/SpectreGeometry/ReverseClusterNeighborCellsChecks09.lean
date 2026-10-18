module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration9RootChunk0 : List Cell := (rootCells configuration9).drop 0 |>.take 8
theorem configuration9RootChunk0_checked : configuration9RootChunk0.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk1 : List Cell := (rootCells configuration9).drop 8 |>.take 8
theorem configuration9RootChunk1_checked : configuration9RootChunk1.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk2 : List Cell := (rootCells configuration9).drop 16 |>.take 8
theorem configuration9RootChunk2_checked : configuration9RootChunk2.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk3 : List Cell := (rootCells configuration9).drop 24 |>.take 8
theorem configuration9RootChunk3_checked : configuration9RootChunk3.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk4 : List Cell := (rootCells configuration9).drop 32 |>.take 8
theorem configuration9RootChunk4_checked : configuration9RootChunk4.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk5 : List Cell := (rootCells configuration9).drop 40 |>.take 8
theorem configuration9RootChunk5_checked : configuration9RootChunk5.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk6 : List Cell := (rootCells configuration9).drop 48 |>.take 8
theorem configuration9RootChunk6_checked : configuration9RootChunk6.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk7 : List Cell := (rootCells configuration9).drop 56 |>.take 8
theorem configuration9RootChunk7_checked : configuration9RootChunk7.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

def configuration9RootChunk8 : List Cell := (rootCells configuration9).drop 64 |>.take 8
theorem configuration9RootChunk8_checked : configuration9RootChunk8.all (fun a =>
    (neighborCells configuration9).all (cellPairFastB configuration9.sharedPath a)) = true := by decide

theorem placement9_checked : configurationCheckedB configuration9 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration9.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration9 = configuration9RootChunk0 ++ configuration9RootChunk1 ++ configuration9RootChunk2 ++ configuration9RootChunk3 ++ configuration9RootChunk4 ++ configuration9RootChunk5 ++ configuration9RootChunk6 ++ configuration9RootChunk7 ++ configuration9RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration9RootChunk0_checked,configuration9RootChunk1_checked,configuration9RootChunk2_checked,configuration9RootChunk3_checked,configuration9RootChunk4_checked,configuration9RootChunk5_checked,configuration9RootChunk6_checked,configuration9RootChunk7_checked,configuration9RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
