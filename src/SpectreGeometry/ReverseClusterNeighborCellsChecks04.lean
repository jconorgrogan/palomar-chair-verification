module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration4RootChunk0 : List Cell := (rootCells configuration4).drop 0 |>.take 8
theorem configuration4RootChunk0_checked : configuration4RootChunk0.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk1 : List Cell := (rootCells configuration4).drop 8 |>.take 8
theorem configuration4RootChunk1_checked : configuration4RootChunk1.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk2 : List Cell := (rootCells configuration4).drop 16 |>.take 8
theorem configuration4RootChunk2_checked : configuration4RootChunk2.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk3 : List Cell := (rootCells configuration4).drop 24 |>.take 8
theorem configuration4RootChunk3_checked : configuration4RootChunk3.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk4 : List Cell := (rootCells configuration4).drop 32 |>.take 8
theorem configuration4RootChunk4_checked : configuration4RootChunk4.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk5 : List Cell := (rootCells configuration4).drop 40 |>.take 8
theorem configuration4RootChunk5_checked : configuration4RootChunk5.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk6 : List Cell := (rootCells configuration4).drop 48 |>.take 8
theorem configuration4RootChunk6_checked : configuration4RootChunk6.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk7 : List Cell := (rootCells configuration4).drop 56 |>.take 8
theorem configuration4RootChunk7_checked : configuration4RootChunk7.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

def configuration4RootChunk8 : List Cell := (rootCells configuration4).drop 64 |>.take 8
theorem configuration4RootChunk8_checked : configuration4RootChunk8.all (fun a =>
    (neighborCells configuration4).all (cellPairFastB configuration4.sharedPath a)) = true := by decide

theorem placement4_checked : configurationCheckedB configuration4 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration4.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration4 = configuration4RootChunk0 ++ configuration4RootChunk1 ++ configuration4RootChunk2 ++ configuration4RootChunk3 ++ configuration4RootChunk4 ++ configuration4RootChunk5 ++ configuration4RootChunk6 ++ configuration4RootChunk7 ++ configuration4RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration4RootChunk0_checked,configuration4RootChunk1_checked,configuration4RootChunk2_checked,configuration4RootChunk3_checked,configuration4RootChunk4_checked,configuration4RootChunk5_checked,configuration4RootChunk6_checked,configuration4RootChunk7_checked,configuration4RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
