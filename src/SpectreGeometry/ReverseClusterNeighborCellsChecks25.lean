module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration25RootChunk0 : List Cell := (rootCells configuration25).drop 0 |>.take 8
theorem configuration25RootChunk0_checked : configuration25RootChunk0.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk1 : List Cell := (rootCells configuration25).drop 8 |>.take 8
theorem configuration25RootChunk1_checked : configuration25RootChunk1.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk2 : List Cell := (rootCells configuration25).drop 16 |>.take 8
theorem configuration25RootChunk2_checked : configuration25RootChunk2.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk3 : List Cell := (rootCells configuration25).drop 24 |>.take 8
theorem configuration25RootChunk3_checked : configuration25RootChunk3.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk4 : List Cell := (rootCells configuration25).drop 32 |>.take 8
theorem configuration25RootChunk4_checked : configuration25RootChunk4.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk5 : List Cell := (rootCells configuration25).drop 40 |>.take 8
theorem configuration25RootChunk5_checked : configuration25RootChunk5.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk6 : List Cell := (rootCells configuration25).drop 48 |>.take 8
theorem configuration25RootChunk6_checked : configuration25RootChunk6.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk7 : List Cell := (rootCells configuration25).drop 56 |>.take 8
theorem configuration25RootChunk7_checked : configuration25RootChunk7.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk8 : List Cell := (rootCells configuration25).drop 64 |>.take 8
theorem configuration25RootChunk8_checked : configuration25RootChunk8.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

def configuration25RootChunk9 : List Cell := (rootCells configuration25).drop 72 |>.take 8
theorem configuration25RootChunk9_checked : configuration25RootChunk9.all (fun a =>
    (neighborCells configuration25).all (cellPairFastB configuration25.sharedPath a)) = true := by decide

theorem placement25_checked : configurationCheckedB configuration25 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration25.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration25 = configuration25RootChunk0 ++ configuration25RootChunk1 ++ configuration25RootChunk2 ++ configuration25RootChunk3 ++ configuration25RootChunk4 ++ configuration25RootChunk5 ++ configuration25RootChunk6 ++ configuration25RootChunk7 ++ configuration25RootChunk8 ++ configuration25RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration25RootChunk0_checked,configuration25RootChunk1_checked,configuration25RootChunk2_checked,configuration25RootChunk3_checked,configuration25RootChunk4_checked,configuration25RootChunk5_checked,configuration25RootChunk6_checked,configuration25RootChunk7_checked,configuration25RootChunk8_checked,configuration25RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
