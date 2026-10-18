module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration18RootChunk0 : List Cell := (rootCells configuration18).drop 0 |>.take 8
theorem configuration18RootChunk0_checked : configuration18RootChunk0.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk1 : List Cell := (rootCells configuration18).drop 8 |>.take 8
theorem configuration18RootChunk1_checked : configuration18RootChunk1.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk2 : List Cell := (rootCells configuration18).drop 16 |>.take 8
theorem configuration18RootChunk2_checked : configuration18RootChunk2.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk3 : List Cell := (rootCells configuration18).drop 24 |>.take 8
theorem configuration18RootChunk3_checked : configuration18RootChunk3.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk4 : List Cell := (rootCells configuration18).drop 32 |>.take 8
theorem configuration18RootChunk4_checked : configuration18RootChunk4.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk5 : List Cell := (rootCells configuration18).drop 40 |>.take 8
theorem configuration18RootChunk5_checked : configuration18RootChunk5.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk6 : List Cell := (rootCells configuration18).drop 48 |>.take 8
theorem configuration18RootChunk6_checked : configuration18RootChunk6.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk7 : List Cell := (rootCells configuration18).drop 56 |>.take 8
theorem configuration18RootChunk7_checked : configuration18RootChunk7.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk8 : List Cell := (rootCells configuration18).drop 64 |>.take 8
theorem configuration18RootChunk8_checked : configuration18RootChunk8.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

def configuration18RootChunk9 : List Cell := (rootCells configuration18).drop 72 |>.take 8
theorem configuration18RootChunk9_checked : configuration18RootChunk9.all (fun a =>
    (neighborCells configuration18).all (cellPairFastB configuration18.sharedPath a)) = true := by decide

theorem placement18_checked : configurationCheckedB configuration18 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration18.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration18 = configuration18RootChunk0 ++ configuration18RootChunk1 ++ configuration18RootChunk2 ++ configuration18RootChunk3 ++ configuration18RootChunk4 ++ configuration18RootChunk5 ++ configuration18RootChunk6 ++ configuration18RootChunk7 ++ configuration18RootChunk8 ++ configuration18RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration18RootChunk0_checked,configuration18RootChunk1_checked,configuration18RootChunk2_checked,configuration18RootChunk3_checked,configuration18RootChunk4_checked,configuration18RootChunk5_checked,configuration18RootChunk6_checked,configuration18RootChunk7_checked,configuration18RootChunk8_checked,configuration18RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
