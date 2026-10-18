module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration15RootChunk0 : List Cell := (rootCells configuration15).drop 0 |>.take 12
theorem configuration15RootChunk0_checked : configuration15RootChunk0.all (fun a =>
    (neighborCells configuration15).all (cellPairFastB configuration15.sharedPath a)) = true := by decide

def configuration15RootChunk1 : List Cell := (rootCells configuration15).drop 12 |>.take 12
theorem configuration15RootChunk1_checked : configuration15RootChunk1.all (fun a =>
    (neighborCells configuration15).all (cellPairFastB configuration15.sharedPath a)) = true := by decide

def configuration15RootChunk2 : List Cell := (rootCells configuration15).drop 24 |>.take 12
theorem configuration15RootChunk2_checked : configuration15RootChunk2.all (fun a =>
    (neighborCells configuration15).all (cellPairFastB configuration15.sharedPath a)) = true := by decide

def configuration15RootChunk3 : List Cell := (rootCells configuration15).drop 36 |>.take 12
theorem configuration15RootChunk3_checked : configuration15RootChunk3.all (fun a =>
    (neighborCells configuration15).all (cellPairFastB configuration15.sharedPath a)) = true := by decide

def configuration15RootChunk4 : List Cell := (rootCells configuration15).drop 48 |>.take 12
theorem configuration15RootChunk4_checked : configuration15RootChunk4.all (fun a =>
    (neighborCells configuration15).all (cellPairFastB configuration15.sharedPath a)) = true := by decide

def configuration15RootChunk5 : List Cell := (rootCells configuration15).drop 60 |>.take 12
theorem configuration15RootChunk5_checked : configuration15RootChunk5.all (fun a =>
    (neighborCells configuration15).all (cellPairFastB configuration15.sharedPath a)) = true := by decide

def configuration15RootChunk6 : List Cell := (rootCells configuration15).drop 72 |>.take 12
theorem configuration15RootChunk6_checked : configuration15RootChunk6.all (fun a =>
    (neighborCells configuration15).all (cellPairFastB configuration15.sharedPath a)) = true := by decide

theorem placement15_checked : configurationCheckedB configuration15 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration15.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration15 = configuration15RootChunk0 ++ configuration15RootChunk1 ++ configuration15RootChunk2 ++ configuration15RootChunk3 ++ configuration15RootChunk4 ++ configuration15RootChunk5 ++ configuration15RootChunk6 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration15RootChunk0_checked,configuration15RootChunk1_checked,configuration15RootChunk2_checked,configuration15RootChunk3_checked,configuration15RootChunk4_checked,configuration15RootChunk5_checked,configuration15RootChunk6_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
