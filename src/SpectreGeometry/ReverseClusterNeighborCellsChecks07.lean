module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration7RootChunk0 : List Cell := (rootCells configuration7).drop 0 |>.take 8
theorem configuration7RootChunk0_checked : configuration7RootChunk0.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk1 : List Cell := (rootCells configuration7).drop 8 |>.take 8
theorem configuration7RootChunk1_checked : configuration7RootChunk1.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk2 : List Cell := (rootCells configuration7).drop 16 |>.take 8
theorem configuration7RootChunk2_checked : configuration7RootChunk2.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk3 : List Cell := (rootCells configuration7).drop 24 |>.take 8
theorem configuration7RootChunk3_checked : configuration7RootChunk3.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk4 : List Cell := (rootCells configuration7).drop 32 |>.take 8
theorem configuration7RootChunk4_checked : configuration7RootChunk4.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk5 : List Cell := (rootCells configuration7).drop 40 |>.take 8
theorem configuration7RootChunk5_checked : configuration7RootChunk5.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk6 : List Cell := (rootCells configuration7).drop 48 |>.take 8
theorem configuration7RootChunk6_checked : configuration7RootChunk6.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk7 : List Cell := (rootCells configuration7).drop 56 |>.take 8
theorem configuration7RootChunk7_checked : configuration7RootChunk7.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

def configuration7RootChunk8 : List Cell := (rootCells configuration7).drop 64 |>.take 8
theorem configuration7RootChunk8_checked : configuration7RootChunk8.all (fun a =>
    (neighborCells configuration7).all (cellPairFastB configuration7.sharedPath a)) = true := by decide

theorem placement7_checked : configurationCheckedB configuration7 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration7.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration7 = configuration7RootChunk0 ++ configuration7RootChunk1 ++ configuration7RootChunk2 ++ configuration7RootChunk3 ++ configuration7RootChunk4 ++ configuration7RootChunk5 ++ configuration7RootChunk6 ++ configuration7RootChunk7 ++ configuration7RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration7RootChunk0_checked,configuration7RootChunk1_checked,configuration7RootChunk2_checked,configuration7RootChunk3_checked,configuration7RootChunk4_checked,configuration7RootChunk5_checked,configuration7RootChunk6_checked,configuration7RootChunk7_checked,configuration7RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
