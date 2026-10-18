module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration6RootChunk0 : List Cell := (rootCells configuration6).drop 0 |>.take 8
theorem configuration6RootChunk0_checked : configuration6RootChunk0.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk1 : List Cell := (rootCells configuration6).drop 8 |>.take 8
theorem configuration6RootChunk1_checked : configuration6RootChunk1.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk2 : List Cell := (rootCells configuration6).drop 16 |>.take 8
theorem configuration6RootChunk2_checked : configuration6RootChunk2.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk3 : List Cell := (rootCells configuration6).drop 24 |>.take 8
theorem configuration6RootChunk3_checked : configuration6RootChunk3.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk4 : List Cell := (rootCells configuration6).drop 32 |>.take 8
theorem configuration6RootChunk4_checked : configuration6RootChunk4.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk5 : List Cell := (rootCells configuration6).drop 40 |>.take 8
theorem configuration6RootChunk5_checked : configuration6RootChunk5.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk6 : List Cell := (rootCells configuration6).drop 48 |>.take 8
theorem configuration6RootChunk6_checked : configuration6RootChunk6.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk7 : List Cell := (rootCells configuration6).drop 56 |>.take 8
theorem configuration6RootChunk7_checked : configuration6RootChunk7.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

def configuration6RootChunk8 : List Cell := (rootCells configuration6).drop 64 |>.take 8
theorem configuration6RootChunk8_checked : configuration6RootChunk8.all (fun a =>
    (neighborCells configuration6).all (cellPairFastB configuration6.sharedPath a)) = true := by decide

theorem placement6_checked : configurationCheckedB configuration6 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration6.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration6 = configuration6RootChunk0 ++ configuration6RootChunk1 ++ configuration6RootChunk2 ++ configuration6RootChunk3 ++ configuration6RootChunk4 ++ configuration6RootChunk5 ++ configuration6RootChunk6 ++ configuration6RootChunk7 ++ configuration6RootChunk8 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration6RootChunk0_checked,configuration6RootChunk1_checked,configuration6RootChunk2_checked,configuration6RootChunk3_checked,configuration6RootChunk4_checked,configuration6RootChunk5_checked,configuration6RootChunk6_checked,configuration6RootChunk7_checked,configuration6RootChunk8_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
