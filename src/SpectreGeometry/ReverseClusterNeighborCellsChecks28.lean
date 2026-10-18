module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration28RootChunk0 : List Cell := (rootCells configuration28).drop 0 |>.take 8
theorem configuration28RootChunk0_checked : configuration28RootChunk0.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk1 : List Cell := (rootCells configuration28).drop 8 |>.take 8
theorem configuration28RootChunk1_checked : configuration28RootChunk1.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk2 : List Cell := (rootCells configuration28).drop 16 |>.take 8
theorem configuration28RootChunk2_checked : configuration28RootChunk2.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk3 : List Cell := (rootCells configuration28).drop 24 |>.take 8
theorem configuration28RootChunk3_checked : configuration28RootChunk3.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk4 : List Cell := (rootCells configuration28).drop 32 |>.take 8
theorem configuration28RootChunk4_checked : configuration28RootChunk4.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk5 : List Cell := (rootCells configuration28).drop 40 |>.take 8
theorem configuration28RootChunk5_checked : configuration28RootChunk5.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk6 : List Cell := (rootCells configuration28).drop 48 |>.take 8
theorem configuration28RootChunk6_checked : configuration28RootChunk6.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk7 : List Cell := (rootCells configuration28).drop 56 |>.take 8
theorem configuration28RootChunk7_checked : configuration28RootChunk7.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk8 : List Cell := (rootCells configuration28).drop 64 |>.take 8
theorem configuration28RootChunk8_checked : configuration28RootChunk8.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

def configuration28RootChunk9 : List Cell := (rootCells configuration28).drop 72 |>.take 8
theorem configuration28RootChunk9_checked : configuration28RootChunk9.all (fun a =>
    (neighborCells configuration28).all (cellPairFastB configuration28.sharedPath a)) = true := by decide

theorem placement28_checked : configurationCheckedB configuration28 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration28.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration28 = configuration28RootChunk0 ++ configuration28RootChunk1 ++ configuration28RootChunk2 ++ configuration28RootChunk3 ++ configuration28RootChunk4 ++ configuration28RootChunk5 ++ configuration28RootChunk6 ++ configuration28RootChunk7 ++ configuration28RootChunk8 ++ configuration28RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration28RootChunk0_checked,configuration28RootChunk1_checked,configuration28RootChunk2_checked,configuration28RootChunk3_checked,configuration28RootChunk4_checked,configuration28RootChunk5_checked,configuration28RootChunk6_checked,configuration28RootChunk7_checked,configuration28RootChunk8_checked,configuration28RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
