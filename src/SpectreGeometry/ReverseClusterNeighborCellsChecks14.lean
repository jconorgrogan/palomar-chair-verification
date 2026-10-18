module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration14RootChunk0 : List Cell := (rootCells configuration14).drop 0 |>.take 8
theorem configuration14RootChunk0_checked : configuration14RootChunk0.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk1 : List Cell := (rootCells configuration14).drop 8 |>.take 8
theorem configuration14RootChunk1_checked : configuration14RootChunk1.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk2 : List Cell := (rootCells configuration14).drop 16 |>.take 8
theorem configuration14RootChunk2_checked : configuration14RootChunk2.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk3 : List Cell := (rootCells configuration14).drop 24 |>.take 8
theorem configuration14RootChunk3_checked : configuration14RootChunk3.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk4 : List Cell := (rootCells configuration14).drop 32 |>.take 8
theorem configuration14RootChunk4_checked : configuration14RootChunk4.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk5 : List Cell := (rootCells configuration14).drop 40 |>.take 8
theorem configuration14RootChunk5_checked : configuration14RootChunk5.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk6 : List Cell := (rootCells configuration14).drop 48 |>.take 8
theorem configuration14RootChunk6_checked : configuration14RootChunk6.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk7 : List Cell := (rootCells configuration14).drop 56 |>.take 8
theorem configuration14RootChunk7_checked : configuration14RootChunk7.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk8 : List Cell := (rootCells configuration14).drop 64 |>.take 8
theorem configuration14RootChunk8_checked : configuration14RootChunk8.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

def configuration14RootChunk9 : List Cell := (rootCells configuration14).drop 72 |>.take 8
theorem configuration14RootChunk9_checked : configuration14RootChunk9.all (fun a =>
    (neighborCells configuration14).all (cellPairFastB configuration14.sharedPath a)) = true := by decide

theorem placement14_checked : configurationCheckedB configuration14 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration14.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration14 = configuration14RootChunk0 ++ configuration14RootChunk1 ++ configuration14RootChunk2 ++ configuration14RootChunk3 ++ configuration14RootChunk4 ++ configuration14RootChunk5 ++ configuration14RootChunk6 ++ configuration14RootChunk7 ++ configuration14RootChunk8 ++ configuration14RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration14RootChunk0_checked,configuration14RootChunk1_checked,configuration14RootChunk2_checked,configuration14RootChunk3_checked,configuration14RootChunk4_checked,configuration14RootChunk5_checked,configuration14RootChunk6_checked,configuration14RootChunk7_checked,configuration14RootChunk8_checked,configuration14RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
