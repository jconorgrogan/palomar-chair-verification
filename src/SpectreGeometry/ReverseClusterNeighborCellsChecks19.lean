module

public import SpectreGeometry.ReverseClusterNeighborCellsData
public import SpectreGeometry.ReverseClusterNeighborCellsFast

@[expose] public section

namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def configuration19RootChunk0 : List Cell := (rootCells configuration19).drop 0 |>.take 8
theorem configuration19RootChunk0_checked : configuration19RootChunk0.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk1 : List Cell := (rootCells configuration19).drop 8 |>.take 8
theorem configuration19RootChunk1_checked : configuration19RootChunk1.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk2 : List Cell := (rootCells configuration19).drop 16 |>.take 8
theorem configuration19RootChunk2_checked : configuration19RootChunk2.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk3 : List Cell := (rootCells configuration19).drop 24 |>.take 8
theorem configuration19RootChunk3_checked : configuration19RootChunk3.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk4 : List Cell := (rootCells configuration19).drop 32 |>.take 8
theorem configuration19RootChunk4_checked : configuration19RootChunk4.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk5 : List Cell := (rootCells configuration19).drop 40 |>.take 8
theorem configuration19RootChunk5_checked : configuration19RootChunk5.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk6 : List Cell := (rootCells configuration19).drop 48 |>.take 8
theorem configuration19RootChunk6_checked : configuration19RootChunk6.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk7 : List Cell := (rootCells configuration19).drop 56 |>.take 8
theorem configuration19RootChunk7_checked : configuration19RootChunk7.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk8 : List Cell := (rootCells configuration19).drop 64 |>.take 8
theorem configuration19RootChunk8_checked : configuration19RootChunk8.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

def configuration19RootChunk9 : List Cell := (rootCells configuration19).drop 72 |>.take 8
theorem configuration19RootChunk9_checked : configuration19RootChunk9.all (fun a =>
    (neighborCells configuration19).all (cellPairFastB configuration19.sharedPath a)) = true := by decide

theorem placement19_checked : configurationCheckedB configuration19 = true := by
  apply configurationFastB_sound
  have hp : decide (pathEdges configuration19.sharedPath ≠ []) = true := by decide
  have hr : rootCells configuration19 = configuration19RootChunk0 ++ configuration19RootChunk1 ++ configuration19RootChunk2 ++ configuration19RootChunk3 ++ configuration19RootChunk4 ++ configuration19RootChunk5 ++ configuration19RootChunk6 ++ configuration19RootChunk7 ++ configuration19RootChunk8 ++ configuration19RootChunk9 := by decide
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hp,?_⟩
  rw [hr]
  simp only [List.all_append,configuration19RootChunk0_checked,configuration19RootChunk1_checked,configuration19RootChunk2_checked,configuration19RootChunk3_checked,configuration19RootChunk4_checked,configuration19RootChunk5_checked,configuration19RootChunk6_checked,configuration19RootChunk7_checked,configuration19RootChunk8_checked,configuration19RootChunk9_checked,Bool.and_self]
end SpectreGeometry.ReverseClusterNeighborCells
