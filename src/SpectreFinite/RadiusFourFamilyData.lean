module

public import SpectreFinite.WindowRotationClosure
public import SpectreFinite.RadiusFourRoot0Data
public import SpectreFinite.RadiusFourRoot1Data
public import SpectreFinite.RadiusFourRoot2Data
public import SpectreFinite.RadiusFourRoot3Data
public import SpectreFinite.RadiusFourRoot4Data
public import SpectreFinite.RadiusFourRoot5Data
public import SpectreFinite.RadiusFourRoot6Data
public import SpectreFinite.RadiusFourRoot7Data
public import SpectreFinite.RadiusFourRoot8Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def familyForKind (k : TileKind) : List Patch :=
  match k.val with
  | 0 => root0Family
  | 1 => root1Family
  | 2 => root2Family
  | 3 => root3Family
  | 4 => root4Family
  | 5 => root5Family
  | 6 => root6Family
  | 7 => root7Family
  | _ => root8Family
def turnZeroFamily : List Patch := (List.finRange 9).flatMap familyForKind
theorem familyForKind_counts : (List.finRange 9).map (fun k => (familyForKind k).length) = [36, 33, 8, 3, 28, 30, 44, 80, 52] := by decide
theorem turnZeroFamily_count : turnZeroFamily.length = 314 := by decide
def allTurnFamily : List Patch := rotationClosure (hexRegion 4) familyForKind
theorem allTurnFamily_count : allTurnFamily.length = 1884 := by decide
end SpectreFinite.HexSearch.RadiusFour
