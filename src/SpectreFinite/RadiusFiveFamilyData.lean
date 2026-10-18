module

public import SpectreFinite.WindowRotationClosure
public import SpectreFinite.RadiusFiveRoot0Data
public import SpectreFinite.RadiusFiveRoot1Data
public import SpectreFinite.RadiusFiveRoot2Data
public import SpectreFinite.RadiusFiveRoot3Data
public import SpectreFinite.RadiusFiveRoot4Data
public import SpectreFinite.RadiusFiveRoot5Data
public import SpectreFinite.RadiusFiveRoot6Data
public import SpectreFinite.RadiusFiveRoot7Data
public import SpectreFinite.RadiusFiveRoot8Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
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
theorem familyForKind_counts : (List.finRange 9).map (fun k => (familyForKind k).length) = [60, 59, 6, 7, 47, 36, 63, 106, 70] := by decide
theorem turnZeroFamily_count : turnZeroFamily.length = 454 := by decide
def allTurnFamily : List Patch := rotationClosure (hexRegion 5) familyForKind
theorem allTurnFamily_count : allTurnFamily.length = 2724 := by decide
end SpectreFinite.HexSearch.RadiusFive
