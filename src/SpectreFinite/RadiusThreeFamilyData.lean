module

public import SpectreFinite.WindowRotationClosure
public import SpectreFinite.RadiusThreeRoot0Data
public import SpectreFinite.RadiusThreeRoot1Data
public import SpectreFinite.RadiusThreeRoot2Data
public import SpectreFinite.RadiusThreeRoot3Data
public import SpectreFinite.RadiusThreeRoot4Data
public import SpectreFinite.RadiusThreeRoot5Data
public import SpectreFinite.RadiusThreeRoot6Data
public import SpectreFinite.RadiusThreeRoot7Data
public import SpectreFinite.RadiusThreeRoot8Data

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
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
theorem familyForKind_counts : (List.finRange 9).map (fun k => (familyForKind k).length) = [22, 26, 1, 2, 22, 25, 23, 48, 38] := by decide
theorem turnZeroFamily_count : turnZeroFamily.length = 207 := by decide
def allTurnFamily : List Patch := rotationClosure (hexRegion 3) familyForKind
theorem allTurnFamily_count : allTurnFamily.length = 1242 := by decide
end SpectreFinite.HexSearch.RadiusThree
