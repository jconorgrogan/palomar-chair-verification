module

public import SpectreFinite.RadiusFourPruningTree0D0
public import SpectreFinite.RadiusFourPruningTree0D1
public import SpectreFinite.RadiusFourPruningTree0D2
public import SpectreFinite.RadiusFourPruningTree0D3
public import SpectreFinite.RadiusFourPruningTree0D4
public import SpectreFinite.RadiusFourPruningTree0D5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def trees0 (d : Fin 6) : KeyTree :=
  match d.val with
  | 0 => tree0_0
  | 1 => tree0_1
  | 2 => tree0_2
  | 3 => tree0_3
  | 4 => tree0_4
  | _ => tree0_5

end SpectreFinite.HexSearch.RadiusFourPruning
