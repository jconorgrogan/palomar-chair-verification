module

public import SpectreFinite.RadiusTwoPruningTree0D0
public import SpectreFinite.RadiusTwoPruningTree0D1
public import SpectreFinite.RadiusTwoPruningTree0D2
public import SpectreFinite.RadiusTwoPruningTree0D3
public import SpectreFinite.RadiusTwoPruningTree0D4
public import SpectreFinite.RadiusTwoPruningTree0D5
public import SpectreFinite.RadiusTwoPruningTree1D0
public import SpectreFinite.RadiusTwoPruningTree1D1
public import SpectreFinite.RadiusTwoPruningTree1D2
public import SpectreFinite.RadiusTwoPruningTree1D3
public import SpectreFinite.RadiusTwoPruningTree1D4
public import SpectreFinite.RadiusTwoPruningTree1D5
public import SpectreFinite.RadiusTwoPruningTree2D0
public import SpectreFinite.RadiusTwoPruningTree2D1
public import SpectreFinite.RadiusTwoPruningTree2D2
public import SpectreFinite.RadiusTwoPruningTree2D3
public import SpectreFinite.RadiusTwoPruningTree2D4
public import SpectreFinite.RadiusTwoPruningTree2D5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwoPruning
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

def trees1 (d : Fin 6) : KeyTree :=
  match d.val with
  | 0 => tree1_0
  | 1 => tree1_1
  | 2 => tree1_2
  | 3 => tree1_3
  | 4 => tree1_4
  | _ => tree1_5

def trees2 (d : Fin 6) : KeyTree :=
  match d.val with
  | 0 => tree2_0
  | 1 => tree2_1
  | 2 => tree2_2
  | 3 => tree2_3
  | 4 => tree2_4
  | _ => tree2_5

end SpectreFinite.HexSearch.RadiusTwoPruning
