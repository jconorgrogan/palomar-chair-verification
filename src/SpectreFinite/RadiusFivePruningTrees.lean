module

public import SpectreFinite.RadiusFivePruningTree0D0
public import SpectreFinite.RadiusFivePruningTree0D1
public import SpectreFinite.RadiusFivePruningTree0D2
public import SpectreFinite.RadiusFivePruningTree0D3
public import SpectreFinite.RadiusFivePruningTree0D4
public import SpectreFinite.RadiusFivePruningTree0D5
public import SpectreFinite.RadiusFivePruningTree1D0
public import SpectreFinite.RadiusFivePruningTree1D1
public import SpectreFinite.RadiusFivePruningTree1D2
public import SpectreFinite.RadiusFivePruningTree1D3
public import SpectreFinite.RadiusFivePruningTree1D4
public import SpectreFinite.RadiusFivePruningTree1D5
public import SpectreFinite.RadiusFivePruningTree2D0
public import SpectreFinite.RadiusFivePruningTree2D1
public import SpectreFinite.RadiusFivePruningTree2D2
public import SpectreFinite.RadiusFivePruningTree2D3
public import SpectreFinite.RadiusFivePruningTree2D4
public import SpectreFinite.RadiusFivePruningTree2D5
public import SpectreFinite.RadiusFivePruningTree3D0
public import SpectreFinite.RadiusFivePruningTree3D1
public import SpectreFinite.RadiusFivePruningTree3D2
public import SpectreFinite.RadiusFivePruningTree3D3
public import SpectreFinite.RadiusFivePruningTree3D4
public import SpectreFinite.RadiusFivePruningTree3D5
public import SpectreFinite.RadiusFivePruningTree4D0
public import SpectreFinite.RadiusFivePruningTree4D1
public import SpectreFinite.RadiusFivePruningTree4D2
public import SpectreFinite.RadiusFivePruningTree4D3
public import SpectreFinite.RadiusFivePruningTree4D4
public import SpectreFinite.RadiusFivePruningTree4D5
public import SpectreFinite.RadiusFivePruningTree5D0
public import SpectreFinite.RadiusFivePruningTree5D1
public import SpectreFinite.RadiusFivePruningTree5D2
public import SpectreFinite.RadiusFivePruningTree5D3
public import SpectreFinite.RadiusFivePruningTree5D4
public import SpectreFinite.RadiusFivePruningTree5D5
public import SpectreFinite.RadiusFivePruningTree6D0
public import SpectreFinite.RadiusFivePruningTree6D1
public import SpectreFinite.RadiusFivePruningTree6D2
public import SpectreFinite.RadiusFivePruningTree6D3
public import SpectreFinite.RadiusFivePruningTree6D4
public import SpectreFinite.RadiusFivePruningTree6D5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
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
def trees3 (d : Fin 6) : KeyTree :=
  match d.val with
  | 0 => tree3_0
  | 1 => tree3_1
  | 2 => tree3_2
  | 3 => tree3_3
  | 4 => tree3_4
  | _ => tree3_5
def trees4 (d : Fin 6) : KeyTree :=
  match d.val with
  | 0 => tree4_0
  | 1 => tree4_1
  | 2 => tree4_2
  | 3 => tree4_3
  | 4 => tree4_4
  | _ => tree4_5
def trees5 (d : Fin 6) : KeyTree :=
  match d.val with
  | 0 => tree5_0
  | 1 => tree5_1
  | 2 => tree5_2
  | 3 => tree5_3
  | 4 => tree5_4
  | _ => tree5_5
def trees6 (d : Fin 6) : KeyTree :=
  match d.val with
  | 0 => tree6_0
  | 1 => tree6_1
  | 2 => tree6_2
  | 3 => tree6_3
  | 4 => tree6_4
  | _ => tree6_5

end SpectreFinite.HexSearch.RadiusFivePruning
