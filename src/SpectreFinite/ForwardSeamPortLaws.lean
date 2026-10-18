module

public import SpectreFinite.ForwardSeamPortKind0
public import SpectreFinite.ForwardSeamPortKind1
public import SpectreFinite.ForwardSeamPortKind2
public import SpectreFinite.ForwardSeamPortKind3
public import SpectreFinite.ForwardSeamPortKind4
public import SpectreFinite.ForwardSeamPortKind5
public import SpectreFinite.ForwardSeamPortKind6
public import SpectreFinite.ForwardSeamPortKind7
public import SpectreFinite.ForwardSeamPortKind8

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution
theorem all_seam_port_laws : ∀ k : TileKind, KindSeamPortLaws k :=
  Fin.cases seam_port_laws_0 (Fin.cases seam_port_laws_1 (Fin.cases seam_port_laws_2 (Fin.cases seam_port_laws_3 (Fin.cases seam_port_laws_4 (Fin.cases seam_port_laws_5 (Fin.cases seam_port_laws_6 (Fin.cases seam_port_laws_7 (Fin.cases seam_port_laws_8 ((fun i => Fin.elim0 i))))))))))
end SpectreFinite.HexSearch.ForwardSubstitution
