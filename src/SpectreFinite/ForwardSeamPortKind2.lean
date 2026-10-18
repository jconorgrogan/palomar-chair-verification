module

public import SpectreFinite.ForwardSeamPortDefinitions

@[expose] public section

namespace SpectreFinite.HexSearch.ForwardSubstitution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem seam_port_laws_2 : KindSeamPortLaws 2 := by
  unfold KindSeamPortLaws
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i))))))))))
end SpectreFinite.HexSearch.ForwardSubstitution
