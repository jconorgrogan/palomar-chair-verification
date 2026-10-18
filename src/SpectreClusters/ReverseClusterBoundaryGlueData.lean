module

public import SpectreClusters.ReverseClusterCocycleData

@[expose] public section

namespace SpectreClusters.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch

/-- The actual ordered vertices of a state side, in its placed orientation. -/
def statePath (a : State) (d : Fin 6) : List Point :=
  (((markedPaths a.1).getD (sideTurn a.2 d).val [])).map (rotate a.2)

def BoundaryGlueCertificate (k : Fin 9) : Prop :=
  ∀ (r : Fin 6) (j : Fin 9) (t : Fin 6) (d : Fin 6), sideMatch (k,r) (j,t) d →
    statePath (k,r) d = ((statePath (j,t) (opposite d)).reverse).map
      (fun p => add (vertexDelta (k,r) (j,t) d) p)
end SpectreClusters.ReverseExistence
