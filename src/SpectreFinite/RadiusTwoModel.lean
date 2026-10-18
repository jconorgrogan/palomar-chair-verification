module

public import SpectreFinite.WindowTableCoverage
public import SpectreFinite.RadiusOnePruningCertified

@[expose] public section


/-! Concrete nineteen-cell axial radius-two CSP. -/
namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def positions (v : Fin 19) : Position :=
  match v.val with
  | 0 => (-2,0)
  | 1 => (-2,1)
  | 2 => (-2,2)
  | 3 => (-1,-1)
  | 4 => (-1,0)
  | 5 => (-1,1)
  | 6 => (-1,2)
  | 7 => (0,-2)
  | 8 => (0,-1)
  | 9 => (0,0)
  | 10 => (0,1)
  | 11 => (0,2)
  | 12 => (1,-2)
  | 13 => (1,-1)
  | 14 => (1,0)
  | 15 => (1,1)
  | 16 => (2,-2)
  | 17 => (2,-1)
  | _ => (2, 0)
theorem positions_eq_hexRegion : (List.finRange 19).map positions = hexRegion 2 := by decide
def constraints : List (Constraint 19 State) :=
  windowConstraints positions RadiusOne.positions SignaturePruning.certifiedFamily (hexRegion 2)
def domains (root : State) : Domains 19 State := rootDomains positions root
end SpectreFinite.HexSearch.RadiusTwo
