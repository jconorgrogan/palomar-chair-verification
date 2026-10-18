module

public import SpectreFinite.WindowTableCoverage
public import SpectreFinite.RadiusTwoPruningLiteral

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def positions (v : Fin 37) : Position :=
  match v.val with
  | 0 => (-3,0)
  | 1 => (-3,1)
  | 2 => (-3,2)
  | 3 => (-3,3)
  | 4 => (-2,-1)
  | 5 => (-2,0)
  | 6 => (-2,1)
  | 7 => (-2,2)
  | 8 => (-2,3)
  | 9 => (-1,-2)
  | 10 => (-1,-1)
  | 11 => (-1,0)
  | 12 => (-1,1)
  | 13 => (-1,2)
  | 14 => (-1,3)
  | 15 => (0,-3)
  | 16 => (0,-2)
  | 17 => (0,-1)
  | 18 => (0,0)
  | 19 => (0,1)
  | 20 => (0,2)
  | 21 => (0,3)
  | 22 => (1,-3)
  | 23 => (1,-2)
  | 24 => (1,-1)
  | 25 => (1,0)
  | 26 => (1,1)
  | 27 => (1,2)
  | 28 => (2,-3)
  | 29 => (2,-2)
  | 30 => (2,-1)
  | 31 => (2,0)
  | 32 => (2,1)
  | 33 => (3,-3)
  | 34 => (3,-2)
  | 35 => (3,-1)
  | _ => (3,0)
theorem positions_eq_hexRegion : (List.finRange 37).map positions = hexRegion 3 := by decide
def constraints : List (Constraint 37 State) :=
  windowConstraints positions (hexRegion 2) RadiusTwoPruning.certifiedFamily (hexRegion 3)
def domains (root : State) : Domains 37 State := rootDomains positions root
theorem covers_of_branches (D : Domains 37 State) (outs : List (List State))
    (v : Fin 37) (h : ∀ s ∈ D v, Covers (restrict D v s) constraints outs) :
    Covers D constraints outs := by
  intro f hf
  exact h (f v) (hf.1 v) f ⟨fits_restrict D f hf.1 v, hf.2⟩
end SpectreFinite.HexSearch.RadiusThree
