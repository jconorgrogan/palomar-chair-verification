module

public import SpectreFinite.WindowTableCoverage
public import SpectreFinite.RadiusThreePruningLiteral

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def positions (v : Fin 61) : Position :=
  match v.val with
  | 0 => (-4,0)
  | 1 => (-4,1)
  | 2 => (-4,2)
  | 3 => (-4,3)
  | 4 => (-4,4)
  | 5 => (-3,-1)
  | 6 => (-3,0)
  | 7 => (-3,1)
  | 8 => (-3,2)
  | 9 => (-3,3)
  | 10 => (-3,4)
  | 11 => (-2,-2)
  | 12 => (-2,-1)
  | 13 => (-2,0)
  | 14 => (-2,1)
  | 15 => (-2,2)
  | 16 => (-2,3)
  | 17 => (-2,4)
  | 18 => (-1,-3)
  | 19 => (-1,-2)
  | 20 => (-1,-1)
  | 21 => (-1,0)
  | 22 => (-1,1)
  | 23 => (-1,2)
  | 24 => (-1,3)
  | 25 => (-1,4)
  | 26 => (0,-4)
  | 27 => (0,-3)
  | 28 => (0,-2)
  | 29 => (0,-1)
  | 30 => (0,0)
  | 31 => (0,1)
  | 32 => (0,2)
  | 33 => (0,3)
  | 34 => (0,4)
  | 35 => (1,-4)
  | 36 => (1,-3)
  | 37 => (1,-2)
  | 38 => (1,-1)
  | 39 => (1,0)
  | 40 => (1,1)
  | 41 => (1,2)
  | 42 => (1,3)
  | 43 => (2,-4)
  | 44 => (2,-3)
  | 45 => (2,-2)
  | 46 => (2,-1)
  | 47 => (2,0)
  | 48 => (2,1)
  | 49 => (2,2)
  | 50 => (3,-4)
  | 51 => (3,-3)
  | 52 => (3,-2)
  | 53 => (3,-1)
  | 54 => (3,0)
  | 55 => (3,1)
  | 56 => (4,-4)
  | 57 => (4,-3)
  | 58 => (4,-2)
  | 59 => (4,-1)
  | _ => (4,0)
theorem positions_eq_hexRegion : (List.finRange 61).map positions = hexRegion 4 := by decide
def constraints : List (Constraint 61 State) :=
  windowConstraints positions (hexRegion 3) RadiusThreePruning.certifiedFamily (hexRegion 4)
def domains (root : State) : Domains 61 State := rootDomains positions root
theorem covers_of_branches (D : Domains 61 State) (outs : List (List State))
    (v : Fin 61) (h : ∀ s ∈ D v, Covers (restrict D v s) constraints outs) :
    Covers D constraints outs := by
  intro f hf
  exact h (f v) (hf.1 v) f ⟨fits_restrict D f hf.1 v, hf.2⟩
end SpectreFinite.HexSearch.RadiusFour
