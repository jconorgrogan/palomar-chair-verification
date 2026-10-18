module

public import SpectreFinite.BoundaryWords

@[expose] public section


/-! Quantitative finite bounds for the exact author supertiles. These are the
local factors for a future iterated area/boundary argument; no hierarchy is
assumed to exist or claimed to have been constructed by these inequalities. -/
namespace SpectreFinite.Boundary

theorem segment_length_bounds : ∀ (k : TileKind) (s : Fin 6),
    1 ≤ (segment k s).length ∧ (segment k s).length ≤ 6 := by decide

theorem supertile_area_bounds (k : TileKind) :
    7 ≤ (children k).length ∧ (children k).length ≤ 8 := by
  rw [nineListedSupertiles_size]
  split <;> decide

theorem boundary_growth_strictly_smaller (k : TileKind) (s : Fin 6) :
    (segment k s).length < (children k).length := by
  have ha := supertile_area_bounds k
  have hb := segment_length_bounds k s
  omega

end SpectreFinite.Boundary
