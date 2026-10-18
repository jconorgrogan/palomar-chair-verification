module

public import SpectreFinite.AxialTranslationWords
public import SpectreFinite.FiniteTranslation
public import SpectreFinite.AreaBoundaryGrowth

@[expose] public section


/-! Quantitative period obstruction for actual finite block sequences.
The construction of iterated parent blocks, the boundary bounds at every
level, and the intersection/equality property remain explicit hypotheses.
This is not a theorem that the marked-hexagon hierarchy already exists. -/
namespace SpectreFinite.HexSearch
open FiniteBoundaryEstimate

theorem translation_eq_zero_of_block_bounds
    (blocks boundary : Nat → List Position) (C : Nat) (v : Position)
    (hn : ∀ n, (blocks n).Nodup)
    (ha : ∀ n, 7^n ≤ (blocks n).length)
    (hb : ∀ n, (boundary n).length ≤ C*6^n)
    (he : ∀ n, ∀ s ∈ primitiveSteps, escape (blocks n) s ⊆ boundary n)
    (hi : ∀ n, (∃ x ∈ blocks n, addPos x v ∈ blocks n) →
      ∀ y, y ∈ blocks n ↔ addPos y v ∈ blocks n) : v = (0,0) := by
  apply Classical.byContradiction
  intro hv
  have hne : ∀ n, blocks n ≠ [] := by
    intro n hz
    have hh := ha n
    have hp : 0 < 7^n := Nat.pow_pos (by decide)
    rw [hz] at hh
    simp only [List.length_nil] at hh
    omega
  have hd : ∀ n, ∀ x ∈ blocks n, addPos x v ∉ blocks n := by
    intro n x hx hin
    apply hv
    exact FiniteTranslation.translation_eq_zero (blocks n) (hn n) (hne n) v
      (hi n ⟨x,hx,hin⟩)
  have hc : ∀ n, (blocks n).length ≤ (v.1.natAbs+v.2.natAbs)*(boundary n).length := by
    intro n
    exact cardinal_le_axial_boundary (blocks n) (boundary n) (hn n) v (he n) (hd n)
  exact AreaBoundaryGrowth.no_uniform_area_boundary_bound
    (fun n => (blocks n).length) (fun n => (boundary n).length)
    C (v.1.natAbs+v.2.natAbs) ha hb hc

end SpectreFinite.HexSearch
