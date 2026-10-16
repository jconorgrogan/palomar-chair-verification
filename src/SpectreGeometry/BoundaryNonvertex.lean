module

public import SpectreGeometry.EdgeNeighborhood

@[expose] public section


/-! Direct integration lemmas for contacts away from the finite vertex set. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem frontier_nonvertex_strict_edge (x : RealPoint) (hx : x ∈ frontier polygonBody)
    (hv : ∀ i : Fin 14, x ≠ realVertex i) :
    ∃ (i : Fin 14) (t : ℝ), 0 < t ∧ t < 1 ∧
      x = interpolate (realVertex i) (realVertex (next i)) t := by
  rw [polygonBody_frontier_eq_edges] at hx
  obtain ⟨i,t,ht,ht',he⟩ := mem_iUnion.1 hx
  have h0 : t ≠ 0 := by
    intro hz
    exact hv i (by simpa [hz] using he)
  have h1 : t ≠ 1 := by
    intro hz
    exact hv (next i) (by simpa [hz] using he)
  exact ⟨i,t,lt_of_le_of_ne ht (Ne.symm h0),lt_of_le_of_ne ht' h1,he⟩

theorem frontier_nonvertex_local_halfplane (x : RealPoint) (hx : x ∈ frontier polygonBody)
    (hv : ∀ i : Fin 14, x ≠ realVertex i) :
    ∃ (i : Fin 14) (U : Set RealPoint), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, (y ∈ polygonBody ↔ 0 ≤ side (realVertex i) (realVertex (next i)) y) ∧
        (y ∈ interior polygonBody ↔ 0 < side (realVertex i) (realVertex (next i)) y) ∧
        (y ∈ frontier polygonBody ↔ side (realVertex i) (realVertex (next i)) y = 0)) := by
  obtain ⟨i,t,ht,ht',he⟩ := frontier_nonvertex_strict_edge x hx hv
  obtain ⟨U,ho,hu,hh⟩ := outer_open_edge_local_halfplane i t ht ht'
  exact ⟨i,U,ho,he ▸ hu,hh⟩

end
end SpectreGeometry
