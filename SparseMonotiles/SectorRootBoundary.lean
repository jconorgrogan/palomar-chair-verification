module

public import SparseMonotiles.PhysicalSectorBoundary
public import SparseMonotiles.SectorArithmetic

@[expose] public section

/-! # A genuine proper sector is a boundary model at its vertex -/
namespace SparseMonotiles
open Set

namespace SectorAngleSum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive-angle sectors contain their vertex. -/
theorem HasSectorAngle.zero_mem {S : Set E} {θ : ℝ}
    (h : HasSectorAngle S θ) (hθ : 0 < θ) : (0 : E) ∈ S := by
  cases h with
  | empty _ => exact (lt_irrefl _ hθ).elim
  | full hS => simp [hS]
  | halfplane n _ hS => simp [hS,normalHalfspace]
  | convex n m _ _ _ hS => simp [hS,normalHalfspace]
  | reflex n m _ _ _ hS => simp [hS,normalHalfspace]

/-- The full plane has angle 2π, as a consequence of the genuine geometric
angle-sum theorem applied to a one-member partition. -/
theorem HasSectorAngle.ne_univ_of_lt_two_pi [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {S : Set E} {θ : ℝ}
    (h : HasSectorAngle S θ) (hθ : θ < 2*Real.pi) : S ≠ univ := by
  intro heq
  have hs := rank_two_geometric_sector_partition_sum hdim (fun _ : Fin 1 => S)
    (fun _ => θ) (fun _ => h)
    (fun v => ⟨0, heq.symm ▸ Set.mem_univ v⟩)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
  have hsum : θ = 2*Real.pi := by simpa using hs
  exact (ne_of_lt hθ) hsum

/-- A proper positive-angle sector has its vertex on its genuine frontier. -/
theorem HasSectorAngle.zero_mem_frontier [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {S : Set E} {θ : ℝ}
    (h : HasSectorAngle S θ) (hθ : 0 < θ) (hθ' : θ < 2*Real.pi) :
    (0 : E) ∈ frontier S := by
  refine ⟨subset_closure (h.zero_mem hθ), ?_⟩
  intro hi
  have hlocal : LocalSetEq (0 : E) S univ := by
    apply Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hi)
    intro x hx
    exact iff_true_intro hx
  have hu : IsPositiveCone (univ : Set E) := by intro t ht v; simp
  exact h.ne_univ_of_lt_two_pi hdim hθ' (h.positive.eq_of_localSetEq hu hlocal)

end SectorAngleSum

/-- The actual allowed angle inventory is strictly between zero and a full turn. -/
theorem angleInventory_pos_lt_two_pi {θ : ℝ} (h : SectorArithmetic.InAngleInventory θ) :
    0 < θ ∧ θ < 2*Real.pi := by
  have hp := Real.pi_pos
  rcases h with h | h | h | ⟨δ,hδ,hδ',h | h⟩ <;> constructor <;> linarith

/-- A proved physical normal-sector germ gives boundary status itself. -/
theorem mem_frontier_of_normal_sector {d : ℕ}
    (R : AffineSubspace ℝ (Point d)) (p : Point d)
    (hdim : Module.finrank ℝ R.directionᗮ = 2)
    {A : Set (Point d)} {S : Set R.directionᗮ} {θ : ℝ}
    (hshape : SectorAngleSum.HasSectorAngle S θ)
    (hθ : 0 < θ) (hθ' : θ < 2*Real.pi)
    (hmodel : LocalSetEq p A (ridgeNormalProjection R p ⁻¹' S)) : p ∈ frontier A := by
  apply hmodel.frontier.mem_iff.mpr
  have heq := (isOpenMap_ridgeNormalProjection R p).preimage_frontier_eq_frontier_preimage
    (continuous_ridgeNormalProjection R p) S
  rw [← heq]
  have hz := hshape.zero_mem_frontier hdim hθ hθ'
  simpa [ridgeNormalProjection] using hz

#print axioms SectorAngleSum.HasSectorAngle.zero_mem_frontier
#print axioms mem_frontier_of_normal_sector
end SparseMonotiles
