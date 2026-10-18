module

public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section


/-! A generic obstruction to mixed chirality once the two closed color unions
have only countably many common points. The physical tiling must derive these
premises from its literal bodies, local finiteness and algebraic contacts.
-/
namespace LiteralPlanar
noncomputable section
open Set

/-- The plane-minus-contacts mechanism does not assume edge-graph connectivity
and permits isolated contacts between tiles. -/
theorem no_closed_color_separation {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E]
    (hdim : 1 < Module.rank ℝ E) (A B : Set E)
    (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ)
    (hcontact : (A ∩ B).Countable)
    (hleft : (A \ B).Nonempty) (hright : (B \ A).Nonempty) : False := by
  have hc := (hcontact.isConnected_compl_of_one_lt_rank hdim).isPreconnected
  have hsub : (A ∩ B)ᶜ ⊆ A ∪ B := by rw [hcover]; exact subset_univ _
  obtain ⟨x, hxA, hxB⟩ := hleft
  obtain ⟨y, hyB, hyA⟩ := hright
  have hx : x ∈ (A ∩ B)ᶜ := fun h => hxB h.2
  have hy : y ∈ (A ∩ B)ᶜ := fun h => hyA h.1
  obtain ⟨z, hz, hzAB⟩ := (isPreconnected_closed_iff.mp hc) A B hA hB hsub
    ⟨x, hx, hxA⟩ ⟨y, hy, hyB⟩
  exact hz hzAB

end
end LiteralPlanar
