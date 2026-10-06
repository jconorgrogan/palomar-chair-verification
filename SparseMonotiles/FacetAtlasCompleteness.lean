module

public import SparseMonotiles.ContactChairChecker

@[expose] public section

/-! Completeness of an exposed-facet atlas follows from a finite check on every
binary carrier cell, every axis, and both signs. The atlas itself need not be
trusted or inferred complete from ownership, exposure, or injectivity. -/
namespace SparseMonotiles.Contact

def binaryFacet {d : ℕ} (b : Fin d → Bool) (j : Fin d) (positive : Bool) : Facet d :=
  ⟨binaryCell b, j, positive⟩

def FacetLookupCompleteAt {d n : ℕ} (g : IndexedGeometry d n)
    (lookup : Facet d → Fin n) (b : Fin d → Bool) (j : Fin d) (positive : Bool) : Prop :=
  IsChairCell (binaryCell b) → ¬ IsChairCell (binaryFacet b j positive).neighbor →
    g.facet (lookup (binaryFacet b j positive)) = binaryFacet b j positive

instance {d n : ℕ} (g : IndexedGeometry d n) (lookup : Facet d → Fin n)
    (b : Fin d → Bool) (j : Fin d) (positive : Bool) :
    Decidable (FacetLookupCompleteAt g lookup b j positive) :=
  inferInstanceAs (Decidable (_ → _ → _))

theorem IndexedGeometry.facet_complete_of_binary_lookup {d n : ℕ}
    (g : IndexedGeometry d n) (lookup : Facet d → Fin n)
    (checked : ∀ b j positive, FacetLookupCompleteAt g lookup b j positive)
    (f : Facet d) (owned : IsChairCell f.cell) (exposed : ¬ IsChairCell f.neighbor) :
    ∃ i, g.facet i = f := by
  let b : Fin d → Bool := fun i => decide (f.cell i = 1)
  have hb : binaryCell b = f.cell := by
    funext i
    rcases owned.1 i with hi | hi <;> simp [binaryCell, b, hi]
  have hf : binaryFacet b f.axis f.positive = f := by
    cases f
    simpa only [binaryFacet, Facet.mk.injEq, and_true] using hb
  have h := checked b f.axis f.positive
  unfold FacetLookupCompleteAt at h
  rw [hb, hf] at h
  exact ⟨lookup f, h owned exposed⟩

#print axioms IndexedGeometry.facet_complete_of_binary_lookup
end SparseMonotiles.Contact
