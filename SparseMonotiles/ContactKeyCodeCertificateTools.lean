module

public import SparseMonotiles.ContactKeyCodeInterface

@[expose] public section

namespace SparseMonotiles.Contact

instance {d : ℕ} (C : KeyCoordinateCode) (f : Facet d) (k : BoxKey d) :
    Decidable (C.RegularKey f k) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Finite checked hypotheses on every key in one indexed facet profile. -/
def IndexedGeometry.CodeValidAt {d n : ℕ} (g : IndexedGeometry d n)
    (C : KeyCoordinateCode) (i : Fin n) : Prop :=
  ∀ k ∈ g.profile i, C.Codes (g.facet i) k ∧ C.RegularKey (g.facet i) k

instance {d n : ℕ} (g : IndexedGeometry d n) (C : KeyCoordinateCode) (i : Fin n) :
    Decidable (g.CodeValidAt C i) := inferInstanceAs (Decidable (∀ k ∈ g.profile i, _))

end SparseMonotiles.Contact
