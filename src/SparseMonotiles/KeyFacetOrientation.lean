module

public import SparseMonotiles.KeySupportAtlas
public import SparseMonotiles.CandidateCompleteness

@[expose] public section

/-!
# Exact orientation certificates for a key on an exposed carrier facet

These finite integer equalities retain the physical bump/dent convention.
`Pose.boxKey` uses a coefficient reversal for contact comparison; that reversal
does not appear here. A bump apex has positive outward signed height and a dent
apex has negative outward signed height.
-/

namespace SparseMonotiles.Contact

def BoxKey.OrientedAt {d : ℕ} (den height : ℤ) (f : Facet d)
    (b : BoxKey d) : Prop :=
  b.radius f.axis = 0 ∧
  b.centre f.axis = den * f.gridFacet.anchor f.axis ∧
  f.normal * (b.apex f.axis - b.centre f.axis) =
    if b.bump then height else -height

instance {d : ℕ} (den height : ℤ) (f : Facet d) (b : BoxKey d) :
    Decidable (b.OrientedAt den height f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def IndexedGeometry.OrientedAt {d n : ℕ} (g : IndexedGeometry d n)
    (height : ℤ) (i : Fin n) : Prop :=
  ∀ b ∈ g.profile i, b.OrientedAt g.denominator height (g.facet i)

instance {d n : ℕ} (g : IndexedGeometry d n) (height : ℤ) (i : Fin n) :
    Decidable (g.OrientedAt height i) :=
  inferInstanceAs (Decidable (∀ b ∈ g.profile i, _))

/-- All elementary hypotheses needed for geometric key orientation and the
registered all-key-pair candidate-completeness theorem, in one finite row. -/
def IndexedGeometry.ProfileValidAt {d n : ℕ} (g : IndexedGeometry d n)
    (height : ℤ) (i : Fin n) : Prop :=
  (g.profile i).Nonempty ∧
  ∀ b ∈ g.profile i,
    b.OnFacet g.denominator (g.facet i) ∧ b.Asymmetric ∧
    b.OrientedAt g.denominator height (g.facet i)

instance {d n : ℕ} (g : IndexedGeometry d n) (height : ℤ) (i : Fin n) :
    Decidable (g.ProfileValidAt height i) :=
  inferInstanceAs (Decidable (_ ∧ ∀ b ∈ g.profile i, _))

end SparseMonotiles.Contact
