module

public import SparseMonotiles.CompactStatement
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section
namespace PalomarMonotiles

/-- All Euclidean isometries preserving the physical tile collection, with
no prescribed centre, orientation, lattice, or registered-frame restriction. -/
def IsEuclideanSymmetry {d : ℕ} (tiles : Set (Set (Point d)))
    (f : Point d ≃ᵢ Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ f '' A ∈ tiles

/-- The full symmetry type, including arbitrary rotations, reflections and translations. -/
def EuclideanSymmetries {d : ℕ} (tiles : Set (Set (Point d))) :=
  {f : Point d ≃ᵢ Point d // IsEuclideanSymmetry tiles f}

/-- Retain the original compactness/existence/no-period claim and add a uniform
finite bound for the full Euclidean symmetry group of every physical tiling.
The bound is 2^5 * 5! = 3840; trivial symmetry is not asserted. -/
def T5StrongClaim : Prop :=
  T5Claim ∧ ∀ tiles : Set (Set (Point 5)), IsTiling T5 tiles →
    Finite (EuclideanSymmetries tiles) ∧ Nat.card (EuclideanSymmetries tiles) ≤ 3840

end PalomarMonotiles
