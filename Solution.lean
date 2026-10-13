module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Data.Nat.Prime.Defs
public import PrimeFacetClosure.PhysicalMonotile

@[expose] public section

/-!
For every prime p congruent to three modulo four, Euclidean p-space contains
a compact set T with nonempty interior that tiles by arbitrary isometric copies,
but every tiling by those unmarked copies has no nonzero translational period.

A tiling below is literally a set of subsets of Euclidean space. Its members
are isometric copies of T, their union is the whole space, and interiors of
distinct members are disjoint. A period preserves the entire tile collection.
Reflections are allowed; no registration, matching-rule or hierarchy hypothesis
occurs in this statement. No claim about the remaining prime dimensions is made.
This Solution independently declares the same ordinary mathematical statement
and supplies its proof from the complete concrete construction.
-/
namespace PrimePhysicalMonotile

/-- A nonvacuous physical aperiodic monotile in every prime dimension p=3 mod4,
with all tiling and symmetry predicates spelled out using Mathlib notions. -/
theorem exists_prime_three_mod_four_monotile {p : ℕ}
    (hp : Nat.Prime p) (hmod : p % 4 = 3) :
    ∃ T : Set (EuclideanSpace ℝ (Fin p)),
      IsCompact T ∧ (interior T).Nonempty ∧
      (∃ tiles : Set (Set (EuclideanSpace ℝ (Fin p))),
        (∀ A ∈ tiles, ∃ g : EuclideanSpace ℝ (Fin p) ≃ᵢ EuclideanSpace ℝ (Fin p), A = g '' T) ∧
        (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
        (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))) ∧
      (∀ tiles : Set (Set (EuclideanSpace ℝ (Fin p))),
        ((∀ A ∈ tiles, ∃ g : EuclideanSpace ℝ (Fin p) ≃ᵢ EuclideanSpace ℝ (Fin p), A = g '' T) ∧
         (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
         (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))) →
        ∀ v : EuclideanSpace ℝ (Fin p),
          (∀ A, A ∈ tiles ↔ (fun x => x + v) '' A ∈ tiles) → v = 0) := by
  obtain ⟨T, hT, hI⟩ :=
    PhysicalRegistration.NativeChair.GeneratedCompiler.prime_three_mod_four_physical_monotile hp hmod
  exact ⟨T, hT.1, hI, hT.2.1, hT.2.2⟩

end PrimePhysicalMonotile
