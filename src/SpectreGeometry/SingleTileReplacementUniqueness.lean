module

public import Mathlib.Topology.Closure

@[expose] public section


namespace SpectreGeometry
open Set

/-- In an interior packing, a regular-closed neighboring carrier cannot meet
the interior of another tile, even at one of its boundary points. -/
theorem interior_disjoint_regular_carrier {X : Type*} [TopologicalSpace X]
    (A B : Set X) (hreg : B ⊆ closure (interior B))
    (hd : Disjoint (interior A) (interior B)) : Disjoint (interior A) B :=
  (hd.closure_right isOpen_interior).mono_right hreg

theorem single_replacement_subset {X I : Type*} [TopologicalSpace X]
    (A B : I → Set X) (root : I)
    (hreg : ∀ i, A i ⊆ closure (interior (A i)))
    (hclosed : IsClosed (B root))
    (hpack : Pairwise fun i j => Disjoint (interior (A i)) (interior (A j)))
    (hcover : ∀ x, ∃ i, x ∈ B i)
    (hsame : ∀ i, i ≠ root → B i = A i) : A root ⊆ B root := by
  have hi : interior (A root) ⊆ B root := by
    intro x hx
    obtain ⟨i,hi⟩ := hcover x
    by_cases he : i = root
    · simpa only [he] using hi
    · rw [hsame i he] at hi
      exact False.elim (Set.disjoint_left.mp
        (interior_disjoint_regular_carrier (A root) (A i) (hreg i)
          (hpack (Ne.symm he))) hx hi)
  exact (hreg root).trans (closure_minimal hi hclosed)

/-- Two regular-closed tilings that agree at every other index must have the
same remaining carrier. No local finiteness or pose rigidity is assumed. -/
theorem single_tile_replacement_unique {X I : Type*} [TopologicalSpace X]
    (A B : I → Set X) (root : I)
    (hAr : ∀ i, A i ⊆ closure (interior (A i)))
    (hBr : ∀ i, B i ⊆ closure (interior (B i)))
    (hAc : IsClosed (A root)) (hBc : IsClosed (B root))
    (hAp : Pairwise fun i j => Disjoint (interior (A i)) (interior (A j)))
    (hBp : Pairwise fun i j => Disjoint (interior (B i)) (interior (B j)))
    (hAv : ∀ x, ∃ i, x ∈ A i) (hBv : ∀ x, ∃ i, x ∈ B i)
    (hsame : ∀ i, i ≠ root → B i = A i) : A root = B root :=
  Set.Subset.antisymm (single_replacement_subset A B root hAr hBc hAp hBv hsame)
    (single_replacement_subset B A root hBr hAc hBp hAv (fun i hi => (hsame i hi).symm))

end SpectreGeometry
