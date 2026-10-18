module

public import Mathlib.Topology.Connected.Basic

@[expose] public section


namespace SpectreGeometry
open Set

/-- A closed set with nonempty interior fills the space if a dense connected
set avoids its frontier. Nonempty interior is essential: a singleton is a
counterexample to the analogous statement with mere nonemptiness. -/
theorem closed_eq_univ_of_dense_preconnected_avoid_frontier
    {X : Type*} [TopologicalSpace X] (S D : Set X) (hS : IsClosed S)
    (hne : (interior S).Nonempty) (hD : Dense D) (hconn : IsPreconnected D)
    (havoid : Disjoint D (frontier S)) : S = Set.univ := by
  have hcover : D ⊆ interior S ∪ Sᶜ := by
    intro x hx
    by_cases hs : x ∈ S
    · apply Or.inl
      by_contra hn
      exact Set.disjoint_left.mp havoid hx ⟨subset_closure hs,hn⟩
    · exact Or.inr hs
  obtain ⟨x,hxS,hxD⟩ := hD.inter_open_nonempty (interior S) isOpen_interior hne
  have hsub : D ⊆ interior S := hconn.subset_left_of_subset_union isOpen_interior
    hS.isOpen_compl (Set.disjoint_left.mpr (by intro y hy hn; exact hn (interior_subset hy))) hcover ⟨x,hxD,hxS⟩
  have hcl : closure D ⊆ S := closure_minimal (hsub.trans interior_subset) hS
  rw [hD.closure_eq] at hcl
  exact Set.eq_univ_of_univ_subset hcl

end SpectreGeometry
