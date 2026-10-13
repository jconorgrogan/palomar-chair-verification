module

public import Mathlib.Topology.Connected.Basic

@[expose] public section

/-!
Finite connected closed-cover propagation for keyed registration.

The geometric inputs remain explicit: a nonempty connected root complex,
finitely many closed candidate companion complexes, dense generic matching,
and pairwise separation on the root. This file does not assume whole-key
matching, nor does it prove the concrete polyhedral hypotheses.
-/

namespace PhysicalRegistration
open Set

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]

/-- A finite closed cover separated on a nonempty connected set has exactly
one member containing the entire set. -/
theorem connected_unique_closed_companion {C : Set X}
    (hC : IsConnected C) (K : ι → Set X)
    (hK : ∀ i, IsClosed (K i))
    (hcover : C ⊆ ⋃ i, K i)
    (hsep : Pairwise fun i j => Disjoint (C ∩ K i) (C ∩ K j)) :
    ∃! i, C ⊆ K i := by
  classical
  obtain ⟨x, hxC⟩ := hC.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hxC)
  let R : Set X := ⋃ j : {j : ι // j ≠ i}, K j.val
  have hR : IsClosed R :=
    isClosed_iUnion_of_finite fun j => hK j.val
  have hsplit : C ⊆ K i ∪ R := by
    intro y hyC
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hyC)
    by_cases hji : j = i
    · subst j
      exact Or.inl hyj
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  have hCi : C ⊆ K i := by
    intro y hyC
    by_contra hyi
    have hyR : y ∈ R := (hsplit hyC).resolve_left hyi
    obtain ⟨z, hzC, hzi, hzR⟩ :=
      isPreconnected_closed_iff.mp hC.isPreconnected (K i) R
        (hK i) hR hsplit ⟨x, hxC, hxi⟩ ⟨y, hyC, hyR⟩
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hzR
    exact Set.disjoint_left.mp (hsep (Ne.symm j.property))
      ⟨hzC, hzi⟩ ⟨hzC, hzj⟩
  refine ⟨i, hCi, ?_⟩
  intro j hCj
  by_contra hji
  exact Set.disjoint_left.mp (hsep hji) ⟨hxC, hCj hxC⟩ ⟨hxC, hxi⟩

/-- Dense generic matching suffices: closedness first upgrades the dense
matches to a cover, and connectedness excludes companion switching. -/
theorem connected_unique_closed_companion_of_dense {C D : Set X}
    (hC : IsConnected C) (K : ι → Set X)
    (hK : ∀ i, IsClosed (K i))
    (hdense : C ⊆ closure D)
    (hmatch : D ⊆ ⋃ i, K i)
    (hsep : Pairwise fun i j => Disjoint (C ∩ K i) (C ∩ K j)) :
    ∃! i, C ⊆ K i := by
  apply connected_unique_closed_companion hC K hK
  · exact hdense.trans (closure_minimal hmatch (isClosed_iUnion_of_finite hK))
  · exact hsep

#print axioms connected_unique_closed_companion
#print axioms connected_unique_closed_companion_of_dense
end PhysicalRegistration
