module

public import Mathlib.Topology.Neighborhoods

@[expose] public section

/-! Finite closed nowhere-dense sets can be avoided inside any nonempty
open set. No Baire-space assumption is necessary or supplied. -/
namespace PhysicalRegistration.NativeMaterialGluing
open Set

/-- Finite avoidance by elementary dense-open intersection induction. -/
theorem exists_mem_open_avoid_closed {X κ : Type*} [TopologicalSpace X] [Finite κ]
    (S : κ → Set X) (hclosed : ∀ k, IsClosed (S k))
    (hempty : ∀ k, interior (S k) = ∅)
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ k, x ∉ S k := by
  classical
  let := Fintype.ofFinite κ
  have hd : ∀ s : Finset κ, Dense (⋂ k ∈ s, (S k)ᶜ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      simp only [Finset.mem_insert, iInter_iInter_eq_or_left]
      exact ((interior_eq_empty_iff_dense_compl.mp (hempty k)).inter_of_isOpen_left
        ih (hclosed k).isOpen_compl)
  obtain ⟨x, hxU, hx⟩ := (hd Finset.univ).inter_open_nonempty U hU hne
  refine ⟨x, hxU, ?_⟩
  simpa only [Finset.mem_univ, iInter_true, mem_iInter, mem_compl_iff] using hx

/-- In particular, finite closed-set frontiers never block a nonempty open set. -/
theorem exists_mem_open_avoid_frontiers {X κ : Type*} [TopologicalSpace X] [Finite κ]
    (S : κ → Set X) (hclosed : ∀ k, IsClosed (S k))
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ k, x ∉ frontier (S k) :=
  exists_mem_open_avoid_closed (fun k => frontier (S k))
    (fun _ => isClosed_frontier) (fun k => interior_frontier (hclosed k)) U hU hne

end PhysicalRegistration.NativeMaterialGluing
