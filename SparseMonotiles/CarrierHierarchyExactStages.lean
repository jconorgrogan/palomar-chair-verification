module

public import SparseMonotiles.CarrierHierarchyCoarsening

@[expose] public section

/-!
Exact supplied-registry instances of the proved one-level hierarchy operator.
These are registered-world statements. The unmarked physical 284/408 contact
law and coarse-law preservation remain separate, explicit obligations.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem RegisteredWorld.has_complete_parent {d : ℕ} (W : RegisteredWorld d)
    (hd : 3 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L) :
    ∃ p, CompleteParent σ r W.tiles p := by
  obtain ⟨t, ht, _⟩ := W.covers (fun _ => 0)
  obtain ⟨p, hp, _⟩ := W.complete_parent_exists hd hL hl t ht
  exact ⟨p, hp⟩

/-- Choose only the common origin; the physical parent partition itself was
proved unique and is not chosen or supplied as an assumption. -/
noncomputable def RegisteredWorld.canonicalCoarsen {d : ℕ} (W : RegisteredWorld d)
    (hd : 3 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L) :
    RegisteredWorld d :=
  W.coarsen hd hr he hL hl (Classical.choose (W.has_complete_parent hd hL hl))
    (Classical.choose_spec (W.has_complete_parent hd hL hl))

def M5 : Set (Pose 5) := {p | p ∈ Catalog5.supplied}
def M7 : Set (Pose 7) := {p | p ∈ Catalog7.supplied}

theorem registered5_unique_physical_parent (W : RegisteredWorld 5) (hl : W.Legal M5)
    (t : Pose 5) (ht : t ∈ W.tiles) :
    ∃! P : PhysicalPose Catalog5.r Catalog5.r_involutive,
      ∃ p, physicalClass Catalog5.r Catalog5.r_involutive p = P ∧
        CompleteParent Catalog5.childPerm Catalog5.r W.tiles p ∧
        ParentContains Catalog5.childPerm Catalog5.r p t :=
  W.unique_physical_parent (by decide) Catalog5.r_involutive Catalog5.child_rule_equivariant
    Catalog5.local_catalog hl t ht

theorem registered7_unique_physical_parent (W : RegisteredWorld 7) (hl : W.Legal M7)
    (t : Pose 7) (ht : t ∈ W.tiles) :
    ∃! P : PhysicalPose Catalog7.r Catalog7.r_involutive,
      ∃ p, physicalClass Catalog7.r Catalog7.r_involutive p = P ∧
        CompleteParent Catalog7.childPerm Catalog7.r W.tiles p ∧
        ParentContains Catalog7.childPerm Catalog7.r p t :=
  W.unique_physical_parent (by decide) Catalog7.r_involutive Catalog7.child_rule_equivariant
    Catalog7.local_catalog hl t ht

noncomputable def registered5Coarsen (W : RegisteredWorld 5) (hl : W.Legal M5) :
    RegisteredWorld 5 :=
  W.canonicalCoarsen (by decide) Catalog5.r_involutive Catalog5.child_rule_equivariant
    Catalog5.local_catalog hl

noncomputable def registered7Coarsen (W : RegisteredWorld 7) (hl : W.Legal M7) :
    RegisteredWorld 7 :=
  W.canonicalCoarsen (by decide) Catalog7.r_involutive Catalog7.child_rule_equivariant
    Catalog7.local_catalog hl

#print axioms registered5_unique_physical_parent
#print axioms registered7_unique_physical_parent
#print axioms registered5Coarsen
#print axioms registered7Coarsen
end SparseMonotiles.CarrierHierarchy
