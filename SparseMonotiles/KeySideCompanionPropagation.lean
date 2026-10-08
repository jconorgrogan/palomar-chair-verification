module

public import SparseMonotiles.KeySideCompanionPropagationGraph
public import SparseMonotiles.KeySideCreaseSeed

@[expose] public section

/-! # Complete K2: a single physical companion covers every key side
All strict-crease geometry, generic world-plane containment, incident counts
and graph connectivity are derived. K1 remains a separate frozen dependency.
-/
namespace SparseMonotiles
open Set Canonical

theorem reference5_exists_strict_side_side_crease (i j : Fin 4) (hij : i ≠ j) (si sj : Bool) :
    ∃ p : Point 5, referenceHalfspaceSlack5 (.inr (i,si)) p=0 ∧
      referenceHalfspaceSlack5 (.inr (j,sj)) p=0 ∧
      ∀ a : PyramidHalfspaceIndex 4, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
        0 < referenceHalfspaceSlack5 a p := by
  refine ⟨keySideCreasePoint ((referenceBox5 true).toKeyData 19200) i j si sj,?_⟩
  apply keySideCreasePoint_full_slacks _ _ referenceSideDistance5_pos i j hij si sj
  change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
  exact_mod_cast referenceBox5_height_pos true

/-- Adjacent closed key sides share an actual generic crease point at which
exactly two physical tiles are incident. No point/ridge/genericity is assumed. -/
theorem T5_exists_generic_shared_key_side_point
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i j : Fin 4) (hij : i ≠ j) (si sj : Bool) :
    ∃ y : Point 5, y ∈ (A : Set (Point 5)) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (j,sj)) x=0}) ∧
      Nat.card (incidentTiles tiles y)=2 := by
  obtain ⟨p,hpi,hpj,hpo⟩ := reference5_exists_strict_side_side_crease i j hij si sj
  exact T5_exists_generic_shared_key_side_point_of_seed ht g hg A hk q hq i j hij si sj hpi hpj hpo

/-- Actual companions covering two adjacent closed key sides are the same
physical tile, by the independently derived generic crease count. -/
theorem T5_adjacent_closed_key_side_companions_eq
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (i j : Fin 4) (hij : i ≠ j) (si sj : Bool)
    {B C : Set (Point 5)} (hB : B ∈ tiles) (hC : C ∈ tiles)
    (hBA : B ≠ (A : Set (Point 5))) (hCA : C ≠ (A : Set (Point 5)))
    (hcoverB : g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) ⊆ B)
    (hcoverC : g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (j,sj)) x=0}) ⊆ C) : B=C := by
  obtain ⟨y,hyA,hyi,hyj,hcard⟩ := T5_exists_generic_shared_key_side_point ht g hg A hk q hq i j hij si sj
  exact IsTiling.companion_eq_of_incident_card_two hcard ⟨A.property,hyA⟩
    ⟨hB,hcoverB hyi⟩ ⟨hC,hcoverC hyj⟩ hBA hCA

/-- Complete K2: one distinct physical tile covers every closed side of an
actual key. The side-facet graph argument includes opposite same-axis sides. -/
theorem T5_entire_key_sides_one_companion
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5) :
    ∃ B ∈ tiles, B ≠ (A : Set (Point 5)) ∧ ∀ (i : Fin 4) (si : Bool),
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) ⊆ B :=
  T5_entire_key_sides_companion_of_strict_seeds ht g hg A hk q hq reference5_exists_strict_side_side_crease

#print axioms T5_exists_generic_shared_key_side_point
#print axioms T5_adjacent_closed_key_side_companions_eq
#print axioms T5_entire_key_sides_one_companion

theorem reference7_exists_strict_side_side_crease (i j : Fin 6) (hij : i ≠ j) (si sj : Bool) :
    ∃ p : Point 7, referenceHalfspaceSlack7 (.inr (i,si)) p=0 ∧
      referenceHalfspaceSlack7 (.inr (j,sj)) p=0 ∧
      ∀ a : PyramidHalfspaceIndex 6, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
        0 < referenceHalfspaceSlack7 a p := by
  refine ⟨keySideCreasePoint ((referenceBox7 true).toKeyData 188160) i j si sj,?_⟩
  apply keySideCreasePoint_full_slacks _ _ referenceSideDistance7_pos i j hij si sj
  change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
  exact_mod_cast referenceBox7_height_pos true

/-- Adjacent closed key sides share an actual generic crease point at which
exactly two physical tiles are incident. No point/ridge/genericity is assumed. -/
theorem T7_exists_generic_shared_key_side_point
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i j : Fin 6) (hij : i ≠ j) (si sj : Bool) :
    ∃ y : Point 7, y ∈ (A : Set (Point 7)) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) ∧
      y ∈ g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (j,sj)) x=0}) ∧
      Nat.card (incidentTiles tiles y)=2 := by
  obtain ⟨p,hpi,hpj,hpo⟩ := reference7_exists_strict_side_side_crease i j hij si sj
  exact T7_exists_generic_shared_key_side_point_of_seed ht g hg A hk q hq i j hij si sj hpi hpj hpo

/-- Actual companions covering two adjacent closed key sides are the same
physical tile, by the independently derived generic crease count. -/
theorem T7_adjacent_closed_key_side_companions_eq
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (i j : Fin 6) (hij : i ≠ j) (si sj : Bool)
    {B C : Set (Point 7)} (hB : B ∈ tiles) (hC : C ∈ tiles)
    (hBA : B ≠ (A : Set (Point 7))) (hCA : C ≠ (A : Set (Point 7)))
    (hcoverB : g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) ⊆ B)
    (hcoverC : g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (j,sj)) x=0}) ⊆ C) : B=C := by
  obtain ⟨y,hyA,hyi,hyj,hcard⟩ := T7_exists_generic_shared_key_side_point ht g hg A hk q hq i j hij si sj
  exact IsTiling.companion_eq_of_incident_card_two hcard ⟨A.property,hyA⟩
    ⟨hB,hcoverB hyi⟩ ⟨hC,hcoverC hyj⟩ hBA hCA

/-- Complete K2: one distinct physical tile covers every closed side of an
actual key. The side-facet graph argument includes opposite same-axis sides. -/
theorem T7_entire_key_sides_one_companion
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7) :
    ∃ B ∈ tiles, B ≠ (A : Set (Point 7)) ∧ ∀ (i : Fin 6) (si : Bool),
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) ⊆ B :=
  T7_entire_key_sides_companion_of_strict_seeds ht g hg A hk q hq reference7_exists_strict_side_side_crease

#print axioms T7_exists_generic_shared_key_side_point
#print axioms T7_adjacent_closed_key_side_companions_eq
#print axioms T7_entire_key_sides_one_companion

end SparseMonotiles
