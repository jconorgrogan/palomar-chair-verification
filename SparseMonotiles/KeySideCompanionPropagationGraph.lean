module

public import SparseMonotiles.KeySideCompanionPropagationPhysical

@[expose] public section

/-! # K2 propagation over the connected graph of actual key sides -/
namespace SparseMonotiles
open Set Canonical

theorem T5_entire_key_sides_companion_of_strict_seeds
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5) (A : tiles)
    {k : KeyData 5} (hk : k ∈ keys5) (q : Contact.Pose 5)
    (hq : keySolid k = q.euclidean '' referenceSolid5)
    (hseed : ∀ i j : Fin 4, i ≠ j → ∀ si sj : Bool, ∃ p : Point 5,
      referenceHalfspaceSlack5 (.inr (i,si)) p=0 ∧
      referenceHalfspaceSlack5 (.inr (j,sj)) p=0 ∧
      ∀ a : PyramidHalfspaceIndex 4, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
        0 < referenceHalfspaceSlack5 a p) :
    ∃ B ∈ tiles, B ≠ (A : Set (Point 5)) ∧ ∀ (i : Fin 4) (si : Bool),
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack5 q (.inr (i,si)) x=0}) ⊆ B := by
  classical
  choose B hB hBA hcover using (fun (i : Fin 4) (si : Bool) =>
    T5_entire_closed_key_side_companion ht g hg A hk q hq i si)
  have hpair : ∀ i j : Fin 4, i ≠ j → ∀ si sj : Bool, B i si=B j sj := by
    intro i j hij si sj
    obtain ⟨p,hpi,hpj,hpo⟩ := hseed i j hij si sj
    obtain ⟨y,hyA,hyi,hyj,hcard⟩ := T5_exists_generic_shared_key_side_point_of_seed
      ht g hg A hk q hq i j hij si sj hpi hpj hpo
    exact IsTiling.companion_eq_of_incident_card_two hcard ⟨A.property,hyA⟩
      ⟨hB i si,hcover i si hyi⟩ ⟨hB j sj,hcover j sj hyj⟩ (hBA i si) (hBA j sj)
  have hall := side_companion_constant_of_distinct_axes (by omega : 2 ≤ 4) B hpair
  refine ⟨B 0 false,hB 0 false,hBA 0 false,?_⟩
  intro i si
  simpa only [hall i 0 si false] using hcover i si

#print axioms T5_entire_key_sides_companion_of_strict_seeds

theorem T7_entire_key_sides_companion_of_strict_seeds
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7) (A : tiles)
    {k : KeyData 7} (hk : k ∈ keys7) (q : Contact.Pose 7)
    (hq : keySolid k = q.euclidean '' referenceSolid7)
    (hseed : ∀ i j : Fin 6, i ≠ j → ∀ si sj : Bool, ∃ p : Point 7,
      referenceHalfspaceSlack7 (.inr (i,si)) p=0 ∧
      referenceHalfspaceSlack7 (.inr (j,sj)) p=0 ∧
      ∀ a : PyramidHalfspaceIndex 6, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
        0 < referenceHalfspaceSlack7 a p) :
    ∃ B ∈ tiles, B ≠ (A : Set (Point 7)) ∧ ∀ (i : Fin 6) (si : Bool),
      g A '' (keySolid k ∩ {x | posedHalfspaceSlack7 q (.inr (i,si)) x=0}) ⊆ B := by
  classical
  choose B hB hBA hcover using (fun (i : Fin 6) (si : Bool) =>
    T7_entire_closed_key_side_companion ht g hg A hk q hq i si)
  have hpair : ∀ i j : Fin 6, i ≠ j → ∀ si sj : Bool, B i si=B j sj := by
    intro i j hij si sj
    obtain ⟨p,hpi,hpj,hpo⟩ := hseed i j hij si sj
    obtain ⟨y,hyA,hyi,hyj,hcard⟩ := T7_exists_generic_shared_key_side_point_of_seed
      ht g hg A hk q hq i j hij si sj hpi hpj hpo
    exact IsTiling.companion_eq_of_incident_card_two hcard ⟨A.property,hyA⟩
      ⟨hB i si,hcover i si hyi⟩ ⟨hB j sj,hcover j sj hyj⟩ (hBA i si) (hBA j sj)
  have hall := side_companion_constant_of_distinct_axes (by omega : 2 ≤ 6) B hpair
  refine ⟨B 0 false,hB 0 false,hBA 0 false,?_⟩
  intro i si
  simpa only [hall i 0 si false] using hcover i si

#print axioms T7_entire_key_sides_companion_of_strict_seeds

end SparseMonotiles
