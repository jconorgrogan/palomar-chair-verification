module

public import SparseMonotiles.CarrierHierarchyRecognition
public import SparseMonotiles.CarrierHierarchyCandidates
public import SparseMonotiles.CarrierHierarchyCatalog5
public import SparseMonotiles.CarrierHierarchyCatalog7

@[expose] public section

/-!
Concrete registry instances of the local recognition theorem. The listed-pose
premise remains explicit: neither the 284-pose nor the 408-pose physical contact
law, nor registration of arbitrary physical tilings, is silently assumed proved.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Supply local geometry from a concrete, kernel-checked pose registry. -/
def LocalPatch.ofListed {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} {ps : List (Pose d)}
    (checked : ∀ p ∈ ps, LocalCatalogFacts σ r p)
    (tiles : Set (Pose d)) (listed : ∀ p ∈ tiles, p ∈ ps)
    (covers : ∀ a, Proper a → ∀ j, ∃ p ∈ tiles, Occupies p (exterior a j))
    (root_disjoint : ∀ p ∈ tiles, ∀ a, Proper a → ¬ Occupies p (fun i => bit a i))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q) : LocalPatch d σ r where
  tiles := tiles
  catalog := fun p hp => checked p (listed p hp)
  covers := covers
  root_disjoint := root_disjoint
  disjoint := disjoint

/-- Normalized root tile; its central candidate parent is anchored at -1. -/
def rootPose (d : ℕ) : Pose d where
  perm := Equiv.refl _
  negative := fun _ => false
  shift := fun _ => 0

private theorem root_parent_outer {d : ℕ} (a : Bits d)
    (σ : Equiv.Perm (Fin d)) :
    compose (centralParent (rootPose d)) (outerPose a σ) = incomingPose a σ := by
  simp only [compose, centralParent, rootPose, outerPose, incomingPose, Pose.sign,
    Bool.false_eq_true, if_false, Equiv.refl_trans, Equiv.refl_apply, Bool.false_xor,
    one_mul, zero_sub, Pose.mk.injEq]
  refine ⟨True.intro, True.intro, ?_⟩
  funext i
  omega

/-- Full incoming coverage gives the actual complete physical parent patch,
including its root central child, rather than merely a collection of labels. -/
theorem LocalPatch.complete_parent_of_nonempty_incoming {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (P : LocalPatch d σ r) (hd : 3 ≤ d) {a : Bits d}
    (ha : Proper a) (hna : NonemptyRole a) (hi : P.incoming a) :
    CompleteParent σ r (insert (rootPose d) P.tiles) (centralParent (rootPose d)) := by
  have hall := P.complete_of_nonempty_incoming hd ha hna hi
  intro q hq
  rcases hq with hq | ⟨b, hb, hq⟩
  · rw [centralChild_parent] at hq
    subst q
    exact ⟨rootPose d, Set.mem_insert _ _, Or.inl rfl⟩
  · rw [root_parent_outer] at hq
    subst q
    obtain ⟨s, hs, hg⟩ := hall b hb
    exact ⟨s, Set.mem_insert_of_mem _ hs, hg⟩

/-- Exact 284-language, preserving the physical right-{id,r} quotient. -/
theorem catalog5_local_recognition
    (tiles : Set (Pose 5)) (listed : ∀ p ∈ tiles, p ∈ Catalog5.supplied)
    (covers : ∀ a, Proper a → ∀ j, ∃ p ∈ tiles, Occupies p (exterior a j))
    (root_disjoint : ∀ p ∈ tiles, ∀ a, Proper a → ¬ Occupies p (fun i => bit a i))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q)
    {a : Bits 5} (ha : Proper a) (hna : NonemptyRole a)
    (hi : ∃ p ∈ tiles, GaugeRel Catalog5.r (incomingPose a (Catalog5.childPerm a)) p) :
    ∀ b, Proper b →
      ∃ p ∈ tiles, GaugeRel Catalog5.r (incomingPose b (Catalog5.childPerm b)) p := by
  exact (LocalPatch.ofListed Catalog5.local_catalog tiles listed covers root_disjoint disjoint).complete_of_nonempty_incoming (by decide) ha hna hi

/-- Exact 408-language; no unproved replacement by the 318-pose E language. -/
theorem catalog7_local_recognition
    (tiles : Set (Pose 7)) (listed : ∀ p ∈ tiles, p ∈ Catalog7.supplied)
    (covers : ∀ a, Proper a → ∀ j, ∃ p ∈ tiles, Occupies p (exterior a j))
    (root_disjoint : ∀ p ∈ tiles, ∀ a, Proper a → ¬ Occupies p (fun i => bit a i))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q)
    {a : Bits 7} (ha : Proper a) (hna : NonemptyRole a)
    (hi : ∃ p ∈ tiles, GaugeRel Catalog7.r (incomingPose a (Catalog7.childPerm a)) p) :
    ∀ b, Proper b →
      ∃ p ∈ tiles, GaugeRel Catalog7.r (incomingPose b (Catalog7.childPerm b)) p := by
  exact (LocalPatch.ofListed Catalog7.local_catalog tiles listed covers root_disjoint disjoint).complete_of_nonempty_incoming (by decide) ha hna hi

#print axioms catalog5_local_recognition
#print axioms catalog7_local_recognition
end SparseMonotiles.CarrierHierarchy
