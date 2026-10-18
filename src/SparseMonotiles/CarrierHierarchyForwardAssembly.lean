module

public import SparseMonotiles.CarrierHierarchyForwardChecker
public import SparseMonotiles.CarrierHierarchyRefinementLaw
public import SparseMonotiles.CarrierHierarchyCoarseSymmetry

@[expose] public section

/-! Assemble independently checked finite forward-pair rows into the exact
refinement rule interface, and expose semantic symmetry transport. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem canonical_table_unique {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {C D : Finset (Pose d)} (hC : IsCanonicalTable σ C) (hD : IsCanonicalTable σ D) : C = D := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, he⟩ := canonical_child_form hD.1 (rootPose d) (hC.2 a ha)
    rw [compose_root_left] at he
    simpa only [he] using hb
  · intro a ha
    obtain ⟨b, hb, he⟩ := canonical_child_form hC.1 (rootPose d) (hD.2 a ha)
    rw [compose_root_left] at he
    simpa only [he] using hb

theorem ForwardRules.change_table {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {C D : Finset (Pose d)} {L : Set (Pose d)}
    (hC : IsCanonicalTable σ C) (hD : IsCanonicalTable σ D) (rules : ForwardRules C L) :
    ForwardRules D L := by
  rw [← canonical_table_unique hC hD]
  exact rules

/-- Finite indexed rows establish every required sibling/cross implication.
The coverage premises are source-index coverage, not legal-world assumptions. -/
theorem forwardRules_of_indexed_pairs {d : ℕ} {α β κ : Type}
    (C : Finset (Pose d)) (L : Set (Pose d))
    (child : α → Pose d) (parent : β → Pose d) (registry : κ → Pose d)
    (child_covers : ∀ a ∈ C, ∃ i, child i = a)
    (parent_covers : ∀ k ∈ L, ∃ i, parent i = k)
    (registry_sound : ∀ i, registry i ∈ L)
    (sibling : α → α → ForwardPairWitness κ)
    (cross : β → α → α → ForwardPairWitness κ)
    (sibling_valid : ∀ a b, child a ≠ child b → (sibling a b).Valid registry (child a) (child b))
    (cross_valid : ∀ k a b,
      (cross k a b).Valid registry (child a) (compose (dilatePose (parent k)) (child b))) :
    ForwardRules C L := by
  constructor
  · intro a ha b hb hne hcontact
    obtain ⟨i, rfl⟩ := child_covers a ha
    obtain ⟨j, rfl⟩ := child_covers b hb
    exact ForwardPairWitness.sound registry L registry_sound (sibling_valid i j hne) hcontact
  · intro k hk a ha b hb hcontact
    obtain ⟨i, rfl⟩ := parent_covers k hk
    obtain ⟨j, rfl⟩ := child_covers a ha
    obtain ⟨l, rfl⟩ := child_covers b hb
    exact ForwardPairWitness.sound registry L registry_sound (cross_valid i j l) hcontact

theorem CellContact.conjugate {d : ℕ} (r : Equiv.Perm (Fin d)) {p q : Pose d}
    (h : CellContact p q) : CellContact (conjugatePose r p) (conjugatePose r q) := by
  obtain ⟨c, e, hc, he, ha⟩ := h
  exact ⟨reindexCell r c, reindexCell r e,
    (conjugatePose_occupies r p c).mpr hc, (conjugatePose_occupies r q e).mpr he,
    reindexCell_adjacent r ha⟩

theorem conjugate_contact_iff {d : ℕ} (r : Equiv.Perm (Fin d)) (p q : Pose d) :
    CellContact (conjugatePose r p) (conjugatePose r q) ↔ CellContact p q := by
  constructor
  · intro h
    simpa only [conjugatePose_symm_cancel] using h.conjugate r.symm
  · exact CellContact.conjugate r

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem dilatePose_conjugate {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) :
    dilatePose (conjugatePose r p) = conjugatePose r (dilatePose p) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [dilatePose]

theorem forward_implication_conjugate {d : ℕ} (r : Equiv.Perm (Fin d)) (L : Set (Pose d))
    (hL : ∀ p ∈ L, conjugatePose r p ∈ L) {p q : Pose d}
    (h : CellContact p q → normalize p q ∈ L) :
    CellContact (conjugatePose r p) (conjugatePose r q) →
      normalize (conjugatePose r p) (conjugatePose r q) ∈ L := by
  intro hc
  rw [← conjugatePose_normalize]
  exact hL _ (h ((conjugate_contact_iff r p q).mp hc))

#print axioms canonical_table_unique
#print axioms forwardRules_of_indexed_pairs
#print axioms forward_implication_conjugate
end SparseMonotiles.CarrierHierarchy
