module
public import SparseMonotiles.ForwardSparseCoverage
public import SparseMonotiles.CarrierHierarchyRefinementLaw
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Check only retained source-role/catalog-index pairs. Coverage is a
separate theorem, so a missing role cannot silently become a legal rule. -/
def sparseMemberChecks {ι κ : Type} (d : ℕ)
    (registry : κ → CoarseFields) (root : CoarseFields)
    (source : ι → CoarseFields) (rows : List (ι × κ)) : Bool :=
  rows.all (fun pair => forwardFieldsMatch d (root.compose (registry pair.2)) (source pair.1))

theorem sparseMemberChecks_sound {d : ℕ} {ι κ : Type}
    (registry : κ → Pose d) (fields : κ → CoarseFields)
    (hregistry : ∀ i, (fields i).Represents (registry i))
    {root : Pose d} {source : ι → Pose d} {rootFields : CoarseFields}
    {sourceFields : ι → CoarseFields}
    (hr : rootFields.Represents root)
    (hs : ∀ i, (sourceFields i).Represents (source i))
    {rows : List (ι × κ)}
    (checked : sparseMemberChecks d fields rootFields sourceFields rows = true)
    {i : ι} {j : κ} (hrow : (i,j) ∈ rows) :
    normalize root (source i) = registry j := by
  have hm := List.all_eq_true.mp checked (i,j) hrow
  exact ForwardFieldsWitness.check_sound registry fields hregistry hr (hs i)
    (w := .member j) hm

/-- Global finite assembly from complete source-index coverage plus checks
only for retained rows. Neither geometric contact nor legality is assumed
for omitted indices: coverage must prove every actual contact is retained. -/
theorem forwardRules_of_sparse_member_rows {d : ℕ} {α β κ : Type}
    (C : Finset (Pose d)) (L : Set (Pose d))
    (child : α → Pose d) (parent : β → Pose d) (registry : κ → Pose d)
    (child_covers : ∀ a ∈ C, ∃ i, child i = a)
    (parent_covers : ∀ k ∈ L, ∃ i, parent i = k)
    (registry_sound : ∀ i, registry i ∈ L)
    (childFields : α → CoarseFields) (parentFields : β → CoarseFields)
    (registryFields : κ → CoarseFields)
    (hchild : ∀ i, (childFields i).Represents (child i))
    (hparent : ∀ i, (parentFields i).Represents (parent i))
    (hregistry : ∀ i, (registryFields i).Represents (registry i))
    (siblingRows : α → List (α × κ))
    (crossRows : β → α → List (α × κ))
    (sibling_coverage : ∀ a b, child a ≠ child b → CellContact (child a) (child b) →
      ∃ j, (b,j) ∈ siblingRows a)
    (cross_coverage : ∀ k a b,
      CellContact (child a) (compose (dilatePose (parent k)) (child b)) →
      ∃ j, (b,j) ∈ crossRows k a)
    (sibling_checked : ∀ a,
      sparseMemberChecks d registryFields (childFields a) childFields (siblingRows a) = true)
    (cross_checked : ∀ k a, sparseMemberChecks d registryFields (childFields a)
      (fun b => (parentFields k).dilate.compose (childFields b)) (crossRows k a) = true) :
    ForwardRules C L := by
  constructor
  · intro a ha b hb hne hc
    obtain ⟨i, rfl⟩ := child_covers a ha
    obtain ⟨j, rfl⟩ := child_covers b hb
    obtain ⟨n, hn⟩ := sibling_coverage i j hne hc
    have he := sparseMemberChecks_sound registry registryFields hregistry
      (hchild i) hchild (sibling_checked i) hn
    rw [he]
    exact registry_sound n
  · intro k hk a ha b hb hc
    obtain ⟨i, rfl⟩ := parent_covers k hk
    obtain ⟨j, rfl⟩ := child_covers a ha
    obtain ⟨l, rfl⟩ := child_covers b hb
    obtain ⟨n, hn⟩ := cross_coverage i j l hc
    have hs : ∀ b,
        ((parentFields i).dilate.compose (childFields b)).Represents
          (compose (dilatePose (parent i)) (child b)) := fun b =>
      CoarseFields.compose_represents (CoarseFields.dilate_represents (hparent i)) (hchild b)
    have he := sparseMemberChecks_sound registry registryFields hregistry
      (hchild j) hs (cross_checked i j) hn
    rw [he]
    exact registry_sound n

#print axioms sparseMemberChecks_sound
#print axioms forwardRules_of_sparse_member_rows
end SparseMonotiles.CarrierHierarchy
