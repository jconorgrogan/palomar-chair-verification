module

public import SpectreFinite.ParentPatterns

@[expose] public section


/-! A fixed axial-index encoding of radius-five rows. Out-of-domain values
are irrelevant to transfer: all lookups used there are proved in-domain. -/
namespace SpectreFinite.HexSearch.ParentOwnership

/-- Zero-based row-major index on the exact ordered axial radius-five ball. -/
def radiusFiveIndex (x : Position) : Nat :=
  (if x.1 < 0 then
    (x.1+5)*(x.1+16)/2 + x.2+5+x.1
  else
    40+11*x.1-x.1*(x.1-1)/2+x.2+5).toNat

def indexedField (row : List State) (x : Position) : State :=
  row.getD (radiusFiveIndex x) (0,0)

def encodedPatch (row : List State) : Patch :=
  restriction (indexedField row) (hexRegion 5)

theorem radiusFiveIndex_correct : ∀ i : Fin 91,
    radiusFiveIndex ((hexRegion 5).getD i.val (0,0)) = i.val := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) ((fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The encoding preserves the entry at every actual domain index. -/
theorem indexedField_at_index (row : List State) (i : Fin 91) :
    indexedField row ((hexRegion 5).getD i.val (0,0)) = row.getD i.val (0,0) := by
  unfold indexedField
  rw [radiusFiveIndex_correct]

theorem encodedPatch_owners (row : List State) (x : Position) (hx : x ∈ hexRegion 3) :
    owners (patchState (encodedPatch row)) x = owners (indexedField row) x := by
  apply owners_local
  intro t d hd
  exact patchState_restriction _ _ _ (radiusThree_candidates_covered x hx t d hd)

theorem encodedPatch_rootParent (row : List State) :
    rootParent (patchState (encodedPatch row)) = rootParent (indexedField row) := by
  apply rootParent_local
  · intro x hx
    exact patchState_restriction _ _ _ (parent_offsets_radiusFive x hx)
  · intro x hx
    exact encodedPatch_owners row x (parent_offsets_radiusThree x hx)

theorem encodedPatch_root (row : List State) :
    patchState (encodedPatch row) (0,0) = indexedField row (0,0) :=
  patchState_restriction _ _ _ (by decide)

def RowProperty (row : List State) : Prop :=
  row.length = 91 ∧ UniqueAt (indexedField row) (0,0) ∧
    (indexedField row (0,0) = (0,0) → ListedRootParent (indexedField row))
instance (row : List State) : Decidable (RowProperty row) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem rowProperty_unique (row : List State) (h : RowProperty row) :
    UniqueAt (patchState (encodedPatch row)) (0,0) := by
  unfold UniqueAt
  rw [encodedPatch_owners row (0,0) (by decide)]
  exact h.2.1

theorem rowProperty_shape (row : List State) (h : RowProperty row)
    (hg : patchState (encodedPatch row) (0,0) = (0,0)) :
    ListedRootParent (patchState (encodedPatch row)) := by
  rw [encodedPatch_root] at hg
  have hs := h.2.2 hg
  unfold ListedRootParent rootParentKinds
  rw [encodedPatch_rootParent]
  exact hs

#print axioms radiusFiveIndex_correct
#print axioms rowProperty_unique
#print axioms rowProperty_shape
end SpectreFinite.HexSearch.ParentOwnership
