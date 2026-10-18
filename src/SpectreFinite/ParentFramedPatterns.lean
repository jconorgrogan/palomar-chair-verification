module

public import SpectreFinite.ParentPatterns
public import SpectreFinite.ParentRotation

@[expose] public section


/-! Complete actual-frame parent regions. Universal classification remains
conditional on a finite-family occurrence theorem for globally legal fields.
No boundary, hierarchy, physical realization, or existence theorem is added. -/
namespace SpectreFinite.HexSearch.ParentOwnership

def normalizedAt (f : Position → State) (a : Position) : Position → State :=
  rotatedField (inverseTurn (f a).2) (shiftedField f a)

def framedChildPatch (f : Position → State) (a : Position) (k : TileKind) : Patch :=
  (childPatch k).map (fun e =>
    (addPos a (rotatePosition (f a).2 e.1), rotateState (f a).2 e.2))

/-- Exact equality of the entire owned position/state set in the actual frame. -/
def ExactParentAt (f : Position → State) (a : Position) (k : TileKind) : Prop :=
  ∀ x : Position, ∀ s : State,
    (a ∈ owners f x ∧ s = f x) ↔ (x,s) ∈ framedChildPatch f a k

theorem rotateState_injective (t : Fin 6) (s v : State)
    (h : rotateState t s = rotateState t v) : s = v := by
  have he := congrArg (rotateState (inverseTurn t)) h
  simpa only [rotateState_inverse] using he

theorem normalizedAt_root (f : Position → State) (a : Position)
    (hgamma : (f a).1 = 0) : normalizedAt f a (0,0) = (0,0) := by
  have hs : shiftedField f a (0,0) = f a := by simp [shiftedField,addPos]
  have h := normalized_root (shiftedField f a)
  rw [hs,hgamma] at h
  exact h

theorem mem_framedChildPatch_iff (f : Position → State) (a : Position) (k : TileKind)
    (x : Position) (s : State) :
    (addPos a (rotatePosition (f a).2 x),rotateState (f a).2 s) ∈ framedChildPatch f a k ↔
      (x,s) ∈ childPatch k := by
  constructor
  · intro h
    obtain ⟨e,he,heq⟩ := List.mem_map.mp h
    have hp := (addPos_left_cancel_iff a _ _).mp (congrArg Prod.fst heq)
    have hx := rotatePosition_injective (f a).2 _ _ hp
    have hs := rotateState_injective (f a).2 _ _ (congrArg Prod.snd heq)
    have ee : e = (x,s) := Prod.ext hx hs
    simpa only [ee] using he
  · intro h
    exact List.mem_map.mpr ⟨(x,s),h,rfl⟩

/-- Full set equality, including cells outside the finite illustrated support,
is transported back from the normalized turn-zero Gamma. -/
theorem exactParentAt_of_rootParent (f : Position → State) (a : Position)
    (hgamma : (f a).1 = 0) (k : TileKind)
    (hshape : rootParent (normalizedAt f a) = childPatch k) : ExactParentAt f a k := by
  have canonical : ∀ y : Position, ∀ v : State,
      (a ∈ owners f (addPos a (rotatePosition (f a).2 y)) ∧
        rotateState (f a).2 v = f (addPos a (rotatePosition (f a).2 y))) ↔
      (addPos a (rotatePosition (f a).2 y),rotateState (f a).2 v) ∈ framedChildPatch f a k := by
    intro y v
    have ho := mem_owners_shift_rotate_iff f a (f a).2 y (0,0)
    have hz : addPos a (rotatePosition (f a).2 (0,0)) = a := by
      rw [rotatePosition_zero]
      simp [addPos]
    rw [hz] at ho
    have hs : rotateState (f a).2 v = f (addPos a (rotatePosition (f a).2 y)) ↔
        v = normalizedAt f a y := by
      rw [normalized_field_value f a (f a).2 y]
      constructor
      · exact rotateState_injective (f a).2 _ _
      · intro h
        exact congrArg (rotateState (f a).2) h
    rw [ho,hs,mem_framedChildPatch_iff]
    exact ((mem_rootParent_iff (normalizedAt f a) (normalizedAt_root f a hgamma) y v).symm).trans
      (by rw [hshape])
  intro x s
  let y := rotatePosition (inverseTurn (f a).2) (subPos x a)
  let v := rotateState (inverseTurn (f a).2) s
  have hx : addPos a (rotatePosition (f a).2 y) = x := by
    rw [show y = rotatePosition (inverseTurn (f a).2) (subPos x a) from rfl,
      rotatePosition_inverse_right]
    apply Prod.ext <;> simp only [subPos,addPos] <;> omega
  have hs : rotateState (f a).2 v = s := rotateState_inverse_right (f a).2 s
  simpa only [hx,hs] using canonical y v

/-- The nine literal author patterns are distinct even as occupied labelled
sets, so no ordering convention can introduce ambiguity in parent kind. -/
theorem childPatch_subset_injective : ∀ k j : TileKind,
    (∀ e ∈ childPatch k, e ∈ childPatch j) → k = j := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (fun i => Fin.elim0 i)))))))))

theorem exactParentAt_kind_unique (f : Position → State) (a : Position) (k j : TileKind)
    (hk : ExactParentAt f a k) (hj : ExactParentAt f a j) : k = j := by
  apply childPatch_subset_injective k j
  intro e he
  have hm := (mem_framedChildPatch_iff f a k e.1 e.2).mpr he
  have ho := (hk _ _).mpr hm
  have hjm := (hj _ _).mp ho
  exact (mem_framedChildPatch_iff f a j e.1 e.2).mp hjm

/-- Universal occurrence is an explicit hypothesis, and is applied to the
normalized globally legal field rather than silently assuming list closure. -/
theorem exact_parent_of_universal_radiusFive_certificate
    (family : List Patch)
    (hcert : ∀ p ∈ family, patchState p (0,0) = (0,0) → ListedRootParent (patchState p))
    (hcomplete : ∀ g : Position → State, GloballyLegal g →
      OccurrenceComplete g (hexRegion 5) family)
    (f : Position → State) (hf : GloballyLegal f)
    (a : Position) (hgamma : (f a).1 = 0) :
    ∃ k : TileKind, ExactParentAt f a k ∧ ∀ j : TileKind, ExactParentAt f a j → j = k := by
  have hg : GloballyLegal (normalizedAt f a) :=
    rotatedField_globallyLegal _ _ (shiftedField_globallyLegal f hf a)
  have hshape := listed_parent_of_radiusFive_certificate family hcert
    (normalizedAt f a) (hcomplete (normalizedAt f a) hg) (0,0)
    (normalizedAt_root f a hgamma)
  have hz : shiftedField (normalizedAt f a) (0,0) = normalizedAt f a := by
    funext x
    simp [shiftedField,addPos]
  rw [hz] at hshape
  obtain ⟨k,hk,_⟩ := listedRootParent_selected (normalizedAt f a) hshape
  have he := exactParentAt_of_rootParent f a hgamma k hk
  exact ⟨k,he,fun j hj => exactParentAt_kind_unique f a j k hj he⟩

#print axioms exactParentAt_of_rootParent
#print axioms childPatch_subset_injective
#print axioms exactParentAt_kind_unique
#print axioms exact_parent_of_universal_radiusFive_certificate
end SpectreFinite.HexSearch.ParentOwnership
