module

public import SpectreFinite.ParentOwnership
public import SpectreFinite.HexRotationComposition

@[expose] public section


/-! Rotation covariance of the actual two-stage owner relation. This is a
semantic statement about arbitrary fields, independent of a finite catalogue. -/
namespace SpectreFinite.HexSearch.ParentOwnership

theorem rotatedField_inverse_left (t : Fin 6) (f : Position → State) :
    rotatedField (inverseTurn t) (rotatedField t f) = f := by
  funext x
  have h := rotatedField_inverse (inverseTurn t) f x
  simpa only [inverseTurn_involutive] using h

theorem primaryOwner_rotate (t : Fin 6) (f : Position → State) (x a : Position)
    (h : PrimaryOwner f x a) :
    PrimaryOwner (rotatedField t f) (rotatePosition t x) (rotatePosition t a) := by
  obtain ⟨hk,d,hd,hx⟩ := h
  refine ⟨?_,d,hd,?_⟩
  · simpa only [rotatedField_apply_rotated, rotateState] using hk
  · rw [rotatedField_apply_rotated]
    change rotatePosition t x = addPos (rotatePosition t a)
      (rotatePosition (rotateTurn t (f a).2) d)
    rw [← rotatePosition_comp, ← rotatePosition_add, ← hx]

theorem secondaryOwner_rotate (t : Fin 6) (f : Position → State) (x a : Position)
    (h : SecondaryOwner f x a) :
    SecondaryOwner (rotatedField t f) (rotatePosition t x) (rotatePosition t a) := by
  obtain ⟨hk,hx⟩ := h
  refine ⟨?_,?_⟩
  · simpa only [rotatedField_apply_rotated, rotateState] using hk
  · rw [rotatedField_apply_rotated]
    change rotatePosition t x = addPos (rotatePosition t a)
      (rotatePosition (rotateTurn t (f a).2) secondaryOffset)
    rw [← rotatePosition_comp, ← rotatePosition_add, ← hx]

theorem primaryOwner_rotate_iff (t : Fin 6) (f : Position → State) (x a : Position) :
    PrimaryOwner (rotatedField t f) (rotatePosition t x) (rotatePosition t a) ↔
      PrimaryOwner f x a := by
  constructor
  · intro h
    have h' := primaryOwner_rotate (inverseTurn t) (rotatedField t f) _ _ h
    simpa only [rotatePosition_inverse, rotatedField_inverse_left] using h'
  · exact primaryOwner_rotate t f x a

theorem secondaryOwner_rotate_iff (t : Fin 6) (f : Position → State) (x a : Position) :
    SecondaryOwner (rotatedField t f) (rotatePosition t x) (rotatePosition t a) ↔
      SecondaryOwner f x a := by
  constructor
  · intro h
    have h' := secondaryOwner_rotate (inverseTurn t) (rotatedField t f) _ _ h
    simpa only [rotatePosition_inverse, rotatedField_inverse_left] using h'
  · exact secondaryOwner_rotate t f x a

theorem mem_primaryOwners_rotate_iff (t : Fin 6) (f : Position → State) (x a : Position) :
    rotatePosition t a ∈ primaryOwners (rotatedField t f) (rotatePosition t x) ↔
      a ∈ primaryOwners f x := by
  rw [mem_primaryOwners_iff, mem_primaryOwners_iff, primaryOwner_rotate_iff]

theorem mem_secondaryOwners_rotate_iff (t : Fin 6) (f : Position → State) (x a : Position) :
    rotatePosition t a ∈ secondaryOwners (rotatedField t f) (rotatePosition t x) ↔
      a ∈ secondaryOwners f x := by
  rw [mem_secondaryOwners_iff, mem_secondaryOwners_iff, secondaryOwner_rotate_iff]

theorem primaryOwners_rotated_empty_iff (t : Fin 6) (f : Position → State) (x : Position) :
    primaryOwners (rotatedField t f) (rotatePosition t x) = [] ↔ primaryOwners f x = [] := by
  constructor
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have h' := (mem_primaryOwners_rotate_iff t f x a).mpr ha
    simp only [h, List.not_mem_nil] at h'
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have h' : rotatePosition t (rotatePosition (inverseTurn t) a) ∈
        primaryOwners (rotatedField t f) (rotatePosition t x) := by
      simpa only [rotatePosition_inverse_right] using ha
    have h'' := (mem_primaryOwners_rotate_iff t f x _).mp h'
    simp only [h, List.not_mem_nil] at h''

/-- Priority of primary owners over secondary owners is itself preserved;
this proves covariance of the actual selected ownership, not just candidates. -/
theorem mem_owners_rotate_iff (t : Fin 6) (f : Position → State) (x a : Position) :
    rotatePosition t a ∈ owners (rotatedField t f) (rotatePosition t x) ↔
      a ∈ owners f x := by
  by_cases h : primaryOwners f x = []
  · have h' := (primaryOwners_rotated_empty_iff t f x).mpr h
    simp only [owners, h, h', ↓reduceIte, mem_secondaryOwners_rotate_iff]
  · have h' : primaryOwners (rotatedField t f) (rotatePosition t x) ≠ [] :=
      fun he => h ((primaryOwners_rotated_empty_iff t f x).mp he)
    simp only [owners, h, h', ↓reduceIte, mem_primaryOwners_rotate_iff]

theorem mem_owners_translate_iff (f : Position → State) (c x a : Position) :
    addPos c a ∈ owners f (addPos c x) ↔ a ∈ owners (shiftedField f c) x := by
  rw [owners_translate]
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    have he' := (addPos_left_cancel_iff c b a).mp he
    simpa only [he'] using hb
  · intro h
    exact List.mem_map.mpr ⟨a,h,rfl⟩

/-- Full affine-frame normalization of the selected owner relation. -/
theorem mem_owners_shift_rotate_iff (f : Position → State) (c : Position)
    (t : Fin 6) (x a : Position) :
    addPos c (rotatePosition t a) ∈ owners f (addPos c (rotatePosition t x)) ↔
      a ∈ owners (rotatedField (inverseTurn t) (shiftedField f c)) x := by
  rw [mem_owners_translate_iff]
  let g := shiftedField f c
  have he : rotatedField t (rotatedField (inverseTurn t) g) = g := by
    funext y
    exact rotatedField_inverse t g y
  have h := mem_owners_rotate_iff t (rotatedField (inverseTurn t) g) x a
  rw [he] at h
  exact h

theorem normalized_field_value (f : Position → State) (c : Position)
    (t : Fin 6) (x : Position) :
    f (addPos c (rotatePosition t x)) =
      rotateState t (rotatedField (inverseTurn t) (shiftedField f c) x) := by
  simp only [rotatedField, inverseTurn_involutive, rotateState_inverse_right, shiftedField]

end SpectreFinite.HexSearch.ParentOwnership
