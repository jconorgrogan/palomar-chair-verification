module

public import SpectreFinite.GlobalRestrictions

@[expose] public section


/-!
Translation of the exact discrete marked-hexagon matching model.
Windows retain positions relative to their centers. No existence of a global
field or correspondence with a physical tiling is assumed or proved.
-/
namespace SpectreFinite.HexSearch

theorem addPos_assoc (a b c : Position) :
    addPos (addPos a b) c = addPos a (addPos b c) := by
  simp [addPos, Int.add_assoc]

theorem addPos_left_cancel_iff (c x y : Position) :
    addPos c x = addPos c y ↔ x = y := by
  rcases x with ⟨xq, xr⟩
  rcases y with ⟨yq, yr⟩
  simp [addPos, Prod.mk.injEq]

/-- Translating both positions preserves exactly the original matching rule;
the tile kinds and turns do not change. -/
theorem matches_translate_iff (c : Position) (x y : Position × State) :
    Matches (addPos c x.1, x.2) (addPos c y.1, y.2) ↔ Matches x y := by
  change
    (addPos c x.1 ≠ addPos c y.1 ∧ ∀ d : Fin 6,
      addPos c y.1 = addPos (addPos c x.1) (direction d) →
      facingMark (placed x) d = -(facingMark (placed y) (opposite d))) ↔
    (x.1 ≠ y.1 ∧ ∀ d : Fin 6,
      y.1 = addPos x.1 (direction d) →
      facingMark (placed x) d = -(facingMark (placed y) (opposite d)))
  simp only [addPos_assoc, Ne, addPos_left_cancel_iff]

def shiftedField (f : Position → State) (center : Position) : Position → State :=
  fun x => f (addPos center x)

theorem shiftedField_globallyLegal (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : GloballyLegal (shiftedField f center) := by
  intro x y hxy
  apply (matches_translate_iff center (x, shiftedField f center x)
    (y, shiftedField f center y)).mp
  exact hf (addPos center x) (addPos center y)
    (fun h => hxy ((addPos_left_cancel_iff center x y).mp h))

abbrev Patch := List (Position × State)

/-- The window at `center`, with every position recorded relative to it. -/
def extract (f : Position → State) (center : Position) (domain : List Position) : Patch :=
  restriction (shiftedField f center) domain

theorem mem_extract_iff (f : Position → State) (center : Position)
    (domain : List Position) (x : Position) (s : State) :
    (x, s) ∈ extract f center domain ↔ x ∈ domain ∧ s = f (addPos center x) := by
  constructor
  · intro h
    obtain ⟨y, hy, he⟩ := List.mem_map.mp h
    have hxy : y = x := congrArg Prod.fst he
    subst y
    exact ⟨hy, (congrArg Prod.snd he).symm⟩
  · rintro ⟨hx, rfl⟩
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem extract_enumerated (f : Position → State) (hf : GloballyLegal f)
    (center : Position) (domain : List Position) (hn : domain.Nodup) :
    extract f center domain ∈ assignments domain :=
  restriction_enumerated (shiftedField f center)
    (shiftedField_globallyLegal f hf center) domain hn

#print axioms addPos_assoc
#print axioms addPos_left_cancel_iff
#print axioms matches_translate_iff
#print axioms shiftedField_globallyLegal
#print axioms mem_extract_iff
#print axioms extract_enumerated
end SpectreFinite.HexSearch
