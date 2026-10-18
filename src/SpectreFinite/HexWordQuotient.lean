module

public import SpectreFinite.HexStepField

@[expose] public section


/-! An algebraic limit interface for finite marked hex complexes. Labels on
all direction words satisfying the local inverse/triangle replacements and
edge matching descend to a total labelled hex-step system. No free action,
planar embedding, or global field is assumed in this construction. -/
namespace SpectreFinite.HexSearch

abbrev HexWord := List (Fin 6)

inductive HexWordRel : HexWord → HexWord → Prop
  | cancel (u v : HexWord) (d : Fin 6) :
      HexWordRel ((u++[d,opposite d])++v) (u++v)
  | triangle (u v : HexWord) (d : Fin 6) :
      HexWordRel ((u++[d,rotateTurn 2 d])++v) ((u++[rotateTurn 1 d])++v)

theorem HexWordRel.append {a b : HexWord} (h : HexWordRel a b) (v : HexWord) :
    HexWordRel (a++v) (b++v) := by
  cases h with
  | cancel u w d => simpa only [List.append_assoc] using HexWordRel.cancel u (w++v) d
  | triangle u w d => simpa only [List.append_assoc] using HexWordRel.triangle u (w++v) d

abbrev HexWordPoint := Quot HexWordRel

def wordPointStep (d : Fin 6) : HexWordPoint → HexWordPoint :=
  Quot.lift (fun w => Quot.mk HexWordRel (w++[d]))
    (fun _ _ h => Quot.sound (h.append [d]))

theorem wordPointStep_mk (d : Fin 6) (w : HexWord) :
    wordPointStep d (Quot.mk HexWordRel w) = Quot.mk HexWordRel (w++[d]) := rfl

def wordPointSystem : HexStepSystem HexWordPoint where
  step := wordPointStep
  opposite_inverse := by
    intro d q
    refine Quot.inductionOn q ?_
    intro w
    apply Quot.sound
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
      using HexWordRel.cancel w [] d
  triangle := by
    intro d q
    refine Quot.inductionOn q ?_
    intro w
    apply Quot.sound
    simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
      using HexWordRel.triangle w [] d

def WordLabelCompatible (L : HexWord → State) : Prop :=
  ∀ a b, HexWordRel a b → L a = L b

def wordPointLabel (L : HexWord → State) (hL : WordLabelCompatible L) : HexWordPoint → State :=
  Quot.lift L hL

theorem wordLabelCompatible_of_rules (L : HexWord → State)
    (hc : ∀ u v d, L ((u++[d,opposite d])++v) = L (u++v))
    (ht : ∀ u v d, L ((u++[d,rotateTurn 2 d])++v) = L ((u++[rotateTurn 1 d])++v)) :
    WordLabelCompatible L := by
  intro a b hab
  cases hab with
  | cancel u v d => exact hc u v d
  | triangle u v d => exact ht u v d

theorem wordPointLabel_matching (L : HexWord → State) (hL : WordLabelCompatible L)
    (hm : ∀ w d, facingMark (placed ((0,0),L w)) d =
      -facingMark (placed ((0,0),L (w++[d]))) (opposite d)) :
    ∀ d q, facingMark (placed ((0,0),wordPointLabel L hL q)) d =
      -facingMark (placed ((0,0),wordPointLabel L hL (wordPointSystem.step d q))) (opposite d) := by
  intro d q
  refine Quot.inductionOn q ?_
  intro w
  exact hm w d

/-- The existence input is a total coherently labelled word system, which
can be obtained from finite deep neighborhoods by finite-alphabet compactness. -/
theorem exists_globallyLegal_of_word_labels (L : HexWord → State)
    (hc : ∀ u v d, L ((u++[d,opposite d])++v) = L (u++v))
    (ht : ∀ u v d, L ((u++[d,rotateTurn 2 d])++v) = L ((u++[rotateTurn 1 d])++v))
    (hm : ∀ w d, facingMark (placed ((0,0),L w)) d =
      -facingMark (placed ((0,0),L (w++[d]))) (opposite d)) :
    ∃ f : Position → State, GloballyLegal f := by
  let hL := wordLabelCompatible_of_rules L hc ht
  exact ⟨wordPointSystem.labelField (wordPointLabel L hL) (Quot.mk HexWordRel []),
    wordPointSystem.labelField_globallyLegal (wordPointLabel L hL)
      (wordPointLabel_matching L hL hm) (Quot.mk HexWordRel [])⟩

end SpectreFinite.HexSearch
