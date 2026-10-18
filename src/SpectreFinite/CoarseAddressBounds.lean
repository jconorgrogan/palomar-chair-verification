module

public import SpectreFinite.HexStepAction
public import SpectreFinite.AxialTranslationWords
public import SpectreFinite.AxialFiniteBoxes

@[expose] public section


/-! Bounded coarse addresses arise from actual native-cell paths. The only
local hypothesis says adjacent native cells stay in one fiber or cross a
proved coarse edge; it does not assume a global chart or action freeness. -/
namespace SpectreFinite.HexSearch
open FiniteBoundaryEstimate

variable {X : Type u} (S : HexStepSystem X) (own : Position → X)
  (hstep : ∀ x d, own (addPos x (direction d)) = own x ∨
    ∃ s : Fin 6, own (addPos x (direction d)) = S.step s (own x))

theorem direction_coordinate_bounds : ∀ d : Fin 6,
    (direction d).1.natAbs ≤ 1 ∧ (direction d).2.natAbs ≤ 1 := by decide

include hstep

theorem exists_word_address (word : List Position)
    (hw : ∀ s ∈ word, ∃ d : Fin 6, direction d = s) (x : Position) :
    ∃ v : Position, v.1.natAbs ≤ word.length ∧ v.2.natAbs ≤ word.length ∧
      own (addPos x (wordDisplacement word)) = S.translate v (own x) := by
  induction word generalizing x with
  | nil => exact ⟨(0,0),by decide,by decide,by simp [wordDisplacement,addPos]⟩
  | cons s ss ih =>
    obtain ⟨d,hd⟩ := hw s (by simp)
    obtain ⟨v,hvq,hvr,hv⟩ := ih (fun t ht => hw t (by simp [ht])) (addPos x s)
    have hdisp : addPos x (wordDisplacement (s::ss)) =
        addPos (addPos x s) (wordDisplacement ss) := (addPos_assoc x s _).symm
    rw [hdisp,hv]
    rcases hstep x d with hs | ⟨e,he⟩
    · rw [hd] at hs
      refine ⟨v,by simpa only [List.length_cons] using Nat.le_trans hvq (Nat.le_succ _),
        by simpa only [List.length_cons] using Nat.le_trans hvr (Nat.le_succ _),?_⟩
      rw [hs]
    · rw [hd] at he
      refine ⟨addPos v (direction e),?_,?_,?_⟩
      · have hn := Int.natAbs_add_le v.1 (direction e).1
        have hb := (direction_coordinate_bounds e).1
        simp only [addPos,List.length_cons]
        omega
      · have hn := Int.natAbs_add_le v.2 (direction e).2
        have hb := (direction_coordinate_bounds e).2
        simp only [addPos,List.length_cons]
        omega
      · rw [he,S.translate_add,S.translate_direction]

theorem exists_bounded_address (x : Position) :
    ∃ v : Position, v.1.natAbs ≤ x.1.natAbs+x.2.natAbs ∧
      v.2.natAbs ≤ x.1.natAbs+x.2.natAbs ∧ own x = S.translate v (own (0,0)) := by
  have h := exists_word_address S own hstep (axialWord x)
    (fun s hs => primitiveSteps_directions s (axialWord_steps x hs)) (0,0)
  simpa only [axialWord_length,axialWord_displacement,addPos,Int.zero_add] using h

noncomputable def boundedAddress (x : Position) : Position :=
  Classical.choose (exists_bounded_address S own hstep x)

theorem boundedAddress_spec (x : Position) :
    (boundedAddress S own hstep x).1.natAbs ≤ x.1.natAbs+x.2.natAbs ∧
    (boundedAddress S own hstep x).2.natAbs ≤ x.1.natAbs+x.2.natAbs ∧
    own x = S.translate (boundedAddress S own hstep x) (own (0,0)) :=
  Classical.choose_spec (exists_bounded_address S own hstep x)

theorem boundedAddress_square (n : Nat) (x : Position) (hx : x ∈ positiveSquare n) :
    (boundedAddress S own hstep x).1.natAbs ≤ 2*n ∧
    (boundedAddress S own hstep x).2.natAbs ≤ 2*n := by
  obtain ⟨hql,hqu,hrl,hru⟩ := positiveSquare_coordinates n x hx
  obtain ⟨hq,hr,he⟩ := boundedAddress_spec S own hstep x
  omega

end SpectreFinite.HexSearch
