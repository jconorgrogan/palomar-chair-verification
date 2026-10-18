module

public import SpectreFinite.HexRotation
public import SpectreFinite.OverlapPruning
public import SpectreFinite.RadiusOneSearch

@[expose] public section


/-! Reconstructing finite windows after root-turn normalization. The total
lookup's default is proved unused for restrictions to the stated domain. -/
namespace SpectreFinite.HexSearch

def patchState : Patch → Position → State
  | [], _ => (0,0)
  | a :: as, x => if a.1 = x then a.2 else patchState as x

theorem patchState_restriction (f : Position → State) (domain : List Position)
    (x : Position) (hx : x ∈ domain) : patchState (restriction f domain) x = f x := by
  induction domain with
  | nil => simp at hx
  | cons a as ih =>
    by_cases ha : a = x
    · subst a
      simp [restriction, patchState]
    · have hx' : x ∈ as := by simpa [List.mem_cons, Ne.symm ha] using hx
      simpa [restriction, patchState, ha] using ih hx'

/-- Output positions keep the specified domain order. Only states are
looked up at inverse-rotated coordinates. -/
def rotatePatch (t : Fin 6) (domain : List Position) (p : Patch) : Patch :=
  domain.map (fun x => (x,rotateState t (patchState p (rotatePosition (inverseTurn t) x))))

theorem rotatePatch_restriction (t : Fin 6) (f : Position → State)
    (domain : List Position)
    (hdom : ∀ x ∈ domain, rotatePosition (inverseTurn t) x ∈ domain) :
    rotatePatch t domain (restriction f domain) = restriction (rotatedField t f) domain := by
  apply List.map_congr_left
  intro x hx
  rw [patchState_restriction f domain _ (hdom x hx)]
  rfl

theorem rotateState_inverse_right (t : Fin 6) (s : State) :
    rotateState t (rotateState (inverseTurn t) s) = s := by
  have h := rotateState_inverse (inverseTurn t) s
  rw [inverseTurn_involutive] at h
  exact h

theorem rotatedField_inverse (t : Fin 6) (f : Position → State) (x : Position) :
    rotatedField t (rotatedField (inverseTurn t) f) x = f x := by
  simp only [rotatedField, inverseTurn_involutive, rotatePosition_inverse_right,
    rotateState_inverse_right]

theorem radiusOne_positions_rotation : ∀ t : Fin 6, ∀ x ∈ RadiusOne.positions,
    rotatePosition t x ∈ RadiusOne.positions := by decide

/-- The normalized field window determines the original window exactly,
including every ordered position and state. -/
theorem normalized_window_reconstruct (f : Position → State) :
    rotatePatch (f (0,0)).2 RadiusOne.positions
      (restriction (rotatedField (inverseTurn (f (0,0)).2) f) RadiusOne.positions) =
      restriction f RadiusOne.positions := by
  rw [rotatePatch_restriction _ _ _ (radiusOne_positions_rotation _)]
  unfold restriction
  apply List.map_congr_left
  intro x _
  rw [rotatedField_inverse]

/-- A global field's window, at any center and any root turn, is a rotation
of an exactly enumerated turn-zero window with its actual root kind. -/
theorem radiusOne_normalized_window (f : Position → State) (hf : GloballyLegal f)
    (center : Position) :
    ∃ p ∈ RadiusOne.assignments ((f center).1, 0),
      extract f center RadiusOne.positions = rotatePatch (f center).2 RadiusOne.positions p := by
  let g := shiftedField f center
  let h := rotatedField (inverseTurn (g (0,0)).2) g
  have hg : GloballyLegal g := shiftedField_globallyLegal f hf center
  have hh : GloballyLegal h := normalized_globallyLegal g hg
  have hcenter : g (0,0) = f center := by simp [g, shiftedField, addPos]
  refine ⟨restriction h RadiusOne.positions, ?_, ?_⟩
  · apply (RadiusOne.mem_assignments_iff _ _).mpr
    refine ⟨?_, restriction_pairwise h hh _ RadiusOne.positions_nodup, ?_⟩
    · simp [restriction, List.map_map, Function.comp_def]
    · intro x hx hxroot
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      have hr := normalized_root g
      change h (0,0) = ((g (0,0)).1,0) at hr
      change q = (0,0) at hxroot
      change h q = ((f center).1,0)
      rw [hxroot, hr, hcenter]
  · have hr := normalized_window_reconstruct g
    change restriction g RadiusOne.positions = rotatePatch (f center).2 RadiusOne.positions
      (restriction (rotatedField (inverseTurn (g (0,0)).2) g) RadiusOne.positions)
    rw [← hcenter]
    exact hr.symm

/-- A complete raw radius-one family obtained from just the nine turn-zero
searches. Rotation is reconstructed in the fixed seven-position order. -/
def allTurnRadiusOne : List Patch :=
  (List.finRange 9).flatMap (fun k => (List.finRange 6).flatMap (fun t =>
    (RadiusOne.assignments (k,0)).map (rotatePatch t RadiusOne.positions)))

theorem allTurnRadiusOne_occurrenceComplete (f : Position → State)
    (hf : GloballyLegal f) : OccurrenceComplete f RadiusOne.positions allTurnRadiusOne := by
  intro center
  obtain ⟨p, hp, he⟩ := radiusOne_normalized_window f hf center
  apply List.mem_flatMap.mpr
  refine ⟨(f center).1, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(f center).2, by simp, ?_⟩
  exact List.mem_map.mpr ⟨p, hp, he.symm⟩

/-- The symmetry-reduced complete initialization is safe for every later
round of the explicitly proved overlap-pruning algorithm. -/
theorem allTurnRadiusOne_pruned_occurrenceComplete (f : Position → State)
    (hf : GloballyLegal f) (offsets : List Position) (n : Nat) :
    OccurrenceComplete f RadiusOne.positions (reduceIter offsets n allTurnRadiusOne) :=
  occurrenceComplete_reduceIter f RadiusOne.positions allTurnRadiusOne offsets
    (allTurnRadiusOne_occurrenceComplete f hf) n

end SpectreFinite.HexSearch
