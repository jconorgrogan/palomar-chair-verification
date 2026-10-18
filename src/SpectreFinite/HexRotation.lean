module

public import SpectreFinite.GlobalRestrictions

@[expose] public section


/-! Exact C6 covariance of the discrete marked-hexagon model. These are
integer-grid and finite-label statements, not a physical correspondence. -/
namespace SpectreFinite.HexSearch

/-- Positive sixty-degree turns in axial coordinates. -/
def rotatePosition (t : Fin 6) (x : Position) : Position :=
  match t.val with
  | 0 => x
  | 1 => (-x.2, x.1+x.2)
  | 2 => (-x.1-x.2, x.1)
  | 3 => (-x.1, -x.2)
  | 4 => (x.2, -x.1-x.2)
  | _ => (x.1+x.2, -x.1)

def rotateTurn (t d : Fin 6) : Fin 6 :=
  ⟨(t.val+d.val)%6, Nat.mod_lt _ (by decide)⟩

def inverseTurn (t : Fin 6) : Fin 6 :=
  ⟨(6-t.val)%6, Nat.mod_lt _ (by decide)⟩

def rotateState (t : Fin 6) (s : State) : State := (s.1, rotateTurn t s.2)

def rotateEntry (t : Fin 6) (x : Position × State) : Position × State :=
  (rotatePosition t x.1, rotateState t x.2)

private theorem six_cases {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) :
    ∀ t, P t :=
  Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3
    (Fin.cases h4 (Fin.cases h5 (fun t => Fin.elim0 t))))))

theorem rotatePosition_add : ∀ t : Fin 6, ∀ x y : Position,
    rotatePosition t (addPos x y) = addPos (rotatePosition t x) (rotatePosition t y) := by
  apply six_cases
  · intro x y
    change (x.1+y.1, x.2+y.2) = ((x.1)+(y.1), (x.2)+(y.2))
    apply Prod.ext <;> dsimp <;> omega
  · intro x y
    change (-(x.2+y.2), (x.1+y.1)+(x.2+y.2)) = ((-(x.2))+(-(y.2)), ((x.1)+(x.2))+((y.1)+(y.2)))
    apply Prod.ext <;> dsimp <;> omega
  · intro x y
    change (-(x.1+y.1)-(x.2+y.2), x.1+y.1) = ((-(x.1)-(x.2))+(-(y.1)-(y.2)), (x.1)+(y.1))
    apply Prod.ext <;> dsimp <;> omega
  · intro x y
    change (-(x.1+y.1), -(x.2+y.2)) = ((-(x.1))+(-(y.1)), (-(x.2))+(-(y.2)))
    apply Prod.ext <;> dsimp <;> omega
  · intro x y
    change (x.2+y.2, -(x.1+y.1)-(x.2+y.2)) = ((x.2)+(y.2), (-(x.1)-(x.2))+(-(y.1)-(y.2)))
    apply Prod.ext <;> dsimp <;> omega
  · intro x y
    change ((x.1+y.1)+(x.2+y.2), -(x.1+y.1)) = (((x.1)+(x.2))+((y.1)+(y.2)), (-(x.1))+(-(y.1)))
    apply Prod.ext <;> dsimp <;> omega

theorem rotatePosition_inverse : ∀ t : Fin 6, ∀ x : Position,
    rotatePosition (inverseTurn t) (rotatePosition t x) = x := by
  apply six_cases
  · intro x
    change (x.1, x.2) = x
    apply Prod.ext <;> dsimp <;> omega
  · intro x
    change ((-(x.2))+((x.1)+(x.2)), -(-(x.2))) = x
    apply Prod.ext <;> dsimp <;> omega
  · intro x
    change (x.1, -(-(x.1)-(x.2))-(x.1)) = x
    apply Prod.ext <;> dsimp <;> omega
  · intro x
    change (-(-(x.1)), -(-(x.2))) = x
    apply Prod.ext <;> dsimp <;> omega
  · intro x
    change (-(x.2)-(-(x.1)-(x.2)), x.2) = x
    apply Prod.ext <;> dsimp <;> omega
  · intro x
    change (-(-(x.1)), ((x.1)+(x.2))+(-(x.1))) = x
    apply Prod.ext <;> dsimp <;> omega

theorem inverseTurn_involutive : ∀ t : Fin 6, inverseTurn (inverseTurn t) = t := by decide

theorem rotatePosition_inverse_right (t : Fin 6) (x : Position) :
    rotatePosition t (rotatePosition (inverseTurn t) x) = x := by
  have h := rotatePosition_inverse (inverseTurn t) x
  rw [inverseTurn_involutive] at h
  exact h

theorem rotatePosition_injective (t : Fin 6) (x y : Position)
    (h : rotatePosition t x = rotatePosition t y) : x = y := by
  have h' := congrArg (rotatePosition (inverseTurn t)) h
  simpa only [rotatePosition_inverse] using h'

theorem rotateTurn_inverse : ∀ t d : Fin 6,
    rotateTurn (inverseTurn t) (rotateTurn t d) = d := by decide

theorem rotateTurn_inverse_right : ∀ t d : Fin 6,
    rotateTurn t (rotateTurn (inverseTurn t) d) = d := by decide

theorem rotateTurn_opposite : ∀ t d : Fin 6,
    rotateTurn t (opposite d) = opposite (rotateTurn t d) := by decide

theorem rotatePosition_direction : ∀ t d : Fin 6,
    rotatePosition t (direction d) = direction (rotateTurn t d) := by decide

private theorem facing_index_rotation : ∀ t d r : Fin 6,
    ((rotateTurn t d).val + 6 - (rotateTurn t r).val)%6 = (d.val+6-r.val)%6 := by decide

theorem facingMark_rotate (t : Fin 6) (x : Position × State) (d : Fin 6) :
    facingMark (placed (rotateEntry t x)) (rotateTurn t d) = facingMark (placed x) d := by
  simp only [facingMark, placed, rotateEntry, rotateState, facing_index_rotation]

theorem rotateState_inverse (t : Fin 6) (s : State) :
    rotateState (inverseTurn t) (rotateState t s) = s := by
  apply Prod.ext
  · rfl
  · exact rotateTurn_inverse t s.2

theorem rotateEntry_inverse (t : Fin 6) (x : Position × State) :
    rotateEntry (inverseTurn t) (rotateEntry t x) = x := by
  apply Prod.ext
  · exact rotatePosition_inverse t x.1
  · exact rotateState_inverse t x.2

/-- All actual edges and signed marks are preserved by the simultaneous
position/frame rotation, including the wraparound turn convention. -/
theorem matches_rotate (t : Fin 6) (x y : Position × State) (h : Matches x y) :
    Matches (rotateEntry t x) (rotateEntry t y) := by
  refine ⟨fun he => h.1 (rotatePosition_injective t x.1 y.1 he), ?_⟩
  intro d hd
  let e := rotateTurn (inverseTurn t) d
  have he : rotateTurn t e = d := rotateTurn_inverse_right t d
  have hadj : y.1 = addPos x.1 (direction e) := by
    apply rotatePosition_injective t
    rw [rotatePosition_add, rotatePosition_direction, he]
    exact hd
  have hm := h.2 e hadj
  have ha := facingMark_rotate t x e
  have hb := facingMark_rotate t y (opposite e)
  rw [rotateTurn_opposite, he] at hb
  rw [he] at ha
  exact ha.trans (hm.trans (congrArg (fun z : Int => -z) hb.symm))

theorem matches_rotate_iff (t : Fin 6) (x y : Position × State) :
    Matches (rotateEntry t x) (rotateEntry t y) ↔ Matches x y := by
  constructor
  · intro h
    have h' := matches_rotate (inverseTurn t) _ _ h
    simpa only [rotateEntry_inverse] using h'
  · exact matches_rotate t x y

/-- The action on fields rotates both support coordinates and tile turns. -/
def rotatedField (t : Fin 6) (f : Position → State) : Position → State :=
  fun x => rotateState t (f (rotatePosition (inverseTurn t) x))

theorem rotatedField_globallyLegal (t : Fin 6) (f : Position → State)
    (hf : GloballyLegal f) : GloballyLegal (rotatedField t f) := by
  intro x y hxy
  have h := hf (rotatePosition (inverseTurn t) x) (rotatePosition (inverseTurn t) y)
    (fun he => hxy (rotatePosition_injective (inverseTurn t) x y he))
  have hr := matches_rotate t _ _ h
  simpa only [rotateEntry, rotatePosition_inverse_right, rotatedField] using hr

theorem rotatePosition_zero : ∀ t : Fin 6, rotatePosition t (0,0) = (0,0) := by decide

theorem rotateTurn_cancel_self : ∀ t : Fin 6, rotateTurn (inverseTurn t) t = 0 := by decide

/-- Every global marked-hexagon field has an exact turn-zero representative
at the origin, with its root kind unchanged. -/
theorem normalized_root (f : Position → State) :
    rotatedField (inverseTurn (f (0,0)).2) f (0,0) = ((f (0,0)).1, 0) := by
  simp only [rotatedField, rotatePosition_zero, rotateState, rotateTurn_cancel_self]

theorem normalized_globallyLegal (f : Position → State) (hf : GloballyLegal f) :
    GloballyLegal (rotatedField (inverseTurn (f (0,0)).2) f) :=
  rotatedField_globallyLegal _ f hf

end SpectreFinite.HexSearch
