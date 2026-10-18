module

public import SpectreFinite.FiniteBoundaryEstimate

@[expose] public section


/-! Every integer translation has a concrete unit-step word. This removes
an abstract word-representability premise from the finite boundary estimate. -/
namespace SpectreFinite.HexSearch.FiniteBoundaryEstimate

def horizontalWord : Int → List Position
  | .ofNat n => List.replicate n (1,0)
  | .negSucc n => List.replicate (n+1) (-1,0)

def verticalWord : Int → List Position
  | .ofNat n => List.replicate n (0,1)
  | .negSucc n => List.replicate (n+1) (0,-1)

def axialWord (v : Position) : List Position := horizontalWord v.1 ++ verticalWord v.2

def primitiveSteps : List Position := [(1,0),(-1,0),(0,1),(0,-1)]

theorem wordDisplacement_append (xs ys : List Position) :
    wordDisplacement (xs++ys) = addPos (wordDisplacement xs) (wordDisplacement ys) := by
  induction xs with
  | nil => simp [wordDisplacement,addPos]
  | cons s ss ih => simp only [List.cons_append,wordDisplacement,ih,addPos_assoc]

theorem wordDisplacement_replicate (n : Nat) (v : Position) :
    wordDisplacement (List.replicate n v) = ((n : Int)*v.1,(n : Int)*v.2) := by
  induction n with
  | zero => simp [wordDisplacement]
  | succ n ih =>
    simp only [List.replicate_succ,wordDisplacement,ih,addPos,Int.natCast_add,
      Int.natCast_one,Int.add_mul,Int.one_mul]
    apply Prod.ext <;> omega

theorem horizontalWord_displacement (q : Int) :
    wordDisplacement (horizontalWord q) = (q,0) := by
  cases q with
  | ofNat n => simp [horizontalWord,wordDisplacement_replicate]
  | negSucc n =>
    rw [horizontalWord,wordDisplacement_replicate]
    apply Prod.ext <;> simp <;> omega

theorem verticalWord_displacement (q : Int) :
    wordDisplacement (verticalWord q) = (0,q) := by
  cases q with
  | ofNat n => simp [verticalWord,wordDisplacement_replicate]
  | negSucc n =>
    rw [verticalWord,wordDisplacement_replicate]
    apply Prod.ext <;> simp <;> omega

theorem axialWord_displacement (v : Position) : wordDisplacement (axialWord v) = v := by
  simp [axialWord,wordDisplacement_append,horizontalWord_displacement,
    verticalWord_displacement,addPos]

theorem axialWord_length (v : Position) : (axialWord v).length = v.1.natAbs + v.2.natAbs := by
  rcases v with ⟨q,r⟩
  cases q <;> cases r <;> simp [axialWord,horizontalWord,verticalWord]

theorem axialWord_steps (v : Position) : axialWord v ⊆ primitiveSteps := by
  rcases v with ⟨q,r⟩
  cases q <;> cases r <;>
    simp [axialWord,horizontalWord,verticalWord,primitiveSteps,List.subset_def]
  all_goals intro a b h; omega

theorem primitiveSteps_directions : ∀ s ∈ primitiveSteps, ∃ d : Fin 6, direction d = s := by
  decide

/-- The bound now uses the actual Manhattan length of an arbitrary axial
translation, with no supplied path or generation hypothesis. -/
theorem cardinal_le_axial_boundary (A B : List Position) (ha : A.Nodup)
    (v : Position) (hb : ∀ s ∈ primitiveSteps, escape A s ⊆ B)
    (hd : ∀ x ∈ A, addPos x v ∉ A) :
    A.length ≤ (v.1.natAbs+v.2.natAbs)*B.length := by
  have h := cardinal_le_word_boundary A B ha (axialWord v)
    (fun s hs => hb s (axialWord_steps v hs)) (by simpa only [axialWord_displacement] using hd)
  rwa [axialWord_length] at h

end SpectreFinite.HexSearch.FiniteBoundaryEstimate
