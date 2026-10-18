module

public import SpectreFinite.OverlapPruning
public import SpectreFinite.RadiusOneSearch

@[expose] public section


/-! Small sound certificates for overlap pruning. Balanced signature trees
are untrusted data: all required coverage and exclusions are proved.
No completeness, existence, physical-tiling, or parent claim is assumed. -/
namespace SpectreFinite.HexSearch.SignaturePruning

structure Window where
  s0 : State
  s1 : State
  s2 : State
  s3 : State
  s4 : State
  s5 : State
  s6 : State
  deriving DecidableEq

def windowPatch (w : Window) : Patch :=
  [((-1,1),w.s0),((0,1),w.s1),((1,0),w.s2),((1,-1),w.s3),((0,-1),w.s4),((-1,0),w.s5),((0,0),w.s6)]

theorem windowPatch_mem0 (w : Window) : ((-1,1),w.s0) ∈ windowPatch w := by
  simp [windowPatch]

theorem windowPatch_mem1 (w : Window) : ((0,1),w.s1) ∈ windowPatch w := by
  simp [windowPatch]

theorem windowPatch_mem2 (w : Window) : ((1,0),w.s2) ∈ windowPatch w := by
  simp [windowPatch]

theorem windowPatch_mem3 (w : Window) : ((1,-1),w.s3) ∈ windowPatch w := by
  simp [windowPatch]

theorem windowPatch_mem4 (w : Window) : ((0,-1),w.s4) ∈ windowPatch w := by
  simp [windowPatch]

theorem windowPatch_mem5 (w : Window) : ((-1,0),w.s5) ∈ windowPatch w := by
  simp [windowPatch]

theorem windowPatch_mem6 (w : Window) : ((0,0),w.s6) ∈ windowPatch w := by
  simp [windowPatch]

def stateCode (s : State) : Nat := 6 * s.1.val + s.2.val

def code4 (a b c d : State) : Nat :=
  ((stateCode a * 54 + stateCode b) * 54 + stateCode c) * 54 + stateCode d

def leftSignature (d : Fin 6) (w : Window) : Nat :=
  match d.val with
  | 0 => code4 w.s5 w.s0 w.s4 w.s6
  | 1 => code4 w.s5 w.s4 w.s6 w.s3
  | 2 => code4 w.s4 w.s6 w.s3 w.s2
  | 3 => code4 w.s6 w.s1 w.s3 w.s2
  | 4 => code4 w.s0 w.s6 w.s1 w.s2
  | _ => code4 w.s5 w.s0 w.s6 w.s1

def rightSignature (d : Fin 6) (w : Window) : Nat :=
  match d.val with
  | 0 => code4 w.s6 w.s1 w.s3 w.s2
  | 1 => code4 w.s0 w.s6 w.s1 w.s2
  | 2 => code4 w.s5 w.s0 w.s6 w.s1
  | 3 => code4 w.s5 w.s0 w.s4 w.s6
  | 4 => code4 w.s5 w.s4 w.s6 w.s3
  | _ => code4 w.s4 w.s6 w.s3 w.s2

theorem overlap_signature (a b : Window) : ∀ d : Fin 6,
    overlap (windowPatch a) (windowPatch b) (direction d) = true →
      leftSignature d a = rightSignature d b := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro h
    have ho := (overlap_iff _ _ _).mp h
    have h0 : a.s5 = b.s6 := ho _ (windowPatch_mem5 a) _ (windowPatch_mem6 b) (by rfl)
    have h1 : a.s0 = b.s1 := ho _ (windowPatch_mem0 a) _ (windowPatch_mem1 b) (by rfl)
    have h2 : a.s4 = b.s3 := ho _ (windowPatch_mem4 a) _ (windowPatch_mem3 b) (by rfl)
    have h3 : a.s6 = b.s2 := ho _ (windowPatch_mem6 a) _ (windowPatch_mem2 b) (by rfl)
    change code4 a.s5 a.s0 a.s4 a.s6 = code4 b.s6 b.s1 b.s3 b.s2
    rw [h0,h1,h2,h3]
  · intro h
    have ho := (overlap_iff _ _ _).mp h
    have h0 : a.s5 = b.s0 := ho _ (windowPatch_mem5 a) _ (windowPatch_mem0 b) (by rfl)
    have h1 : a.s4 = b.s6 := ho _ (windowPatch_mem4 a) _ (windowPatch_mem6 b) (by rfl)
    have h2 : a.s6 = b.s1 := ho _ (windowPatch_mem6 a) _ (windowPatch_mem1 b) (by rfl)
    have h3 : a.s3 = b.s2 := ho _ (windowPatch_mem3 a) _ (windowPatch_mem2 b) (by rfl)
    change code4 a.s5 a.s4 a.s6 a.s3 = code4 b.s0 b.s6 b.s1 b.s2
    rw [h0,h1,h2,h3]
  · intro h
    have ho := (overlap_iff _ _ _).mp h
    have h0 : a.s4 = b.s5 := ho _ (windowPatch_mem4 a) _ (windowPatch_mem5 b) (by rfl)
    have h1 : a.s6 = b.s0 := ho _ (windowPatch_mem6 a) _ (windowPatch_mem0 b) (by rfl)
    have h2 : a.s3 = b.s6 := ho _ (windowPatch_mem3 a) _ (windowPatch_mem6 b) (by rfl)
    have h3 : a.s2 = b.s1 := ho _ (windowPatch_mem2 a) _ (windowPatch_mem1 b) (by rfl)
    change code4 a.s4 a.s6 a.s3 a.s2 = code4 b.s5 b.s0 b.s6 b.s1
    rw [h0,h1,h2,h3]
  · intro h
    have ho := (overlap_iff _ _ _).mp h
    have h0 : a.s6 = b.s5 := ho _ (windowPatch_mem6 a) _ (windowPatch_mem5 b) (by rfl)
    have h1 : a.s1 = b.s0 := ho _ (windowPatch_mem1 a) _ (windowPatch_mem0 b) (by rfl)
    have h2 : a.s3 = b.s4 := ho _ (windowPatch_mem3 a) _ (windowPatch_mem4 b) (by rfl)
    have h3 : a.s2 = b.s6 := ho _ (windowPatch_mem2 a) _ (windowPatch_mem6 b) (by rfl)
    change code4 a.s6 a.s1 a.s3 a.s2 = code4 b.s5 b.s0 b.s4 b.s6
    rw [h0,h1,h2,h3]
  · intro h
    have ho := (overlap_iff _ _ _).mp h
    have h0 : a.s0 = b.s5 := ho _ (windowPatch_mem0 a) _ (windowPatch_mem5 b) (by rfl)
    have h1 : a.s6 = b.s4 := ho _ (windowPatch_mem6 a) _ (windowPatch_mem4 b) (by rfl)
    have h2 : a.s1 = b.s6 := ho _ (windowPatch_mem1 a) _ (windowPatch_mem6 b) (by rfl)
    have h3 : a.s2 = b.s3 := ho _ (windowPatch_mem2 a) _ (windowPatch_mem3 b) (by rfl)
    change code4 a.s0 a.s6 a.s1 a.s2 = code4 b.s5 b.s4 b.s6 b.s3
    rw [h0,h1,h2,h3]
  · intro h
    have ho := (overlap_iff _ _ _).mp h
    have h0 : a.s5 = b.s4 := ho _ (windowPatch_mem5 a) _ (windowPatch_mem4 b) (by rfl)
    have h1 : a.s0 = b.s6 := ho _ (windowPatch_mem0 a) _ (windowPatch_mem6 b) (by rfl)
    have h2 : a.s6 = b.s3 := ho _ (windowPatch_mem6 a) _ (windowPatch_mem3 b) (by rfl)
    have h3 : a.s1 = b.s2 := ho _ (windowPatch_mem1 a) _ (windowPatch_mem2 b) (by rfl)
    change code4 a.s5 a.s0 a.s6 a.s1 = code4 b.s4 b.s6 b.s3 b.s2
    rw [h0,h1,h2,h3]

inductive KeyTree where
  | empty
  | node (key : Nat) (left right : KeyTree)

def accepts : KeyTree → Nat → Bool
  | .empty, _ => false
  | .node k left right, n =>
      if n = k then true else if n < k then accepts left n else accepts right n

/-- The tree may be any over-approximation. Its construction is not trusted. -/
def Covers (trees : Fin 6 → KeyTree) (family : List Window) : Prop :=
  ∀ w ∈ family, ∀ d : Fin 6, accepts (trees d) (rightSignature d w) = true

inductive Verdict where
  | keep (window : Window)
  | reject (window : Window) (direction : Fin 6)

def Verdict.window : Verdict → Window
  | .keep w => w
  | .reject w _ => w

def Verdict.kept : Verdict → Option Window
  | .keep w => some w
  | .reject _ _ => none

def checkVerdict (trees : Fin 6 → KeyTree) : Verdict → Bool
  | .keep _ => true
  | .reject w d => !(accepts (trees d) (leftSignature d w))

def checkCoverage (trees : Fin 6 → KeyTree) (v : Verdict) : Bool :=
  (List.finRange 6).all (fun d => accepts (trees d) (rightSignature d v.window))

def checkRows (trees : Fin 6 → KeyTree) (rows : List Verdict) : Bool :=
  rows.all (fun v => checkCoverage trees v && checkVerdict trees v)

/-- A certificate round retains every occurring window in the input family.
Only coverage and rejection checks are needed; extension existence for kept
patches is deliberately not assumed. -/
theorem certified_round (trees : Fin 6 → KeyTree) (rows : List Verdict)
    (hcheck : checkRows trees rows = true)
    (f : Position → State)
    (hf : OccurrenceComplete f RadiusOne.positions
      ((rows.map Verdict.window).map windowPatch)) :
    OccurrenceComplete f RadiusOne.positions
      ((rows.filterMap Verdict.kept).map windowPatch) := by
  have hall := List.all_eq_true.mp hcheck
  have hcover : Covers trees (rows.map Verdict.window) := by
    intro w hw d
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    have hc := (Bool.and_eq_true_iff.mp (hall v hv)).1
    exact List.all_eq_true.mp hc d (by simp)
  intro center
  obtain ⟨w,hw,he⟩ := List.mem_map.mp (hf center)
  obtain ⟨v,hv,hvw⟩ := List.mem_map.mp hw
  cases v with
  | keep w' =>
      have hw' : w' = w := hvw
      subst w
      exact List.mem_map.mpr ⟨w',List.mem_filterMap.mpr ⟨.keep w',hv,rfl⟩,he⟩
  | reject w' d =>
      have hw' : w' = w := hvw
      subst w
      have hreject : accepts (trees d) (leftSignature d w') = false := by
        have h := (Bool.and_eq_true_iff.mp (hall (.reject w' d) hv)).2
        change (!accepts (trees d) (leftSignature d w')) = true at h
        cases he : accepts (trees d) (leftSignature d w') with
        | false => rfl
        | true => rw [he] at h; exact Bool.noConfusion h
      obtain ⟨q,hq,hqe⟩ := List.mem_map.mp (hf (addPos center (direction d)))
      have hov := extract_overlap f center (direction d) RadiusOne.positions RadiusOne.positions
      rw [← he, ← hqe] at hov
      have hs := overlap_signature w' q d hov
      have ha := hcover q hq d
      rw [← hs, hreject] at ha
      exact Bool.noConfusion ha

theorem checkRows_append (trees : Fin 6 → KeyTree) (a b : List Verdict)
    (ha : checkRows trees a = true) (hb : checkRows trees b = true) :
    checkRows trees (a ++ b) = true := by
  change (a ++ b).all _ = true
  rw [List.all_append]
  change (checkRows trees a && checkRows trees b) = true
  rw [ha,hb]
  rfl

end SpectreFinite.HexSearch.SignaturePruning
