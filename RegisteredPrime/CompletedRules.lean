module
public import Uniform.U4
@[expose] public section
namespace RegisteredPrime
open Uniform
structure Parameters where
  p : Nat
  prime : Uniform.IsPrime p
  odd : p ≠ 2
  mu : Nat
  g : Nat
  mu_nonzero : ¬ p ∣ mu
  mu_square : Uniform.IsSquareMod p mu
  g_nonzero : ¬ p ∣ g
  g_nonsquare : ¬ Uniform.IsSquareMod p g
abbrev Mask (p : Nat) := Fin p → Bool
def Proper {p : Nat} (A : Mask p) : Prop := ∃ i, A i = false
def NonemptyMask {p : Nat} (A : Mask p) : Prop := ∃ i, A i = true
def extendMask {p : Nat} (A : Mask p) (i : Nat) : Bool :=
  if h : i < p then A ⟨i, h⟩ else false
@[simp] theorem extendMask_at {p : Nat} (A : Mask p) (i : Fin p) :
    extendMask A i.val = A i := by simp [extendMask]
theorem extend_nonempty_proper {p : Nat} (A : Mask p)
    (hA : NonemptyMask A) (hp : Proper A) : NonemptyProperOn p (extendMask A) := by
  obtain ⟨i, hi⟩ := hA
  obtain ⟨j, hj⟩ := hp
  exact ⟨⟨i.val, i.isLt, by simpa using hi⟩, ⟨j.val, j.isLt, by simpa using hj⟩⟩
inductive Role (p : Nat) where
  | central
  | outer (A : Mask p) (proper : Proper A)
noncomputable def outerFrame (P : Parameters) (A : Mask P.p) : Frame := by
  classical
  exact if NonemptyMask A then lamChild P.p P.mu P.g (extendMask A)
  else scalarFrame P.p P.mu
noncomputable def childFrame (P : Parameters) : Role P.p → Frame
  | .central => scalarFrame P.p P.mu
  | .outer A _ => outerFrame P A
def childShift (P : Parameters) : Role P.p → Fin P.p → Int
  | .central, _ => 1
  | .outer A _, i => if A i then 4 else 0
theorem scalar_rotation (p mu : Nat) (hp : IsPrime p) (hp2 : p ≠ 2)
    (hmu0 : ¬ p ∣ mu) (hmu : IsSquareMod p mu) :
    IsRotation p (scalarFrame p mu) := by
  obtain ⟨hperm, hz⟩ := U3_zolotarev p mu hp hp2 hmu0
  have hs : permSign p (mulMap p mu) = 1 := by
    rcases neg_one_pow_cases (invCount p (mulMap p mu)) with h | h
    · exact h
    · have heuler : ((mu : Int) ^ ((p - 1) / 2)) % (p : Int) = (-1) % (p : Int) := by
        rw [← hz]
        exact congrArg (fun x : Int => x % (p : Int)) h
      exact False.elim (((U3_euler p mu hp hp2 hmu0).mp heuler) hmu)
  refine ⟨hperm, ?_⟩
  change permSign p (mulMap p mu) * signProd p (fun _ => false) = 1
  simp [hs, signProd_eq, negCount]
theorem outerFrame_rotation (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    IsRotation P.p (outerFrame P A) := by
  classical
  unfold outerFrame
  split
  · next hn =>
      exact ((U3_lambda_rotation P.p P.mu P.g P.prime P.odd P.mu_nonzero
        P.mu_square P.g_nonzero).mpr P.g_nonsquare) _ (extend_nonempty_proper A hn hA)
  · exact scalar_rotation P.p P.mu P.prime P.odd P.mu_nonzero P.mu_square
theorem all_child_frames_rotation (P : Parameters) (r : Role P.p) :
    IsRotation P.p (childFrame P r) := by
  cases r with
  | central => exact scalar_rotation P.p P.mu P.prime P.odd P.mu_nonzero P.mu_square
  | outer A hA => exact outerFrame_rotation P A hA
@[simp] theorem outerFrame_neg (P : Parameters) (A : Mask P.p) (i : Fin P.p) :
    (outerFrame P A).neg i.val = A i := by
  classical
  unfold outerFrame
  split
  · simp [lamChild]
  · next h =>
      have hi : A i = false := by
        cases he : A i
        · rfl
        · exact False.elim (h ⟨i, he⟩)
      simp [scalarFrame, hi]
@[simp] theorem empty_outer_frame (P : Parameters) :
    outerFrame P (fun _ => false) = scalarFrame P.p P.mu := by
  classical
  simp [outerFrame, NonemptyMask]
@[simp] theorem central_frame (P : Parameters) :
    childFrame P .central = scalarFrame P.p P.mu := rfl
noncomputable def childIndex (P : Parameters) (r : Role P.p) (i : Fin P.p) : Fin P.p :=
  ⟨(childFrame P r).perm i.val, (all_child_frames_rotation P r).1.1 _ i.isLt⟩
theorem childIndex_injective (P : Parameters) (r : Role P.p)
    (i j : Fin P.p) (h : childIndex P r i = childIndex P r j) : i = j := by
  apply Fin.ext
  exact (all_child_frames_rotation P r).1.2 _ _ i.isLt j.isLt (congrArg Fin.val h)
theorem childIndex_surjective (P : Parameters) (r : Role P.p) (j : Fin P.p) :
    ∃ i, childIndex P r i = j := by
  obtain ⟨i, hi, hij⟩ := (all_child_frames_rotation P r).1.surj j.val j.isLt
  exact ⟨⟨i, hi⟩, Fin.ext hij⟩
end RegisteredPrime
