module

public import Init

@[expose] public section


/-! Integer iteration of a specified invertible step; no freeness assumption. -/
namespace SpectreFinite.HexSearch

structure ReversibleStep (X : Type u) where
  forward : X → X
  backward : X → X
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ x, forward (backward x) = x

namespace ReversibleStep

def iterate (f : X → X) : Nat → X → X
  | 0, x => x
  | n+1, x => f (iterate f n x)

def act (A : ReversibleStep X) : Int → X → X
  | .ofNat n, x => iterate A.forward n x
  | .negSucc n, x => iterate A.backward (n+1) x

@[simp] theorem act_zero (A : ReversibleStep X) (x : X) : A.act 0 x = x := rfl
@[simp] theorem act_one (A : ReversibleStep X) (x : X) : A.act 1 x = A.forward x := rfl
@[simp] theorem act_neg_one (A : ReversibleStep X) (x : X) : A.act (-1) x = A.backward x := rfl

theorem act_succ (A : ReversibleStep X) (n : Int) (x : X) :
    A.act (n+1) x = A.forward (A.act n x) := by
  cases n with
  | ofNat n =>
    have h : (Int.ofNat n)+1 = Int.ofNat (n+1) := rfl
    rw [h]
    rfl
  | negSucc n =>
    cases n with
    | zero => exact (A.forward_backward x).symm
    | succ n =>
      have h : (Int.negSucc (n+1))+1 = Int.negSucc n := by omega
      rw [h]
      exact (A.forward_backward (iterate A.backward (n+1) x)).symm

theorem act_pred (A : ReversibleStep X) (n : Int) (x : X) :
    A.act (n-1) x = A.backward (A.act n x) := by
  have h := A.act_succ (n-1) x
  have hn : n-1+1 = n := by omega
  rw [hn] at h
  rw [h, A.backward_forward]

private theorem integer_induction {P : Int → Prop} (hz : P 0)
    (hs : ∀ n, P n → P (n+1)) (hp : ∀ n, P n → P (n-1)) : ∀ n, P n := by
  intro n
  cases n with
  | ofNat n =>
    induction n with
    | zero => exact hz
    | succ n ih =>
      have h := hs (Int.ofNat n) ih
      have hn : Int.ofNat n + 1 = Int.ofNat (n+1) := rfl
      rwa [hn] at h
  | negSucc n =>
    induction n with
    | zero => exact hp 0 hz
    | succ n ih =>
      have h := hp (Int.negSucc n) ih
      have hn : Int.negSucc n - 1 = Int.negSucc (n+1) := by omega
      rwa [hn] at h

theorem act_add (A : ReversibleStep X) (a b : Int) (x : X) :
    A.act (a+b) x = A.act a (A.act b x) := by
  apply integer_induction (P := fun a => A.act (a+b) x = A.act a (A.act b x))
  · simp
  · intro n ih
    have hn : n+1+b = (n+b)+1 := by omega
    rw [hn, A.act_succ, A.act_succ, ih]
  · intro n ih
    have hn : n-1+b = (n+b)-1 := by omega
    rw [hn, A.act_pred, A.act_pred, ih]

theorem map_backward (A : ReversibleStep X) (B : ReversibleStep Y)
    (f : X → Y) (hf : ∀ x, f (A.forward x) = B.forward (f x)) (x : X) :
    f (A.backward x) = B.backward (f x) := by
  have h := congrArg B.backward (hf (A.backward x))
  rw [A.forward_backward, B.backward_forward] at h
  exact h.symm

private theorem map_iterate (f : X → Y) (a : X → X) (b : Y → Y)
    (h : ∀ x, f (a x) = b (f x)) (n : Nat) (x : X) :
    f (iterate a n x) = iterate b n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate, h, ih]

theorem map_act (A : ReversibleStep X) (B : ReversibleStep Y)
    (f : X → Y) (hf : ∀ x, f (A.forward x) = B.forward (f x))
    (n : Int) (x : X) : f (A.act n x) = B.act n (f x) := by
  cases n with
  | ofNat n => exact map_iterate f A.forward B.forward hf n x
  | negSucc n => exact map_iterate f A.backward B.backward (A.map_backward B f hf) (n+1) x

theorem act_commute (A B : ReversibleStep X)
    (h : ∀ x, A.forward (B.forward x) = B.forward (A.forward x))
    (a b : Int) (x : X) : A.act a (B.act b x) = B.act b (A.act a x) := by
  have hb : ∀ x, B.act b (A.forward x) = A.forward (B.act b x) :=
    fun x => (B.map_act B A.forward h b x).symm
  exact (A.map_act A (B.act b) hb a x).symm

end ReversibleStep
end SpectreFinite.HexSearch
