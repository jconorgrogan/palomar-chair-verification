module

public import SpectreFinite.AxialQuotientReduction
public import SpectreFinite.HexStepAction

@[expose] public section


/-! A coarse finite-fiber cover of the native axial lattice forces an axial
integer action to have trivial stabilizers at its specified root. The cover
and linear address bound are explicit hypotheses; freeness, transitivity,
and a coordinate chart on the acted-on type are not hypotheses. -/
namespace SpectreFinite.HexSearch

structure AxialAction (X : Type u) where
  act : Position → X → X
  zero : ∀ x, act (0,0) x = x
  add : ∀ u v x, act (addPos u v) x = act u (act v x)

namespace AxialAction

variable (A : AxialAction X)

def negVector (v : Position) : Position := (-v.1,-v.2)
def swapVector (v : Position) : Position := (v.2,v.1)

theorem kernel_neg (root : X) (v : Position) (h : A.act v root = root) :
    A.act (negVector v) root = root := by
  have hh := congrArg (A.act (negVector v)) h
  rw [← A.add] at hh
  have he : addPos (negVector v) v = (0,0) := by
    apply Prod.ext <;> dsimp [addPos,negVector] <;> omega
  rw [he,A.zero] at hh
  exact hh.symm

theorem kernel_nat_scale (root : X) (v : Position) (h : A.act v root = root)
    (n : Nat) : A.act (scalePosition (n:Int) v) root = root := by
  induction n with
  | zero => simpa [scalePosition] using A.zero root
  | succ n ih =>
    have he : scalePosition ((n+1:Nat):Int) v =
        addPos v (scalePosition (n:Int) v) := by
      apply Prod.ext <;> simp [scalePosition,addPos,Int.add_mul,Int.add_comm]
    rw [he,A.add,ih,h]

theorem kernel_scale (root : X) (v : Position) (h : A.act v root = root)
    (n : Int) : A.act (scalePosition n v) root = root := by
  cases n with
  | ofNat n => exact A.kernel_nat_scale root v h n
  | negSucc n =>
    have hn : scalePosition (Int.negSucc n) v =
        negVector (scalePosition ((n+1:Nat):Int) v) := by
      apply Prod.ext <;> simp [scalePosition,negVector,Int.negSucc_eq,Int.neg_mul]
    rw [hn]
    exact A.kernel_neg root _ (A.kernel_nat_scale root v h (n+1))

theorem reduceFirst_same_orbit (root : X) (v x : Position)
    (h : A.act v root = root) :
    A.act (reduceFirst v x) root = A.act x root := by
  have hs := A.kernel_scale root v h (x.1/v.1)
  have ha := A.add (reduceFirst v x) (scalePosition (x.1/v.1) v) root
  rw [reduceFirst_reconstruct,hs] at ha
  exact ha.symm

private theorem flatMap_length_bound (xs : List Position) (f : Position → List Position)
    (M : Nat) (h : ∀ x, (f x).length ≤ M) :
    (xs.flatMap f).length ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,
      Nat.one_mul]
    have hh := h x
    omega

/-- The finite counting contradiction for a kernel vector with positive first
coordinate. This is the only place where growth and the actual cover are used. -/
theorem no_positive_first_kernel (root : X) (fiber : X → List Position)
    (address : Position → Position) (M : Nat)
    (fiber_bound : ∀ x, (fiber x).length ≤ M)
    (cover : ∀ p, p ∈ fiber (A.act (address p) root))
    (address_bound : ∀ n p, p ∈ positiveSquare n →
      (address p).1.natAbs ≤ 2*n ∧ (address p).2.natAbs ≤ 2*n)
    (v : Position) (hv : 0 < v.1) (kernel : A.act v root = root) : False := by
  let C := v.1.toNat*(2*(v.2.natAbs+1)+1)
  have hcount : ∀ n : Nat, (n+1)*(n+1) ≤ (M*C)*(2*n+1) := by
    intro n
    let reps := representativeRectangle v (2*n)
    let cells := reps.flatMap (fun w => fiber (A.act w root))
    have hsub : positiveSquare n ⊆ cells := by
      intro p hp
      have hb := address_bound n p hp
      apply List.mem_flatMap.mpr
      refine ⟨reduceFirst v (address p),?_,?_⟩
      · exact reduceFirst_mem_rectangle v (address p) hv (2*n) hb.1 hb.2
      · rw [A.reduceFirst_same_orbit root v (address p) kernel]
        exact cover p
    have hsq := (positiveSquare_nodup n).length_le_of_subset hsub
    have hlen := flatMap_length_bound reps (fun w => fiber (A.act w root)) M
      (fun w => fiber_bound (A.act w root))
    have hrep := representativeRectangle_linear_bound v (2*n)
    rw [positiveSquare_length] at hsq
    calc
      (n+1)*(n+1) ≤ cells.length := hsq
      _ ≤ reps.length*M := hlen
      _ ≤ (C*(2*n+1))*M := Nat.mul_le_mul_right M hrep
      _ = (M*C)*(2*n+1) := by ac_rfl
  let K := M*C
  have hc := hcount (2*K)
  change (2*K+1)*(2*K+1) ≤ K*(2*(2*K)+1) at hc
  have hu : K*(2*(2*K)+1) ≤ (2*K)*(2*K+1) := by
    calc
      _ ≤ K*(2*(2*K+1)) := Nat.mul_le_mul_left K (by omega)
      _ = (2*K)*(2*K+1) := by ac_rfl
  have hl : (2*K)*(2*K+1) < (2*K+1)*(2*K+1) :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  omega

/-- Exchange the two coordinate directions of an axial action. -/
def swap : AxialAction X where
  act v x := A.act (swapVector v) x
  zero := A.zero
  add u v x := A.add (swapVector u) (swapVector v) x

/-- Uniformly finite fibers, actual coverage, and the specified linear bound
on native-cell addresses imply that every root stabilizer is zero. -/
theorem kernel_eq_zero (root : X) (fiber : X → List Position)
    (address : Position → Position) (M : Nat)
    (fiber_bound : ∀ x, (fiber x).length ≤ M)
    (cover : ∀ p, p ∈ fiber (A.act (address p) root))
    (address_bound : ∀ n p, p ∈ positiveSquare n →
      (address p).1.natAbs ≤ 2*n ∧ (address p).2.natAbs ≤ 2*n)
    (v : Position) (kernel : A.act v root = root) : v = (0,0) := by
  have hfirst : v.1 = 0 := by
    have hnpos : ¬ 0 < v.1 := fun hv =>
      A.no_positive_first_kernel root fiber address M fiber_bound cover address_bound v hv kernel
    have hnneg : ¬ v.1 < 0 := by
      intro hv
      exact A.no_positive_first_kernel root fiber address M fiber_bound cover address_bound
        (negVector v) (by dsimp [negVector]; omega) (A.kernel_neg root v kernel)
    omega
  have hcover : ∀ p, p ∈ fiber (A.swap.act (swapVector (address p)) root) := cover
  have hbound : ∀ n p, p ∈ positiveSquare n →
      (swapVector (address p)).1.natAbs ≤ 2*n ∧
      (swapVector (address p)).2.natAbs ≤ 2*n := by
    intro n p hp
    exact ⟨(address_bound n p hp).2,(address_bound n p hp).1⟩
  have hk : A.swap.act (swapVector v) root = root := kernel
  have hsecond : v.2 = 0 := by
    have hnpos : ¬ 0 < v.2 := by
      intro hv
      exact A.swap.no_positive_first_kernel root fiber (fun p => swapVector (address p)) M
        fiber_bound hcover hbound (swapVector v) hv hk
    have hnneg : ¬ v.2 < 0 := by
      intro hv
      exact A.swap.no_positive_first_kernel root fiber (fun p => swapVector (address p)) M
        fiber_bound hcover hbound (negVector (swapVector v))
        (by dsimp [negVector,swapVector]; omega)
        (A.swap.kernel_neg root (swapVector v) hk)
    omega
  exact Prod.ext hfirst hsecond

/-- The orbit map is injective, derived from finite growth rather than assumed. -/
theorem orbit_injective (root : X) (fiber : X → List Position)
    (address : Position → Position) (M : Nat)
    (fiber_bound : ∀ x, (fiber x).length ≤ M)
    (cover : ∀ p, p ∈ fiber (A.act (address p) root))
    (address_bound : ∀ n p, p ∈ positiveSquare n →
      (address p).1.natAbs ≤ 2*n ∧ (address p).2.natAbs ≤ 2*n) :
    Function.Injective (fun v => A.act v root) := by
  intro u v h
  have hh := congrArg (A.act (negVector v)) h
  rw [← A.add,← A.add] at hh
  have he : addPos (negVector v) v = (0,0) := by
    apply Prod.ext <;> dsimp [addPos,negVector] <;> omega
  rw [he,A.zero] at hh
  have hz := A.kernel_eq_zero root fiber address M fiber_bound cover address_bound _ hh
  have hq := congrArg Prod.fst hz
  have hr := congrArg Prod.snd hz
  apply Prod.ext <;> dsimp [addPos,negVector] at hq hr ⊢ <;> omega

end AxialAction

/-- The locally derived hex-step translations satisfy exactly the action
axioms required by the finite-growth criterion. -/
def HexStepSystem.axialAction (S : HexStepSystem X) : AxialAction X where
  act := S.translate
  zero := S.translate_zero
  add := S.translate_add

end SpectreFinite.HexSearch
