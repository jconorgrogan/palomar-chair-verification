module

public import SpectreFinite.AxialFiniteBoxes

@[expose] public section


/-! Exact representative reduction modulo a vector with positive first
coordinate. A bounded square reduces to a rectangle of constant width and
linear height. This is arithmetic only; it does not assume an action is free. -/
namespace SpectreFinite.HexSearch

def scalePosition (n : Int) (v : Position) : Position := (n*v.1,n*v.2)

def reduceFirst (v x : Position) : Position :=
  (x.1 % v.1, x.2 - (x.1 / v.1)*v.2)

theorem reduceFirst_reconstruct (v x : Position) :
    addPos (reduceFirst v x) (scalePosition (x.1/v.1) v) = x := by
  apply Prod.ext
  · have h := Int.emod_add_mul_ediv x.1 v.1
    simp only [addPos,reduceFirst,scalePosition]
    rw [Int.mul_comm (x.1/v.1) v.1]
    exact h
  · simp only [addPos,reduceFirst,scalePosition]
    omega

theorem reduceFirst_second_bound (v x : Position) (R : Nat)
    (hq : x.1.natAbs ≤ R) (hr : x.2.natAbs ≤ R) :
    (reduceFirst v x).2.natAbs ≤ R*(v.2.natAbs+1) := by
  have hdiv := Int.natAbs_ediv_le_natAbs x.1 v.1
  have hm : ((x.1/v.1)*v.2).natAbs ≤ R*v.2.natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul_right _ (Nat.le_trans hdiv hq)
  have hs := Int.natAbs_sub_le x.2 ((x.1/v.1)*v.2)
  change (x.2-(x.1/v.1)*v.2).natAbs ≤ _
  calc
    _ ≤ x.2.natAbs + ((x.1/v.1)*v.2).natAbs := hs
    _ ≤ R+R*v.2.natAbs := Nat.add_le_add hr hm
    _ = R*(v.2.natAbs+1) := by simp [Nat.mul_add,Nat.add_comm]

def representativeRectangle (v : Position) (R : Nat) : List Position :=
  let K := R*(v.2.natAbs+1)
  axialRectangle 0 (-(K:Int)) v.1.toNat (2*K+1)

theorem reduceFirst_mem_rectangle (v x : Position) (hv : 0 < v.1) (R : Nat)
    (hq : x.1.natAbs ≤ R) (hr : x.2.natAbs ≤ R) :
    reduceFirst v x ∈ representativeRectangle v R := by
  apply (mem_axialRectangle_iff _ _ _ _ _).mpr
  have hlow := Int.emod_nonneg x.1 (by omega : v.1 ≠ 0)
  have hhigh := Int.emod_lt_of_pos x.1 hv
  have hsecond := reduceFirst_second_bound v x R hq hr
  change 0 ≤ x.1 % v.1 ∧ x.1 % v.1 < 0+(v.1.toNat:Int) ∧ _
  refine ⟨hlow,by omega,?_⟩
  omega

theorem representativeRectangle_length (v : Position) (R : Nat) :
    (representativeRectangle v R).length =
      v.1.toNat*(2*(R*(v.2.natAbs+1))+1) :=
  axialRectangle_length _ _ _ _

theorem representativeRectangle_linear_bound (v : Position) (R : Nat) :
    (representativeRectangle v R).length ≤
      (v.1.toNat*(2*(v.2.natAbs+1)+1))*(R+1) := by
  rw [representativeRectangle_length]
  have h : 2*(R*(v.2.natAbs+1))+1 ≤ (2*(v.2.natAbs+1)+1)*(R+1) := by
    let C := v.2.natAbs+1
    change 2*(R*C)+1 ≤ (2*C+1)*(R+1)
    have he : 2*(R*C) = (2*C)*R := by ac_rfl
    have hh : (2*C+1)*(R+1) = (2*C)*R+R+(2*C+1) := by
      rw [Nat.mul_add (2*C+1) R 1, Nat.add_mul (2*C) 1 R]
      simp only [Nat.mul_one,Nat.one_mul]
    rw [he,hh]
    omega
  have hh := Nat.mul_le_mul_left v.1.toNat h
  simpa only [Nat.mul_assoc] using hh

end SpectreFinite.HexSearch
