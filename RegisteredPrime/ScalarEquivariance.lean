module
public import RegisteredPrime.PoseAlgebra
@[expose] public section
namespace RegisteredPrime
open Uniform
theorem support_card_congr {p : Nat} {A B : Nat → Bool}
    (h : ∀ i, i < p → A i = B i) : suppCard p A = suppCard p B := by
  exact countP_congr_range h
theorem support_sum_congr {p : Nat} {A B : Nat → Bool}
    (h : ∀ i, i < p → A i = B i) : suppSum p A = suppSum p B := by
  unfold suppSum
  rw [filter_sum_eq, filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]
theorem mean_congr_support {p : Nat} {A B : Nat → Bool}
    (h : ∀ i, i < p → A i = B i) : zA p A = zA p B := by
  unfold zA
  rw [support_card_congr h, support_sum_congr h]
theorem lamPerm_congr_support {p mu g : Nat} {A B : Nat → Bool}
    (h : ∀ i, i < p → A i = B i) (i : Nat) : lamPerm p mu g A i = lamPerm p mu g B i := by
  unfold lamPerm
  rw [support_card_congr h, mean_congr_support h]
@[simp] theorem central_index_value (P : Parameters) (i : Fin P.p) :
    ((arithmeticChild P .central).frame.perm i).val = (P.mu * i.val) % P.p := rfl
theorem central_inverse_value (P : Parameters) (mui : Nat) (hmu : (P.mu * mui) % P.p = 1)
    (i : Fin P.p) : ((arithmeticChild P .central).frame.inverse i).val = (mui * i.val) % P.p := by
  have hp0 : 0 < P.p := by have := P.prime.two_le; omega
  let j : Fin P.p := ⟨(mui * i.val) % P.p, Nat.mod_lt _ hp0⟩
  have h : (arithmeticChild P .central).frame.perm j = i := by
    apply Fin.ext
    exact empty_hole_carry P.p P.mu mui P.prime hmu i.val i.isLt
  have he : (arithmeticChild P .central).frame.inverse i = j := by
    calc
      _ = (arithmeticChild P .central).frame.inverse
          ((arithmeticChild P .central).frame.perm j) := by rw [h]
      _ = j := (arithmeticChild P .central).frame.left_inverse j
  exact congrArg Fin.val he
noncomputable def scalarRole (P : Parameters) (A : Mask P.p) : Mask P.p :=
  fun i => A ((arithmeticChild P .central).frame.inverse i)
@[simp] theorem scalarRole_at (P : Parameters) (A : Mask P.p) (i : Fin P.p) :
    scalarRole P A ((arithmeticChild P .central).frame.perm i) = A i := by
  simp [scalarRole, (arithmeticChild P .central).frame.left_inverse]
theorem scalarRole_proper (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    Proper (scalarRole P A) := by
  obtain ⟨i, hi⟩ := hA
  exact ⟨(arithmeticChild P .central).frame.perm i, by rw [scalarRole_at]; exact hi⟩
theorem scalarRole_nonempty (P : Parameters) (A : Mask P.p) (hA : NonemptyMask A) :
    NonemptyMask (scalarRole P A) := by
  obtain ⟨i, hi⟩ := hA
  exact ⟨(arithmeticChild P .central).frame.perm i, by rw [scalarRole_at]; exact hi⟩
theorem scalarRole_extend (P : Parameters) (A : Mask P.p) (mui : Nat)
    (hmu : (P.mu * mui) % P.p = 1) (i : Nat) (hi : i < P.p) :
    extendMask (scalarRole P A) i = scaleSupp P.p mui (extendMask A) i := by
  have hp0 : 0 < P.p := by have := P.prime.two_le; omega
  have hm := Nat.mod_lt (mui * i) hp0
  simp only [extendMask, hi, dite_true, scaleSupp, hm]
  change A ((arithmeticChild P .central).frame.inverse ⟨i, hi⟩) = A ⟨(mui * i) % P.p, hm⟩
  apply congrArg A
  apply Fin.ext
  exact central_inverse_value P mui hmu ⟨i, hi⟩
theorem scalar_covariant_permutation (p mu mui g : Nat) (hp : IsPrime p)
    (hmu : (mu * mui) % p = 1) (A : Nat → Bool) (hA : NonemptyProperOn p A)
    (i : Nat) (hi : i < p) :
    lamPerm p mu g (scaleSupp p mui A) ((mu * i) % p) =
      (mu * lamPerm p mu g A i) % p := by
  have h := (U4_square_scalar p mu g mu mui hp hmu A hA i hi).1
  change (mui * lamPerm p mu g (scaleSupp p mui A) ((mu * i) % p)) % p =
    lamPerm p mu g A i at h
  have hm := congrArg (fun j => (mu * j) % p) h
  have hp0 : 0 < p := by have := hp.two_le; omega
  have hl := lamPerm_lt p mu g hp0 (scaleSupp p mui A) ((mu * i) % p)
  have hc := empty_hole_carry p mu mui hp hmu
    (lamPerm p mu g (scaleSupp p mui A) ((mu * i) % p)) hl
  change (mu * ((mui * lamPerm p mu g (scaleSupp p mui A) ((mu * i) % p)) % p)) % p = _ at hm
  rw [show (mu * ((mui * lamPerm p mu g (scaleSupp p mui A) ((mu * i) % p)) % p)) % p =
    lamPerm p mu g (scaleSupp p mui A) ((mu * i) % p) from hc] at hm
  exact hm
@[simp] theorem outer_index_value (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (hnA : NonemptyMask A) (i : Fin P.p) :
    ((arithmeticChild P (.outer A hA)).frame.perm i).val =
      lamPerm P.p P.mu P.g (extendMask A) i.val := by
  simp [arithmeticChild, childIndex, childFrame, outerFrame, hnA, lamChild]
theorem child_scalar_permutation (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (i : Fin P.p) :
    (arithmeticChild P (.outer (scalarRole P A) (scalarRole_proper P A hA))).frame.perm
        ((arithmeticChild P .central).frame.perm i) =
      (arithmeticChild P .central).frame.perm ((arithmeticChild P (.outer A hA)).frame.perm i) := by
  classical
  by_cases hnA : NonemptyMask A
  · obtain ⟨mui, hmu⟩ := exists_inv P.prime P.mu_nonzero
    apply Fin.ext
    rw [outer_index_value P _ _ (scalarRole_nonempty P A hnA), central_index_value]
    change lamPerm P.p P.mu P.g (extendMask (scalarRole P A))
        (((arithmeticChild P .central).frame.perm i).val) =
      (P.mu * ((arithmeticChild P (.outer A hA)).frame.perm i).val) % P.p
    rw [central_index_value, outer_index_value P A hA hnA]
    rw [lamPerm_congr_support (scalarRole_extend P A mui hmu)]
    exact scalar_covariant_permutation P.p P.mu mui P.g P.prime hmu (extendMask A)
      (extend_nonempty_proper A hnA hA) i.val i.isLt
  · have hA0 : A = fun _ => false := by
      funext j
      cases hj : A j
      · rfl
      · exact False.elim (hnA ⟨j, hj⟩)
    subst A
    have hB0 : scalarRole P (fun _ => false) = fun _ => false := rfl
    simp only [hB0]
    apply Fin.ext
    simp [arithmeticChild, childIndex, childFrame, outerFrame, NonemptyMask, scalarFrame]
end RegisteredPrime
