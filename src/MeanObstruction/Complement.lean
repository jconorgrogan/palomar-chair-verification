module
public import MeanObstruction.Support
@[expose] public section
namespace RegisteredPrime.MeanObstruction
open Uniform

def complement (A : Nat → Bool) : Nat → Bool := fun i => !(A i)

theorem card_complement_list (l : List Nat) (A : Nat → Bool) :
    l.countP A + l.countP (complement A) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, List.length_cons, complement]
    rcases Bool.eq_false_or_eq_true (A a) with hAa | hAa <;> simp_all <;> omega

theorem card_complement (p : Nat) (A : Nat → Bool) :
    suppCard p A + suppCard p (complement A) = p := by
  simpa [suppCard] using card_complement_list (List.range p) A

theorem sum_complement_list (l : List Nat) (A : Nat → Bool) :
    (l.filter A).sum + (l.filter (complement A)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.sum_cons, complement]
    rcases Bool.eq_false_or_eq_true (A a) with hAa | hAa <;> simp_all <;> omega

theorem sum_complement (p : Nat) (A : Nat → Bool) :
    suppSum p A + suppSum p (complement A) = (List.range p).sum :=
  sum_complement_list (List.range p) A

theorem sum_range_double (n : Nat) :
    2 * ((List.range n).sum : Int) = (n : Int) * ((n : Int) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.sum_append]
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int.natCast_add,
      Int.natCast_one]
    grind

theorem sum_universe_zero {p : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) :
    MEq p ((List.range p).sum : Int) 0 := by
  have hp3 := hp.three_le hp2
  have h2 : ¬ (p : Int) ∣ (2 : Int) :=
    int_not_dvd (p := p) (a := 2) (IsPrime.not_dvd_of_pos_lt (by omega) (by omega))
  have he : MEq p (((List.range p).sum : Int) * 2) (0 * 2) := by
    have hd := MEq.zero_of_dvd (Int.dvd_mul_right (p : Int) ((p : Int) - 1))
    exact (MEq.of_eq (by have := sum_range_double p; omega)).trans hd
  exact he.cancel hp h2

theorem complement_proper {p : Nat} {A : Nat → Bool} (hA : NonemptyProperOn p A) :
    NonemptyProperOn p (complement A) := by
  obtain ⟨⟨i, hi, hAi⟩, ⟨j, hj, hAj⟩⟩ := hA
  exact ⟨⟨j, hj, by simp [complement, hAj]⟩,
    ⟨i, hi, by simp [complement, hAi]⟩⟩

/-- In an odd prime field a proper nonempty set and its complement have the same mean. -/
theorem mean_complement {p : Nat} (hp : IsPrime p) (hp2 : p ≠ 2)
    (A : Nat → Bool) (hA : NonemptyProperOn p A) :
    zA p (complement A) = zA p A := by
  have hc := card_complement p A
  have hs := sum_complement p A
  have hcard : MEq p (suppCard p (complement A)) (-(suppCard p A : Int)) := by
    have h := (MEq.zero_of_dvd (Int.dvd_refl (p : Int))).sub
      (MEq.refl (suppCard p A : Int))
    exact (MEq.of_eq (by omega)).trans (h.trans (MEq.of_eq (by omega)))
  have hsum : MEq p (suppSum p (complement A)) (-(suppSum p A : Int)) := by
    have h := (sum_universe_zero hp hp2).sub (MEq.refl (suppSum p A : Int))
    exact (MEq.of_eq (by omega)).trans (h.trans (MEq.of_eq (by omega)))
  have hmean := mean_equation hp A hA
  have hneg : MEq p ((-(suppCard p A : Int)) * zA p A) (-(suppSum p A : Int)) := by
    have h := (MEq.refl (-1 : Int)).mul hmean
    exact (MEq.of_eq (by grind)).trans (h.trans (MEq.of_eq (by grind)))
  have heq : MEq p ((suppCard p (complement A) : Int) * zA p A)
      (suppSum p (complement A)) :=
    ((hcard.mul (MEq.refl (zA p A : Int))).trans hneg).trans hsum.symm
  apply Eq.symm
  apply (U1_zA p hp (complement A) (complement_proper hA)).2.2
  · exact (U1_zA p hp A hA).1
  · exact MEq.nat_mod (by simpa only [Int.natCast_mul] using heq)

end RegisteredPrime.MeanObstruction
