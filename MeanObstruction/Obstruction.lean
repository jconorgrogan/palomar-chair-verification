module
public import MeanObstruction.Complement
@[expose] public section
namespace RegisteredPrime.MeanObstruction
open Uniform

/-- The bounded-mask hypothesis supplied by the positive-wall argument.
Only nonempty proper source and target masks are tested. -/
def MeanStableAt (p j : Nat) (L : Nat → Bool) : Prop :=
  ∀ A : Nat → Bool, NonemptyProperOn p A → A j = true →
    NonemptyProperOn p (symmDiff A L) → zA p A = zA p (symmDiff A L)

theorem pair_difference_eq (L : Nat → Bool) (j x : Nat) :
    symmDiff (pair j x) L = toggle (toggle L j) x := by
  funext i
  simp [pair, toggle, symmDiff]

theorem pair_difference_card {p j x : Nat} (hj : j < p) (hx : x < p)
    (hne : j ≠ x) (L : Nat → Bool) (hLj : L j = true) (hLx : L x = false) :
    suppCard p (symmDiff (pair j x) L) = suppCard p L := by
  have htx : toggle L j x = false := by
    simp [toggle, singleton, symmDiff, Ne.symm hne, hLx]
  have h1 := card_toggle hj L
  have h2 := card_toggle hx (toggle L j)
  rw [htx] at h2
  rw [hLj] at h1
  rw [pair_difference_eq]
  simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
  omega

theorem pair_difference_sum {p j x : Nat} (hj : j < p) (hx : x < p)
    (hne : j ≠ x) (L : Nat → Bool) (hLj : L j = true) (hLx : L x = false) :
    (suppSum p (symmDiff (pair j x) L) : Int) = (suppSum p L : Int) - j + x := by
  have htx : toggle L j x = false := by
    simp [toggle, singleton, symmDiff, Ne.symm hne, hLx]
  have h1 := sum_toggle hj L
  have h2 := sum_toggle hx (toggle L j)
  rw [htx] at h2
  rw [hLj] at h1
  rw [pair_difference_eq]
  simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
  omega

theorem pair_difference_proper {p j x : Nat} (hj : j < p) (hx : x < p)
    (hne : j ≠ x) (L : Nat → Bool) (hLj : L j = true) (hLx : L x = false) :
    NonemptyProperOn p (symmDiff (pair j x) L) := by
  refine ⟨⟨x, hx, ?_⟩, ⟨j, hj, ?_⟩⟩
  · simp [symmDiff, pair_at_right hne, hLx]
  · simp [symmDiff, pair_at_left hne, hLj]

/-- The singleton test centers L at j. If removing j empties L, the same
identity is immediate; thus the singleton endpoint is included. -/
theorem centered_sum_of_stable {p j : Nat} (hp : IsPrime p) (hj : j < p)
    (L : Nat → Bool) (hLj : L j = true) (hstable : MeanStableAt p j L) :
    MEq p (suppSum p L) ((suppCard p L : Int) * j) := by
  classical
  by_cases hn : ∃ y, y < p ∧ toggle L j y = true
  · have hT : NonemptyProperOn p (toggle L j) :=
      ⟨hn, ⟨j, hj, by simp [toggle, symmDiff, singleton, hLj]⟩⟩
    have hz : zA p (toggle L j) = j :=
      (hstable (singleton j) (singleton_proper hp.two_le hj)
        (by simp [singleton]) hT).symm.trans (mean_singleton hp hj)
    have he := mean_equation hp (toggle L j) hT
    rw [hz, card_toggle hj L, sum_toggle hj L, hLj] at he
    simp only [ite_true] at he
    have ha := he.add (MEq.refl (j : Int))
    exact ((MEq.of_eq (by grind)).trans
      (ha.trans (MEq.of_eq (by grind)))).symm
  · have he : ∀ i, i < p → L i = singleton j i := by
      intro i hi
      by_cases hij : i = j
      · subst i; simp [singleton, hLj]
      · have ht : toggle L j i = false := by
          rcases (Bool.eq_false_or_eq_true (toggle L j i)).symm with h | h
          · exact h
          · exact False.elim (hn ⟨i, hi, h⟩)
        simpa [toggle, symmDiff, singleton, hij] using ht
    rw [sum_congr he, card_congr he, sum_singleton hj, card_singleton hj]
    exact MEq.of_eq (by simp)

/-- Distinct bounded coordinates have invertible nonzero difference modulo p. -/
theorem difference_not_dvd {p j x : Nat} (hj : j < p) (hx : x < p) (hne : j ≠ x) :
    ¬ (p : Int) ∣ (j : Int) - x := by
  intro hd
  have he : MEq p (j : Int) x := hd
  have he' := he.eq_of_lt (by omega) (by omega) (by omega) (by omega)
  exact hne (by omega)

/-- A proper stable L containing j is forced to have cardinality two by
one eligible pair {j,x} with x outside L. -/
theorem card_two_of_stable {p j : Nat} (hp : IsPrime p) (hp2 : p ≠ 2)
    (hj : j < p) (L : Nat → Bool) (hLj : L j = true)
    (hL : NonemptyProperOn p L) (hstable : MeanStableAt p j L) :
    suppCard p L = 2 := by
  obtain ⟨x, hx, hLx⟩ := hL.2
  have hne : j ≠ x := by intro h; subst x; rw [hLj] at hLx; contradiction
  have hA := pair_proper (hp.three_le hp2) hj hx hne
  have hD := pair_difference_proper hj hx hne L hLj hLx
  have hz := hstable (pair j x) hA (pair_at_left hne) hD
  have heA := mean_equation hp (pair j x) hA
  have heD := mean_equation hp (symmDiff (pair j x) L) hD
  rw [card_pair hj hx hne, sum_pair hj hx hne] at heA
  simp only [Int.natCast_add] at heA
  rw [pair_difference_card hj hx hne L hLj hLx,
    pair_difference_sum hj hx hne L hLj hLx, ← hz] at heD
  have hcenter := centered_sum_of_stable hp hj L hLj hstable
  have hDcenter := heD.trans ((hcenter.sub (MEq.refl (j : Int))).add
    (MEq.refl (x : Int)))
  have hscaledA := heA.mul (MEq.refl (suppCard p L : Int))
  have hscaledD := hDcenter.mul (MEq.refl (2 : Int))
  have hcancel : MEq p (((suppCard p L : Int) - 2) * ((j : Int) - x))
      (0 * ((j : Int) - x)) := by
    have hz0 := (hscaledD.sub hscaledA).symm
    exact (MEq.of_eq (by grind)).trans
      (hz0.trans (MEq.of_eq (by grind)))
  have hkmod := hcancel.cancel hp (difference_not_dvd hj hx hne)
  have hk2 : MEq p (suppCard p L) 2 := by
    have h := hkmod.add (MEq.refl (2 : Int))
    exact (MEq.of_eq (by grind)).trans (h.trans (MEq.of_eq (by grind)))
  have hbound := suppCard_bounds hL
  have he := hk2.eq_of_lt (by omega) (by omega) (by omega)
    (by have := hp.three_le hp2; omega)
  omega

/-- A two-element support containing j cannot have mean j. -/
theorem card_two_sum_ne {p j : Nat} (hj : j < p) (L : Nat → Bool)
    (hLj : L j = true) (hk : suppCard p L = 2) :
    ¬ MEq p (suppSum p L) ((2 : Int) * j) := by
  have hlen : ((List.range p).filter L).length = 2 := by
    simpa only [suppCard, List.countP_eq_length_filter] using hk
  have hjmem : j ∈ (List.range p).filter L := by
    simp [List.mem_filter, hj, hLj]
  have hnd : ((List.range p).filter L).Nodup := List.nodup_range.filter L
  have hsub : ∀ y ∈ (List.range p).filter L, y < p := by
    intro y hy
    exact List.mem_range.mp (List.mem_filter.mp hy).1
  cases he : (List.range p).filter L with
  | nil => simp [he] at hlen
  | cons a t =>
    cases ht : t with
    | nil => simp [he, ht] at hlen
    | cons b u =>
      have hu : u = [] := by simpa [he, ht] using hlen
      subst u
      have hab : a ≠ b := by simpa [he, ht] using hnd
      have ha : a < p := hsub a (by simp [he, ht])
      have hb : b < p := hsub b (by simp [he, ht])
      have hjab : j = a ∨ j = b := by simpa [he, ht] using hjmem
      have hs : suppSum p L = a + b := by simp [suppSum, he, ht]
      intro hmean
      rw [hs, Int.natCast_add] at hmean
      rcases hjab with hja | hjb
      · rw [hja] at hmean
        have hba : MEq p (b : Int) a := by
          have h := hmean.sub (MEq.refl (a : Int))
          exact (MEq.of_eq (by omega)).trans (h.trans (MEq.of_eq (by omega)))
        have heq := hba.eq_of_lt (by omega) (by omega) (by omega) (by omega)
        exact hab (by omega)
      · rw [hjb] at hmean
        have hab' : MEq p (a : Int) b := by
          have h := hmean.sub (MEq.refl (b : Int))
          exact (MEq.of_eq (by omega)).trans (h.trans (MEq.of_eq (by omega)))
        have heq := hab'.eq_of_lt (by omega) (by omega) (by omega) (by omega)
        exact hab (by omega)

/-- The branch containing j includes the singleton L={j}; no eligibility
hypothesis is silently imposed on its empty singleton difference. -/
theorem full_of_stable_of_mem {p j : Nat} (hp : IsPrime p) (hp2 : p ≠ 2)
    (hj : j < p) (L : Nat → Bool) (hLj : L j = true)
    (hstable : MeanStableAt p j L) : ∀ i, i < p → L i = true := by
  intro i hi
  rcases (Bool.eq_false_or_eq_true (L i)).symm with hLi | hLi
  · have hL : NonemptyProperOn p L := ⟨⟨j, hj, hLj⟩, ⟨i, hi, hLi⟩⟩
    have hk := card_two_of_stable hp hp2 hj L hLj hL hstable
    have hs := centered_sum_of_stable hp hj L hLj hstable
    rw [hk] at hs
    exact False.elim (card_two_sum_ne hj L hLj hk hs)
  · exact hLi

/-- Complementing the fixed mask preserves the exact eligible mean tests. -/
theorem stable_complement {p j : Nat} (hp : IsPrime p) (hp2 : p ≠ 2)
    (L : Nat → Bool) (hstable : MeanStableAt p j L) :
    MeanStableAt p j (complement L) := by
  intro A hA hAj hD
  have he : symmDiff A (complement L) = complement (symmDiff A L) := by
    funext i
    rcases Bool.eq_false_or_eq_true (A i) with hAi | hAi <;>
      rcases Bool.eq_false_or_eq_true (L i) with hLi | hLi <;>
      simp [symmDiff, complement, hAi, hLi]
  have hinv : complement (symmDiff A (complement L)) = symmDiff A L := by
    rw [he]
    funext i
    simp [complement]
  have hAL : NonemptyProperOn p (symmDiff A L) := by
    rw [← hinv]
    exact complement_proper hD
  exact (hstable A hA hAj hAL).trans
    ((mean_complement hp hp2 (symmDiff A L) hAL).symm.trans (congrArg (zA p) he.symm))

/-- Finite-field mean obstruction for the actual bounded masks: invariance
under all eligible symmetric-difference tests through j forces L to be empty
or full. This is uniform for every odd prime, including p=3. -/
theorem mean_obstruction {p j : Nat} (hp : IsPrime p) (hp2 : p ≠ 2)
    (hj : j < p) (L : Nat → Bool)
    (hstable : ∀ A : Nat → Bool, NonemptyProperOn p A → A j = true →
      NonemptyProperOn p (symmDiff A L) → zA p A = zA p (symmDiff A L)) :
    (∀ i, i < p → L i = false) ∨ (∀ i, i < p → L i = true) := by
  rcases (Bool.eq_false_or_eq_true (L j)).symm with hLj | hLj
  · left
    have hCj : complement L j = true := by simp [complement, hLj]
    have hC := full_of_stable_of_mem hp hp2 hj (complement L) hCj
      (stable_complement hp hp2 L hstable)
    intro i hi
    have h := hC i hi
    simpa [complement] using h
  · exact Or.inr (full_of_stable_of_mem hp hp2 hj L hLj hstable)

end RegisteredPrime.MeanObstruction
