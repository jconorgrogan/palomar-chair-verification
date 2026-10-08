module

public import Uniform.Arith

@[expose] public section

/-! U1: free cycling iff prime; units mod n iff prime; `z_A` exists uniquely for prime `p`. -/
namespace Uniform

/-- every `k` with `1 ≤ k ≤ n-1` is invertible mod `n` iff `n` is prime -/
theorem U1_units (n : Nat) (hn : 2 ≤ n) :
    (∀ k, 1 ≤ k → k ≤ n - 1 → ∃ j, (k * j) % n = 1) ↔ IsPrime n := by
  constructor
  · intro h
    refine ⟨hn, fun m hm => ?_⟩
    have hm0 : m ≠ 0 := by rintro rfl; have := Nat.eq_zero_of_zero_dvd hm; omega
    have hmn : m ≤ n := Nat.le_of_dvd (by omega) hm
    by_cases h1 : m = 1
    · exact Or.inl h1
    by_cases h2 : m = n
    · exact Or.inr h2
    exfalso
    obtain ⟨j, hj⟩ := h m (by omega) (by omega)
    have : m ∣ (m * j) % n := (Nat.dvd_mod_iff hm).2 (Nat.dvd_mul_right m j)
    rw [hj] at this
    exact h1 (Nat.dvd_one.1 this)
  · intro hp k hk1 hk2
    exact exists_inv hp (IsPrime.not_dvd_of_pos_lt (by omega) (by omega))

/-- shift invariance propagates along multiples of the shift -/
private theorem shift_iter {n c : Nat} {A : Fin n → Bool}
    (hA : ∀ i j : Fin n, j.val = (i.val + c) % n → A j = A i) (i : Fin n) (t : Nat)
    (h : (i.val + t * c) % n < n) : A ⟨(i.val + t * c) % n, h⟩ = A i := by
  induction t with
  | zero =>
    have : (⟨(i.val + 0 * c) % n, h⟩ : Fin n) = i := by
      apply Fin.ext; simp [Nat.mod_eq_of_lt i.isLt]
    rw [this]
  | succ t ih =>
    have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have ht : (i.val + t * c) % n < n := Nat.mod_lt _ hpos
    rw [← ih ht]
    apply hA
    simp only
    rw [Nat.mod_add_mod, Nat.succ_mul, Nat.add_assoc]

theorem U1_shift (n : Nat) (hn : 2 ≤ n) :
    (∃ c, 0 < c ∧ c < n ∧ ∃ A : Fin n → Bool, NonemptyProper A ∧
        ∀ i j : Fin n, j.val = (i.val + c) % n → A j = A i) ↔ ¬ IsPrime n := by
  constructor
  · rintro ⟨c, hc0, hcn, A, ⟨⟨i1, hi1⟩, ⟨i0, hi0⟩⟩, hA⟩ hp
    obtain ⟨c', hc'⟩ := exists_inv hp (IsPrime.not_dvd_of_pos_lt hc0 hcn)
    -- every value of A equals A i0
    have hall : ∀ i' : Fin n, A i' = A i0 := by
      intro i'
      let t := c' * (i'.val + n - i0.val)
      have key : (i0.val + t * c) % n = i'.val := by
        have e1 : t * c = (i'.val + n - i0.val) * (c * c') := by
          simp only [t]; grind
        rw [e1, Nat.add_mod, Nat.mul_mod (i'.val + n - i0.val), hc', Nat.mul_one,
          Nat.mod_mod, ← Nat.add_mod]
        have : i0.val + (i'.val + n - i0.val) = i'.val + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i'.isLt]
      have hlt : (i0.val + t * c) % n < n := Nat.mod_lt _ (by omega)
      have := shift_iter hA i0 t hlt
      have e : (⟨(i0.val + t * c) % n, hlt⟩ : Fin n) = i' := Fin.ext key
      rw [e] at this; exact this
    have := hall i1
    rw [hi1, hi0] at this
    exact Bool.noConfusion this
  · intro hnp
    have : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
      apply Classical.byContradiction
      intro hne
      apply hnp
      refine ⟨hn, fun m hm => ?_⟩
      apply Classical.byContradiction
      intro h
      exact hne ⟨m, hm, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
    obtain ⟨m, hm, hm1, hmn⟩ := this
    have hm0 : m ≠ 0 := by rintro rfl; have := Nat.eq_zero_of_zero_dvd hm; omega
    have hmle : m ≤ n := Nat.le_of_dvd (by omega) hm
    refine ⟨m, by omega, by omega, fun i => decide (i.val % m = 0), ⟨⟨⟨0, by omega⟩, by simp⟩,
      ⟨⟨1, by omega⟩, by simp [Nat.mod_eq_of_lt (show 1 < m by omega)]⟩⟩, ?_⟩
    intro i j hj
    simp only [hj, Nat.mod_mod_of_dvd _ hm, Nat.add_mod_right]

/-- for `p` prime and `A` nonempty proper, `|A| ∈ [1, p-1]` -/
theorem suppCard_bounds {p : Nat} {A : Nat → Bool} (hA : NonemptyProperOn p A) :
    1 ≤ suppCard p A ∧ suppCard p A < p := by
  obtain ⟨⟨i1, hi1p, hi1⟩, ⟨i0, hi0p, hi0⟩⟩ := hA
  constructor
  · unfold suppCard
    have : 0 < (List.range p).countP A := List.countP_pos_iff.2 ⟨i1, List.mem_range.2 hi1p, hi1⟩
    omega
  · unfold suppCard
    have hle := List.countP_le_length (p := A) (l := List.range p)
    have hne : (List.range p).countP A ≠ (List.range p).length := by
      intro h
      have := List.countP_eq_length.1 h i0 (List.mem_range.2 hi0p)
      rw [hi0] at this; exact Bool.noConfusion this
    simp at hle hne; omega

theorem U1_zA (p : Nat) (hp : IsPrime p) (A : Nat → Bool) (hA : NonemptyProperOn p A) :
    zA p A < p ∧ (suppCard p A * zA p A) % p = suppSum p A % p ∧
    ∀ z, z < p → (suppCard p A * z) % p = suppSum p A % p → z = zA p A := by
  have h2 := hp.two_le
  obtain ⟨hk1, hkp⟩ := suppCard_bounds hA
  have hk : ¬ p ∣ suppCard p A := IsPrime.not_dvd_of_pos_lt (by omega) hkp
  obtain ⟨k', hk'⟩ := exists_inv hp hk
  -- a solution exists
  let P : Nat → Bool := fun z => (suppCard p A * z) % p == suppSum p A % p
  have hex : ∃ z, z ∈ List.range p ∧ P z := by
    refine ⟨(k' * suppSum p A) % p, List.mem_range.2 (Nat.mod_lt _ (by omega)), ?_⟩
    simp only [P, beq_iff_eq]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_mod, hk', Nat.one_mul,
      Nat.mod_mod]
  have hsome := List.find?_isSome.2 hex
  obtain ⟨z0, hz0⟩ := Option.isSome_iff_exists.1 hsome
  have hz0mem := List.mem_of_find?_eq_some hz0
  have hz0P := List.find?_some hz0
  have hzA : zA p A = z0 := by unfold zA; rw [hz0]; rfl
  have hz0P' : (suppCard p A * z0) % p = suppSum p A % p := by simpa [P] using hz0P
  refine ⟨hzA ▸ List.mem_range.1 hz0mem, hzA ▸ hz0P', fun z hz hzP => ?_⟩
  rw [hzA]
  exact mul_mod_inj hp hk hz (List.mem_range.1 hz0mem) (hzP.trans hz0P'.symm)

end Uniform
