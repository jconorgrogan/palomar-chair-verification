module

public import Uniform.Lists

@[expose] public section

/-! Elementary number theory in core Lean: Euclid's lemma, congruences on `Int`, inverses, Fermat. -/
namespace Uniform

theorem IsPrime.two_le {p : Nat} (hp : IsPrime p) : 2 ≤ p := hp.1

theorem IsPrime.coprime_of_not_dvd {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) :
    Nat.Coprime p a := by
  rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h | h
  · exact h
  · exact absurd (h ▸ Nat.gcd_dvd_right p a) ha

theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · exact Or.inr ((hp.coprime_of_not_dvd ha).dvd_of_dvd_mul_left h)

theorem IsPrime.int_dvd_mul {p : Nat} (hp : IsPrime p) {x y : Int} (h : (p : Int) ∣ x * y) :
    (p : Int) ∣ x ∨ (p : Int) ∣ y := by
  rw [Int.ofNat_dvd_left, Int.natAbs_mul] at h
  rcases hp.dvd_mul h with h | h
  · exact Or.inl (Int.ofNat_dvd_left.2 h)
  · exact Or.inr (Int.ofNat_dvd_left.2 h)

theorem IsPrime.not_dvd_of_pos_lt {p i : Nat} (h0 : 0 < i) (hi : i < p) : ¬ p ∣ i := by
  intro h; have := Nat.le_of_dvd h0 h; omega

theorem IsPrime.not_dvd_mul {p a b : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    ¬ p ∣ a * b := fun h => (hp.dvd_mul h).elim ha hb

theorem IsPrime.not_dvd_pow {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) (k : Nat) :
    ¬ p ∣ a ^ k := by
  induction k with
  | zero => simp; have := hp.two_le; omega
  | succ k ih => rw [Nat.pow_succ]; exact hp.not_dvd_mul ih ha

/-- Congruence modulo `p` on `Int`. -/
def MEq (p : Nat) (a b : Int) : Prop := (p : Int) ∣ a - b

theorem MEq.refl {p : Nat} (a : Int) : MEq p a a := ⟨0, by simp⟩
theorem MEq.of_eq {p : Nat} {a b : Int} (h : a = b) : MEq p a b := h ▸ MEq.refl a
theorem MEq.symm {p : Nat} {a b : Int} (h : MEq p a b) : MEq p b a := by
  obtain ⟨k, hk⟩ := h; exact ⟨-k, by grind⟩
theorem MEq.trans {p : Nat} {a b c : Int} (h1 : MEq p a b) (h2 : MEq p b c) : MEq p a c := by
  obtain ⟨k, hk⟩ := h1; obtain ⟨l, hl⟩ := h2; exact ⟨k + l, by grind⟩
theorem MEq.add {p : Nat} {a b c d : Int} (h1 : MEq p a b) (h2 : MEq p c d) :
    MEq p (a + c) (b + d) := by
  obtain ⟨k, hk⟩ := h1; obtain ⟨l, hl⟩ := h2; exact ⟨k + l, by grind⟩
theorem MEq.sub {p : Nat} {a b c d : Int} (h1 : MEq p a b) (h2 : MEq p c d) :
    MEq p (a - c) (b - d) := by
  obtain ⟨k, hk⟩ := h1; obtain ⟨l, hl⟩ := h2; exact ⟨k - l, by grind⟩
theorem MEq.mul {p : Nat} {a b c d : Int} (h1 : MEq p a b) (h2 : MEq p c d) :
    MEq p (a * c) (b * d) := by
  obtain ⟨k, hk⟩ := h1; obtain ⟨l, hl⟩ := h2; exact ⟨a * l + k * d, by grind⟩
theorem MEq.pow {p : Nat} {a b : Int} (h : MEq p a b) (n : Nat) : MEq p (a ^ n) (b ^ n) := by
  induction n with
  | zero => rw [Int.pow_zero, Int.pow_zero]; exact MEq.refl _
  | succ n ih => rw [Int.pow_succ, Int.pow_succ]; exact ih.mul h
theorem MEq.emod_self {p : Nat} (a : Int) : MEq p (a % p) a := by
  refine ⟨-(a / p), ?_⟩
  rw [Int.emod_def]; grind
theorem MEq.zero_of_dvd {p : Nat} {a : Int} (h : (p : Int) ∣ a) : MEq p a 0 := by
  simpa [MEq] using h
theorem MEq.dvd_of_zero {p : Nat} {a : Int} (h : MEq p a 0) : (p : Int) ∣ a := by
  simpa [MEq] using h
theorem MEq.dvd_iff {p : Nat} {a b : Int} (h : MEq p a b) : (p : Int) ∣ a ↔ (p : Int) ∣ b := by
  obtain ⟨k, hk⟩ := h
  constructor
  · rintro ⟨l, hl⟩; exact ⟨l - k, by grind⟩
  · rintro ⟨l, hl⟩; exact ⟨l + k, by grind⟩

theorem MEq.cancel {p : Nat} (hp : IsPrime p) {a b c : Int} (hc : ¬ (p : Int) ∣ c)
    (h : MEq p (a * c) (b * c)) : MEq p a b := by
  have : (p : Int) ∣ (a - b) * c := by
    obtain ⟨k, hk⟩ := h; exact ⟨k, by grind⟩
  rcases hp.int_dvd_mul this with h | h
  · exact h
  · exact absurd h hc

theorem MEq.eq_of_lt {p : Nat} {a b : Int} (h : MEq p a b) (ha : 0 ≤ a) (ha' : a < p)
    (hb : 0 ≤ b) (hb' : b < p) : a = b := by
  obtain ⟨k, hk⟩ := h
  have hp : (0 : Int) < p := by omega
  by_cases hk0 : k = 0
  · subst hk0; omega
  · rcases Int.lt_or_gt_of_ne hk0 with hlt | hgt
    · have : (p : Int) * k ≤ (p : Int) * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · have : (p : Int) * 1 ≤ (p : Int) * k := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega

theorem MEq.nat_mod {p : Nat} {a b : Nat} (h : MEq p a b) : a % p = b % p := by
  have h1 : MEq p ((a % p : Nat) : Int) ((b % p : Nat) : Int) := by
    simp only [Int.natCast_emod]
    exact ((MEq.emod_self _).trans h).trans (MEq.emod_self _).symm
  by_cases hp : p = 0
  · subst hp; obtain ⟨k, hk⟩ := h; simp at hk; simp; omega
  · have := h1.eq_of_lt (by omega) (by have := Nat.mod_lt a (Nat.pos_of_ne_zero hp); omega)
      (by omega) (by have := Nat.mod_lt b (Nat.pos_of_ne_zero hp); omega)
    omega

theorem MEq.of_nat_mod {p : Nat} {a b : Nat} (h : a % p = b % p) : MEq p a b := by
  have h1 : MEq p ((a % p : Nat) : Int) a := by simp only [Int.natCast_emod]; exact MEq.emod_self _
  have h2 : MEq p ((b % p : Nat) : Int) b := by simp only [Int.natCast_emod]; exact MEq.emod_self _
  rw [h] at h1
  exact h1.symm.trans h2

theorem MEq.not_one_neg_one {p : Nat} (hp : 3 ≤ p) : ¬ MEq p 1 (-1) := by
  rintro ⟨k, hk⟩
  have : (p : Int) * k = 2 := by omega
  by_cases hk0 : k ≤ 0
  · have : (p : Int) * k ≤ (p : Int) * 0 := Int.mul_le_mul_of_nonneg_left hk0 (by omega)
    omega
  · have : (p : Int) * 1 ≤ (p : Int) * k := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega

/-- multiplication by a unit is injective on residues -/
theorem mul_mod_inj {p a i j : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) (hi : i < p) (hj : j < p)
    (h : (a * i) % p = (a * j) % p) : i = j := by
  have h1 : MEq p ((i : Int) * a) ((j : Int) * a) := by
    have := MEq.of_nat_mod h
    simp only [Int.natCast_mul] at this
    exact (MEq.of_eq (Int.mul_comm _ _)).trans (this.trans (MEq.of_eq (Int.mul_comm _ _)))
  have hc : ¬ (p : Int) ∣ (a : Int) := fun h => ha (Int.natCast_dvd_natCast.1 h)
  have := (h1.cancel hp hc).eq_of_lt (by omega) (by omega) (by omega) (by omega)
  omega

theorem mulMap_perm {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) : IsPermOn p (mulMap p a) :=
  ⟨fun i _ => Nat.mod_lt _ (by have := hp.two_le; omega),
   fun i j hi hj h => mul_mod_inj hp ha hi hj h⟩

/-- inverses modulo a prime -/
theorem exists_inv {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) : ∃ b, (a * b) % p = 1 := by
  obtain ⟨x, _, hx⟩ := (mulMap_perm hp ha).surj 1 (by have := hp.two_le; omega)
  exact ⟨x, hx⟩

theorem not_dvd_prod_int {p : Nat} (hp : IsPrime p) (l : List Int)
    (h : ∀ x ∈ l, ¬ (p : Int) ∣ x) : ¬ (p : Int) ∣ l.prod := by
  induction l with
  | nil =>
    simp only [List.prod_nil]; intro h1
    have := Int.eq_one_of_dvd_one (by omega) h1; have := hp.two_le; omega
  | cons a t ih =>
    simp only [List.prod_cons]
    intro h1
    rcases hp.int_dvd_mul h1 with h2 | h2
    · exact h a List.mem_cons_self h2
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) h2

theorem MEq.prod_map {p : Nat} {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ x ∈ l, MEq p (f x) (g x)) : MEq p (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => exact MEq.refl _
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h a List.mem_cons_self).mul (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Fermat's little theorem. -/
theorem fermat {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) : MEq p ((a : Int) ^ (p - 1)) 1 := by
  have h2 := hp.two_le
  let l := List.range' 1 (p - 1)
  have hl : ∀ i ∈ l, 0 < i ∧ i < p := by
    intro i hi; simp [l, List.mem_range'_1] at hi; omega
  have hperm : (l.map (mulMap p a)).Perm l := by
    apply perm_of_nodup_subset
    · exact nodup_map_of_injOn List.nodup_range' (fun x hx y hy hxy =>
        mul_mod_inj hp ha (hl x hx).2 (hl y hy).2 hxy)
    · exact List.nodup_range'
    · intro y hy
      rcases List.mem_map.1 hy with ⟨x, hx, rfl⟩
      have hx' := hl x hx
      have hlt : mulMap p a x < p := Nat.mod_lt _ (by omega)
      have hne : mulMap p a x ≠ 0 := by
        intro h0
        have : p ∣ a * x := Nat.dvd_of_mod_eq_zero h0
        exact hp.not_dvd_mul ha (IsPrime.not_dvd_of_pos_lt hx'.1 hx'.2) this
      simp [l, List.mem_range'_1]; omega
    · simp
  -- products in Int
  have hP : ((l.map (fun i : Nat => ((mulMap p a i : Nat) : Int)))).prod = (l.map (fun i : Nat => (i : Int))).prod := by
    have := perm_prod_int (hperm.map (fun i : Nat => (i : Int)))
    rw [List.map_map] at this
    exact this
  have hcong : MEq p (l.map (fun i : Nat => ((mulMap p a i : Nat) : Int))).prod
      (l.map (fun i : Nat => (a : Int) * (i : Int))).prod :=
    MEq.prod_map l _ _ (fun i _ => by
      simp only [mulMap, Int.natCast_emod, Int.natCast_mul]; exact MEq.emod_self _)
  rw [hP, prod_map_mul_int, prod_map_const_int] at hcong
  have hlen : l.length = p - 1 := by simp [l]
  rw [hlen] at hcong
  have hnd : ¬ (p : Int) ∣ (l.map (fun i : Nat => (i : Int))).prod := by
    apply not_dvd_prod_int hp
    intro x hx
    rcases List.mem_map.1 hx with ⟨i, hi, rfl⟩
    have := hl i hi
    intro hd
    exact IsPrime.not_dvd_of_pos_lt this.1 this.2 (Int.natCast_dvd_natCast.1 hd)
  have : MEq p (((a : Int) ^ (p - 1)) * (l.map (fun i : Nat => (i : Int))).prod)
      (1 * (l.map (fun i : Nat => (i : Int))).prod) := by
    rw [Int.one_mul]; exact hcong.symm
  exact this.cancel hp hnd

end Uniform
