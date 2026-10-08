module

public import Uniform.Arith

@[expose] public section

/-! The sign of a permutation: Vandermonde reindexing and multiplicativity. -/
namespace Uniform

theorem mem_pairs {n : Nat} {a b : Nat} : (a, b) ∈ pairs n ↔ a < b ∧ b < n := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    simp only [pairs, List.mem_append, ih, List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨i, hi, rfl, rfl⟩) <;> omega
    · intro h
      by_cases hb : b < n
      · exact Or.inl ⟨h.1, hb⟩
      · exact Or.inr ⟨a, by omega, rfl, by omega⟩

theorem mem_pairs' {n : Nat} {q : Nat × Nat} : q ∈ pairs n ↔ q.1 < q.2 ∧ q.2 < n := by
  obtain ⟨a, b⟩ := q; exact mem_pairs

theorem nodup_pairs (n : Nat) : (pairs n).Nodup := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    simp only [pairs]
    rw [List.nodup_append]
    refine ⟨ih, nodup_map_of_injOn List.nodup_range (fun x _ y _ h => by
      simp only [Prod.mk.injEq] at h; exact h.1), ?_⟩
    intro q hq r hr hqr
    rw [mem_pairs'] at hq
    rcases List.mem_map.1 hr with ⟨i, _, rfl⟩
    rw [hqr] at hq; simp at hq

theorem length_pairs (n : Nat) : 2 * (pairs n).length + n = n * n := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    simp only [pairs, List.length_append, List.length_map, List.length_range]
    grind

/-- `ord2 a b` = the pair `(min, max)`. -/
def ord2 (a b : Nat) : Nat × Nat := if b < a then (b, a) else (a, b)

/-- `∏_{i<j<n} (x (σ j) - x (σ i))`. -/
def Vprod (n : Nat) (x : Nat → Int) (σ : Nat → Nat) : Int :=
  ((pairs n).map (fun q => x (σ q.2) - x (σ q.1))).prod

theorem term_split (x : Nat → Int) (a b : Nat) :
    x b - x a = (if b < a then (-1 : Int) else 1) * (x (ord2 a b).2 - x (ord2 a b).1) := by
  unfold ord2
  by_cases h : b < a
  · simp only [h, ite_true]; grind
  · simp only [h, ite_false]; grind

theorem ord2_perm {n : Nat} {σ : Nat → Nat} (hσ : IsPermOn n σ) :
    ((pairs n).map (fun q => ord2 (σ q.1) (σ q.2))).Perm (pairs n) := by
  have inj := hσ.2
  have lt := hσ.1
  rw [List.perm_ext_iff_of_nodup _ (nodup_pairs n)]
  · intro r
    obtain ⟨a, b⟩ := r
    rw [mem_pairs, List.mem_map]
    constructor
    · rintro ⟨⟨u, v⟩, huv, he⟩
      rw [mem_pairs] at huv
      have hne : σ u ≠ σ v := fun h => by have := inj u v (by omega) huv.2 h; omega
      have hu := lt u (by omega); have hv := lt v huv.2
      unfold ord2 at he
      by_cases hc : σ v < σ u
      · simp only [hc, ite_true, Prod.mk.injEq] at he; omega
      · simp only [hc, ite_false, Prod.mk.injEq] at he; omega
    · rintro ⟨hab, hbn⟩
      obtain ⟨u, hu, rfl⟩ := hσ.surj a (by omega)
      obtain ⟨v, hv, rfl⟩ := hσ.surj b hbn
      have huv : u ≠ v := by rintro rfl; omega
      by_cases h : u < v
      · refine ⟨(u, v), mem_pairs.2 ⟨h, hv⟩, ?_⟩
        simp only [ord2, show ¬ σ v < σ u by omega, ite_false]
      · refine ⟨(v, u), mem_pairs.2 ⟨by omega, hu⟩, ?_⟩
        simp only [ord2, hab, ite_true]
  · apply nodup_map_of_injOn (nodup_pairs n)
    rintro ⟨q1, q2⟩ hq ⟨r1, r2⟩ hr h
    rw [mem_pairs] at hq hr
    have h1 := lt q1 (by omega); have h2 := lt q2 hq.2
    have h3 := lt r1 (by omega); have h4 := lt r2 hr.2
    simp only [ord2] at h
    by_cases c1 : σ q2 < σ q1 <;> by_cases c2 : σ r2 < σ r1 <;>
      simp only [c1, c2, ite_true, ite_false, Prod.mk.injEq] at h <;> obtain ⟨e1, e2⟩ := h
    · have := inj _ _ (by omega) (by omega) e1; have := inj _ _ (by omega) (by omega) e2
      simp only [Prod.mk.injEq]; omega
    · have := inj _ _ (by omega) (by omega) e1; have := inj _ _ (by omega) (by omega) e2
      simp only [Prod.mk.injEq]; omega
    · have := inj _ _ (by omega) (by omega) e1; have := inj _ _ (by omega) (by omega) e2
      simp only [Prod.mk.injEq]; omega
    · have := inj _ _ (by omega) (by omega) e1; have := inj _ _ (by omega) (by omega) e2
      simp only [Prod.mk.injEq]; omega

/-- Vandermonde sign lemma: permuting the variables multiplies the product by the sign. -/
theorem vandermonde_perm {n : Nat} (x : Nat → Int) {σ : Nat → Nat} (hσ : IsPermOn n σ) :
    Vprod n x σ = permSign n σ * Vprod n x (fun i => i) := by
  unfold Vprod permSign invCount
  have e1 : (pairs n).map (fun q => x (σ q.2) - x (σ q.1))
      = (pairs n).map (fun q => (if σ q.2 < σ q.1 then (-1 : Int) else 1) *
          (x (ord2 (σ q.1) (σ q.2)).2 - x (ord2 (σ q.1) (σ q.2)).1)) := by
    apply List.map_congr_left
    intro q _
    exact term_split x (σ q.1) (σ q.2)
  rw [e1, prod_map_mul_int]
  have e2 := prod_signs (pairs n) (fun q => decide (σ q.2 < σ q.1))
  simp only [decide_eq_true_eq] at e2
  rw [e2]
  congr 1
  have e3 := perm_prod_int ((ord2_perm hσ).map (fun r : Nat × Nat => x r.2 - x r.1))
  rw [List.map_map] at e3
  exact e3

theorem Vprod_id_pos (n : Nat) : 0 < Vprod n (fun i => (i : Int)) (fun i => i) := by
  unfold Vprod
  have : ∀ y ∈ (pairs n).map (fun q => ((q.2 : Nat) : Int) - ((q.1 : Nat) : Int)), 0 < y := by
    intro y hy
    rcases List.mem_map.1 hy with ⟨q, hq, rfl⟩
    rw [mem_pairs'] at hq; omega
  generalize (pairs n).map (fun q => ((q.2 : Nat) : Int) - ((q.1 : Nat) : Int)) = l at this
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.prod_cons]
    exact Int.mul_pos (this a List.mem_cons_self) (ih (fun y hy => this y (List.mem_cons_of_mem _ hy)))

theorem IsPermOn.comp {n : Nat} {σ τ : Nat → Nat} (hσ : IsPermOn n σ) (hτ : IsPermOn n τ) :
    IsPermOn n (fun i => σ (τ i)) :=
  ⟨fun i hi => hσ.1 _ (hτ.1 i hi),
   fun i j hi hj h => hτ.2 i j hi hj (hσ.2 _ _ (hτ.1 i hi) (hτ.1 j hj) h)⟩

/-- the sign is multiplicative -/
theorem permSign_comp {n : Nat} {σ τ : Nat → Nat} (hσ : IsPermOn n σ) (hτ : IsPermOn n τ) :
    permSign n (fun i => σ (τ i)) = permSign n σ * permSign n τ := by
  have hV : Vprod n (fun i : Nat => (i : Int)) (fun i => i) ≠ 0 := by
    have := Vprod_id_pos n; omega
  have h1 := vandermonde_perm (fun i : Nat => (i : Int)) (hσ.comp hτ)
  have h2 : Vprod n (fun i : Nat => (i : Int)) (fun i => σ (τ i))
      = Vprod n (fun i => ((σ i : Nat) : Int)) τ := rfl
  have h3 := vandermonde_perm (fun i => ((σ i : Nat) : Int)) hτ
  have h4 : Vprod n (fun i => ((σ i : Nat) : Int)) (fun i => i)
      = Vprod n (fun i : Nat => (i : Int)) σ := rfl
  have h5 := vandermonde_perm (fun i : Nat => (i : Int)) hσ
  rw [h2, h3, h4, h5] at h1
  have : permSign n (fun i => σ (τ i)) * Vprod n (fun i : Nat => (i : Int)) (fun i => i)
      = (permSign n σ * permSign n τ) * Vprod n (fun i : Nat => (i : Int)) (fun i => i) := by
    rw [← h1]; grind
  exact Int.eq_of_mul_eq_mul_right hV this

theorem invCount_comp {n : Nat} {σ τ : Nat → Nat} (hσ : IsPermOn n σ) (hτ : IsPermOn n τ) :
    invCount n (fun i => σ (τ i)) % 2 = (invCount n σ + invCount n τ) % 2 := by
  have := permSign_comp hσ hτ
  unfold permSign at this
  rw [← Int.pow_add] at this
  exact neg_one_pow_inj this

theorem countP_xor_mod {α : Type} (l : List α) (f g : α → Bool) :
    (l.countP (fun i => xor (f i) (g i))) % 2 = (l.countP f + l.countP g) % 2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    cases f a <;> cases g a <;> simp <;> omega

theorem signProd_eq (d : Nat) (s : Nat → Bool) : signProd d s = (-1) ^ negCount d s := by
  unfold signProd negCount; exact prod_signs _ _

theorem neg_one_pow_congr {a b : Nat} (h : a % 2 = b % 2) : (-1 : Int) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq, neg_one_pow_eq, h]

theorem negCount_comp (d : Nat) (F C : Frame) (hF : IsPermOn d F.perm) :
    negCount d (F.comp C).neg % 2 = (negCount d F.neg + negCount d C.neg) % 2 := by
  unfold negCount Frame.comp
  simp only
  rw [countP_xor_mod, countP_comp_perm hF]

theorem rotation_parity {d : Nat} {F : Frame} (hF : IsRotation d F) :
    negCount d F.neg % 2 = invCount d F.perm % 2 := by
  have h := hF.2
  unfold permSign at h
  rw [signProd_eq, ← Int.pow_add] at h
  rw [neg_one_pow_eq] at h
  by_cases hc : (invCount d F.perm + negCount d F.neg) % 2 = 0
  · omega
  · simp [hc] at h

theorem rotation_of_parity {d : Nat} {F : Frame} (hp : IsPermOn d F.perm)
    (h : negCount d F.neg % 2 = invCount d F.perm % 2) : IsRotation d F := by
  refine ⟨hp, ?_⟩
  unfold permSign
  rw [signProd_eq, ← Int.pow_add, neg_one_pow_eq]
  have : (invCount d F.perm + negCount d F.neg) % 2 = 0 := by omega
  simp [this]

theorem IsRotation.comp {d : Nat} {F C : Frame} (hF : IsRotation d F) (hC : IsRotation d C) :
    IsRotation d (F.comp C) := by
  refine rotation_of_parity (F := F.comp C) (hC.1.comp hF.1) ?_
  rw [negCount_comp d F C hF.1]
  have e : (F.comp C).perm = fun i => C.perm (F.perm i) := rfl
  rw [e, invCount_comp hC.1 hF.1]
  have := rotation_parity hF; have := rotation_parity hC
  omega

theorem invCount_id (n : Nat) : invCount n (fun i => i) = 0 := by
  unfold invCount
  rw [List.countP_eq_zero]
  intro q hq
  rw [mem_pairs'] at hq
  simp; omega

theorem IsRotation.id (d : Nat) : IsRotation d Frame.id := by
  apply rotation_of_parity ⟨fun i hi => hi, fun i j _ _ h => h⟩
  unfold Frame.id negCount
  simp only
  rw [invCount_id]; simp

end Uniform
