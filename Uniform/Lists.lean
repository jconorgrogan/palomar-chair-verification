module

public import Uniform.Defs

@[expose] public section

/-! List infrastructure: pigeonhole, reindexing of counts / sums / products along a permutation. -/
namespace Uniform

theorem nodup_map_of_injOn {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hl.2 (fun x hx y hy h =>
      hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) h)⟩
    rintro ⟨x, hx, hfx⟩
    have := hf x (List.mem_cons_of_mem _ hx) a List.mem_cons_self hfx
    exact hl.1 (this ▸ hx)

/-- Pigeonhole: a duplicate-free sublist-by-membership of a duplicate-free list, at least as long,
is a permutation of it. -/
theorem perm_of_nodup_subset {α : Type} {l m : List α} (hl : l.Nodup) (hm : m.Nodup)
    (hsub : l ⊆ m) (hlen : m.length ≤ l.length) : l.Perm m := by
  rw [List.perm_ext_iff_of_nodup hl hm]
  intro a
  refine ⟨fun h => hsub h, fun h => ?_⟩
  apply Classical.byContradiction
  intro ha
  have h1 : (a :: l).Nodup := List.nodup_cons.2 ⟨ha, hl⟩
  have h2 : a :: l ⊆ m := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h
    · exact hsub hx
  have := List.Nodup.length_le_of_subset h1 h2
  simp at this; omega

theorem IsPermOn.map_range_perm {n : Nat} {σ : Nat → Nat} (h : IsPermOn n σ) :
    ((List.range n).map σ).Perm (List.range n) := by
  apply perm_of_nodup_subset
  · exact nodup_map_of_injOn List.nodup_range
      (fun x hx y hy hxy => h.2 x y (List.mem_range.1 hx) (List.mem_range.1 hy) hxy)
  · exact List.nodup_range
  · intro y hy
    rcases List.mem_map.1 hy with ⟨x, hx, rfl⟩
    exact List.mem_range.2 (h.1 x (List.mem_range.1 hx))
  · simp

theorem IsPermOn.surj {n : Nat} {σ : Nat → Nat} (h : IsPermOn n σ) (y : Nat) (hy : y < n) :
    ∃ x, x < n ∧ σ x = y := by
  have : y ∈ (List.range n).map σ := h.map_range_perm.symm.subset (List.mem_range.2 hy)
  rcases List.mem_map.1 this with ⟨x, hx, hxy⟩
  exact ⟨x, List.mem_range.1 hx, hxy⟩

theorem countP_comp_perm {n : Nat} {σ : Nat → Nat} (h : IsPermOn n σ) (s : Nat → Bool) :
    (List.range n).countP (fun i => s (σ i)) = (List.range n).countP s := by
  have := h.map_range_perm.countP_eq s
  rw [List.countP_map] at this
  exact this

theorem sum_comp_perm {n : Nat} {σ : Nat → Nat} (h : IsPermOn n σ) (F : Nat → Nat) :
    ((List.range n).map (fun i => F (σ i))).sum = ((List.range n).map F).sum := by
  have := (h.map_range_perm.map F).sum_nat
  rw [List.map_map] at this
  exact this

theorem perm_prod_int {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.prod = l₂.prod := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp only [List.prod_cons]; grind
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem prod_map_mul_int {α : Type} (l : List α) (f g : α → Int) :
    (l.map (fun x => f x * g x)).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.prod_cons, ih]; grind

theorem prod_map_const_int {α : Type} (l : List α) (c : Int) :
    (l.map (fun _ => c)).prod = c ^ l.length := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons]; grind

/-- product of `±1` signs -/
theorem prod_signs {α : Type} (l : List α) (P : α → Bool) :
    (l.map (fun x => if P x then (-1 : Int) else 1)).prod = (-1) ^ (l.countP P) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.countP_cons]
    cases P a <;> simp [Int.pow_succ] <;> grind

theorem neg_one_pow_eq (k : Nat) : (-1 : Int) ^ k = if k % 2 = 0 then 1 else -1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Int.pow_succ, ih]
    by_cases h : k % 2 = 0
    · have : (k + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (k + 1) % 2 = 0 := by omega
      simp [h, this]

theorem neg_one_pow_inj {a b : Nat} (h : (-1 : Int) ^ a = (-1 : Int) ^ b) : a % 2 = b % 2 := by
  rw [neg_one_pow_eq, neg_one_pow_eq] at h
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;> simp [ha, hb] at h <;> omega

theorem neg_one_pow_add (a b : Nat) : (-1 : Int) ^ (a + b) = (-1) ^ a * (-1) ^ b := Int.pow_add _ _ _

end Uniform
