module

public import PhysicalRegistration.ComponentCoefficients

@[expose] public section

/-!
# Exact component equations for product-facet graph copies

All coefficients below are the existing, computed finite component-rank times
orientation assignment. Numerical component ranks are never transported:
only their equality relation is used. This module does not assume or assert
that a geometric product contact graph has this form.
-/
namespace ProductClosure.ProductGraph
noncomputable section
open PhysicalRegistration.ComponentCoefficients

variable {V W P Q : Type*}

/-- Literal disjoint union, with no cross-type edges. -/
def disjointSum (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr u, .inr v => H.Adj u v
    | _, _ => False
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact h.symm
    · exact h.elim
    · exact h.elim
    · exact h.symm⟩
  loopless := ⟨by
    rintro (u | u) h
    · exact G.loopless.irrefl u h
    · exact H.loopless.irrefl u h⟩

/-- A factor graph copied once for each passive state. -/
def copies (G : SimpleGraph V) (P : Type*) : SimpleGraph (V × P) where
  Adj u v := G.Adj u.1 v.1 ∧ u.2 = v.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- A product facet has one of two types. Copies of distinct types never meet. -/
def productGraph (G : SimpleGraph V) (H : SimpleGraph W) (P Q : Type*) :
    SimpleGraph ((V × P) ⊕ (W × Q)) :=
  disjointSum (copies G P) (copies H Q)

theorem copies_walk_invariants (G : SimpleGraph V) {u v : V × P}
    (w : (copies G P).Walk u v) : G.Reachable u.1 v.1 ∧ u.2 = v.2 := by
  induction w with
  | nil => exact ⟨.rfl, rfl⟩
  | cons h w ih => exact ⟨h.1.reachable.trans ih.1, h.2.trans ih.2⟩

theorem copies_reachable_iff (G : SimpleGraph V) (u v : V × P) :
    (copies G P).Reachable u v ↔ G.Reachable u.1 v.1 ∧ u.2 = v.2 := by
  constructor
  · rintro ⟨w⟩
    exact copies_walk_invariants G w
  · rcases u with ⟨u, p⟩
    rcases v with ⟨v, q⟩
    rintro ⟨h, rfl⟩
    exact h.map (show G →g copies G P from ⟨fun x => (x, p), fun h => ⟨h, rfl⟩⟩)

private def sumReach (G : SimpleGraph V) (H : SimpleGraph W) :
    V ⊕ W → V ⊕ W → Prop
  | .inl u, .inl v => G.Reachable u v
  | .inr u, .inr v => H.Reachable u v
  | _, _ => False

private theorem sum_walk_invariants (G : SimpleGraph V) (H : SimpleGraph W)
    {u v : V ⊕ W} (w : (disjointSum G H).Walk u v) : sumReach G H u v := by
  induction w with
  | @nil u => cases u <;> exact SimpleGraph.Reachable.rfl
  | @cons u v w h p ih =>
    cases u <;> cases v <;> cases w <;>
      simp only [disjointSum, sumReach] at h ih ⊢ <;>
      try contradiction
    · exact h.reachable.trans ih
    · exact h.reachable.trans ih

@[simp] theorem sum_reachable_inl_iff (G : SimpleGraph V) (H : SimpleGraph W)
    (u v : V) : (disjointSum G H).Reachable (.inl u) (.inl v) ↔ G.Reachable u v := by
  constructor
  · rintro ⟨w⟩
    exact sum_walk_invariants G H w
  · exact fun h => h.map ⟨Sum.inl, fun h => h⟩

@[simp] theorem sum_reachable_inr_iff (G : SimpleGraph V) (H : SimpleGraph W)
    (u v : W) : (disjointSum G H).Reachable (.inr u) (.inr v) ↔ H.Reachable u v := by
  constructor
  · rintro ⟨w⟩
    exact sum_walk_invariants G H w
  · exact fun h => h.map ⟨Sum.inr, fun h => h⟩

@[simp] theorem not_sum_reachable_cross (G : SimpleGraph V) (H : SimpleGraph W)
    (u : V) (v : W) : ¬(disjointSum G H).Reachable (.inl u) (.inr v) := by
  rintro ⟨w⟩
  exact sum_walk_invariants G H w

@[simp] theorem product_reachable_left (G : SimpleGraph V) (H : SimpleGraph W)
    (u v : V × P) :
    (productGraph G H P Q).Reachable (.inl u) (.inl v) ↔
      G.Reachable u.1 v.1 ∧ u.2 = v.2 := by
  simp [productGraph, copies_reachable_iff]

@[simp] theorem product_reachable_right (G : SimpleGraph V) (H : SimpleGraph W)
    (u v : W × Q) :
    (productGraph G H P Q).Reachable (.inr u) (.inr v) ↔
      H.Reachable u.1 v.1 ∧ u.2 = v.2 := by
  simp [productGraph, copies_reachable_iff]

/-- Orientation can acquire a fixed sign on each orbit copy. -/
def productOrientation (χ : V → ℤ) (ψ : W → ℤ) (ε : P → ℤ) (η : Q → ℤ) :
    (V × P) ⊕ (W × Q) → ℤ
  | .inl (v,p) => ε p * χ v
  | .inr (w,q) => η q * ψ w

private theorem sign_mul {a b : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem productOrientation_sign (χ : V → ℤ) (ψ : W → ℤ) (ε : P → ℤ) (η : Q → ℤ)
    (hχ : ∀ v, χ v = 1 ∨ χ v = -1) (hψ : ∀ w, ψ w = 1 ∨ ψ w = -1)
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) (hη : ∀ q, η q = 1 ∨ η q = -1)
    (u : (V × P) ⊕ (W × Q)) :
    productOrientation χ ψ ε η u = 1 ∨ productOrientation χ ψ ε η u = -1 := by
  cases u with
  | inl u => exact sign_mul (hε u.2) (hχ u.1)
  | inr u => exact sign_mul (hη u.2) (hψ u.1)

variable [Fintype V] [Fintype W] [Fintype P] [Fintype Q]
variable [LinearOrder V] [LinearOrder W]
variable [LinearOrder ((V × P) ⊕ (W × Q))]

/-- Every literal coefficient equation on a left-type facet is exactly the
factor equation plus equality of the passive label. Both graph orderings
are arbitrary; their numerical ranks need not agree. -/
theorem product_value_left_iff
    (G : SimpleGraph V) (H : SimpleGraph W)
    (χ : V → ℤ) (ψ : W → ℤ) (ε : P → ℤ) (η : Q → ℤ)
    (hχ : ∀ v, χ v = 1 ∨ χ v = -1) (hψ : ∀ w, ψ w = 1 ∨ ψ w = -1)
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) (hη : ∀ q, η q = 1 ∨ η q = -1)
    (u v : V × P) :
    value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inl v) =
      -value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inl u) ↔
      u.2 = v.2 ∧ value G χ v.1 = -value G χ u.1 := by
  rw [opposite_value_iff _ _ (productOrientation_sign χ ψ ε η hχ hψ hε hη),
    product_reachable_left, opposite_value_iff G χ hχ]
  change (G.Reachable u.1 v.1 ∧ u.2 = v.2) ∧ ε v.2 * χ v.1 = -(ε u.2 * χ u.1) ↔ _
  constructor
  · rintro ⟨⟨hc, hp⟩, hs⟩
    refine ⟨hp, hc, ?_⟩
    rw [← hp] at hs
    rcases hε u.2 with he | he <;> simp_all <;> omega
  · rintro ⟨hp, hc, hs⟩
    exact ⟨⟨hc, hp⟩, by simp [hp, hs]⟩

/-- The symmetric right-type coefficient pullback. -/
theorem product_value_right_iff
    (G : SimpleGraph V) (H : SimpleGraph W)
    (χ : V → ℤ) (ψ : W → ℤ) (ε : P → ℤ) (η : Q → ℤ)
    (hχ : ∀ v, χ v = 1 ∨ χ v = -1) (hψ : ∀ w, ψ w = 1 ∨ ψ w = -1)
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) (hη : ∀ q, η q = 1 ∨ η q = -1)
    (u v : W × Q) :
    value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inr v) =
      -value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inr u) ↔
      u.2 = v.2 ∧ value H ψ v.1 = -value H ψ u.1 := by
  rw [opposite_value_iff _ _ (productOrientation_sign χ ψ ε η hχ hψ hε hη),
    product_reachable_right, opposite_value_iff H ψ hψ]
  change (H.Reachable u.1 v.1 ∧ u.2 = v.2) ∧ η v.2 * ψ v.1 = -(η u.2 * ψ u.1) ↔ _
  constructor
  · rintro ⟨⟨hc, hp⟩, hs⟩
    refine ⟨hp, hc, ?_⟩
    rw [← hp] at hs
    rcases hη u.2 with he | he <;> simp_all <;> omega
  · rintro ⟨hp, hc, hs⟩
    exact ⟨⟨hc, hp⟩, by simp [hp, hs]⟩

/-- Coefficient opposition cannot switch facet type. -/
theorem product_value_not_cross
    (G : SimpleGraph V) (H : SimpleGraph W)
    (χ : ((V × P) ⊕ (W × Q)) → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1) (u : V × P) (v : W × Q) :
    value (productGraph G H P Q) χ (.inr v) ≠
      -value (productGraph G H P Q) χ (.inl u) := by
  rw [ne_eq, opposite_value_iff _ _ hχ]
  simp [productGraph]

#print axioms product_value_left_iff
#print axioms product_value_right_iff
#print axioms product_value_not_cross
end
end ProductClosure.ProductGraph
