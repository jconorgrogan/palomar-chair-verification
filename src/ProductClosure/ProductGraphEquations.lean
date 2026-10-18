module

public import ProductClosure.ProductGraphComponents
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

/-! All-site equations and odd walks for the actual component coefficients.
These statements quantify over every copy and every site, not a selected key.
-/
namespace ProductClosure.ProductGraph
noncomputable section
open PhysicalRegistration.ComponentCoefficients

variable {V W P Q : Type*}

/-- Coefficient opposition is invariant under a graph isomorphism even when
its source and target have completely different component-rank orders. -/
theorem coefficient_opposition_reindex
    [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (χ : V → ℤ) (ψ : W → ℤ)
    (hχ : ∀ v, χ v = 1 ∨ χ v = -1) (hψ : ∀ w, ψ w = 1 ∨ ψ w = -1)
    (hflip : ∀ u v, ψ (e v) = -ψ (e u) ↔ χ v = -χ u) (u v : V) :
    value H ψ (e v) = -value H ψ (e u) ↔ value G χ v = -value G χ u := by
  rw [opposite_value_iff H ψ hψ, SimpleGraph.Iso.reachable_iff,
    hflip, opposite_value_iff G χ hχ]

/-- All equations for a factor candidate occur in every passive orbit copy.
The reverse implication uses any existing passive copy. -/
theorem all_left_site_equations_iff
    [Fintype V] [Fintype W] [Fintype P] [Fintype Q] [Nonempty P]
    [LinearOrder V] [LinearOrder W] [LinearOrder ((V × P) ⊕ (W × Q))]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (χ : V → ℤ) (ψ : W → ℤ) (ε : P → ℤ) (η : Q → ℤ)
    (hχ : ∀ v, χ v = 1 ∨ χ v = -1) (hψ : ∀ w, ψ w = 1 ∨ ψ w = -1)
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) (hη : ∀ q, η q = 1 ∨ η q = -1)
    (R : V → V → Prop) :
    (∀ p u v, R u v →
      value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inl (v,p)) =
        -value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inl (u,p))) ↔
      ∀ u v, R u v → value G χ v = -value G χ u := by
  constructor
  · intro hall u v huv
    let p : P := Classical.choice inferInstance
    exact ((product_value_left_iff G H χ ψ ε η hχ hψ hε hη (u,p) (v,p)).mp
      (hall p u v huv)).2
  · intro hall p u v huv
    exact (product_value_left_iff G H χ ψ ε η hχ hψ hε hη (u,p) (v,p)).mpr
      ⟨rfl, hall u v huv⟩

theorem all_right_site_equations_iff
    [Fintype V] [Fintype W] [Fintype P] [Fintype Q] [Nonempty Q]
    [LinearOrder V] [LinearOrder W] [LinearOrder ((V × P) ⊕ (W × Q))]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (χ : V → ℤ) (ψ : W → ℤ) (ε : P → ℤ) (η : Q → ℤ)
    (hχ : ∀ v, χ v = 1 ∨ χ v = -1) (hψ : ∀ w, ψ w = 1 ∨ ψ w = -1)
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) (hη : ∀ q, η q = 1 ∨ η q = -1)
    (R : W → W → Prop) :
    (∀ q u v, R u v →
      value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inr (v,q)) =
        -value (productGraph G H P Q) (productOrientation χ ψ ε η) (.inr (u,q))) ↔
      ∀ u v, R u v → value H ψ v = -value H ψ u := by
  constructor
  · intro hall u v huv
    let q : Q := Classical.choice inferInstance
    exact ((product_value_right_iff G H χ ψ ε η hχ hψ hε hη (u,q) (v,q)).mp
      (hall q u v huv)).2
  · intro hall q u v huv
    exact (product_value_right_iff G H χ ψ ε η hχ hψ hε hη (u,q) (v,q)).mpr
      ⟨rfl, hall u v huv⟩

/-- Orientation transport is proved by composing actual graph edges. -/
theorem walk_orientation (G : SimpleGraph V) (χ : V → ℤ)
    (hedge : ∀ u v, G.Adj u v → χ v = -χ u)
    {u v : V} (w : G.Walk u v) : χ v = (-1 : ℤ)^w.length * χ u := by
  induction w with
  | nil => simp
  | @cons u v w h p ih =>
    rw [ih, hedge u v h]
    simp only [SimpleGraph.Walk.length_cons, pow_succ]
    simp [mul_neg, neg_mul]

/-- Opposite computed coefficients produce an odd walk, with no assumed
bipartite coloring certificate beyond properness-derived edge orientation. -/
theorem opposite_coefficients_odd_walk [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (χ : V → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1)
    (hedge : ∀ u v, G.Adj u v → χ v = -χ u)
    (u v : V) (hc : value G χ v = -value G χ u) :
    ∃ w : G.Walk u v, Odd w.length := by
  obtain ⟨⟨w⟩, hflip⟩ := (opposite_value_iff G χ hχ u v).mp hc
  refine ⟨w, ?_⟩
  have he := walk_orientation G χ hedge w
  have hp : (-1 : ℤ)^w.length = -1 := by
    rcases hχ u with hu | hu <;> rw [hflip, hu] at he <;> simp only [mul_one, mul_neg_one] at he <;> omega
  exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)).mp hp

/-- Conversely any odd walk gives coefficient opposition, using the actual
component assignment rather than freely supplied numerical labels. -/
theorem odd_walk_opposite_coefficients [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (χ : V → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1)
    (hedge : ∀ u v, G.Adj u v → χ v = -χ u)
    {u v : V} (w : G.Walk u v) (hw : Odd w.length) :
    value G χ v = -value G χ u := by
  apply (opposite_value_iff G χ hχ u v).mpr
  refine ⟨w.reachable, ?_⟩
  rw [walk_orientation G χ hedge w, hw.neg_one_pow]
  simp

#print axioms coefficient_opposition_reindex
#print axioms all_left_site_equations_iff
#print axioms all_right_site_equations_iff
#print axioms opposite_coefficients_odd_walk
#print axioms odd_walk_opposite_coefficients
end
end ProductClosure.ProductGraph
