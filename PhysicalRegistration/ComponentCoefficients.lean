module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Canonical component ranks and signed coefficients for a finite ordered
site graph. The site order is an explicit input: when instantiated with the
manuscript's lexicographic native-site order, these are exactly its labels.
No graph-coloring, nonzero-coefficient, or matching certificate is assumed. -/
namespace PhysicalRegistration.ComponentCoefficients
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev componentVertices (G : SimpleGraph V) (u : V) : Finset V :=
  Finset.univ.filter (G.Reachable u)

theorem self_mem_componentVertices (G : SimpleGraph V) (u : V) :
    u ∈ componentVertices G u := by simp [SimpleGraph.Reachable.refl]

def least (G : SimpleGraph V) (u : V) : V :=
  (componentVertices G u).min' ⟨u, self_mem_componentVertices G u⟩

theorem reachable_least (G : SimpleGraph V) (u : V) : G.Reachable u (least G u) := by
  have h := Finset.min'_mem (componentVertices G u) ⟨u, self_mem_componentVertices G u⟩
  simpa [least, componentVertices] using h

theorem least_eq_of_reachable {G : SimpleGraph V} {u v : V}
    (h : G.Reachable u v) : least G u = least G v := by
  have hs : componentVertices G u = componentVertices G v := by
    ext w
    simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun huw => h.symm.trans huw, fun hvw => h.trans hvw⟩
  unfold least
  congr 1

theorem least_eq_iff_reachable (G : SimpleGraph V) (u v : V) :
    least G u = least G v ↔ G.Reachable u v := by
  constructor
  · intro h
    have hu := reachable_least G u
    rw [h] at hu
    exact hu.trans (reachable_least G v).symm
  · exact least_eq_of_reachable

def representatives (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun u => least G u = u)

theorem least_mem_representatives (G : SimpleGraph V) (u : V) :
    least G u ∈ representatives G := by
  simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (least_eq_of_reachable (reachable_least G u)).symm

/-- Components are ranked 1,2,... by their least site in the supplied order. -/
def label (G : SimpleGraph V) (u : V) : ℕ :=
  ((representatives G).filter (fun v => v ≤ least G u)).card

def count (G : SimpleGraph V) : ℕ := (representatives G).card

theorem label_pos (G : SimpleGraph V) (u : V) : 0 < label G u := by
  apply Finset.card_pos.mpr
  exact ⟨least G u, Finset.mem_filter.mpr ⟨least_mem_representatives G u, le_rfl⟩⟩

theorem label_le_count (G : SimpleGraph V) (u : V) : label G u ≤ count G :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem label_lt_of_least_lt {G : SimpleGraph V} {u v : V}
    (h : least G u < least G v) : label G u < label G v := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro w hw
    obtain ⟨hw, hwu⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw, hwu.trans h.le⟩
  · intro he
    have hv : least G v ∈ (representatives G).filter (fun w => w ≤ least G v) :=
      Finset.mem_filter.mpr ⟨least_mem_representatives G v, le_rfl⟩
    rw [← he] at hv
    exact (not_le_of_gt h) (Finset.mem_filter.mp hv).2

theorem label_eq_iff_reachable (G : SimpleGraph V) (u v : V) :
    label G u = label G v ↔ G.Reachable u v := by
  constructor
  · intro h
    apply (least_eq_iff_reachable G u v).mp
    rcases lt_trichotomy (least G u) (least G v) with hlt | heq | hgt
    · have := label_lt_of_least_lt hlt
      omega
    · exact heq
    · have := label_lt_of_least_lt hgt
      omega
  · intro h
    unfold label
    rw [least_eq_of_reachable h]

/-- The literal integer coefficient assignment, with no zero labels. -/
def value (G : SimpleGraph V) (χ : V → ℤ) (u : V) : ℤ := (label G u : ℤ) * χ u

theorem value_nonzero (G : SimpleGraph V) (χ : V → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1) (u : V) : value G χ u ≠ 0 := by
  have hp : (0 : ℤ) < label G u := by exact_mod_cast label_pos G u
  rcases hχ u with h | h <;> simp [value, h] <;> omega

theorem abs_value (G : SimpleGraph V) (χ : V → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1) (u : V) :
    |value G χ u| = (label G u : ℤ) := by
  have hp : (0 : ℤ) ≤ label G u := Int.natCast_nonneg _
  rcases hχ u with h | h <;> simp [value, h, abs_of_nonneg hp]

theorem abs_value_le_count (G : SimpleGraph V) (χ : V → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1) (u : V) :
    |value G χ u| ≤ (count G : ℤ) := by
  rw [abs_value G χ hχ]
  exact_mod_cast label_le_count G u

/-- Opposite coefficients recover both component identity and orientation
reversal. Neither is imposed as a hypothesis on a candidate mate. -/
theorem opposite_value_iff (G : SimpleGraph V) (χ : V → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1) (u v : V) :
    value G χ v = -value G χ u ↔ G.Reachable u v ∧ χ v = -χ u := by
  have hu : (0 : ℤ) < label G u := by exact_mod_cast label_pos G u
  have hv : (0 : ℤ) < label G v := by exact_mod_cast label_pos G v
  constructor
  · intro h
    have habs := congrArg abs h
    rw [abs_neg, abs_value G χ hχ, abs_value G χ hχ] at habs
    have hl : label G u = label G v := by exact_mod_cast habs.symm
    refine ⟨(label_eq_iff_reachable G u v).mp hl, ?_⟩
    rcases hχ u with h1 | h1 <;> rcases hχ v with h2 | h2 <;>
      simp only [value, h1, h2] at h ⊢ <;> nlinarith
  · rintro ⟨hconn, hflip⟩
    have hl := (label_eq_iff_reachable G u v).mpr hconn
    simp only [value, ← hl, hflip, mul_neg]

theorem edge_value_neg (G : SimpleGraph V) (χ : V → ℤ)
    (hχ : ∀ u, χ u = 1 ∨ χ u = -1)
    (hedge : ∀ u v, G.Adj u v → χ v = -χ u)
    {u v : V} (h : G.Adj u v) : value G χ v = -value G χ u :=
  (opposite_value_iff G χ hχ u v).mpr ⟨h.reachable, hedge u v h⟩

end
end PhysicalRegistration.ComponentCoefficients
