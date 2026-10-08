module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Arithmetic of finite generic-sector partitions

This module proves the arithmetic steps of K1 and K2 in the expanded registration
argument for the final one-height T5 and T7.  Angles are actual real angles, and
all comparisons use `Real.pi_pos`.

The input is a *finite list* of sector angles whose sum is the complementary
angle.  Producing that list from a physical tiling, proving its angle inventory,
and proving that its sum is the complementary angle are separate geometric
obligations.  None of those geometric conclusions is asserted by this module.
In particular, the results here do not establish registration or either final
aperiodic-monotile goal.
-/

namespace SparseMonotiles
namespace SectorArithmetic

/-- The angle inventory supplied by the strong final-height bound.
The parameter `δ` need not distinguish different physical creases. -/
def InAngleInventory (θ : ℝ) : Prop :=
  θ = Real.pi / 2 ∨ θ = Real.pi ∨ θ = 3 * Real.pi / 2 ∨
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 4 ∧
      (θ = Real.pi - δ ∨ θ = Real.pi + δ)

/-- A finite arithmetic sector partition.  This is an explicit input, not a
conclusion about the local geometry of an arbitrary physical tiling. -/
def SectorPartition (angles : List ℝ) (total : ℝ) : Prop :=
  (∀ θ ∈ angles, InAngleInventory θ) ∧ angles.sum = total

/-- Every allowed local material sector has angle at least a right angle. -/
theorem sector_angle_lower_bound {θ : ℝ} (hθ : InAngleInventory θ) :
    Real.pi / 2 ≤ θ := by
  have hpi := Real.pi_pos
  rcases hθ with h | h | h | ⟨δ, hδ, hδ', h | h⟩ <;> linarith

/-- There is a gap above the only smallest angle in the inventory. -/
theorem sector_angle_eq_half_pi_or_gt_three_quarters {θ : ℝ}
    (hθ : InAngleInventory θ) :
    θ = Real.pi / 2 ∨ 3 * Real.pi / 4 < θ := by
  have hpi := Real.pi_pos
  rcases hθ with h | h | h | ⟨δ, hδ, hδ', h | h⟩
  · exact Or.inl h
  all_goals right; linarith

/-- The two exclusions used in the ordinary K2 proof follow from the strict
quarter-pi bound, without an independent nonresonance assumption. -/
theorem quarter_deviations_pair_ne_half_pi {δ ε : ℝ}
    (hδ : δ < Real.pi / 4) (hε : ε < Real.pi / 4) :
    δ + ε ≠ Real.pi / 2 := by
  linarith

theorem quarter_deviations_triple_ne_pi {δ ε ζ : ℝ}
    (hδ : δ < Real.pi / 4) (hε : ε < Real.pi / 4)
    (hζ : ζ < Real.pi / 4) :
    δ + ε + ζ ≠ Real.pi := by
  have hpi := Real.pi_pos
  linarith

/-- The sum bound explicitly counts every entry of the finite sector list. -/
theorem sector_sum_ge_count (angles : List ℝ)
    (h : ∀ θ ∈ angles, InAngleInventory θ) :
    (angles.length : ℝ) * (Real.pi / 2) ≤ angles.sum := by
  induction angles with
  | nil => simp
  | cons θ angles ih =>
    have hθ := sector_angle_lower_bound (h θ (by simp))
    have htail : ∀ φ ∈ angles, InAngleInventory φ := by
      intro φ hφ
      exact h φ (by simp [hφ])
    have hi := ih htail
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.sum_cons]
    nlinarith

/-- A real-valued count bound, convenient for arbitrary total-angle bounds. -/
theorem sector_count_bound {angles : List ℝ} {total : ℝ}
    (h : SectorPartition angles total) :
    (angles.length : ℝ) ≤ total / (Real.pi / 2) := by
  have hp : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  apply (le_div_iff₀ hp).2
  simpa [h.2] using sector_sum_ge_count angles h.1

/-- Fewer than three right angles allow at most two sectors. -/
theorem sector_length_le_two {angles : List ℝ}
    (h : ∀ θ ∈ angles, InAngleInventory θ)
    (hsum : angles.sum < 3 * Real.pi / 2) :
    angles.length ≤ 2 := by
  have hlower := sector_sum_ge_count angles h
  have hpi := Real.pi_pos
  by_contra hn
  have hlen : 3 ≤ angles.length := by omega
  have hcast : (3 : ℝ) ≤ (angles.length : ℝ) := by exact_mod_cast hlen
  nlinarith

/-- A positive sub-pi total allows exactly one sector. -/
theorem sector_length_eq_one_of_sum_lt_pi {angles : List ℝ}
    (h : ∀ θ ∈ angles, InAngleInventory θ)
    (hpos : 0 < angles.sum) (hsum : angles.sum < Real.pi) :
    angles.length = 1 := by
  have hlower := sector_sum_ge_count angles h
  have hpi := Real.pi_pos
  have hne : angles ≠ [] := by
    intro he
    simp [he] at hpos
  have hlenpos : 0 < angles.length := List.length_pos_iff.mpr hne
  have hlenlt : angles.length < 2 := by
    by_contra hn
    have hlen : 2 ≤ angles.length := by omega
    have hcast : (2 : ℝ) ≤ (angles.length : ℝ) := by exact_mod_cast hlen
    nlinarith
  omega

/-- Two allowed sectors either are both right angles, or their sum exceeds
five quarters of pi. This is stronger than the exclusions required in K2. -/
theorem two_sector_sum_cases {θ φ : ℝ}
    (hθ : InAngleInventory θ) (hφ : InAngleInventory φ) :
    (θ = Real.pi / 2 ∧ φ = Real.pi / 2) ∨
      5 * Real.pi / 4 < θ + φ := by
  have hθlow := sector_angle_lower_bound hθ
  have hφlow := sector_angle_lower_bound hφ
  rcases sector_angle_eq_half_pi_or_gt_three_quarters hθ with heθ | hgθ
  · rcases sector_angle_eq_half_pi_or_gt_three_quarters hφ with heφ | hgφ
    · exact Or.inl ⟨heθ, heφ⟩
    · right; linarith
  · right; linarith

/-- Complete short-sum classification of finite allowed-sector lists. -/
theorem finite_sector_sum_cases {angles : List ℝ}
    (h : ∀ θ ∈ angles, InAngleInventory θ)
    (hpos : 0 < angles.sum) (hsum : angles.sum ≤ 5 * Real.pi / 4) :
    (∃ θ, angles = [θ]) ∨ angles = [Real.pi / 2, Real.pi / 2] := by
  have hpi := Real.pi_pos
  have hlen : angles.length ≤ 2 :=
    sector_length_le_two h (by linarith)
  cases angles with
  | nil => simp at hpos
  | cons θ tail =>
    cases tail with
    | nil => exact Or.inl ⟨θ, rfl⟩
    | cons φ tail =>
      cases tail with
      | nil =>
        have hθ : InAngleInventory θ := h θ (by simp)
        have hφ : InAngleInventory φ := h φ (by simp)
        rcases two_sector_sum_cases hθ hφ with ⟨heθ, heφ⟩ | hg
        · exact Or.inr (by simp [heθ, heφ])
        · simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
          linarith
      | cons ψ tail => simp at hlen

/-- K1 arithmetic: a half-plane is either one flat sector or two carrier
right-angle sectors. No geometric carrier-seam exclusion is asserted here. -/
theorem pi_sector_classification {angles : List ℝ}
    (h : SectorPartition angles Real.pi) :
    angles = [Real.pi] ∨ angles = [Real.pi / 2, Real.pi / 2] := by
  have hpi := Real.pi_pos
  rcases finite_sector_sum_cases h.1 (by rw [h.2]; exact hpi)
      (by rw [h.2]; linarith) with ⟨θ, he⟩ | he
  · left
    have hθ : θ = Real.pi := by simpa [he] using h.2
    simpa [hθ] using he
  · exact Or.inr he

/-- Every positive total up to five quarters of pi, other than pi itself,
can be filled by only one allowed sector. -/
theorem single_sector_of_short_nonpi_total {angles : List ℝ} {total : ℝ}
    (h : SectorPartition angles total) (hpos : 0 < total)
    (hshort : total ≤ 5 * Real.pi / 4) (hne : total ≠ Real.pi) :
    angles = [total] := by
  rcases finite_sector_sum_cases h.1 (by rwa [h.2]) (by rwa [h.2]) with
    ⟨θ, he⟩ | he
  · have hθ : θ = total := by simpa [he] using h.2
    simpa [hθ] using he
  · have heq : Real.pi = total := by
      have hs := h.2
      simp only [he, List.sum_cons, List.sum_nil, add_zero] at hs
      linarith
    exact False.elim (hne heq.symm)

/-- K2 arithmetic on the smaller complement of a pi-plus-delta crease. -/
theorem pi_sub_deviation_sector_classification {angles : List ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < Real.pi / 4)
    (h : SectorPartition angles (Real.pi - δ)) :
    angles = [Real.pi - δ] := by
  have hpi := Real.pi_pos
  exact single_sector_of_short_nonpi_total h (by linarith) (by linarith)
    (by linarith)

/-- K2 arithmetic on the larger complement of a pi-minus-delta crease. -/
theorem pi_add_deviation_sector_classification {angles : List ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < Real.pi / 4)
    (h : SectorPartition angles (Real.pi + δ)) :
    angles = [Real.pi + δ] := by
  have hpi := Real.pi_pos
  exact single_sector_of_short_nonpi_total h (by linarith) (by linarith)
    (by linarith)

/-- The unique sector complementary to a key crease is a non-flat sector.
The geometric interpretation as one companion tile still requires the sector
list to have one entry per actual companion tile. -/
theorem key_crease_complement_classification {angles : List ℝ} {θ δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < Real.pi / 4)
    (hθ : θ = Real.pi - δ ∨ θ = Real.pi + δ)
    (h : SectorPartition angles (2 * Real.pi - θ)) :
    angles = [2 * Real.pi - θ] ∧ 2 * Real.pi - θ ≠ Real.pi := by
  rcases hθ with he | he
  · have htotal : 2 * Real.pi - θ = Real.pi + δ := by rw [he]; ring
    rw [htotal] at h ⊢
    exact ⟨pi_add_deviation_sector_classification hδ hδ' h, by linarith⟩
  · have htotal : 2 * Real.pi - θ = Real.pi - δ := by rw [he]; ring
    rw [htotal] at h ⊢
    exact ⟨pi_sub_deviation_sector_classification hδ hδ' h, by linarith⟩

/-- No allowed sector can fit inside a wedge of angle below pi/2. -/
theorem no_sector_fits_small_wedge {θ width : ℝ}
    (hθ : InAngleInventory θ) (hw : width < Real.pi / 2) :
    ¬ θ ≤ width := by
  have hlower := sector_angle_lower_bound hθ
  linarith

/-- No finite list of allowed sectors fills a positive wedge below pi/2,
including the empty-list edge case. This is the arithmetic seam contradiction
used after the independent geometric strip-crossing argument in K1. -/
theorem no_sector_partition_small_wedge {width : ℝ}
    (hwpos : 0 < width) (hw : width < Real.pi / 2) :
    ¬ ∃ angles, SectorPartition angles width := by
  rintro ⟨angles, h⟩
  have hlower := sector_sum_ge_count angles h.1
  have hne : angles ≠ [] := by
    intro he
    have hz : (0 : ℝ) = width := by simpa [he] using h.2
    linarith
  have hlen : 1 ≤ angles.length := List.length_pos_iff.mpr hne
  have hcast : (1 : ℝ) ≤ (angles.length : ℝ) := by exact_mod_cast hlen
  have hpi := Real.pi_pos
  rw [h.2] at hlower
  nlinarith

#print axioms sector_angle_lower_bound
#print axioms sector_angle_eq_half_pi_or_gt_three_quarters
#print axioms quarter_deviations_pair_ne_half_pi
#print axioms quarter_deviations_triple_ne_pi
#print axioms sector_sum_ge_count
#print axioms sector_count_bound
#print axioms sector_length_le_two
#print axioms sector_length_eq_one_of_sum_lt_pi
#print axioms two_sector_sum_cases
#print axioms finite_sector_sum_cases
#print axioms pi_sector_classification
#print axioms single_sector_of_short_nonpi_total
#print axioms pi_sub_deviation_sector_classification
#print axioms pi_add_deviation_sector_classification
#print axioms key_crease_complement_classification
#print axioms no_sector_fits_small_wedge
#print axioms no_sector_partition_small_wedge

end SectorArithmetic
end SparseMonotiles
