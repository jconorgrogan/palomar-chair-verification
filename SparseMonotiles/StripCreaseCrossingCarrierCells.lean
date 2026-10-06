module

public import SparseMonotiles.CarrierFacetHalfspace
public import SparseMonotiles.CarrierRidgeInventory

@[expose] public section

/-! # Exposed unit facets extracted from a native carrier quadrant -/
namespace SparseMonotiles
open Set

/-- Every inward tangent direction of an actual closed carrier cell belongs
to the exact native carrier cone at the point. -/
theorem cell_inward_direction_mem_carrierLinearCone {d : ℕ} (c : Contact.Cell d)
    (hc : Contact.IsChairCell c) {p v : Point d} (hp : p ∈ closedIntegerCell c)
    (hv : ∀ a, (p a = (c a : ℝ) → 0 ≤ v a) ∧
      (p a = (c a : ℝ)+1 → v a ≤ 0)) : v ∈ carrierLinearCone p := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    rcases hc.1 a with h | h <;> have hh := hp a <;> simp only [h,Int.cast_zero,Int.cast_one] at hh <;>
      constructor <;> linarith [hh.1,hh.2]
  · intro a ha
    apply (hv a).1
    rcases hc.1 a with h | h
    · simpa [h,show (1 : ℝ)+1=2 by norm_num] using ha
    · have hh := (hp a).1
      simp only [h,Int.cast_one] at hh
      linarith
  · intro a ha
    apply (hv a).2
    rcases hc.1 a with h | h
    · have hh := (hp a).2
      simp only [h,Int.cast_zero,zero_add] at hh
      linarith
    · simpa [h,show (1 : ℝ)+1=2 by norm_num] using ha
  · obtain ⟨a,ha⟩ := hc.2
    have hp1 : p a ≤ 1 := by simpa [ha] using (hp a).2
    rcases lt_or_eq_of_le hp1 with hlt | heq
    · exact Or.inl ⟨a,hlt⟩
    · exact Or.inr ⟨a,heq,(hv a).2 (by simpa [ha] using heq)⟩

/-- Native signed unit coordinate direction, positive for inward-positive. -/
noncomputable def carrierCellAxisVector {d : ℕ} (a : Fin d) (positive : Bool) : Point d :=
  EuclideanSpace.single a (if positive then 1 else -1)

/-- The inward coordinate ray at either endpoint of a carrier cell is an
actual allowed carrier direction. -/
theorem carrierCellAxisVector_mem_cone {d : ℕ} (c : Contact.Cell d)
    (hc : Contact.IsChairCell c) {p : Point d} (hp : p ∈ closedIntegerCell c)
    (a : Fin d) (b : Bool) (hend : p a = (c a : ℝ)+(if b then 0 else 1)) :
    carrierCellAxisVector a b ∈ carrierLinearCone p := by
  apply cell_inward_direction_mem_carrierLinearCone c hc hp
  intro j
  by_cases hja : j = a
  · subst j
    cases b <;> constructor <;> intro heq <;>
      simp [carrierCellAxisVector,EuclideanSpace.single_apply] <;> simp only [Bool.false_eq_true,if_false,if_true] at hend <;>
      linarith
  · simp [carrierCellAxisVector,EuclideanSpace.single_apply,hja]

/-- A critical integer coordinate of a carrier-cell point is an endpoint of
that unit interval. -/
theorem carrierCell_critical_coordinate_endpoint {d : ℕ} (c : Contact.Cell d)
    (hc : Contact.IsChairCell c) {p : Point d} (hp : p ∈ closedIntegerCell c)
    (a : Fin d) (ha : a ∈ carrierCriticalAxes p) :
    p a = (c a : ℝ) ∨ p a = (c a : ℝ)+1 := by
  have hh := hp a
  rcases hc.1 a with hc | hc <;>
    rcases (mem_carrierCriticalAxes p a).mp ha with h | h | h <;>
    simp_all [hc,h] <;> linarith

/-- The quadrant orientation determines which endpoint of every incident
carrier cell lies at the seam. No owner cell is assumed in advance. -/
theorem carrierCell_endpoint_of_cone_halfspace {d : ℕ} (c : Contact.Cell d)
    (hc : Contact.IsChairCell c) {p : Point d} (hp : p ∈ closedIntegerCell c)
    (a : Fin d) (b : Bool) (ha : a ∈ carrierCriticalAxes p)
    (hcone : carrierLinearCone p ⊆ carrierAxisHalfspace a b) :
    p a = (c a : ℝ)+(if b then 0 else 1) := by
  rcases carrierCell_critical_coordinate_endpoint c hc hp a ha with hl | hu
  · cases b
    · have hv := hcone (carrierCellAxisVector_mem_cone c hc hp a true (by simpa using hl))
      norm_num [carrierAxisHalfspace,carrierCellAxisVector,EuclideanSpace.single_apply] at hv
    · simpa using hl
  · cases b
    · exact hu
    · have hv := hcone (carrierCellAxisVector_mem_cone c hc hp a false hu)
      norm_num [carrierAxisHalfspace,carrierCellAxisVector,EuclideanSpace.single_apply] at hv

/-- Every other coordinate lies strictly within its owner unit interval if
only the two genuine carrier axes are critical. -/
theorem carrierCell_other_coordinates_strict {d : ℕ} (c : Contact.Cell d)
    (hc : Contact.IsChairCell c) {p : Point d} (hp : p ∈ closedIntegerCell c)
    (i j : Fin d) (hcritical : ∀ a ∈ carrierCriticalAxes p, a = i ∨ a = j) :
    ∀ a, a ≠ i → a ≠ j → (c a : ℝ) < p a ∧ p a < (c a : ℝ)+1 := by
  intro a hai haj
  have hnot : a ∉ carrierCriticalAxes p := fun ha => (hcritical a ha).elim hai haj
  have hlo : p a ≠ (c a : ℝ) := by
    intro heq
    apply hnot
    rcases hc.1 a with h | h <;> norm_num [heq,h]
  have hhi : p a ≠ (c a : ℝ)+1 := by
    intro heq
    apply hnot
    rcases hc.1 a with h | h <;> norm_num [heq,h]
  exact ⟨lt_of_le_of_ne (hp a).1 hlo.symm,lt_of_le_of_ne (hp a).2 hhi⟩

/-- The unit facet facing out of a carrier quadrant is exposed: a hypothetical
chair cell across it would contribute the forbidden opposite coordinate ray. -/
theorem carrier_quadrant_facet_exposed {d : ℕ} (c : Contact.Cell d)
    (hc : Contact.IsChairCell c) {p : Point d} (hp : p ∈ closedIntegerCell c)
    (a : Fin d) (b : Bool) (hend : p a = (c a : ℝ)+(if b then 0 else 1))
    (hcone : carrierLinearCone p ⊆ carrierAxisHalfspace a b) :
    ¬ Contact.IsChairCell ({cell := c,axis := a,positive := !b} : Contact.Facet d).neighbor := by
  let f : Contact.Facet d := {cell := c,axis := a,positive := !b}
  intro hneighbor
  have hpn : p ∈ closedIntegerCell f.neighbor := by
    intro j
    by_cases hja : j = a
    · subst j
      cases b <;>
        simp [f,Contact.Facet.neighbor,Contact.Facet.normal] at hend ⊢ <;>
        constructor <;> linarith
    · simpa [f,Contact.Facet.neighbor,hja] using hp j
  have hen : p a = (f.neighbor a : ℝ)+(if !b then 0 else 1) := by
    cases b <;> simp [f,Contact.Facet.neighbor,Contact.Facet.normal] at hend ⊢ <;> linarith
  have hv := hcone (carrierCellAxisVector_mem_cone f.neighbor hneighbor hpn a (!b) hen)
  cases b <;> norm_num [carrierAxisHalfspace,carrierCellAxisVector,EuclideanSpace.single_apply] at hv

/-- Two distinct certified active axes exhaust any rank-two carrier
inventory. All other unit-cell coordinates are consequently strict. -/
theorem carrier_critical_axes_covered_of_card_le_two {d : ℕ} (p : Point d)
    (i j : Fin d) (hij : i ≠ j)
    (hi : i ∈ carrierCriticalAxes p) (hj : j ∈ carrierCriticalAxes p)
    (hcard : (carrierCriticalAxes p).card ≤ 2) :
    ∀ a ∈ carrierCriticalAxes p, a = i ∨ a = j := by
  classical
  intro a ha
  by_contra h
  push_neg at h
  have hsub : ({i,j,a} : Finset (Fin d)) ⊆ carrierCriticalAxes p := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hle := Finset.card_le_card hsub
  have heq : ({i,j,a} : Finset (Fin d)).card = 3 := by simp [hij,h.1,h.2,Ne.symm h.1,Ne.symm h.2]
  rw [heq] at hle
  omega

/-- A native right quadrant at a carrier point yields a concrete owner unit
cell, the two correctly oriented exposed facets, and a relative-interior unit
ridge point. This is the unit-facet extraction needed by the quarter strip. -/
theorem carrier_quadrant_exists_exposed_edge {d : ℕ} {p : Point d}
    (hp : p ∈ carrier d) (i j : Fin d) (b c : Bool) (hij : i ≠ j)
    (hi : i ∈ carrierCriticalAxes p) (hj : j ∈ carrierCriticalAxes p)
    (hcritical : ∀ a ∈ carrierCriticalAxes p, a = i ∨ a = j)
    (hcone : carrierLinearCone p = carrierAxisHalfspace i b ∩ carrierAxisHalfspace j c) :
    ∃ q : Contact.Cell d, Contact.IsChairCell q ∧ p ∈ closedIntegerCell q ∧
      p i = (q i : ℝ)+(if b then 0 else 1) ∧
      p j = (q j : ℝ)+(if c then 0 else 1) ∧
      (∀ a, a ≠ i → a ≠ j → (q a : ℝ) < p a ∧ p a < (q a : ℝ)+1) ∧
      ¬ Contact.IsChairCell ({cell := q,axis := i,positive := !b} : Contact.Facet d).neighbor ∧
      ¬ Contact.IsChairCell ({cell := q,axis := j,positive := !c} : Contact.Facet d).neighbor := by
  obtain ⟨q,hq,hpq⟩ := (mem_carrier_iff_exists_chairCell p).mp hp
  have hsubi : carrierLinearCone p ⊆ carrierAxisHalfspace i b := hcone ▸ inter_subset_left
  have hsubj : carrierLinearCone p ⊆ carrierAxisHalfspace j c := hcone ▸ inter_subset_right
  have hendi := carrierCell_endpoint_of_cone_halfspace q hq hpq i b hi hsubi
  have hendj := carrierCell_endpoint_of_cone_halfspace q hq hpq j c hj hsubj
  exact ⟨q,hq,hpq,hendi,hendj,carrierCell_other_coordinates_strict q hq hpq i j hcritical,
    carrier_quadrant_facet_exposed q hq hpq i b hendi hsubi,
    carrier_quadrant_facet_exposed q hq hpq j c hendj hsubj⟩

#print axioms carrier_critical_axes_covered_of_card_le_two
#print axioms cell_inward_direction_mem_carrierLinearCone
#print axioms carrierCell_endpoint_of_cone_halfspace
#print axioms carrier_quadrant_facet_exposed
#print axioms carrier_quadrant_exists_exposed_edge
end SparseMonotiles
