module

public import SparseMonotiles.CarrierHierarchyBoxes

@[expose] public section

/-!
The two-candidate parent reduction for actual complete canonical child patches.
The conclusion lives in the physical right-{id,r} quotient. Complete means that
all canonical children are actually present up to that gauge, never separate
compatible edge labels. No smaller framed contact-language lift is used.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def physicalClass {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) (p : Pose d) : PhysicalPose r hr :=
  Quotient.mk (gaugeSetoid r hr) p

def CompleteParent {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) (tiles : Set (Pose d)) (p : Pose d) : Prop :=
  ∀ q ∈ children σ p, ∃ s ∈ tiles, GaugeRel r q s

def ParentContains {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) (p t : Pose d) : Prop :=
  ∃ q ∈ children σ p, GaugeRel r q t

private theorem class_parent_of_center {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) {p t : Pose d}
    (h : physicalClass r hr (centralChild p) = physicalClass r hr t) :
    physicalClass r hr p = physicalClass r hr (centralParent t) := by
  have hp := congrArg (physicalParent r hr) h
  change physicalClass r hr (centralParent (centralChild p)) =
    physicalClass r hr (centralParent t) at hp
  simpa [centralParent_child] using hp

/-- Every complete candidate parent containing a tile is its central candidate
or its actual hole-owner's central candidate. This is proved using the real
computed outer-hole ownership, not supplied as a hierarchy interface. -/
theorem complete_parent_two_candidates {d : ℕ}
    (σ : Bits d → Equiv.Perm (Fin d)) (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) (tiles : Set (Pose d))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q)
    {p t o : Pose d} (ho : o ∈ tiles) (owns : Occupies o (hole t))
    (complete : CompleteParent σ r tiles p) (contains : ParentContains σ r p t) :
    physicalClass r hr p = physicalClass r hr (centralParent t) ∨
      physicalClass r hr p = physicalClass r hr (centralParent o) := by
  obtain ⟨q, hq, hqt⟩ := contains
  rcases hq with hq | ⟨a, ha, hq⟩
  · left
    subst q
    exact class_parent_of_center r hr (Quotient.sound hqt)
  · right
    subst q
    have hh := gauge_hole_eq hqt
    have hc : Occupies (centralChild p) (hole t) := by
      rw [← hh]
      exact central_owns_child_hole p ha (σ a)
    obtain ⟨s, hs, hcs⟩ := complete (centralChild p) (Or.inl rfl)
    have hsc : Occupies s (hole t) := (gauge_occupies_iff hcs _).mp hc
    have hso : s = o := disjoint s hs o ho _ hsc owns
    have he : physicalClass r hr (centralChild p) = physicalClass r hr o := by
      subst s
      exact Quotient.sound hcs
    exact class_parent_of_center r hr he

#print axioms complete_parent_two_candidates
end SparseMonotiles.CarrierHierarchy
