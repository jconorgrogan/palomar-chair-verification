module

public import SparseMonotiles.CarrierHierarchyParent

@[expose] public section

namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Signed affine composition in the checker's output-row convention. -/
def compose {d : ℕ} (p q : Pose d) : Pose d where
  perm := p.perm.trans q.perm
  negative := fun i => xor (p.negative i) (q.negative (p.perm i))
  shift := fun i => p.sign i * q.shift (p.perm i) + p.shift i

@[simp] theorem compose_sign {d : ℕ} (p q : Pose d) (i : Fin d) :
    (compose p q).sign i = p.sign i * q.sign (p.perm i) := by
  cases hp : p.negative i <;> cases hq : q.negative (p.perm i) <;>
    simp [compose, Pose.sign, hp, hq]

/-- Lower-corner correction composes correctly, including negative rows. -/
theorem compose_cell {d : ℕ} (p q : Pose d) (c : Cell d) :
    (compose p q).cell c = p.cell (q.cell c) := by
  funext i
  simp only [Pose.cell]
  rw [compose_sign]
  simp only [compose, Equiv.trans_apply, Pose.sign]
  rcases Bool.eq_false_or_eq_true (p.negative i) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (q.negative (p.perm i)) with hq | hq <;>
    simp [hp, hq] <;> ring

theorem compose_central {d : ℕ} (p : Pose d) :
    compose p (centralPose d) = centralChild p := by
  cases p with
  | mk σ a v =>
    simp only [compose, centralPose, centralChild, Pose.sign, Pose.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · funext i
      cases a i <;> rfl
    · funext i
      simp [add_comm]

/-- Full canonical child patch of an unscaled undecorated carrier parent. -/
def children {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (p : Pose d) : Set (Pose d) :=
  {q | q = centralChild p ∨ ∃ a, Proper a ∧ q = compose p (outerPose a (σ a))}

/-- Actual complete candidate star determined by its central tile. -/
def star {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (t : Pose d) : Set (Pose d) :=
  children σ (centralParent t)

theorem mem_star_center {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (t : Pose d) :
    t ∈ star σ t := Or.inl (centralChild_parent t).symm

/-- The missing unit cell of a registered chair. -/
def hole {d : ℕ} (p : Pose d) : Cell d := p.cell (fun _ => 1)

theorem not_occupies_hole {d : ℕ} (p : Pose d) : ¬ Occupies p (hole p) := by
  intro h
  have h' : IsChairCell (fun _ : Fin d => (1 : ℤ)) := by
    simpa [Occupies, hole, p.inverseCell_cell] using h
  obtain ⟨i, hi⟩ := h'.2
  exact one_ne_zero hi

/-- The inward corner removed from outer role a is precisely 1+a. -/
theorem outer_hole {d : ℕ} (a : Bits d) (σ : Equiv.Perm (Fin d)) :
    hole (outerPose a σ) = fun i => 1 + bit a i := by
  funext i
  cases h : a i <;> simp [hole, outerPose, Pose.cell, Pose.sign, bit, h]

/-- This computed hole is genuinely owned by the canonical central child. -/
theorem central_owns_outer_hole {d : ℕ} {a : Bits d} (ha : Proper a)
    (σ : Equiv.Perm (Fin d)) :
    Occupies (centralPose d) (hole (outerPose a σ)) := by
  rw [occupies_central, outer_hole]
  constructor
  · intro i
    cases h : a i <;> simp [bit, h]
  · obtain ⟨i, hi⟩ := ha
    exact ⟨i, by simp [bit, hi]⟩

/-- Exact injectivity of the posed unit-cell action, with no pose registration
or matching-law assumption. -/
theorem cell_injective {d : ℕ} (p : Pose d) : Function.Injective p.cell := by
  intro a b h
  have hh := congrArg p.inverseCell h
  simpa [p.inverseCell_cell] using hh

/-- Occupancy commutes with affine composition. -/
theorem occupies_compose_cell {d : ℕ} (p q : Pose d) (c : Cell d) :
    Occupies (compose p q) (p.cell c) ↔ Occupies q c := by
  have he : (compose p q).inverseCell (p.cell c) = q.inverseCell c := by
    apply cell_injective (compose p q)
    rw [Pose.cell_inverseCell, compose_cell, Pose.cell_inverseCell]
  simp only [Occupies, he]

/-- The central child owns every outer child's hole in every parent frame. -/
theorem central_owns_child_hole {d : ℕ} (p : Pose d)
    {a : Bits d} (ha : Proper a) (σ : Equiv.Perm (Fin d)) :
    Occupies (centralChild p) (hole (compose p (outerPose a σ))) := by
  change Occupies (centralChild p) ((compose p (outerPose a σ)).cell (fun _ => 1))
  rw [compose_cell, ← compose_central]
  exact (occupies_compose_cell p (centralPose d) _).mpr (central_owns_outer_hole ha σ)

#print axioms compose_cell
#print axioms central_owns_child_hole
end SparseMonotiles.CarrierHierarchy
