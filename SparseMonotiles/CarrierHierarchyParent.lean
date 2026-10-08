module

public import SparseMonotiles.CarrierHierarchyCells

@[expose] public section

/-!
The unscaled undecorated-carrier parent determined by its central child, for the
μ = 1 substitutions used by T5 and T7. It is an actual pose operation, with an
inverse central-child operation. It commutes with right multiplication by any
unsigned coordinate involution, so it descends to the precise right-{id,r}
quotient used for T5. No claim of a global lift to a smaller contact language is
made. Physical realization of this quotient still requires the separate exact
body-symmetry and registration theorems.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Unscaled parent: its central child has shift v + G·1. -/
def centralParent {d : ℕ} (t : Pose d) : Pose d where
  perm := t.perm
  negative := t.negative
  shift := fun i => t.shift i - t.sign i

/-- Central child of an unscaled parent, not refinement of the decorated body. -/
def centralChild {d : ℕ} (p : Pose d) : Pose d where
  perm := p.perm
  negative := p.negative
  shift := fun i => p.shift i + p.sign i

theorem centralChild_parent {d : ℕ} (t : Pose d) :
    centralChild (centralParent t) = t := by
  cases t with
  | mk σ a v =>
    simp only [centralChild, centralParent, Pose.sign, Pose.mk.injEq, true_and]
    funext i
    change (v i - (if a i then (-1 : ℤ) else 1)) + (if a i then (-1 : ℤ) else 1) = v i
    exact sub_add_cancel _ _

theorem centralParent_child {d : ℕ} (p : Pose d) :
    centralParent (centralChild p) = p := by
  cases p with
  | mk σ a v =>
    simp only [centralChild, centralParent, Pose.sign, Pose.mk.injEq, true_and]
    funext i
    change (v i + (if a i then (-1 : ℤ) else 1)) - (if a i then (-1 : ℤ) else 1) = v i
    exact add_sub_cancel_right _ _

/-- The actual candidate parent is uniquely fixed by its central child. -/
theorem central_parent_unique {d : ℕ} {p t : Pose d}
    (h : centralChild p = t) : p = centralParent t := by
  rw [← h, centralParent_child]

/-- Right multiplication by an unsigned coordinate permutation. In the
output-row convention the permutation is r ∘ p.perm, not p.perm ∘ r. -/
def rightGauge {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) : Pose d where
  perm := p.perm.trans r
  negative := p.negative
  shift := p.shift

@[simp] theorem centralParent_rightGauge {d : ℕ} (r : Equiv.Perm (Fin d))
    (p : Pose d) : centralParent (rightGauge r p) = rightGauge r (centralParent p) := rfl

@[simp] theorem centralChild_rightGauge {d : ℕ} (r : Equiv.Perm (Fin d))
    (p : Pose d) : centralChild (rightGauge r p) = rightGauge r (centralChild p) := rfl

/-- In particular, the unscaled parent anchor is representative-independent. -/
theorem centralParent_anchor_gauge {d : ℕ} (r : Equiv.Perm (Fin d))
    (p : Pose d) : (centralParent (rightGauge r p)).shift = (centralParent p).shift := rfl

private theorem rightGauge_twice {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) (p : Pose d) :
    rightGauge r (rightGauge r p) = p := by
  cases p with
  | mk σ a v =>
    simp only [rightGauge]
    congr 1
    ext i
    exact congrArg Fin.val (hr (σ i))

/-- Exactly two allowed representatives, without quotienting by the entire
coordinate-permutation group or presupposing all body self-isometries. -/
def GaugeRel {d : ℕ} (r : Equiv.Perm (Fin d)) (p q : Pose d) : Prop :=
  q = p ∨ q = rightGauge r p

def gaugeSetoid {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) : Setoid (Pose d) where
  r := GaugeRel r
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro p q h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (rightGauge_twice r hr p).symm
    trans := by
      intro p q s hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (rightGauge_twice r hr p) }

abbrev PhysicalPose {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) := Quotient (gaugeSetoid r hr)

theorem centralParent_respects_gauge {d : ℕ} (r : Equiv.Perm (Fin d))
    {p q : Pose d} (h : GaugeRel r p q) :
    GaugeRel r (centralParent p) (centralParent q) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem centralChild_respects_gauge {d : ℕ} (r : Equiv.Perm (Fin d))
    {p q : Pose d} (h : GaugeRel r p q) :
    GaugeRel r (centralChild p) (centralChild q) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

def physicalParent {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) : PhysicalPose r hr → PhysicalPose r hr :=
  Quotient.map centralParent (fun _ _ h => centralParent_respects_gauge r h)

def physicalCentralChild {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) : PhysicalPose r hr → PhysicalPose r hr :=
  Quotient.map centralChild (fun _ _ h => centralChild_respects_gauge r h)

/-- The quotient parent and central-child maps are mutually inverse. -/
theorem physicalCentralChild_parent {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) (t : PhysicalPose r hr) :
    physicalCentralChild r hr (physicalParent r hr t) = t := by
  refine Quotient.inductionOn t ?_
  intro p
  change Quotient.mk _ (centralChild (centralParent p)) = Quotient.mk _ p
  rw [centralChild_parent]

theorem physicalParent_child {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) (p : PhysicalPose r hr) :
    physicalParent r hr (physicalCentralChild r hr p) = p := by
  refine Quotient.inductionOn p ?_
  intro p
  change Quotient.mk _ (centralParent (centralChild p)) = Quotient.mk _ p
  rw [centralParent_child]

/-- No independent choice of representatives at different parents or levels is
needed to compute the unique physical candidate central parent. -/
theorem physical_parent_unique {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) {p t : PhysicalPose r hr}
    (h : physicalCentralChild r hr p = t) : p = physicalParent r hr t := by
  rw [← h, physicalParent_child]

#print axioms central_parent_unique
#print axioms physical_parent_unique
#print axioms physicalCentralChild_parent
end SparseMonotiles.CarrierHierarchy
