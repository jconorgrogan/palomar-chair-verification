module

public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

/-!
# Local geometry of finite Boolean combinations of continuous inequalities

A constraint is active at `p` exactly when its defining function vanishes there.
Every inactive constraint has constant strict sign on one common neighborhood.
Thus every Boolean combination of finitely many predicates `0 ≤ f i x` has the
same germ as the expression obtained by freezing its inactive atoms at `p`.
For a feasible intersection, only the active inequalities remain.

The argument uses continuity at the point, not affinity or polyhedrality.
Continuous affine forms are an immediate specialization. `LocalSetEq.closure`
also permits passing from a Boolean set to its closure, as needed for a body
formed by closing a union-minus-dents construction.

This file proves generic infrastructure only. It does not claim a complete
face/ridge inventory, or any registration statement, for either exact tile.
-/

namespace SparseMonotiles

open Set Filter
open scoped Topology

section LocalEquality

variable {X : Type*} [TopologicalSpace X]

/-- Two sets agree on a neighborhood of a point. -/
def LocalSetEq (p : X) (s t : Set X) : Prop :=
  ∀ᶠ x in 𝓝 p, x ∈ s ↔ x ∈ t

namespace LocalSetEq

@[refl] theorem refl (p : X) (s : Set X) : LocalSetEq p s s :=
  Eventually.of_forall fun _ => Iff.rfl

@[symm] theorem symm {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    LocalSetEq p t s := h.mono fun _ hx => hx.symm

@[trans] theorem trans {p : X} {s t u : Set X}
    (hst : LocalSetEq p s t) (htu : LocalSetEq p t u) : LocalSetEq p s u :=
  (hst.and htu).mono fun _ hx => hx.1.trans hx.2

/-- Local equality is witnessed by an open neighborhood. -/
theorem exists_open {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, x ∈ s ↔ x ∈ t := by
  obtain ⟨U, hU, hopen, hp⟩ := mem_nhds_iff.mp h
  exact ⟨U, hopen, hp, fun x hx => hU hx⟩

/-- An open neighborhood with equal restrictions gives equal germs. -/
theorem of_open {p : X} {s t U : Set X} (hU : IsOpen U) (hp : p ∈ U)
    (h : ∀ x ∈ U, x ∈ s ↔ x ∈ t) : LocalSetEq p s t :=
  Filter.Eventually.mono (hU.mem_nhds hp) fun x hx => h x hx

theorem mem_iff {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    p ∈ s ↔ p ∈ t := h.self_of_nhds

theorem compl {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    LocalSetEq p sᶜ tᶜ := h.mono fun _ hx => not_congr hx

theorem inter {p : X} {s t u v : Set X}
    (hst : LocalSetEq p s t) (huv : LocalSetEq p u v) :
    LocalSetEq p (s ∩ u) (t ∩ v) :=
  (hst.and huv).mono fun _ hx => and_congr hx.1 hx.2

theorem union {p : X} {s t u v : Set X}
    (hst : LocalSetEq p s t) (huv : LocalSetEq p u v) :
    LocalSetEq p (s ∪ u) (t ∪ v) :=
  (hst.and huv).mono fun _ hx => or_congr hx.1 hx.2

theorem diff {p : X} {s t u v : Set X}
    (hst : LocalSetEq p s t) (huv : LocalSetEq p u v) :
    LocalSetEq p (s \ u) (t \ v) := hst.inter huv.compl

/-- Closure is local: no separation or regularity hypothesis is needed. -/
theorem closure {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    LocalSetEq p (_root_.closure s) (_root_.closure t) := by
  obtain ⟨U, hU, hp, heq⟩ := h.exists_open
  apply of_open hU hp
  intro x hx
  constructor
  · intro hs
    apply closure_mono (s := U ∩ s) (t := t) _ (hU.inter_closure ⟨hx, hs⟩)
    intro y hy
    exact (heq y hy.1).mp hy.2
  · intro ht
    apply closure_mono (s := U ∩ t) (t := s) _ (hU.inter_closure ⟨hx, ht⟩)
    intro y hy
    exact (heq y hy.1).mpr hy.2

end LocalSetEq
end LocalEquality

section MetricLocalEquality

variable {X : Type*} [PseudoMetricSpace X]

/-- A positive-radius ball witnesses local equality in a pseudometric space. -/
theorem LocalSetEq.exists_ball {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r, x ∈ s ↔ x ∈ t :=
  Metric.eventually_nhds_iff_ball.mp h

theorem LocalSetEq.of_ball {p : X} {s t : Set X} {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ Metric.ball p r, x ∈ s ↔ x ∈ t) : LocalSetEq p s t :=
  Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, h⟩

end MetricLocalEquality

section SignFreezing

variable {X ι : Type*} [TopologicalSpace X]

/-- A continuous function nonzero at the base point keeps that strict sign nearby. -/
theorem eventually_same_strict_sign {f : X → ℝ} {p : X}
    (hf : ContinuousAt f p) (hp : f p ≠ 0) :
    ∀ᶠ x in 𝓝 p, (0 < f x ∧ 0 < f p) ∨ (f x < 0 ∧ f p < 0) := by
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · exact (hf.eventually (Iio_mem_nhds hneg)).mono fun _ hx => Or.inr ⟨hx, hneg⟩
  · exact (hf.eventually (Ioi_mem_nhds hpos)).mono fun _ hx => Or.inl ⟨hx, hpos⟩

/-- Finitely many inactive constraints keep their signs on one common neighborhood. -/
theorem eventually_inactive_signs [Finite ι] (f : ι → X → ℝ) (p : X)
    (hf : ∀ i, ContinuousAt (f i) p) :
    ∀ᶠ x in 𝓝 p, ∀ i, f i p ≠ 0 →
      (0 < f i x ∧ 0 < f i p) ∨ (f i x < 0 ∧ f i p < 0) := by
  apply eventually_all.mpr
  intro i
  by_cases hi : f i p = 0
  · exact Eventually.of_forall fun _ hne => (hne hi).elim
  · exact (eventually_same_strict_sign (hf i) hi).mono fun _ hx _ => hx

/-- In particular, inactive weak-halfspace predicates are locally constant. -/
theorem eventually_inactive_nonneg [Finite ι] (f : ι → X → ℝ) (p : X)
    (hf : ∀ i, ContinuousAt (f i) p) :
    ∀ᶠ x in 𝓝 p, ∀ i, f i p ≠ 0 → (0 ≤ f i x ↔ 0 ≤ f i p) := by
  apply (eventually_inactive_signs f p hf).mono
  intro x hx i hi
  rcases hx i hi with hpos | hneg
  · exact ⟨fun _ => le_of_lt hpos.2, fun _ => le_of_lt hpos.1⟩
  · exact ⟨fun h => False.elim (not_le_of_gt hneg.1 h),
      fun h => False.elim (not_le_of_gt hneg.2 h)⟩

/-- One open neighborhood simultaneously freezes all inactive signs. -/
theorem exists_open_inactive_signs [Finite ι] (f : ι → X → ℝ) (p : X)
    (hf : ∀ i, ContinuousAt (f i) p) :
    ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, ∀ i, f i p ≠ 0 →
      (0 < f i x ∧ 0 < f i p) ∨ (f i x < 0 ∧ f i p < 0) := by
  obtain ⟨U, hsub, hopen, hp⟩ := mem_nhds_iff.mp (eventually_inactive_signs f p hf)
  exact ⟨U, hopen, hp, fun x hx => hsub hx⟩

/-- Active atoms retain their variable value; inactive atoms take their value at `p`. -/
noncomputable def frozenHalfspacePredicates (f : ι → X → ℝ) (p x : X) : ι → Prop := by
  classical
  exact fun i => if f i p = 0 then 0 ≤ f i x else 0 ≤ f i p

/-- Freezing works for every truth function, hence for every finite Boolean expression. -/
theorem localSetEq_freeze_truthFunction [Finite ι]
    (f : ι → X → ℝ) (p : X) (hf : ∀ i, ContinuousAt (f i) p)
    (Φ : (ι → Prop) → Prop) :
    LocalSetEq p {x | Φ (fun i => 0 ≤ f i x)}
      {x | Φ (frozenHalfspacePredicates f p x)} := by
  classical
  apply (eventually_inactive_nonneg f p hf).mono
  intro x hx
  have heq : (fun i => 0 ≤ f i x) = frozenHalfspacePredicates f p x := by
    funext i
    apply propext
    by_cases hi : f i p = 0
    · simp [frozenHalfspacePredicates, hi]
    · simpa [frozenHalfspacePredicates, hi] using hx i hi
  change Φ (fun i => 0 ≤ f i x) ↔ Φ (frozenHalfspacePredicates f p x)
  rw [heq]

/-- A feasible finite intersection has the germ of its active constraints alone. -/
theorem localSetEq_active_intersection [Finite ι]
    (f : ι → X → ℝ) (p : X) (hf : ∀ i, ContinuousAt (f i) p)
    (hp : ∀ i, 0 ≤ f i p) :
    LocalSetEq p {x | ∀ i, 0 ≤ f i x}
      {x | ∀ i, f i p = 0 → 0 ≤ f i x} := by
  apply (eventually_inactive_nonneg f p hf).mono
  intro x hx
  constructor
  · intro h i _
    exact h i
  · intro h i
    by_cases hi : f i p = 0
    · exact h i hi
    · exact (hx i hi).mpr (hp i)

/-- An empty active set at a feasible point makes the whole intersection a neighborhood. -/
theorem intersection_mem_nhds_of_strict [Finite ι]
    (f : ι → X → ℝ) (p : X) (hf : ∀ i, ContinuousAt (f i) p)
    (hp : ∀ i, 0 < f i p) : {x | ∀ i, 0 ≤ f i x} ∈ 𝓝 p := by
  apply (eventually_inactive_nonneg f p hf).mono
  intro x hx i
  exact (hx i (ne_of_gt (hp i))).mpr (le_of_lt (hp i))

end SignFreezing

/-- Finite Boolean syntax; atoms name weak-halfspace predicates. -/
inductive HalfspaceFormula (ι : Type*) where
  | truth : HalfspaceFormula ι
  | falsity : HalfspaceFormula ι
  | atom : ι → HalfspaceFormula ι
  | conj : HalfspaceFormula ι → HalfspaceFormula ι → HalfspaceFormula ι
  | disj : HalfspaceFormula ι → HalfspaceFormula ι → HalfspaceFormula ι
  | neg : HalfspaceFormula ι → HalfspaceFormula ι

namespace HalfspaceFormula

variable {ι X : Type*}

/-- Interpret a Boolean formula under a proposition-valued assignment. -/
def eval (a : ι → Prop) : HalfspaceFormula ι → Prop
  | .truth => True
  | .falsity => False
  | .atom i => a i
  | .conj A B => eval a A ∧ eval a B
  | .disj A B => eval a A ∨ eval a B
  | .neg A => ¬ eval a A

/-- Syntactically replace each inactive atom by its truth value at the base point. -/
noncomputable def freeze (f : ι → X → ℝ) (p : X) :
    HalfspaceFormula ι → HalfspaceFormula ι := by
  classical
  exact fun A => match A with
    | .truth => .truth
    | .falsity => .falsity
    | .atom i => if f i p = 0 then .atom i else if 0 ≤ f i p then .truth else .falsity
    | .conj A B => .conj (freeze f p A) (freeze f p B)
    | .disj A B => .disj (freeze f p A) (freeze f p B)
    | .neg A => .neg (freeze f p A)

/-- The syntactic freezing operation has the frozen-assignment semantics. -/
theorem eval_freeze (f : ι → X → ℝ) (p x : X) (A : HalfspaceFormula ι) :
    eval (fun i => 0 ≤ f i x) (freeze f p A) ↔
      eval (frozenHalfspacePredicates f p x) A := by
  classical
  induction A with
  | truth => rfl
  | falsity => rfl
  | atom i =>
      by_cases hi : f i p = 0
      · simp [freeze, eval, frozenHalfspacePredicates, hi]
      · by_cases hpos : 0 ≤ f i p <;>
          simp [freeze, eval, frozenHalfspacePredicates, hi, hpos]
  | conj A B hA hB => exact and_congr hA hB
  | disj A B hA hB => exact or_congr hA hB
  | neg A hA => exact not_congr hA

/-- The subset represented by a Boolean formula in the given halfspace predicates. -/
def region (f : ι → X → ℝ) (A : HalfspaceFormula ι) : Set X :=
  {x | eval (fun i => 0 ≤ f i x) A}

/-- Every finite Boolean formula agrees locally with its syntactically frozen formula. -/
theorem localSetEq_freeze [TopologicalSpace X] [Finite ι]
    (f : ι → X → ℝ) (p : X) (hf : ∀ i, ContinuousAt (f i) p)
    (A : HalfspaceFormula ι) : LocalSetEq p (region f A) (region f (freeze f p A)) := by
  apply (localSetEq_freeze_truthFunction f p hf (fun a => eval a A)).mono
  intro x hx
  exact hx.trans (eval_freeze f p x A).symm

/-- The same local reduction is valid after taking closure. -/
theorem localSetEq_closure_freeze [TopologicalSpace X] [Finite ι]
    (f : ι → X → ℝ) (p : X) (hf : ∀ i, ContinuousAt (f i) p)
    (A : HalfspaceFormula ι) :
    LocalSetEq p (closure (region f A)) (closure (region f (freeze f p A))) :=
  (localSetEq_freeze f p hf A).closure

end HalfspaceFormula

section MetricFreezing

variable {X ι : Type*} [PseudoMetricSpace X] [Finite ι]

/-- Metric-ball form of simultaneous inactive-sign freezing. -/
theorem exists_ball_inactive_signs (f : ι → X → ℝ) (p : X)
    (hf : ∀ i, ContinuousAt (f i) p) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r, ∀ i, f i p ≠ 0 →
      (0 < f i x ∧ 0 < f i p) ∨ (f i x < 0 ∧ f i p < 0) :=
  Metric.eventually_nhds_iff_ball.mp (eventually_inactive_signs f p hf)

/-- Metric-ball form of the active-constraint description of a feasible intersection. -/
theorem exists_ball_active_intersection (f : ι → X → ℝ) (p : X)
    (hf : ∀ i, ContinuousAt (f i) p) (hp : ∀ i, 0 ≤ f i p) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r,
      (∀ i, 0 ≤ f i x) ↔ (∀ i, f i p = 0 → 0 ≤ f i x) :=
  (localSetEq_active_intersection f p hf hp).exists_ball

/-- Metric-ball form of Boolean freezing, also available after closure via `LocalSetEq`. -/
theorem HalfspaceFormula.exists_ball_freeze (f : ι → X → ℝ) (p : X)
    (hf : ∀ i, ContinuousAt (f i) p) (A : HalfspaceFormula ι) :
    ∃ r > 0, ∀ x ∈ Metric.ball p r,
      x ∈ A.region f ↔ x ∈ (A.freeze f p).region f :=
  (A.localSetEq_freeze f p hf).exists_ball

end MetricFreezing

section AffineSpecialization

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [Finite ι]

/-- Continuous affine forms satisfy the generic freezing theorem without extra geometry. -/
theorem continuousAffine_localSetEq_freeze
    (f : ι → E →ᴬ[ℝ] ℝ) (p : E) (A : HalfspaceFormula ι) :
    LocalSetEq p (A.region (fun i => f i))
      ((A.freeze (fun i => f i) p).region (fun i => f i)) :=
  A.localSetEq_freeze (fun i => f i) p (fun i => (f i).continuous.continuousAt)

/-- Feasible intersections of continuous affine halfspaces have only their active germ. -/
theorem continuousAffine_localSetEq_active_intersection
    (f : ι → E →ᴬ[ℝ] ℝ) (p : E) (hp : ∀ i, 0 ≤ f i p) :
    LocalSetEq p {x | ∀ i, 0 ≤ f i x}
      {x | ∀ i, f i p = 0 → 0 ≤ f i x} :=
  localSetEq_active_intersection (fun i => f i) p
    (fun i => (f i).continuous.continuousAt) hp

end AffineSpecialization

#print axioms LocalSetEq.closure
#print axioms eventually_inactive_signs
#print axioms localSetEq_freeze_truthFunction
#print axioms localSetEq_active_intersection
#print axioms HalfspaceFormula.localSetEq_freeze
#print axioms HalfspaceFormula.localSetEq_closure_freeze
#print axioms exists_ball_active_intersection
#print axioms continuousAffine_localSetEq_freeze
#print axioms continuousAffine_localSetEq_active_intersection

end SparseMonotiles
