module

public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ENNReal.BigOperators

@[expose] public section

/-!
# Additivity of geometric sector widths

Closed arcs on the additive circle have their actual radian length as Haar
measure. A finite cover by closed arcs with disjoint open arcs consequently
has total width equal to the circumference. No angle-sum hypothesis occurs.

Applying this theorem to a cone requires a separate proof that its unit-circle
trace is the indicated arc. An arbitrary positive cone is not asserted to be
an arc.
-/

namespace SparseMonotiles
namespace SectorAngleSum

open Set Metric MeasureTheory
open scoped ENNReal

variable {T : ℝ} [Fact (0 < T)]

/-- A closed circular arc of radian width `θ`, represented by its midpoint.
Widths are kept in `[0,T]` by the hypotheses of the geometric theorems. -/
def closedArc (c : AddCircle T) (θ : ℝ) : Set (AddCircle T) :=
  closedBall c (θ / 2)

/-- Its boundary-free open arc; at full circumference only the antipode is
omitted, which does not change the radian measure. -/
def openArc (c : AddCircle T) (θ : ℝ) : Set (AddCircle T) :=
  ball c (θ / 2)

/-- The actual measure of a closed arc is its width. -/
theorem measure_closedArc (c : AddCircle T) {θ : ℝ} (hθ : θ ≤ T) :
    volume (closedArc c θ) = ENNReal.ofReal θ := by
  rw [closedArc, AddCircle.volume_closedBall]
  congr 1
  rw [show 2 * (θ / 2) = θ by ring, min_eq_right hθ]

/-- Arc endpoints have zero measure, including zero and full-width cases. -/
theorem closedArc_ae_eq_openArc (c : AddCircle T) (θ : ℝ) :
    closedArc c θ =ᵐ[volume] openArc c θ :=
  AddCircle.closedBall_ae_eq_ball

/-- Finite geometric circular partitions have the full circumference as the
sum of their widths. The only partition premises are coverage and disjointness
of the open arcs; touching closed endpoints are allowed. -/
theorem sum_width_eq_circumference {ι : Type*} [Fintype ι]
    (center : ι → AddCircle T) (width : ι → ℝ)
    (hwidth : ∀ i, 0 ≤ width i ∧ width i ≤ T)
    (hcover : (⋃ i, closedArc (center i) (width i)) = univ)
    (hdisjoint : Pairwise (fun i j =>
      Disjoint (openArc (center i) (width i)) (openArc (center j) (width j)))) :
    ∑ i, width i = T := by
  have hd : Pairwise (fun i j =>
      AEDisjoint volume (closedArc (center i) (width i))
        (closedArc (center j) (width j))) := by
    intro i j hij
    exact (hdisjoint hij).aedisjoint.congr
      (closedArc_ae_eq_openArc (center i) (width i))
      (closedArc_ae_eq_openArc (center j) (width j))
  have hm := measure_iUnion₀ hd (fun i =>
    (measurableSet_closedBall : MeasurableSet (closedArc (center i) (width i))).nullMeasurableSet)
  rw [hcover, AddCircle.measure_univ, tsum_fintype] at hm
  simp_rw [measure_closedArc _ (hwidth _).2] at hm
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hwidth i).1)] at hm
  have hr := congrArg ENNReal.toReal hm
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ T from (Fact.out : 0 < T).le),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => (hwidth i).1))] using hr.symm

/-- The plane's circumference specialization, with actual radian units. -/
theorem sum_width_eq_two_pi {ι : Type*} [Fintype ι]
    (center : ι → AddCircle (2 * Real.pi)) (width : ι → ℝ)
    (hwidth : ∀ i, 0 ≤ width i ∧ width i ≤ 2 * Real.pi)
    (hcover : (⋃ i, closedArc (center i) (width i)) = univ)
    (hdisjoint : Pairwise (fun i j =>
      Disjoint (openArc (center i) (width i)) (openArc (center j) (width j)))) :
    ∑ i, width i = 2 * Real.pi := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  exact sum_width_eq_circumference center width hwidth hcover hdisjoint

#print axioms sum_width_eq_circumference
#print axioms sum_width_eq_two_pi

end SectorAngleSum
end SparseMonotiles
