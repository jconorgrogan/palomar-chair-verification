module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section


/-!
# Angular measure of literal planar halfspace sectors

Angular measure is the ordinary Haar measure on `Real.Angle`, normalized to
total mass `2 * pi`. Membership is determined by the inner product of an
actual cos/sin unit direction with an actual planar normal. No sector angle
or angle-sum law is assumed.
-/

namespace PhysicalRegistration.PlanarSectorMeasure
open Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace
noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

noncomputable instance angleMeasureSpace : MeasureSpace Real.Angle :=
  AddCircle.measureSpace (2 * Real.pi)

instance angleBorelSpace : BorelSpace Real.Angle := by
  change @BorelSpace (AddCircle (2 * Real.pi)) _ _
  infer_instance

instance angleFiniteMeasure : IsFiniteMeasure (volume : Measure Real.Angle) :=
  AddCircle.isFiniteMeasure (2 * Real.pi)

instance angleHaarMeasure : IsAddHaarMeasure (volume : Measure Real.Angle) := by
  change IsAddHaarMeasure (volume : Measure (AddCircle (2 * Real.pi)))
  infer_instance

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The actual unit direction with angular coordinate `θ`. -/
def direction (θ : Real.Angle) : Plane := WithLp.toLp 2 ![θ.cos, θ.sin]

/-- Directions lying in the closed material halfplane with outward normal `n`. -/
def halfplane (n : Plane) : Set Real.Angle := {θ | ⟪n, direction θ⟫_ℝ ≤ 0}

theorem inner_direction (α θ : Real.Angle) :
    ⟪direction α, direction θ⟫_ℝ = (θ - α).cos := by
  simp [direction, PiLp.inner_apply, Fin.sum_univ_two, sub_eq_add_neg,
    Real.Angle.cos_add, mul_comm]

theorem norm_direction (θ : Real.Angle) : ‖direction θ‖ = 1 := by
  have h := @real_inner_self_eq_norm_sq Plane _ _ (direction θ)
  rw [inner_direction, sub_self, Real.Angle.cos_zero] at h
  nlinarith [norm_nonneg (direction θ)]

theorem direction_ne_zero (θ : Real.Angle) : direction θ ≠ 0 := by
  intro h
  have := norm_direction θ
  simp [h] at this

theorem angle_direction (α θ : Real.Angle) :
    InnerProductGeometry.angle (direction α) (direction θ) = |(θ - α).toReal| := by
  rw [InnerProductGeometry.angle, inner_direction, norm_direction, norm_direction,
    mul_one, div_one, ← Real.Angle.cos_toReal, ← Real.cos_abs]
  exact Real.arccos_cos (abs_nonneg _) (Real.Angle.abs_toReal_le_pi _)

/-- The same literal halfplane in angular coordinates. -/
def angularHalfplane (α : Real.Angle) : Set Real.Angle :=
  {θ | (θ - α).cos ≤ 0}

theorem halfplane_direction (α : Real.Angle) : halfplane (direction α) = angularHalfplane α := by
  ext θ
  simp [halfplane, angularHalfplane, inner_direction]

theorem halfplane_pos_smul {r : ℝ} (hr : 0 < r) (n : Plane) :
    halfplane (r • n) = halfplane n := by
  ext θ
  simp only [halfplane, mem_ofPred_eq, real_inner_smul_left]
  constructor <;> intro h <;> nlinarith

theorem measurableSet_angularHalfplane (α : Real.Angle) :
    MeasurableSet (angularHalfplane α) := by
  exact isClosed_le (Real.Angle.continuous_cos.comp (continuous_id.sub continuous_const))
    continuous_const |>.measurableSet

private theorem cos_nonpos_iff_in_chart {x : ℝ}
    (hx₁ : -(Real.pi / 2) < x) (hx₂ : x ≤ Real.pi + Real.pi / 2) :
    Real.cos x ≤ 0 ↔ Real.pi / 2 ≤ x := by
  constructor
  · intro h
    by_contra hn
    have hp := Real.cos_pos_of_mem_Ioo ⟨hx₁, lt_of_not_ge hn⟩
    linarith
  · intro h
    exact Real.cos_nonpos_of_pi_div_two_le_of_le h hx₂

private theorem canonical_intersection_lift {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδπ : δ < Real.pi) :
    ((fun x : ℝ => (x : Real.Angle)) ⁻¹'
        (angularHalfplane 0 ∩ angularHalfplane (δ : Real.Angle))) ∩
        Ioc (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi) =
      Icc (Real.pi / 2 + δ) (3 * Real.pi / 2) := by
  ext x
  simp only [mem_inter_iff, mem_preimage, angularHalfplane, mem_ofPred_eq,
    sub_zero, ← Real.Angle.coe_sub, Real.Angle.cos_coe, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨hc, hd⟩, hx₁, hx₂⟩
    have hx : Real.pi / 2 ≤ x :=
      (cos_nonpos_iff_in_chart hx₁ (by linarith)).mp hc
    have hdlo : Real.pi / 2 ≤ x - δ := by
      by_contra hn
      have hlow : -(Real.pi / 2) < x - δ := by linarith
      have hp := Real.cos_pos_of_mem_Ioo ⟨hlow, lt_of_not_ge hn⟩
      linarith
    constructor <;> linarith
  · rintro ⟨hx₁, hx₂⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    · exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
    · linarith [Real.pi_pos]
    · linarith

/-- The intersection mass is derived from its exact real interval lift. -/
theorem volume_angularHalfplane_inter {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδπ : δ < Real.pi) :
    volume (angularHalfplane 0 ∩ angularHalfplane (δ : Real.Angle)) =
      ENNReal.ofReal (Real.pi - δ) := by
  have hp := AddCircle.add_projection_respects_measure (2 * Real.pi) (-(Real.pi / 2))
    (U := angularHalfplane 0 ∩ angularHalfplane (δ : Real.Angle))
    ((measurableSet_angularHalfplane 0).inter (measurableSet_angularHalfplane _))
  change volume (angularHalfplane 0 ∩ angularHalfplane (δ : Real.Angle)) =
    volume (((fun x : ℝ => (x : Real.Angle)) ⁻¹'
      (angularHalfplane 0 ∩ angularHalfplane (δ : Real.Angle))) ∩
      Ioc (-(Real.pi / 2)) (-(Real.pi / 2) + 2 * Real.pi)) at hp
  rw [hp, canonical_intersection_lift hδ₀ hδπ, Real.volume_Icc]
  congr 1
  ring

/-- Every literal angular halfplane has angular mass `pi`. -/
theorem volume_angularHalfplane (α : Real.Angle) :
    volume (angularHalfplane α) = ENNReal.ofReal Real.pi := by
  have hz : volume (angularHalfplane 0) = ENNReal.ofReal Real.pi := by
    simpa using volume_angularHalfplane_inter (δ := 0) (by rfl) Real.pi_pos
  have heq : angularHalfplane α = (fun θ : Real.Angle => θ + -α) ⁻¹' angularHalfplane 0 := by
    ext θ
    simp [angularHalfplane, sub_eq_add_neg]
  rw [heq, measure_preimage_add_right, hz]

/-- The reflex material sector has the complementary `pi + δ` mass. -/
theorem volume_angularHalfplane_union {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδπ : δ < Real.pi) :
    volume (angularHalfplane 0 ∪ angularHalfplane (δ : Real.Angle)) =
      ENNReal.ofReal (Real.pi + δ) := by
  have h := measure_union_add_inter (μ := (volume : Measure Real.Angle))
    (angularHalfplane 0) (measurableSet_angularHalfplane (δ : Real.Angle))
  rw [volume_angularHalfplane_inter hδ₀ hδπ, volume_angularHalfplane,
    volume_angularHalfplane] at h
  apply (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp
  rw [h, ← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le,
    ← ENNReal.ofReal_add (by linarith : 0 ≤ Real.pi + δ) (by linarith : 0 ≤ Real.pi - δ)]
  congr 1
  ring

/-- Rotation of both concrete halfplanes preserves their intersection mass. -/
theorem volume_angularHalfplane_inter_add (α δ : Real.Angle) :
    volume (angularHalfplane α ∩ angularHalfplane (α + δ)) =
      volume (angularHalfplane 0 ∩ angularHalfplane δ) := by
  have heq : angularHalfplane α ∩ angularHalfplane (α + δ) =
      (fun θ : Real.Angle => θ + -α) ⁻¹' (angularHalfplane 0 ∩ angularHalfplane δ) := by
    ext θ
    simp only [angularHalfplane, mem_inter_iff, mem_ofPred_eq, mem_preimage, sub_zero]
    abel_nf
  rw [heq, measure_preimage_add_right]

/-- Reflection changes the sign of the second normal angle without changing mass. -/
theorem volume_angularHalfplane_inter_neg (δ : Real.Angle) :
    volume (angularHalfplane 0 ∩ angularHalfplane (-δ)) =
      volume (angularHalfplane 0 ∩ angularHalfplane δ) := by
  calc
    _ = volume (angularHalfplane (-δ) ∩ angularHalfplane ((-δ) + δ)) := by
      simp [inter_comm]
    _ = _ := volume_angularHalfplane_inter_add (-δ) δ

/-- The arbitrary-rotation formula, including either orientation of the normals. -/
theorem volume_angularHalfplane_inter_general (α β : Real.Angle)
    (h : |(β - α).toReal| < Real.pi) :
    volume (angularHalfplane α ∩ angularHalfplane β) =
      ENNReal.ofReal (Real.pi - |(β - α).toReal|) := by
  have hrot := volume_angularHalfplane_inter_add α (β - α)
  simp only [add_sub_cancel] at hrot
  rw [hrot]
  let δ := (β - α).toReal
  have hcoe : (δ : Real.Angle) = β - α := Real.Angle.coe_toReal _
  change volume (angularHalfplane 0 ∩ angularHalfplane (β - α)) =
    ENNReal.ofReal (Real.pi - |δ|)
  conv_lhs => rw [← hcoe]
  by_cases hd : 0 ≤ δ
  · rw [abs_of_nonneg hd] at h ⊢
    exact volume_angularHalfplane_inter hd h
  · have hd' : 0 ≤ -δ := by linarith
    rw [abs_of_neg (lt_of_not_ge hd)] at h ⊢
    rw [← neg_neg (δ : Real.Angle), volume_angularHalfplane_inter_neg,
      ← Real.Angle.coe_neg]
    exact volume_angularHalfplane_inter hd' h

/-- Every nonzero vector in the real Euclidean plane has an actual polar representation. -/
theorem exists_pos_smul_direction {n : Plane} (hn : n ≠ 0) :
    ∃ (r : ℝ) (α : Real.Angle), 0 < r ∧ n = r • direction α := by
  let z : ℂ := ⟨n 0, n 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply hn
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  refine ⟨‖z‖, (z.arg : Real.Angle), norm_pos_iff.mpr hz, ?_⟩
  ext i
  fin_cases i
  · simp [direction, z]
  · simp [direction, z]

/-- The measure formula for two arbitrary, non-antipodal, nonzero outward normals. -/
theorem volume_halfplane_inter {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (hangle : InnerProductGeometry.angle n m < Real.pi) :
    volume (halfplane n ∩ halfplane m) =
      ENNReal.ofReal (Real.pi - InnerProductGeometry.angle n m) := by
  obtain ⟨r, α, hr, rfl⟩ := exists_pos_smul_direction hn
  obtain ⟨s, β, hs, rfl⟩ := exists_pos_smul_direction hm
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hs, angle_direction] at hangle ⊢
  rw [halfplane_pos_smul hr, halfplane_pos_smul hs, halfplane_direction, halfplane_direction]
  exact volume_angularHalfplane_inter_general α β hangle

theorem measurableSet_halfplane (n : Plane) : MeasurableSet (halfplane n) := by
  by_cases hn : n = 0
  · simp [hn, halfplane]
  · obtain ⟨r, α, hr, rfl⟩ := exists_pos_smul_direction hn
    rw [halfplane_pos_smul hr, halfplane_direction]
    exact measurableSet_angularHalfplane α

theorem volume_halfplane {n : Plane} (hn : n ≠ 0) :
    volume (halfplane n) = ENNReal.ofReal Real.pi := by
  obtain ⟨r, α, hr, rfl⟩ := exists_pos_smul_direction hn
  rw [halfplane_pos_smul hr, halfplane_direction, volume_angularHalfplane]

/-- The reflex sector of arbitrary nonzero non-antipodal outward normals. -/
theorem volume_halfplane_union {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (hangle : InnerProductGeometry.angle n m < Real.pi) :
    volume (halfplane n ∪ halfplane m) =
      ENNReal.ofReal (Real.pi + InnerProductGeometry.angle n m) := by
  have h := measure_union_add_inter (μ := (volume : Measure Real.Angle))
    (halfplane n) (measurableSet_halfplane m)
  rw [volume_halfplane_inter hn hm hangle, volume_halfplane hn, volume_halfplane hm] at h
  apply (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp
  rw [h, ← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le,
    ← ENNReal.ofReal_add
      (by linarith [Real.pi_pos, InnerProductGeometry.angle_nonneg n m])
      (by linarith : 0 ≤ Real.pi - InnerProductGeometry.angle n m)]
  congr 1
  ring

/-- Orthogonal nonzero normals cut a quarter of the direction circle. -/
theorem volume_orthogonal_quadrant {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (horth : ⟪n, m⟫_ℝ = 0) :
    volume (halfplane n ∩ halfplane m) = ENNReal.ofReal (Real.pi / 2) := by
  have ha := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two n m).mp horth
  rw [volume_halfplane_inter hn hm (by rw [ha]; linarith [Real.pi_pos]), ha]
  congr 1
  ring

instance angleNullSingleton : NullSingletonClass (volume : Measure Real.Angle) where
  measure_singleton θ := by
    have h := AddCircle.volume_closedBall (2 * Real.pi) (x := θ) 0
    change volume (Metric.closedBall θ 0) = ENNReal.ofReal (min (2 * Real.pi) (2 * 0)) at h
    simpa only [Metric.closedBall_zero, mul_zero, min_eq_right Real.two_pi_pos.le,
      ENNReal.ofReal_zero] using h

/-- A genuine planar line has only finitely many unit directions. -/
theorem finite_normal_boundary {n : Plane} (hn : n ≠ 0) :
    {θ | ⟪n, direction θ⟫_ℝ = 0}.Finite := by
  obtain ⟨r, α, hr, rfl⟩ := exists_pos_smul_direction hn
  have heq : {θ | ⟪r • direction α, direction θ⟫_ℝ = 0} =
      {α + (Real.pi / 2 : ℝ), α + (-Real.pi / 2 : ℝ)} := by
    ext θ
    simp only [mem_ofPred_eq, real_inner_smul_left, inner_direction, mul_eq_zero,
      ne_of_gt hr, false_or, Real.Angle.cos_eq_zero_iff, mem_insert_iff,
      mem_singleton_iff]
    constructor <;> intro h <;> rcases h with h | h
    · left; exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · right; exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · left; rw [h]; abel
    · right; rw [h]; abel
  rw [heq]
  exact (finite_singleton _).insert _

theorem volume_normal_boundary {n : Plane} (hn : n ≠ 0) :
    volume {θ | ⟪n, direction θ⟫_ℝ = 0} = 0 :=
  (finite_normal_boundary hn).measure_zero volume

/-- Strict material halfplanes differ from closed ones only on a null line. -/
def strictHalfplane (n : Plane) : Set Real.Angle := {θ | ⟪n, direction θ⟫_ℝ < 0}

theorem strictHalfplane_ae_halfplane {n : Plane} (hn : n ≠ 0) :
    strictHalfplane n =ᵐ[volume] halfplane n := by
  apply ae_iff.mpr
  apply measure_mono_null (t := {θ | ⟪n, direction θ⟫_ℝ = 0}) _ (volume_normal_boundary hn)
  intro θ hθ
  simp only [strictHalfplane, halfplane, mem_ofPred_eq] at hθ ⊢
  by_contra hne
  exact hθ (propext (lt_iff_le_and_ne.trans (and_iff_left hne)))

/-- All four orthogonal strict sign quadrants have mass `pi/2`; negate either
normal to select its other sign. -/
theorem volume_strict_orthogonal_quadrant {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (horth : ⟪n, m⟫_ℝ = 0) :
    volume (strictHalfplane n ∩ strictHalfplane m) = ENNReal.ofReal (Real.pi / 2) := by
  rw [measure_congr ((strictHalfplane_ae_halfplane hn).inter (strictHalfplane_ae_halfplane hm))]
  exact volume_orthogonal_quadrant hn hm horth

theorem finite_frontier_halfplane {n : Plane} (hn : n ≠ 0) :
    (frontier (halfplane n)).Finite := by
  obtain ⟨r, α, hr, rfl⟩ := exists_pos_smul_direction hn
  rw [halfplane_pos_smul hr, halfplane_direction]
  apply (finite_normal_boundary (direction_ne_zero α)).subset
  intro θ hθ
  have h := frontier_le_subset_eq
    (Real.Angle.continuous_cos.comp (continuous_id.sub continuous_const))
    continuous_const hθ
  simpa [inner_direction] using h

theorem finite_frontier_inter {s t : Set Real.Angle}
    (hs : (frontier s).Finite) (ht : (frontier t).Finite) :
    (frontier (s ∩ t)).Finite := by
  apply (hs.union ht).subset
  exact (frontier_inter_subset s t).trans (union_subset_union inter_subset_left inter_subset_right)

theorem finite_frontier_union {s t : Set Real.Angle}
    (hs : (frontier s).Finite) (ht : (frontier t).Finite) :
    (frontier (s ∪ t)).Finite := by
  apply (hs.union ht).subset
  exact (frontier_union_subset s t).trans (union_subset_union inter_subset_left inter_subset_right)

/-- Conservation of actual angular measure for any finite measurable cover
whose interiors are pairwise disjoint and whose boundaries are finite.
These hypotheses can be established from physical germs; no angle-sum law is input. -/
theorem finite_sector_cover_total {ι : Type*} [Fintype ι] (S : ι → Set Real.Angle)
    (hS : ∀ i, MeasurableSet (S i)) (hb : ∀ i, (frontier (S i)).Finite)
    (hd : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j)))
    (hc : ⋃ i, S i = univ) :
    ∑ i, volume (S i) = ENNReal.ofReal (2 * Real.pi) := by
  have had : Pairwise (fun i j => AEDisjoint volume (S i) (S j)) := by
    intro i j hij
    apply measure_mono_null (t := frontier (S i) ∪ frontier (S j)) _
      (((hb i).union (hb j)).measure_zero volume)
    intro θ hθ
    by_cases hi : θ ∈ interior (S i)
    · right
      exact ⟨subset_closure hθ.2, fun hj => (Set.disjoint_left.mp (hd hij)) hi hj⟩
    · left
      exact ⟨subset_closure hθ.1, hi⟩
  have hm := measure_iUnion₀ had (fun i => (hS i).nullMeasurableSet)
  rw [hc, tsum_fintype] at hm
  rw [← hm]
  exact AddCircle.measure_univ (2 * Real.pi)

/-- The real-valued conservation law used for material-angle balance. -/
theorem finite_sector_cover_total_real {ι : Type*} [Fintype ι] (S : ι → Set Real.Angle)
    (hS : ∀ i, MeasurableSet (S i)) (hb : ∀ i, (frontier (S i)).Finite)
    (hd : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j)))
    (hc : ⋃ i, S i = univ) :
    ∑ i, (volume (S i)).toReal = 2 * Real.pi := by
  have h := congrArg ENNReal.toReal (finite_sector_cover_total S hS hb hd hc)
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top volume (S i)),
    ENNReal.toReal_ofReal Real.two_pi_pos.le] at h
  exact h

/-- One of the four open sign cells of two actual normal coordinates. -/
def signQuadrant (n m : Plane) (q : Bool × Bool) : Set Real.Angle :=
  strictHalfplane (if q.1 then n else -n) ∩
    strictHalfplane (if q.2 then m else -m)

theorem volume_signQuadrant {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (horth : ⟪n, m⟫_ℝ = 0) (q : Bool × Bool) :
    volume (signQuadrant n m q) = ENNReal.ofReal (Real.pi / 2) := by
  rcases q with ⟨a, b⟩
  cases a <;> cases b <;> simp only [signQuadrant, Bool.false_eq_true, ite_false, ite_true]
  all_goals apply volume_strict_orthogonal_quadrant <;> simp_all

theorem nullMeasurableSet_strictHalfplane (n : Plane) :
    NullMeasurableSet (strictHalfplane n) volume := by
  by_cases hn : n = 0
  · simp [hn, strictHalfplane]
  · exact (measurableSet_halfplane n).nullMeasurableSet.congr
      (strictHalfplane_ae_halfplane hn).symm

theorem nullMeasurableSet_signQuadrant (n m : Plane) (q : Bool × Bool) :
    NullMeasurableSet (signQuadrant n m q) volume :=
  (nullMeasurableSet_strictHalfplane _).inter (nullMeasurableSet_strictHalfplane _)

theorem pairwise_disjoint_signQuadrant (n m : Plane) :
    Pairwise (fun q r => Disjoint (signQuadrant n m q) (signQuadrant n m r)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [signQuadrant, strictHalfplane, Set.disjoint_left]
  all_goals intros; linarith

/-- A Boolean selection of actual orthogonal sign cells has an integer
multiple of a quarter-turn as its angular mass. -/
theorem volume_selected_signQuadrants {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (horth : ⟪n, m⟫_ℝ = 0) (Q : Finset (Bool × Bool)) :
    volume (⋃ q ∈ Q, signQuadrant n m q) =
      ENNReal.ofReal ((Q.card : ℝ) * (Real.pi / 2)) := by
  rw [measure_biUnion_finset₀
    (fun _ _ _ _ h => (pairwise_disjoint_signQuadrant n m h).aedisjoint)
    (fun q _ => nullMeasurableSet_signQuadrant n m q)]
  simp_rw [volume_signQuadrant hn hm horth]
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]


/-- A literal Boolean rule applied to the two actual inner-product signs. -/
def booleanSignSector (n m : Plane) (P : Bool × Bool → Prop) : Set Real.Angle :=
  {θ | P (decide (⟪n, direction θ⟫_ℝ < 0), decide (⟪m, direction θ⟫_ℝ < 0))}

theorem signQuadrant_mem_iff {n m : Plane} {θ : Real.Angle}
    (hn : ⟪n, direction θ⟫_ℝ ≠ 0) (hm : ⟪m, direction θ⟫_ℝ ≠ 0)
    (q : Bool × Bool) :
    θ ∈ signQuadrant n m q ↔
      q = (decide (⟪n, direction θ⟫_ℝ < 0), decide (⟪m, direction θ⟫_ℝ < 0)) := by
  rcases q with ⟨a, b⟩
  cases a <;> cases b <;>
    rcases lt_or_gt_of_ne hn with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hm with h₂ | h₂ <;>
    simp [signQuadrant, strictHalfplane, h₁, h₂, not_lt_of_gt]

/-- The axes are null, so any literal Boolean sign rule has exactly the mass
of the open quadrants it selects. -/
theorem booleanSignSector_ae_quadrants {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Bool × Bool → Prop) [DecidablePred P] :
    booleanSignSector n m P =ᵐ[volume] ⋃ q ∈ (Finset.univ.filter P), signQuadrant n m q := by
  classical
  apply ae_iff.mpr
  apply measure_mono_null (t := {θ | ⟪n, direction θ⟫_ℝ = 0} ∪ {θ | ⟪m, direction θ⟫_ℝ = 0}) _
    (measure_union_null (volume_normal_boundary hn) (volume_normal_boundary hm))
  intro θ hθ
  by_contra h
  have hnθ : ⟪n, direction θ⟫_ℝ ≠ 0 := fun h' => h (Or.inl h')
  have hmθ : ⟪m, direction θ⟫_ℝ ≠ 0 := fun h' => h (Or.inr h')
  apply hθ
  apply propext
  simp [booleanSignSector, signQuadrant_mem_iff hnθ hmθ]

/-- Every Boolean sign germ on two independent orthogonal coordinates has an
actual angular mass that is an integer multiple of `pi/2`. -/
theorem volume_booleanSignSector {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (horth : ⟪n, m⟫_ℝ = 0) (P : Bool × Bool → Prop) [DecidablePred P] :
    volume (booleanSignSector n m P) =
      ENNReal.ofReal (((Finset.univ.filter P).card : ℝ) * (Real.pi / 2)) := by
  classical
  rw [measure_congr (booleanSignSector_ae_quadrants hn hm P)]
  exact volume_selected_signQuadrants hn hm horth _


/-- The same literal halfplane calculation in any isometrically coordinatized
real two-dimensional normal plane. -/
def halfplaneIn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : Plane ≃ₗᵢ[ℝ] E) (n : E) : Set Real.Angle :=
  {θ | ⟪n, e (direction θ)⟫_ℝ ≤ 0}

theorem halfplaneIn_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : Plane ≃ₗᵢ[ℝ] E) (n : E) : halfplaneIn e n = halfplane (e.symm n) := by
  ext θ
  have hi := e.inner_map_map (e.symm n) (direction θ)
  simpa [halfplaneIn, halfplane] using congrArg (fun x : ℝ => x ≤ 0) hi

theorem volume_halfplaneIn_inter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : Plane ≃ₗᵢ[ℝ] E) {n m : E} (hn : n ≠ 0) (hm : m ≠ 0)
    (hangle : InnerProductGeometry.angle n m < Real.pi) :
    volume (halfplaneIn e n ∩ halfplaneIn e m) =
      ENNReal.ofReal (Real.pi - InnerProductGeometry.angle n m) := by
  rw [halfplaneIn_eq, halfplaneIn_eq]
  have ha : InnerProductGeometry.angle (e.symm n) (e.symm m) = InnerProductGeometry.angle n m :=
    e.symm.toLinearIsometry.angle_map n m
  rw [volume_halfplane_inter (by simpa using hn) (by simpa using hm) (by rwa [ha]), ha]

theorem volume_halfplaneIn_union {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : Plane ≃ₗᵢ[ℝ] E) {n m : E} (hn : n ≠ 0) (hm : m ≠ 0)
    (hangle : InnerProductGeometry.angle n m < Real.pi) :
    volume (halfplaneIn e n ∪ halfplaneIn e m) =
      ENNReal.ofReal (Real.pi + InnerProductGeometry.angle n m) := by
  rw [halfplaneIn_eq, halfplaneIn_eq]
  have ha : InnerProductGeometry.angle (e.symm n) (e.symm m) = InnerProductGeometry.angle n m :=
    e.symm.toLinearIsometry.angle_map n m
  rw [volume_halfplane_union (by simpa using hn) (by simpa using hm) (by rwa [ha]), ha]

theorem finite_frontier_strictHalfplane {n : Plane} (hn : n ≠ 0) :
    (frontier (strictHalfplane n)).Finite := by
  obtain ⟨r, α, hr, rfl⟩ := exists_pos_smul_direction hn
  have heq : strictHalfplane (r • direction α) = {θ | (θ - α).cos < 0} := by
    ext θ
    simp only [strictHalfplane, mem_ofPred_eq, real_inner_smul_left, inner_direction]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  apply (finite_normal_boundary (direction_ne_zero α)).subset
  intro θ hθ
  have h := frontier_lt_subset_eq
    (Real.Angle.continuous_cos.comp (continuous_id.sub continuous_const))
    continuous_const hθ
  simpa [inner_direction] using h

/-- Sign cells with the coordinate axes assigned to the nonnegative side. -/
def signCell (n m : Plane) (q : Bool × Bool) : Set Real.Angle :=
  (if q.1 then strictHalfplane n else halfplane (-n)) ∩
    (if q.2 then strictHalfplane m else halfplane (-m))

theorem signCell_mem_iff (n m : Plane) (θ : Real.Angle) (q : Bool × Bool) :
    θ ∈ signCell n m q ↔
      q = (decide (⟪n, direction θ⟫_ℝ < 0), decide (⟪m, direction θ⟫_ℝ < 0)) := by
  rcases q with ⟨a, b⟩
  cases a <;> cases b <;> simp [signCell, strictHalfplane, halfplane]

theorem finite_frontier_signCell {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (q : Bool × Bool) : (frontier (signCell n m q)).Finite := by
  rcases q with ⟨a, b⟩
  cases a <;> cases b <;> apply finite_frontier_inter
  all_goals first
    | exact finite_frontier_halfplane (neg_ne_zero.mpr hn)
    | exact finite_frontier_halfplane (neg_ne_zero.mpr hm)
    | exact finite_frontier_strictHalfplane hn
    | exact finite_frontier_strictHalfplane hm

theorem finite_frontier_biUnion_finset {ι : Type*} (Q : Finset ι) (S : ι → Set Real.Angle)
    (h : ∀ q ∈ Q, (frontier (S q)).Finite) : (frontier (⋃ q ∈ Q, S q)).Finite := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert a Q ha ih =>
    rw [Finset.set_biUnion_insert]
    exact finite_frontier_union (h a (by simp)) (ih (fun q hq => h q (by simp [hq])))

/-- Boolean sign-sector boundaries are derived finite, rather than assumed null. -/
theorem finite_frontier_booleanSignSector {n m : Plane} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Bool × Bool → Prop) : (frontier (booleanSignSector n m P)).Finite := by
  classical
  have heq : booleanSignSector n m P = ⋃ q ∈ (Finset.univ.filter P), signCell n m q := by
    ext θ
    simp [booleanSignSector, signCell_mem_iff]
  rw [heq]
  exact finite_frontier_biUnion_finset _ _ (fun q _ => finite_frontier_signCell hn hm q)


/-- Finite cover conservation when overlaps are contained in a specified
finite exceptional set, as supplied by strict-sign ambient germs. -/
theorem finite_sector_cover_total_except {ι : Type*} [Fintype ι]
    (S : ι → Set Real.Angle) (E : Set Real.Angle) (hE : E.Finite)
    (hS : ∀ i, NullMeasurableSet (S i) volume)
    (hd : Pairwise fun i j => S i ∩ S j ⊆ E)
    (hc : ⋃ i, S i = univ) :
    ∑ i, volume (S i) = ENNReal.ofReal (2 * Real.pi) := by
  have had : Pairwise (fun i j => AEDisjoint volume (S i) (S j)) :=
    fun i j hij => measure_mono_null (hd hij) (hE.measure_zero volume)
  have hm := measure_iUnion₀ had hS
  rw [hc, tsum_fintype] at hm
  rw [← hm]
  exact AddCircle.measure_univ (2 * Real.pi)

theorem finite_sector_cover_total_except_real {ι : Type*} [Fintype ι]
    (S : ι → Set Real.Angle) (E : Set Real.Angle) (hE : E.Finite)
    (hS : ∀ i, NullMeasurableSet (S i) volume)
    (hd : Pairwise fun i j => S i ∩ S j ⊆ E)
    (hc : ⋃ i, S i = univ) :
    ∑ i, (volume (S i)).toReal = 2 * Real.pi := by
  have h := congrArg ENNReal.toReal (finite_sector_cover_total_except S E hE hS hd hc)
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top volume (S i)),
    ENNReal.toReal_ofReal Real.two_pi_pos.le] at h
  exact h


end
end PhysicalRegistration.PlanarSectorMeasure
