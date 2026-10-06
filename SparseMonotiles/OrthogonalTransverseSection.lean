module

public import SparseMonotiles.PolyhedralGerms
public import SparseMonotiles.GenericRidgePoints
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section

/-!
# Orthogonal transverse sections of frozen physical germs

A frozen affine Boolean germ whose active planes contain an affine ridge is
exactly the pullback of a set in the ridge's orthogonal normal space. The
projection is continuous and open, so this assertion includes both closure
and ambient interior. In particular, intrinsic normal-space interiors are
not confused with intersections of ambient interiors with an arbitrary plane.
-/

namespace SparseMonotiles

open Set Metric
open scoped Topology

section OrthogonalProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Translate a physical point to its orthogonal transverse coordinate. -/
noncomputable def ridgeNormalProjection (R : AffineSubspace ℝ E) (p : E) :
    E → R.directionᗮ := fun x => R.directionᗮ.orthogonalProjection (x - p)

/-- The normal section has a canonical continuous right inverse. -/
@[simp] theorem ridgeNormalProjection_section (R : AffineSubspace ℝ E) (p : E)
    (v : R.directionᗮ) : ridgeNormalProjection R p (p + v) = v := by
  simp [ridgeNormalProjection, add_sub_cancel_left,
    Submodule.orthogonalProjection_mem_subspace_eq_self]

theorem continuous_ridgeNormalProjection (R : AffineSubspace ℝ E) (p : E) :
    Continuous (ridgeNormalProjection R p) :=
  R.directionᗮ.orthogonalProjection.continuous.comp (continuous_id.sub continuous_const)

theorem isOpenMap_ridgeNormalProjection (R : AffineSubspace ℝ E) (p : E) :
    IsOpenMap (ridgeNormalProjection R p) := by
  have hsurj : Function.Surjective R.directionᗮ.orthogonalProjection := by
    intro v
    exact ⟨v, Submodule.orthogonalProjection_mem_subspace_eq_self v⟩
  exact (R.directionᗮ.orthogonalProjection.isOpenMap hsurj).comp
    (Homeomorph.subRight p).isOpenMap

/-- Closure commutes with pullback by the genuine orthogonal projection. -/
theorem ridgeNormalProjection_preimage_closure (R : AffineSubspace ℝ E) (p : E)
    (S : Set R.directionᗮ) :
    closure (ridgeNormalProjection R p ⁻¹' S) =
      ridgeNormalProjection R p ⁻¹' closure S :=
  ((isOpenMap_ridgeNormalProjection R p).preimage_closure_eq_closure_preimage
    (continuous_ridgeNormalProjection R p) S).symm

/-- Ambient interior is the pullback of intrinsic normal-space interior. -/
theorem ridgeNormalProjection_preimage_interior (R : AffineSubspace ℝ E) (p : E)
    (S : Set R.directionᗮ) :
    interior (ridgeNormalProjection R p ⁻¹' S) =
      ridgeNormalProjection R p ⁻¹' interior S :=
  ((isOpenMap_ridgeNormalProjection R p).preimage_interior_eq_interior_preimage
    (continuous_ridgeNormalProjection R p) S).symm

/-- A form vanishing on a ridge kills every vector tangent to that ridge. -/
theorem affine_linear_eq_zero_on_ridge_direction
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : E →ᵃ[ℝ] ℝ) (hf : ∀ y ∈ R, f y = 0)
    {v : E} (hv : v ∈ R.direction) : f.linear v = 0 := by
  have h := hf (v + p) (AffineSubspace.vadd_mem_of_mem_direction hv hp)
  have heq := f.map_vadd p v
  change f (v + p) = f.linear v + f p at heq
  rw [h, hf p hp, add_zero] at heq
  exact heq.symm

/-- Active forms genuinely factor through the orthogonal projection. -/
theorem affine_eq_at_ridgeNormalProjection
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : E →ᵃ[ℝ] ℝ) (hf : ∀ y ∈ R, f y = 0) (x : E) :
    f x = f (p + (ridgeNormalProjection R p x : E)) := by
  have hdir : x - p - (ridgeNormalProjection R p x : E) ∈ R.direction := by
    simpa only [ridgeNormalProjection, Submodule.coe_orthogonalProjectionOnto_apply,
      R.direction.orthogonal_orthogonal] using
      R.directionᗮ.sub_starProjection_mem_orthogonal (x - p)
  have hz := affine_linear_eq_zero_on_ridge_direction R hp f hf hdir
  have heq := f.linearMap_vsub x (p + (ridgeNormalProjection R p x : E))
  change f.linear (x - (p + (ridgeNormalProjection R p x : E))) =
    f x - f (p + (ridgeNormalProjection R p x : E)) at heq
  rw [sub_add_eq_sub_sub, hz] at heq
  exact sub_eq_zero.mp heq.symm

end OrthogonalProjection

section FrozenSection

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The unclosed frozen section, in the normal subspace's own topology. -/
noncomputable def frozenRidgeSection (R : AffineSubspace ℝ E) (p : E)
    (f : ι → E →ᵃ[ℝ] ℝ) (A : HalfspaceFormula ι) : Set R.directionᗮ :=
  {v | p + (v : E) ∈ (A.freeze (fun i => f i) p).region (fun i => f i)}

/-- All Boolean operations, including complements, factor simultaneously. -/
theorem frozen_region_eq_normal_preimage
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : ι → E →ᵃ[ℝ] ℝ) (A : HalfspaceFormula ι)
    (hactive : ∀ i, f i p = 0 → ∀ y ∈ R, f i y = 0) :
    (A.freeze (fun i => f i) p).region (fun i => f i) =
      ridgeNormalProjection R p ⁻¹' frozenRidgeSection R p f A := by
  ext x
  change (A.freeze (fun i => f i) p).eval (fun i => 0 ≤ f i x) ↔
    (A.freeze (fun i => f i) p).eval
      (fun i => 0 ≤ f i (p + (ridgeNormalProjection R p x : E)))
  rw [HalfspaceFormula.eval_freeze, HalfspaceFormula.eval_freeze]
  have heq : frozenHalfspacePredicates (fun i => f i) p x =
      frozenHalfspacePredicates (fun i => f i) p
        (p + (ridgeNormalProjection R p x : E)) := by
    funext i
    by_cases hi : f i p = 0
    · simp only [frozenHalfspacePredicates, hi, if_true]
      rw [affine_eq_at_ridgeNormalProjection R hp (f i) (hactive i hi)]
    · simp only [frozenHalfspacePredicates, hi, if_false]
  rw [heq]

/-- The closed frozen material germ is exactly a normal-space pullback. -/
theorem closure_frozen_region_eq_normal_preimage
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : ι → E →ᵃ[ℝ] ℝ) (A : HalfspaceFormula ι)
    (hactive : ∀ i, f i p = 0 → ∀ y ∈ R, f i y = 0) :
    closure ((A.freeze (fun i => f i) p).region (fun i => f i)) =
      ridgeNormalProjection R p ⁻¹' closure (frozenRidgeSection R p f A) := by
  rw [frozen_region_eq_normal_preimage R hp f A hactive,
    ridgeNormalProjection_preimage_closure]

/-- Closed section interiors are genuine relative interiors, transported by
an open projection rather than by restricting an ambient interior to a plane. -/
theorem interior_closure_frozen_region_eq_normal_preimage
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : ι → E →ᵃ[ℝ] ℝ) (A : HalfspaceFormula ι)
    (hactive : ∀ i, f i p = 0 → ∀ y ∈ R, f i y = 0) :
    interior (closure ((A.freeze (fun i => f i) p).region (fun i => f i))) =
      ridgeNormalProjection R p ⁻¹' interior (closure (frozenRidgeSection R p f A)) := by
  rw [closure_frozen_region_eq_normal_preimage R hp f A hactive,
    ridgeNormalProjection_preimage_interior]

/-- The original closed affine Boolean material has this exact transverse germ. -/
theorem localSetEq_closed_normal_section [Finite ι]
    (R : AffineSubspace ℝ E) {p : E} (hp : p ∈ R)
    (f : ι → E →ᵃ[ℝ] ℝ) (A : HalfspaceFormula ι)
    (hactive : ∀ i, f i p = 0 → ∀ y ∈ R, f i y = 0) :
    LocalSetEq p (closure (A.region (fun i => f i)))
      (ridgeNormalProjection R p ⁻¹' closure (frozenRidgeSection R p f A)) := by
  rw [← closure_frozen_region_eq_normal_preimage R hp f A hactive]
  exact A.localSetEq_closure_freeze (fun i => f i) p
    (fun i => (f i).continuous_of_finiteDimensional.continuousAt)

end FrozenSection

section PositiveHomogeneity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Invariance under every strictly positive dilation. No convexity is assumed. -/
def IsPositiveCone (S : Set E) : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ v, t • v ∈ S ↔ v ∈ S

/-- Positive dilation invariance passes through closure. -/
theorem IsPositiveCone.closure {S : Set E} (hS : IsPositiveCone S) :
    IsPositiveCone (closure S) := by
  intro t ht v
  let e : E ≃ₜ E := Homeomorph.smulOfNeZero t ht.ne'
  have he : e ⁻¹' S = S := Set.ext (hS t ht)
  have hc : e ⁻¹' _root_.closure S = _root_.closure S := by
    rw [e.preimage_closure, he]
  exact Set.ext_iff.mp hc v

/-- Positive dilation invariance passes through intrinsic interior. -/
theorem IsPositiveCone.interior {S : Set E} (hS : IsPositiveCone S) :
    IsPositiveCone (interior S) := by
  intro t ht v
  let e : E ≃ₜ E := Homeomorph.smulOfNeZero t ht.ne'
  have he : e ⁻¹' S = S := Set.ext (hS t ht)
  have hc : e ⁻¹' _root_.interior S = _root_.interior S := by
    rw [e.preimage_interior, he]
  exact Set.ext_iff.mp hc v

/-- An affine form active at the origin of a section is homogeneous there. -/
theorem affine_at_base_smul (f : E →ᵃ[ℝ] ℝ) (p v : E) (t : ℝ)
    (hp : f p = 0) : f (p + t • v) = t * f (p + v) := by
  have h1 := f.map_vadd p (t • v)
  have h2 := f.map_vadd p v
  change f (t • v + p) = f.linear (t • v) + f p at h1
  change f (v + p) = f.linear v + f p at h2
  simp only [hp, add_zero, map_smul, smul_eq_mul] at h1 h2
  simpa only [add_comm] using h1.trans (congrArg (t * ·) h2.symm)

end PositiveHomogeneity

section HomogeneousFrozenSection

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Freezing affine inequalities produces a genuine homogeneous normal-space
Boolean cone, even when the Boolean expression contains complements. -/
theorem frozenRidgeSection_isPositiveCone
    (R : AffineSubspace ℝ E) (p : E) (f : ι → E →ᵃ[ℝ] ℝ)
    (A : HalfspaceFormula ι) : IsPositiveCone (frozenRidgeSection R p f A) := by
  intro t ht v
  change (A.freeze (fun i => f i) p).eval (fun i => 0 ≤ f i (p + t • (v : E))) ↔
    (A.freeze (fun i => f i) p).eval (fun i => 0 ≤ f i (p + (v : E)))
  rw [HalfspaceFormula.eval_freeze, HalfspaceFormula.eval_freeze]
  have heq : frozenHalfspacePredicates (fun i => f i) p (p + t • (v : E)) =
      frozenHalfspacePredicates (fun i => f i) p (p + (v : E)) := by
    funext i
    apply propext
    by_cases hi : f i p = 0
    · simp only [frozenHalfspacePredicates, hi, if_true,
        affine_at_base_smul (f i) p (v : E) t hi, mul_nonneg_iff_of_pos_left ht]
    · simp only [frozenHalfspacePredicates, hi, if_false]
  rw [heq]

/-- This is the closed, homogeneous material cone, not only an unclosed Boolean set. -/
theorem closure_frozenRidgeSection_isPositiveCone
    (R : AffineSubspace ℝ E) (p : E) (f : ι → E →ᵃ[ℝ] ℝ)
    (A : HalfspaceFormula ι) : IsPositiveCone (closure (frozenRidgeSection R p f A)) :=
  (frozenRidgeSection_isPositiveCone R p f A).closure

end HomogeneousFrozenSection

section LocalPartitionTransfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A local ambient pullback partition transfers to a local partition in the
normal subspace, with its intrinsic interiors. Openness is essential here. -/
theorem ridgeNormalProjection_local_partition {κ : Type*}
    (R : AffineSubspace ℝ E) (p : E) (C : κ → Set R.directionᗮ)
    {ε : ℝ}
    (hpart : ∀ y ∈ ball p ε,
      (∃ a, y ∈ ridgeNormalProjection R p ⁻¹' C a) ∧
      ∀ a b, a ≠ b → ¬ (y ∈ interior (ridgeNormalProjection R p ⁻¹' C a) ∧
        y ∈ interior (ridgeNormalProjection R p ⁻¹' C b))) :
    ∀ v ∈ ball (0 : R.directionᗮ) ε,
      (∃ a, v ∈ C a) ∧
      ∀ a b, a ≠ b → ¬ (v ∈ interior (C a) ∧ v ∈ interior (C b)) := by
  intro v hv
  have hv' : p + (v : E) ∈ ball p ε := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
      Submodule.norm_coe] using hv
  obtain ⟨hcover, hdisj⟩ := hpart (p + (v : E)) hv'
  constructor
  · obtain ⟨a, ha⟩ := hcover
    exact ⟨a, by simpa only [mem_preimage, ridgeNormalProjection_section] using ha⟩
  · intro a b hab habv
    apply hdisj a b hab
    simpa only [ridgeNormalProjection_preimage_interior, mem_preimage,
      ridgeNormalProjection_section] using habv

end LocalPartitionTransfer

section GlobalConePartition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every vector can be moved into a given positive-radius ball by a
strictly positive dilation. -/
theorem exists_pos_smul_mem_ball (v : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t • v ∈ ball (0 : E) ε := by
  let t := ε / (‖v‖ + 1)
  have ht : 0 < t := div_pos hε (by positivity)
  refine ⟨t, ht, ?_⟩
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  change ε / (‖v‖ + 1) * ‖v‖ < ε
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : 0 < ‖v‖ + 1)).mpr
  nlinarith

/-- A local comparison of genuine homogeneous sections determines the entire
sections. This transfers exact wedge identifications to global normal cones. -/
theorem IsPositiveCone.eq_of_localSetEq {S T : Set E}
    (hS : IsPositiveCone S) (hT : IsPositiveCone T)
    (heq : LocalSetEq (0 : E) S T) : S = T := by
  obtain ⟨ε, hε, heq⟩ := heq.exists_ball
  ext v
  obtain ⟨t, ht, hv⟩ := exists_pos_smul_mem_ball v hε
  exact (hS t ht v).symm.trans ((heq (t • v) hv).trans (hT t ht v))

/-- Positive homogeneity extends a partition of one positive-radius ball to
the entire normal space. Both coverage and intrinsic-interior separation
are transported by the same positive dilation. -/
theorem positiveCones_global_partition_of_local {κ : Type*}
    (C : κ → Set E) (hcone : ∀ a, IsPositiveCone (C a))
    {ε : ℝ} (hε : 0 < ε)
    (hpart : ∀ v ∈ ball (0 : E) ε,
      (∃ a, v ∈ C a) ∧
      ∀ a b, a ≠ b → ¬ (v ∈ interior (C a) ∧ v ∈ interior (C b))) :
    (∀ v, ∃ a, v ∈ C a) ∧
      ∀ a b, a ≠ b → Disjoint (interior (C a)) (interior (C b)) := by
  have hshrink (v : E) : ∃ t : ℝ, 0 < t ∧ t • v ∈ ball (0 : E) ε :=
    exists_pos_smul_mem_ball v hε
  constructor
  · intro v
    obtain ⟨t, ht, hv⟩ := hshrink v
    obtain ⟨a, ha⟩ := (hpart (t • v) hv).1
    exact ⟨a, (hcone a t ht v).mp ha⟩
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro v ha hb
    obtain ⟨t, ht, hv⟩ := hshrink v
    exact (hpart (t • v) hv).2 a b hab
      ⟨((hcone a).interior t ht v).mpr ha, ((hcone b).interior t ht v).mpr hb⟩

end GlobalConePartition

section IdentifyNormalCones

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Local equality of ambient cone pullbacks gives global equality of the
normal cones. The section through the base point supplies the local comparison. -/
theorem normalCones_eq_of_localSetEq
    (R : AffineSubspace ℝ E) (p : E) {S T : Set R.directionᗮ}
    (hS : IsPositiveCone S) (hT : IsPositiveCone T)
    (heq : LocalSetEq p (ridgeNormalProjection R p ⁻¹' S)
      (ridgeNormalProjection R p ⁻¹' T)) : S = T := by
  apply hS.eq_of_localSetEq hT
  obtain ⟨ε, hε, heq⟩ := heq.exists_ball
  apply LocalSetEq.of_ball hε
  intro v hv
  have hv' : p + (v : E) ∈ ball p ε := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
      Submodule.norm_coe] using hv
  simpa only [mem_preimage, ridgeNormalProjection_section] using
    heq (p + (v : E)) hv'

end IdentifyNormalCones

#print axioms isOpenMap_ridgeNormalProjection
#print axioms closure_frozen_region_eq_normal_preimage
#print axioms interior_closure_frozen_region_eq_normal_preimage
#print axioms localSetEq_closed_normal_section

#print axioms frozenRidgeSection_isPositiveCone
#print axioms closure_frozenRidgeSection_isPositiveCone
#print axioms ridgeNormalProjection_local_partition
#print axioms positiveCones_global_partition_of_local
#print axioms normalCones_eq_of_localSetEq

end SparseMonotiles
