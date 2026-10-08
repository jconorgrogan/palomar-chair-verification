module

public import SparseMonotiles.SectorRegularity
public import SparseMonotiles.SectorAngleSumInventories
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Supporting-line alignment at a two-right-quadrant seam

This normal-plane argument uses actual orthogonal unit normals. A quadrant
contained in the complement of a flat material halfplane and touching its
boundary at a nonzero point must have one genuine side along that boundary.
-/
namespace SparseMonotiles
open Set
open SectorAngleSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Two orthogonal unit vectors span a two-dimensional real normal space. -/
theorem orthogonal_unit_pair_decomposition (hdim : Module.finrank ℝ E = 2)
    (n m : E) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : inner (𝕜 := ℝ) n m = 0)
    (v : E) : v = inner (𝕜 := ℝ) n v • n + inner (𝕜 := ℝ) m v • m := by
  have hmn : inner (𝕜 := ℝ) m n = 0 := by rw [real_inner_comm]; exact hnm
  have hon : Orthonormal ℝ (![n,m] : Fin 2 → E) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [real_inner_self_eq_norm_sq,hn,hm,hnm,hmn]
  have hspan := hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [hdim])
  let B := OrthonormalBasis.mk hon hspan.ge
  simpa [B,Fin.sum_univ_two] using (B.sum_repr' v).symm

/-- A right quadrant contains no line. -/
theorem orthogonal_quadrant_pointed (hdim : Module.finrank ℝ E = 2)
    (n m : E) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : inner (𝕜 := ℝ) n m = 0)
    {v : E} (hv : v ∈ normalHalfspace n ∩ normalHalfspace m)
    (hnv : -v ∈ normalHalfspace n ∩ normalHalfspace m) : v = 0 := by
  have hnn : inner (𝕜 := ℝ) n v = 0 := by
    have hh : 0 ≤ -inner (𝕜 := ℝ) n v := by simpa [normalHalfspace] using hnv.1
    exact le_antisymm (by linarith) hv.1
  have hmm : inner (𝕜 := ℝ) m v = 0 := by
    have hh : 0 ≤ -inner (𝕜 := ℝ) m v := by simpa [normalHalfspace] using hnv.2
    exact le_antisymm (by linarith) hv.2
  rw [orthogonal_unit_pair_decomposition hdim n m hn hm hnm v,hnn,hmm,zero_smul,zero_smul,add_zero]

/-- Disjoint interiors from a flat root put the whole regular closed sector
in the complementary closed halfplane. -/
theorem sector_subset_opposite_halfplane_of_disjoint {S : Set E} {θ : ℝ}
    (hS : HasSectorAngle S θ) (root : E)
    (hdis : Disjoint (interior (normalHalfspace root)) (interior S)) :
    ∀ v ∈ S, inner (𝕜 := ℝ) root v ≤ 0 := by
  have hd := hdis.closure_right isOpen_interior
  rw [hS.regular_closed] at hd
  intro v hv
  by_contra h
  have hpos : 0 < inner (𝕜 := ℝ) root v := lt_of_not_ge h
  have hi : v ∈ interior (normalHalfspace root) := by
    apply mem_interior.mpr
    refine ⟨{x : E | 0 < inner (𝕜 := ℝ) root x},?_,
      isOpen_lt continuous_const (continuous_const.inner continuous_id),hpos⟩
    intro x hx
    change 0 ≤ inner (𝕜 := ℝ) root x
    exact hx.le
  exact Set.disjoint_left.mp hd hi hv

/-- Touching the flat boundary forces one actual quadrant side to coincide
with that boundary; the inward normals are oppositely oriented. -/
theorem orthogonal_quadrant_touching_halfplane_alignment
    (hdim : Module.finrank ℝ E = 2) (root n m : E) (hroot : root ≠ 0)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : inner (𝕜 := ℝ) n m = 0)
    (hcontained : ∀ v ∈ normalHalfspace n ∩ normalHalfspace m,
      inner (𝕜 := ℝ) root v ≤ 0)
    {q : E} (hq : q ≠ 0) (hqn : q ∈ normalHalfspace n ∩ normalHalfspace m)
    (hboundary : inner (𝕜 := ℝ) root q = 0) :
    (∃ c : ℝ, 0 < c ∧ root = (-c) • n) ∨
      (∃ c : ℝ, 0 < c ∧ root = (-c) • m) := by
  have hnn : inner (𝕜 := ℝ) n n = 1 := by rw [real_inner_self_eq_norm_sq,hn]; norm_num
  have hmm : inner (𝕜 := ℝ) m m = 1 := by rw [real_inner_self_eq_norm_sq,hm]; norm_num
  have hmn : inner (𝕜 := ℝ) m n = 0 := by rw [real_inner_comm,hnm]
  have ha : inner (𝕜 := ℝ) n root ≤ 0 := by
    rw [real_inner_comm]
    exact hcontained n ⟨by change 0 ≤ inner (𝕜 := ℝ) n n; rw [hnn]; norm_num,
      by change 0 ≤ inner (𝕜 := ℝ) m n; rw [hmn]⟩
  have hb : inner (𝕜 := ℝ) m root ≤ 0 := by
    rw [real_inner_comm]
    exact hcontained m ⟨by change 0 ≤ inner (𝕜 := ℝ) n m; rw [hnm],
      by change 0 ≤ inner (𝕜 := ℝ) m m; rw [hmm]; norm_num⟩
  have hr := orthogonal_unit_pair_decomposition hdim n m hn hm hnm root
  have hqr := orthogonal_unit_pair_decomposition hdim n m hn hm hnm q
  have hqpos : 0 < inner (𝕜 := ℝ) n q ∨ 0 < inner (𝕜 := ℝ) m q := by
    by_contra h
    push_neg at h
    have hnq : inner (𝕜 := ℝ) n q = 0 := le_antisymm h.1 hqn.1
    have hmq : inner (𝕜 := ℝ) m q = 0 := le_antisymm h.2 hqn.2
    exact hq (by simpa [hnq,hmq] using hqr)
  have hsum : inner (𝕜 := ℝ) n root * inner (𝕜 := ℝ) n q +
      inner (𝕜 := ℝ) m root * inner (𝕜 := ℝ) m q = 0 := by
    rw [hr,inner_add_left,inner_smul_left,inner_smul_left] at hboundary
    simpa [inner_add_left,inner_smul_left] using hboundary
  rcases hqpos with hpos | hpos
  · have hprod := mul_nonpos_of_nonpos_of_nonneg hb hqn.2
    have hazero : inner (𝕜 := ℝ) n root = 0 := by
      have hmul : inner (𝕜 := ℝ) n root * inner (𝕜 := ℝ) n q = 0 :=
        le_antisymm (mul_nonpos_of_nonpos_of_nonneg ha hpos.le) (by linarith)
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hpos)
    have hbnz : inner (𝕜 := ℝ) m root ≠ 0 := by
      intro hz
      exact hroot (by simpa [hazero,hz] using hr)
    refine Or.inr ⟨-inner (𝕜 := ℝ) m root,neg_pos.mpr (lt_of_le_of_ne hb hbnz),?_⟩
    simpa [hazero] using hr
  · have hprod := mul_nonpos_of_nonpos_of_nonneg ha hqn.1
    have hbzero : inner (𝕜 := ℝ) m root = 0 := by
      have hmul : inner (𝕜 := ℝ) m root * inner (𝕜 := ℝ) m q = 0 :=
        le_antisymm (mul_nonpos_of_nonpos_of_nonneg hb hpos.le) (by linarith)
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hpos)
    have hanz : inner (𝕜 := ℝ) n root ≠ 0 := by
      intro hz
      exact hroot (by simpa [hbzero,hz] using hr)
    refine Or.inl ⟨-inner (𝕜 := ℝ) n root,neg_pos.mpr (lt_of_le_of_ne ha hanz),?_⟩
    simpa [hbzero] using hr

/-- Closed companions of a flat root cover its boundary by a direct limit
from outside the root, so boundary ownership is never assumed. -/
theorem closed_companions_cover_flat_boundary (root : E) (hroot : root ≠ 0)
    {S T : Set E} (hS : IsClosed S) (hT : IsClosed T)
    (hcover : ∀ v, v ∈ normalHalfspace root ∨ v ∈ S ∨ v ∈ T)
    {q : E} (hq : inner (𝕜 := ℝ) root q = 0) : q ∈ S ∨ q ∈ T := by
  have hclosed : IsClosed ((fun t : ℝ => q-t•root) ⁻¹' (S ∪ T)) :=
    (hS.union hT).preimage (continuous_const.sub (continuous_id.smul continuous_const))
  have hsub : Ioi (0 : ℝ) ⊆ (fun t : ℝ => q-t•root) ⁻¹' (S ∪ T) := by
    intro t ht
    rcases hcover (q-t•root) with hr | hs | ht'
    · have hpos : 0 < inner (𝕜 := ℝ) root root := real_inner_self_pos.mpr hroot
      have hle : 0 ≤ inner (𝕜 := ℝ) root (q-t•root) := hr
      rw [inner_sub_right,inner_smul_right,hq] at hle
      exact (not_le_of_gt (mul_pos ht hpos) (by linarith)).elim
    · exact Or.inl hs
    · exact Or.inr ht'
  have hz : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by simp
  have hm := closure_minimal hsub hclosed hz
  simpa using hm

/-- Every two-dimensional normal space has a nonzero vector in the
boundary line of a given flat halfplane. -/
theorem exists_nonzero_flat_boundary (hdim : Module.finrank ℝ E = 2) (root : E) :
    ∃ q : E, q ≠ 0 ∧ inner (𝕜 := ℝ) root q = 0 := by
  let f : E →ₗ[ℝ] ℝ := (innerSL ℝ root).toLinearMap
  have hnull := f.finrank_range_add_finrank_ker
  have hrange := (LinearMap.range f).finrank_le
  simp only [Module.finrank_self] at hrange
  rw [hdim] at hnull
  have hk : 0 < Module.finrank ℝ (LinearMap.ker f) := by omega
  letI : Nontrivial (LinearMap.ker f) := Module.nontrivial_of_finrank_pos hk
  obtain ⟨q,hq⟩ := exists_ne (0 : LinearMap.ker f)
  refine ⟨q,fun heq => hq (Subtype.ext heq),q.property⟩

/-- In an actual cover by one flat halfplane and two right quadrants, both
quadrants have a genuine boundary line equal to the flat boundary. Boundary
coverage follows from closedness, not a face-to-face or ownership premise. -/
theorem two_quadrants_flat_boundary_alignment
    (hdim : Module.finrank ℝ E = 2) (root n₁ m₁ n₂ m₂ : E) (hroot : root ≠ 0)
    (hn₁ : ‖n₁‖ = 1) (hm₁ : ‖m₁‖ = 1) (ho₁ : inner (𝕜 := ℝ) n₁ m₁ = 0)
    (hn₂ : ‖n₂‖ = 1) (hm₂ : ‖m₂‖ = 1) (ho₂ : inner (𝕜 := ℝ) n₂ m₂ = 0)
    (hcover : ∀ v, v ∈ normalHalfspace root ∨
      v ∈ normalHalfspace n₁ ∩ normalHalfspace m₁ ∨
      v ∈ normalHalfspace n₂ ∩ normalHalfspace m₂)
    (hdis₁ : Disjoint (interior (normalHalfspace root))
      (interior (normalHalfspace n₁ ∩ normalHalfspace m₁)))
    (hdis₂ : Disjoint (interior (normalHalfspace root))
      (interior (normalHalfspace n₂ ∩ normalHalfspace m₂))) :
    ((∃ c : ℝ, 0 < c ∧ root = (-c) • n₁) ∨ (∃ c : ℝ, 0 < c ∧ root = (-c) • m₁)) ∧
    ((∃ c : ℝ, 0 < c ∧ root = (-c) • n₂) ∨ (∃ c : ℝ, 0 < c ∧ root = (-c) • m₂)) := by
  have hne {v : E} (hv : ‖v‖ = 1) : v ≠ 0 := by intro hz; simp [hz] at hv
  have hshape₁ := (orthogonal_normal_angle_inventory n₁ m₁ (hne hn₁) (hne hm₁) ho₁).1.1
  have hshape₂ := (orthogonal_normal_angle_inventory n₂ m₂ (hne hn₂) (hne hm₂) ho₂).1.1
  have hclosed₁ : IsClosed (normalHalfspace n₁ ∩ normalHalfspace m₁) := by
    rw [← hshape₁.regular_closed]; exact isClosed_closure
  have hclosed₂ : IsClosed (normalHalfspace n₂ ∩ normalHalfspace m₂) := by
    rw [← hshape₂.regular_closed]; exact isClosed_closure
  have hc₁ := sector_subset_opposite_halfplane_of_disjoint hshape₁ root hdis₁
  have hc₂ := sector_subset_opposite_halfplane_of_disjoint hshape₂ root hdis₂
  obtain ⟨q,hq,hqboundary⟩ := exists_nonzero_flat_boundary hdim root
  have hnq : -q ≠ 0 := neg_ne_zero.mpr hq
  have hnqboundary : inner (𝕜 := ℝ) root (-q) = 0 := by simp [hqboundary]
  have hqcover := closed_companions_cover_flat_boundary root hroot hclosed₁ hclosed₂ hcover hqboundary
  have hnqcover := closed_companions_cover_flat_boundary root hroot hclosed₁ hclosed₂ hcover hnqboundary
  rcases hqcover with hq₁ | hq₂ <;> rcases hnqcover with hnq₁ | hnq₂
  · exact (hq (orthogonal_quadrant_pointed hdim n₁ m₁ hn₁ hm₁ ho₁ hq₁ hnq₁)).elim
  · exact ⟨orthogonal_quadrant_touching_halfplane_alignment hdim root n₁ m₁ hroot hn₁ hm₁ ho₁ hc₁
      hq hq₁ hqboundary,
      orthogonal_quadrant_touching_halfplane_alignment hdim root n₂ m₂ hroot hn₂ hm₂ ho₂ hc₂
      hnq hnq₂ hnqboundary⟩
  · exact ⟨orthogonal_quadrant_touching_halfplane_alignment hdim root n₁ m₁ hroot hn₁ hm₁ ho₁ hc₁
      hnq hnq₁ hnqboundary,
      orthogonal_quadrant_touching_halfplane_alignment hdim root n₂ m₂ hroot hn₂ hm₂ ho₂ hc₂
      hq hq₂ hqboundary⟩
  · exact (hq (orthogonal_quadrant_pointed hdim n₂ m₂ hn₂ hm₂ ho₂ hq₂ hnq₂)).elim

/-- The normal proportionality gives exact equality of supporting lines. -/
theorem normal_zero_planes_eq_of_negative_multiple {root n : E} {c : ℝ}
    (hc : 0 < c) (h : root = (-c) • n) :
    {v : E | inner (𝕜 := ℝ) root v = 0} = {v : E | inner (𝕜 := ℝ) n v = 0} := by
  ext v
  simp [h,inner_smul_left,ne_of_gt hc]

#print axioms exists_nonzero_flat_boundary
#print axioms two_quadrants_flat_boundary_alignment
#print axioms normal_zero_planes_eq_of_negative_multiple
#print axioms orthogonal_unit_pair_decomposition
#print axioms orthogonal_quadrant_pointed
#print axioms sector_subset_opposite_halfplane_of_disjoint
#print axioms orthogonal_quadrant_touching_halfplane_alignment
#print axioms closed_companions_cover_flat_boundary
end SparseMonotiles
