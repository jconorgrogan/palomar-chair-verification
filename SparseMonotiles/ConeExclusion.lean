module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Boundary-segment obstruction to a flat companion face

If every interior point of a set lies between two of its boundary points, a
convex set containing its boundary contains its entire interior in its own
interior. Thus the two interiors cannot be disjoint when the first is nonempty.

The abstract endpoint hypothesis is discharged here for the canonical cone
over a bounded coordinate box of positive dimension. The endpoints are obtained
by varying one tangential coordinate with height fixed. This is the convexity
step of E1; identification of the actual side-face tangent cone with this model,
and the preceding tiling/crease coverage hypotheses, are separate obligations.
-/

namespace SparseMonotiles

open Set
open scoped Topology

section Abstract

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]

/-- Every interior point is on a segment with endpoints on the boundary. -/
def BoundarySegmentCover (K : Set E) : Prop :=
  ∀ z ∈ interior K, ∃ a ∈ frontier K, ∃ b ∈ frontier K, z ∈ segment ℝ a b

/-- Explicit endpoint form of the convexity step; no cone assumption is hidden. -/
theorem interior_subset_of_boundary_segments {K L : Set E}
    (hsegments : BoundarySegmentCover K) (hboundary : frontier K ⊆ L)
    (hconvex : Convex ℝ L) : interior K ⊆ L := by
  intro z hz
  obtain ⟨a, ha, b, hb, hab⟩ := hsegments z hz
  exact hconvex.segment_subset (hboundary ha) (hboundary hb) hab

/-- Because the covered set is open, it is contained in the other interior. -/
theorem interior_subset_interior_of_boundary_segments {K L : Set E}
    (hsegments : BoundarySegmentCover K) (hboundary : frontier K ⊆ L)
    (hconvex : Convex ℝ L) : interior K ⊆ interior L :=
  interior_maximal (interior_subset_of_boundary_segments hsegments hboundary hconvex)
    isOpen_interior

/-- A nonempty interior with boundary-segment coverage cannot be interior-disjoint
from a convex set containing its boundary. -/
theorem not_disjoint_interiors_of_boundary_segments {K L : Set E}
    (hne : (interior K).Nonempty) (hsegments : BoundarySegmentCover K)
    (hboundary : frontier K ⊆ L) (hconvex : Convex ℝ L) :
    ¬ Disjoint (interior K) (interior L) := by
  intro hd
  obtain ⟨z, hz⟩ := hne
  exact Set.disjoint_left.mp hd hz
    (interior_subset_interior_of_boundary_segments hsegments hboundary hconvex hz)

/-- The stronger boundary-in-boundary premise used in E1 gives the same obstruction. -/
theorem not_disjoint_interiors_of_boundary_subset_frontier {K L : Set E}
    (hclosed : IsClosed L) (hne : (interior K).Nonempty)
    (hsegments : BoundarySegmentCover K) (hboundary : frontier K ⊆ frontier L)
    (hconvex : Convex ℝ L) : ¬ Disjoint (interior K) (interior L) :=
  not_disjoint_interiors_of_boundary_segments hne hsegments
    (hboundary.trans hclosed.frontier_subset) hconvex

end Abstract

section LineEndpoints

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

omit [TopologicalSpace E] in
/-- Oppositely signed line parameters put the initial point between the exits. -/
theorem mem_segment_line_exits (z v : E) {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    z ∈ segment ℝ (z + a • v) (z + b • v) := by
  have hden : 0 < b - a := by linarith
  have hsum : b / (b - a) + (-a) / (b - a) = 1 := by
    field_simp
    ring
  have hcancel : b / (b - a) * a + (-a) / (b - a) * b = 0 := by ring
  refine ⟨b / (b - a), (-a) / (b - a), div_nonneg hb.le hden.le,
    div_nonneg (neg_nonneg.mpr ha.le) hden.le, hsum, ?_⟩
  rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm,
    ← add_smul, ← add_smul, hsum, hcancel, one_smul, zero_smul, add_zero]

/-- The explicit two-exit premise suffices; boundedness is only needed upstream
when constructing those exits. No continuity of scalar multiplication is assumed. -/
theorem boundarySegmentCover_of_line_exits {K : Set E}
    (hexits : ∀ z ∈ interior K, ∃ v : E, ∃ a b : ℝ,
      a < 0 ∧ 0 < b ∧ z + a • v ∈ frontier K ∧ z + b • v ∈ frontier K) :
    BoundarySegmentCover K := by
  intro z hz
  obtain ⟨v, a, b, ha, hb, hleft, hright⟩ := hexits z hz
  exact ⟨z + a • v, hleft, z + b • v, hright, mem_segment_line_exits z v ha hb⟩

/-- Direct bounded-line-exit formulation of the abstract convexity obstruction. -/
theorem not_disjoint_interiors_of_line_exits {K L : Set E}
    (hne : (interior K).Nonempty)
    (hexits : ∀ z ∈ interior K, ∃ v : E, ∃ a b : ℝ,
      a < 0 ∧ 0 < b ∧ z + a • v ∈ frontier K ∧ z + b • v ∈ frontier K)
    (hboundary : frontier K ⊆ L) (hconvex : Convex ℝ L) :
    ¬ Disjoint (interior K) (interior L) :=
  not_disjoint_interiors_of_boundary_segments hne
    (boundarySegmentCover_of_line_exits hexits) hboundary hconvex

end LineEndpoints

section Escape

variable {X : Type*} [TopologicalSpace X]

/-- A continuous curve that immediately leaves a set certifies a boundary point.
Closedness of the set is unnecessary because the point itself belongs to it. -/
theorem mem_frontier_of_continuous_escape {K : Set X} {p : X} (hp : p ∈ K)
    (c : ℝ → X) (hc : Continuous c) (hc0 : c 0 = p)
    (hout : ∀ t < 0, c t ∉ K) : p ∈ frontier K := by
  refine ⟨subset_closure hp, ?_⟩
  intro hpi
  have hzero : (0 : ℝ) ∈ c ⁻¹' interior K := by simpa only [mem_preimage, hc0] using hpi
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_interior.preimage hc).mem_nhds hzero)
  have hmid : a / 2 ∈ Ioo a b := by constructor <;> linarith [hab.1, hab.2]
  exact hout (a / 2) (by linarith [hab.1]) (interior_subset (hsub hmid))

end Escape

section BoxCone

variable {ι : Type*} [DecidableEq ι]

/-- The cone from the origin over the bounded box at height one. -/
def boxPyramidCone (lo hi : ι → ℝ) : Set ((ι → ℝ) × ℝ) :=
  {p | 0 ≤ p.2 ∧ ∀ i, p.2 * lo i ≤ p.1 i ∧ p.1 i ≤ p.2 * hi i}

/-- The lower endpoint of a horizontal coordinate section. -/
def boxConeLower (lo : ι → ℝ) (j : ι) (p : (ι → ℝ) × ℝ) : (ι → ℝ) × ℝ :=
  (Function.update p.1 j (p.2 * lo j), p.2)

/-- The upper endpoint of a horizontal coordinate section. -/
def boxConeUpper (hi : ι → ℝ) (j : ι) (p : (ι → ℝ) × ℝ) : (ι → ℝ) × ℝ :=
  (Function.update p.1 j (p.2 * hi j), p.2)

theorem boxConeLower_mem {lo hi : ι → ℝ} (hw : ∀ i, lo i ≤ hi i)
    (j : ι) {p : (ι → ℝ) × ℝ} (hp : p ∈ boxPyramidCone lo hi) :
    boxConeLower lo j p ∈ boxPyramidCone lo hi := by
  refine ⟨hp.1, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    simpa [boxConeLower] using And.intro (le_refl (p.2 * lo j))
      (mul_le_mul_of_nonneg_left (hw j) hp.1)
  · simpa [boxConeLower, Function.update_of_ne hij] using hp.2 i

theorem boxConeUpper_mem {lo hi : ι → ℝ} (hw : ∀ i, lo i ≤ hi i)
    (j : ι) {p : (ι → ℝ) × ℝ} (hp : p ∈ boxPyramidCone lo hi) :
    boxConeUpper hi j p ∈ boxPyramidCone lo hi := by
  refine ⟨hp.1, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    simpa [boxConeUpper] using And.intro
      (mul_le_mul_of_nonneg_left (hw j) hp.1) (le_refl (p.2 * hi j))
  · simpa [boxConeUpper, Function.update_of_ne hij] using hp.2 i

/-- Both explicit exits of a coordinate section lie on the boundary. -/
theorem boxConeLower_mem_frontier {lo hi : ι → ℝ} (hw : ∀ i, lo i ≤ hi i)
    (j : ι) {p : (ι → ℝ) × ℝ} (hp : p ∈ boxPyramidCone lo hi) :
    boxConeLower lo j p ∈ frontier (boxPyramidCone lo hi) := by
  apply mem_frontier_of_continuous_escape (boxConeLower_mem hw j hp)
    (fun t : ℝ => (Function.update p.1 j (p.2 * lo j + t), p.2))
  · have hupdate : Continuous (fun t : ℝ => Function.update p.1 j (p.2 * lo j + t)) :=
      (continuous_const : Continuous (fun _ : ℝ => p.1)).update j
        (continuous_const.add continuous_id)
    exact hupdate.prodMk continuous_const
  · simp [boxConeLower]
  · intro t ht hmem
    have hj := (hmem.2 j).1
    simp only [Function.update_self] at hj
    linarith

theorem boxConeUpper_mem_frontier {lo hi : ι → ℝ} (hw : ∀ i, lo i ≤ hi i)
    (j : ι) {p : (ι → ℝ) × ℝ} (hp : p ∈ boxPyramidCone lo hi) :
    boxConeUpper hi j p ∈ frontier (boxPyramidCone lo hi) := by
  apply mem_frontier_of_continuous_escape (boxConeUpper_mem hw j hp)
    (fun t : ℝ => (Function.update p.1 j (p.2 * hi j - t), p.2))
  · have hupdate : Continuous (fun t : ℝ => Function.update p.1 j (p.2 * hi j - t)) :=
      (continuous_const : Continuous (fun _ : ℝ => p.1)).update j
        (continuous_const.sub continuous_id)
    exact hupdate.prodMk continuous_const
  · simp [boxConeUpper]
  · intro t ht hmem
    have hj := (hmem.2 j).2
    simp only [Function.update_self] at hj
    linarith

/-- A point between the two selected coordinate values lies on their segment. -/
theorem mem_segment_coordinate_update (p : (ι → ℝ) × ℝ) (j : ι) {l u : ℝ}
    (hl : l ≤ p.1 j) (hu : p.1 j ≤ u) :
    p ∈ segment ℝ (Function.update p.1 j l, p.2)
      (Function.update p.1 j u, p.2) := by
  by_cases hlu : l = u
  · have hpj : p.1 j = l := le_antisymm (hlu ▸ hu) hl
    have heq : (Function.update p.1 j l, p.2) = p := by
      rw [← hpj, Function.update_eq_self]
    rw [heq]
    exact left_mem_segment ℝ p _
  · have hlt : l < u := lt_of_le_of_ne (hl.trans hu) hlu
    have hden : 0 < u - l := sub_pos.mpr hlt
    have hsum : (u - p.1 j) / (u - l) + (p.1 j - l) / (u - l) = 1 := by
      field_simp
      ring
    refine ⟨(u - p.1 j) / (u - l), (p.1 j - l) / (u - l),
      div_nonneg (sub_nonneg.mpr hu) hden.le,
      div_nonneg (sub_nonneg.mpr hl) hden.le, hsum, ?_⟩
    apply Prod.ext
    · funext i
      change (u - p.1 j) / (u - l) * Function.update p.1 j l i +
        (p.1 j - l) / (u - l) * Function.update p.1 j u i = p.1 i
      by_cases hij : i = j
      · subst i
        simp only [Function.update_self]
        field_simp
        ring
      · simp only [Function.update_of_ne hij]
        nlinarith [congrArg (fun x : ℝ => x * p.1 i) hsum]
    · change (u - p.1 j) / (u - l) * p.2 + (p.1 j - l) / (u - l) * p.2 = p.2
      nlinarith [congrArg (fun x : ℝ => x * p.2) hsum]

/-- Horizontal line through `p`, parallel to the selected base-box axis. -/
def boxConeHorizontalLine (p : (ι → ℝ) × ℝ) (j : ι) (t : ℝ) : (ι → ℝ) × ℝ :=
  (Function.update p.1 j (p.1 j + t), p.2)

/-- Its direction is a nonzero base-parallel coordinate vector. -/
def boxConeHorizontalDirection (j : ι) : (ι → ℝ) × ℝ :=
  (Function.update (fun _ => 0) j 1, 0)

theorem boxConeHorizontalLine_eq (p : (ι → ℝ) × ℝ) (j : ι) (t : ℝ) :
    boxConeHorizontalLine p j t = p + t • boxConeHorizontalDirection j := by
  apply Prod.ext
  · funext i
    by_cases hij : i = j
    · subst i
      simp [boxConeHorizontalLine, boxConeHorizontalDirection]
    · simp [boxConeHorizontalLine, boxConeHorizontalDirection, Function.update_of_ne hij]
  · simp [boxConeHorizontalLine, boxConeHorizontalDirection]

theorem boxConeHorizontalDirection_ne_zero (j : ι) :
    boxConeHorizontalDirection j ≠ 0 := by
  intro h
  have hj := congrArg (fun p : (ι → ℝ) × ℝ => p.1 j) h
  simp [boxConeHorizontalDirection] at hj

/-- The full line section is exactly a bounded closed interval in its parameter.
The interval contains zero whenever `p` belongs to the cone. -/
theorem boxPyramidCone_horizontal_section {lo hi : ι → ℝ} (j : ι)
    {p : (ι → ℝ) × ℝ} (hp : p ∈ boxPyramidCone lo hi) :
    boxConeHorizontalLine p j ⁻¹' boxPyramidCone lo hi =
      Icc (p.2 * lo j - p.1 j) (p.2 * hi j - p.1 j) := by
  ext t
  constructor
  · intro ht
    have hj := ht.2 j
    simp only [boxConeHorizontalLine, Function.update_self] at hj
    exact ⟨by linarith [hj.1], by linarith [hj.2]⟩
  · intro ht
    refine ⟨hp.1, ?_⟩
    intro i
    by_cases hij : i = j
    · subst i
      change p.2 * lo j ≤ Function.update p.1 j (p.1 j + t) j ∧
        Function.update p.1 j (p.1 j + t) j ≤ p.2 * hi j
      simp only [Function.update_self]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · simpa [boxConeHorizontalLine, Function.update_of_ne hij] using hp.2 i

/-- The two boundary points are the actual exits of the bounded line section. -/
theorem boxPyramidCone_horizontal_endpoints (lo hi : ι → ℝ) (j : ι)
    (p : (ι → ℝ) × ℝ) :
    boxConeHorizontalLine p j (p.2 * lo j - p.1 j) = boxConeLower lo j p ∧
    boxConeHorizontalLine p j (p.2 * hi j - p.1 j) = boxConeUpper hi j p := by
  constructor <;> simp [boxConeHorizontalLine, boxConeLower, boxConeUpper]

omit [DecidableEq ι] in
/-- The defining halfspaces are convex. -/
theorem convex_boxPyramidCone (lo hi : ι → ℝ) : Convex ℝ (boxPyramidCone lo hi) := by
  intro p hp q hq a b ha hb hab
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_⟩
  intro i
  change (a * p.2 + b * q.2) * lo i ≤ a * p.1 i + b * q.1 i ∧
    a * p.1 i + b * q.1 i ≤ (a * p.2 + b * q.2) * hi i
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hp.2 i).1 ha,
      mul_le_mul_of_nonneg_left (hq.2 i).1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left (hp.2 i).2 ha,
      mul_le_mul_of_nonneg_left (hq.2 i).2 hb]

omit [DecidableEq ι] in
/-- Opposite vectors can both lie in the cone only at its apex. -/
theorem boxPyramidCone_pointed {lo hi : ι → ℝ} {p : (ι → ℝ) × ℝ}
    (hp : p ∈ boxPyramidCone lo hi) (hn : -p ∈ boxPyramidCone lo hi) : p = 0 := by
  have ht : p.2 = 0 := le_antisymm (by simpa using hn.1) hp.1
  apply Prod.ext
  · funext i
    have hj := hp.2 i
    simp only [ht, zero_mul] at hj
    exact le_antisymm hj.2 hj.1
  · exact ht

omit [DecidableEq ι] in
/-- Strict inequalities give an explicit open subset when the box has finitely
many coordinates. -/
theorem boxPyramidCone_strict_subset_interior [Finite ι] (lo hi : ι → ℝ) :
    {p : (ι → ℝ) × ℝ | 0 < p.2 ∧
      ∀ i, p.2 * lo i < p.1 i ∧ p.1 i < p.2 * hi i} ⊆
      interior (boxPyramidCone lo hi) := by
  apply interior_maximal
  · intro p hp
    exact ⟨hp.1.le, fun i => ⟨(hp.2 i).1.le, (hp.2 i).2.le⟩⟩
  · have heq : {p : (ι → ℝ) × ℝ | 0 < p.2 ∧
        ∀ i, p.2 * lo i < p.1 i ∧ p.1 i < p.2 * hi i} =
        {p : (ι → ℝ) × ℝ | 0 < p.2} ∩
        ⋂ i, {p : (ι → ℝ) × ℝ | p.2 * lo i < p.1 i ∧ p.1 i < p.2 * hi i} := by
      ext p
      simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    rw [heq]
    refine (isOpen_lt continuous_const continuous_snd).inter (isOpen_iInter_of_finite ?_)
    intro i
    exact (isOpen_lt (continuous_snd.mul continuous_const)
      ((continuous_apply i).comp continuous_fst)).inter
      (isOpen_lt ((continuous_apply i).comp continuous_fst)
        (continuous_snd.mul continuous_const))

omit [DecidableEq ι] in
/-- A finite box with strictly positive widths gives a full-dimensional cone. -/
theorem boxPyramidCone_interior_nonempty [Finite ι] {lo hi : ι → ℝ}
    (hw : ∀ i, lo i < hi i) : (interior (boxPyramidCone lo hi)).Nonempty := by
  refine ⟨((fun i => (lo i + hi i) / 2), 1),
    boxPyramidCone_strict_subset_interior lo hi ?_⟩
  refine ⟨zero_lt_one, ?_⟩
  intro i
  change 1 * lo i < (lo i + hi i) / 2 ∧ (lo i + hi i) / 2 < 1 * hi i
  constructor <;> linarith [hw i]

/-- Boundary endpoint coverage is unconditional for a nonempty-coordinate box cone.
It holds even for a degenerate box and for the cone apex. -/
theorem boxPyramidCone_boundarySegmentCover {lo hi : ι → ℝ}
    (hw : ∀ i, lo i ≤ hi i) (j : ι) : BoundarySegmentCover (boxPyramidCone lo hi) := by
  intro p hp
  have hpk := interior_subset hp
  refine ⟨boxConeLower lo j p, boxConeLower_mem_frontier hw j hpk,
    boxConeUpper hi j p, boxConeUpper_mem_frontier hw j hpk, ?_⟩
  exact mem_segment_coordinate_update p j (hpk.2 j).1 (hpk.2 j).2

/-- The complete convexity obstruction for the canonical positive-dimensional box cone. -/
theorem boxPyramidCone_not_disjoint_interiors {lo hi : ι → ℝ}
    (hw : ∀ i, lo i ≤ hi i) (j : ι) {L : Set ((ι → ℝ) × ℝ)}
    (hne : (interior (boxPyramidCone lo hi)).Nonempty)
    (hboundary : frontier (boxPyramidCone lo hi) ⊆ L) (hconvex : Convex ℝ L) :
    ¬ Disjoint (interior (boxPyramidCone lo hi)) (interior L) :=
  not_disjoint_interiors_of_boundary_segments hne
    (boxPyramidCone_boundarySegmentCover hw j) hboundary hconvex

/-- No separate nonempty-interior or endpoint hypothesis remains for a finite,
positive-dimensional, nondegenerate box cone. -/
theorem boxPyramidCone_exclusion [Finite ι] {lo hi : ι → ℝ}
    (hw : ∀ i, lo i < hi i) (j : ι) {L : Set ((ι → ℝ) × ℝ)}
    (hboundary : frontier (boxPyramidCone lo hi) ⊆ L) (hconvex : Convex ℝ L) :
    ¬ Disjoint (interior (boxPyramidCone lo hi)) (interior L) :=
  boxPyramidCone_not_disjoint_interiors (fun i => (hw i).le) j
    (boxPyramidCone_interior_nonempty hw) hboundary hconvex

/-- E1's boundary-in-boundary version for a closed convex companion cone. -/
theorem boxPyramidCone_exclusion_of_frontier_subset [Finite ι] {lo hi : ι → ℝ}
    (hw : ∀ i, lo i < hi i) (j : ι) {L : Set ((ι → ℝ) × ℝ)}
    (hclosed : IsClosed L)
    (hboundary : frontier (boxPyramidCone lo hi) ⊆ frontier L) (hconvex : Convex ℝ L) :
    ¬ Disjoint (interior (boxPyramidCone lo hi)) (interior L) :=
  boxPyramidCone_exclusion hw j (hboundary.trans hclosed.frontier_subset) hconvex

end BoxCone

end SparseMonotiles
