module

public import SparseMonotiles.SectorAngleSumTwoNormals
public import SparseMonotiles.SectorAngleSumConeTopology
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Angle sum for actual finite planar half-space sector partitions

The geometric input is an equality with an actual half-plane, intersection of
two half-planes, or union of two half-planes. The angle assigned to each shape
is calculated from the ordinary Euclidean angle between its inward normals.
The full `2π` sum is a theorem, rather than part of the input.
-/

namespace SparseMonotiles
namespace SectorAngleSum

open Set Metric InnerProductGeometry
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real inward-normal half-space through the origin. -/
def normalHalfspace (n : E) : Set E := {v | 0 ≤ ⟪n,v⟫_ℝ}

/-- The trace of a genuine half-plane in any orthonormal planar coordinates. -/
theorem plane_halfplane_trace (e : ℂ ≃ₗᵢ[ℝ] E) (n : E) (hn : n ≠ 0) :
    angularTraceWith e (normalHalfspace n) =
      closedArc (Complex.arg (e.symm n)) Real.pi := by
  have hi (q : AddCircle (2*Real.pi)) :
      ⟪n,e (direction q)⟫_ℝ = ⟪e.symm n,direction q⟫_ℝ := by
    rw [← e.inner_map_map, e.apply_symm_apply]
  have hne : e.symm n ≠ 0 := by simpa using e.symm.injective.ne hn
  simpa only [angularTraceWith, normalHalfspace, mem_setOf_eq, hi] using
    halfplane_trace (e.symm n) hne

/-- Actual planar intersections/unions have widths computed from the
coordinate-independent Euclidean angle between their inward normals. -/
theorem plane_two_halfplanes_traces (e : ℂ ≃ₗᵢ[ℝ] E) (n m : E)
    (hn : n ≠ 0) (hm : m ≠ 0) (ha : angle n m < Real.pi) :
    ∃ c : AddCircle (2*Real.pi),
      angularTraceWith e (normalHalfspace n ∩ normalHalfspace m) =
        closedArc c (Real.pi-angle n m) ∧
      angularTraceWith e (normalHalfspace n ∪ normalHalfspace m) =
        closedArc c (Real.pi+angle n m) := by
  have hi (n : E) (q : AddCircle (2*Real.pi)) :
      ⟪n,e (direction q)⟫_ℝ = ⟪e.symm n,direction q⟫_ℝ := by
    rw [← e.inner_map_map, e.apply_symm_apply]
  have hn' : e.symm n ≠ 0 := by simpa using e.symm.injective.ne hn
  have hm' : e.symm m ≠ 0 := by simpa using e.symm.injective.ne hm
  have he : angle (e.symm n) (e.symm m) = angle n m := e.symm.toLinearIsometry.angle_map n m
  obtain ⟨c,hc,hu⟩ := two_halfplanes_traces (e.symm n) (e.symm m) hn' hm' (by rwa [he])
  rw [he] at hc hu
  exact ⟨c, by simpa only [angularTraceWith, normalHalfspace, mem_inter_iff, mem_setOf_eq, hi] using hc,
    by simpa only [angularTraceWith, normalHalfspace, mem_union, mem_setOf_eq, hi] using hu⟩

theorem isPositiveCone_normalHalfspace (n : E) : IsPositiveCone (normalHalfspace n) := by
  intro t ht v
  change 0 ≤ ⟪n,t • v⟫_ℝ ↔ 0 ≤ ⟪n,v⟫_ℝ
  rw [inner_smul_right]
  exact mul_nonneg_iff_of_pos_left ht

/-- The geometric sector classification. Angles are determined by the actual
normal vectors, not supplied by an assumed circular partition. Empty and full
regions are included to handle constant local material germs honestly. -/
inductive HasSectorAngle (S : Set E) : ℝ → Prop
  | empty (hS : S = ∅) : HasSectorAngle S 0
  | full (hS : S = univ) : HasSectorAngle S (2*Real.pi)
  | halfplane (n : E) (hn : n ≠ 0) (hS : S = normalHalfspace n) :
      HasSectorAngle S Real.pi
  | convex (n m : E) (hn : n ≠ 0) (hm : m ≠ 0) (ha : angle n m < Real.pi)
      (hS : S = normalHalfspace n ∩ normalHalfspace m) :
      HasSectorAngle S (Real.pi-angle n m)
  | reflex (n m : E) (hn : n ≠ 0) (hm : m ≠ 0) (ha : angle n m < Real.pi)
      (hS : S = normalHalfspace n ∪ normalHalfspace m) :
      HasSectorAngle S (Real.pi+angle n m)

/-- Every geometric sector angle lies in the actual radian range. -/
theorem HasSectorAngle.bounds {S : Set E} {θ : ℝ} (h : HasSectorAngle S θ) :
    0 ≤ θ ∧ θ ≤ 2*Real.pi := by
  cases h with
  | empty => constructor <;> linarith [Real.pi_pos]
  | full => constructor <;> linarith [Real.pi_pos]
  | halfplane => constructor <;> linarith [Real.pi_pos]
  | convex n m _ _ ha => constructor <;> linarith [Real.pi_pos, angle_nonneg n m]
  | reflex n m _ _ ha => constructor <;> linarith [Real.pi_pos, angle_nonneg n m]

/-- Every shape in the inventory is a genuine positive cone. -/
theorem HasSectorAngle.positive {S : Set E} {θ : ℝ} (h : HasSectorAngle S θ) :
    IsPositiveCone S := by
  cases h with
  | empty hS => subst S; intro t ht v; simp
  | full hS => subst S; intro t ht v; simp
  | halfplane n hn hS => subst S; exact isPositiveCone_normalHalfspace n
  | convex n m hn hm ha hS =>
      subst S
      intro t ht v
      simp only [mem_inter_iff, isPositiveCone_normalHalfspace n t ht v,
        isPositiveCone_normalHalfspace m t ht v]
  | reflex n m hn hm ha hS =>
      subst S
      intro t ht v
      simp only [mem_union, isPositiveCone_normalHalfspace n t ht v,
        isPositiveCone_normalHalfspace m t ht v]

/-- Arc sandwich suffices even for empty sectors: their zero-width open arc
is empty, while the harmless closed endpoint has measure zero. -/
theorem HasSectorAngle.arc_sandwich {S : Set E} {θ : ℝ}
    (h : HasSectorAngle S θ) (e : ℂ ≃ₗᵢ[ℝ] E) :
    ∃ c : AddCircle (2*Real.pi),
      angularTraceWith e S ⊆ closedArc c θ ∧
      openArc c θ ⊆ angularTraceWith e (interior S) := by
  have hp : IsPositiveCone (e ⁻¹' S) := by
    intro t ht v
    change e (t • v) ∈ S ↔ e v ∈ S
    rw [map_smul]
    exact h.positive t ht (e v)
  have lift (c : AddCircle (2*Real.pi)) (θ : ℝ)
      (he : angularTraceWith e S = closedArc c θ) :
      openArc c θ ⊆ angularTraceWith e (interior S) := by
    have hpre : e ⁻¹' interior S = interior (e ⁻¹' S) := by
      change e.toHomeomorph ⁻¹' interior S = interior (e.toHomeomorph ⁻¹' S)
      exact e.toHomeomorph.preimage_interior S
    change openArc c θ ⊆ angularTrace (e ⁻¹' interior S)
    rw [hpre]
    exact openArc_subset_trace_interior hp c θ he
  cases h with
  | empty hS =>
      subst S
      refine ⟨0, ?_, ?_⟩
      · simp [angularTraceWith]
      · simp [openArc, angularTraceWith]
  | full hS =>
      subst S
      refine ⟨0, ?_, ?_⟩
      · have hu : closedArc (0 : AddCircle (2*Real.pi)) (2*Real.pi) = univ := by
          apply AddCircle.closedBall_eq_univ_of_half_period_le (2*Real.pi) (by positivity)
          rw [abs_of_pos Real.two_pi_pos]
        rw [hu]; exact subset_univ _
      · simp [angularTraceWith]
  | halfplane n hn hS =>
      have he : angularTraceWith e S = closedArc (Complex.arg (e.symm n)) Real.pi := by
        rw [hS]; exact plane_halfplane_trace e n hn
      exact ⟨_, he.subset, lift _ _ he⟩
  | convex n m hn hm ha hS =>
      obtain ⟨c,hc,hu⟩ := plane_two_halfplanes_traces e n m hn hm ha
      rw [← hS] at hc
      exact ⟨c,hc.subset,lift _ _ hc⟩
  | reflex n m hn hm ha hS =>
      obtain ⟨c,hc,hu⟩ := plane_two_halfplanes_traces e n m hn hm ha
      rw [← hS] at hu
      exact ⟨c,hu.subset,lift _ _ hu⟩

/-- Finite actual geometric sectors covering a plane with disjoint intrinsic
interiors necessarily have total angle `2π`. No arc or angle-sum premise. -/
theorem geometric_sector_partition_sum {ι : Type*} [Fintype ι]
    (e : ℂ ≃ₗᵢ[ℝ] E) (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j)))) :
    ∑ i, width i = 2*Real.pi := by
  choose c hc hi using fun i => (hshape i).arc_sandwich e
  apply sum_width_eq_two_pi c width (fun i => (hshape i).bounds)
  · apply eq_univ_of_forall
    intro q
    obtain ⟨i,hmem⟩ := hcover (e (direction q))
    exact mem_iUnion.mpr ⟨i,hc i hmem⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro q hqi hqj
    exact Set.disjoint_left.mp (hdisjoint hij) (hi i hqi) (hi j hqj)

/-- The rank-two formulation constructs its own orthonormal coordinates. -/
theorem rank_two_geometric_sector_partition_sum {ι : Type*} [Fintype ι]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j)))) :
    ∑ i, width i = 2*Real.pi := by
  let b : OrthonormalBasis (Fin 2) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  exact geometric_sector_partition_sum (Complex.isometryOfOrthonormal b) sector width hshape hcover hdisjoint

#print axioms plane_two_halfplanes_traces
#print axioms geometric_sector_partition_sum
#print axioms rank_two_geometric_sector_partition_sum

end SectorAngleSum
end SparseMonotiles
