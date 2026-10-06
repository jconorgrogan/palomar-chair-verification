module

public import SparseMonotiles.SectorAngleSumHalfplanes
public import SparseMonotiles.OrthogonalTransverseSection

@[expose] public section

/-!
# Positive-cone interiors and genuine angular partitions

The argument map is continuous away from zero. Positive homogeneity therefore
lifts open angular subarcs into the ambient interior of a cone. Thus intrinsic
normal-plane interior disjointness really implies open-arc disjointness; no
ambient-slice interior shortcut or angle-sum premise is used.
-/

namespace SparseMonotiles
namespace SectorAngleSum

open Set Metric Filter
open scoped Topology

/-- The angular trace of a subset of the complex plane. -/
def angularTrace (S : Set ℂ) : Set (AddCircle (2 * Real.pi)) := direction ⁻¹' S

/-- An open angular neighborhood in a positive cone gives a genuine ambient
interior point of that cone. -/
theorem direction_mem_interior_of_open_trace {S : Set ℂ} (hS : IsPositiveCone S)
    {U : Set (AddCircle (2 * Real.pi))} (hU : IsOpen U)
    (hUS : U ⊆ angularTrace S) {q : AddCircle (2 * Real.pi)} (hq : q ∈ U) :
    direction q ∈ interior S := by
  have harg : ((Complex.arg (direction q) : ℝ) : AddCircle (2 * Real.pi)) = q :=
    Real.Angle.arg_toCircle _
  have hc : ContinuousAt (fun z : ℂ => (Complex.arg z : AddCircle (2 * Real.pi)))
      (direction q) := Complex.continuousAt_arg_coe_angle (direction_ne_zero q)
  have hUmem : U ∈ 𝓝 ((Complex.arg (direction q) : ℝ) : AddCircle (2 * Real.pi)) := by
    rw [harg]
    exact hU.mem_nhds hq
  have hu : ∀ᶠ z : ℂ in 𝓝 (direction q), (Complex.arg z : AddCircle (2 * Real.pi)) ∈ U :=
    hc hUmem
  have hn : ∀ᶠ z : ℂ in 𝓝 (direction q), z ≠ 0 :=
    isOpen_ne_fun continuous_id continuous_const |>.mem_nhds (direction_ne_zero q)
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hu, hn] with z hz hzn
  have hd : direction (Complex.arg z) ∈ S := hUS hz
  have hs := (hS ‖z‖ (norm_pos_iff.mpr hzn) (direction (Complex.arg z))).mpr hd
  rwa [norm_smul_direction_arg] at hs

/-- A represented closed arc automatically has its open arc in the cone's
ambient interior. Closed endpoints require no special handling. -/
theorem openArc_subset_trace_interior {S : Set ℂ} (hS : IsPositiveCone S)
    (c : AddCircle (2 * Real.pi)) (θ : ℝ)
    (htrace : angularTrace S = closedArc c θ) :
    openArc c θ ⊆ angularTrace (interior S) := by
  intro q hq
  exact direction_mem_interior_of_open_trace hS isOpen_ball
    (by rw [htrace]; exact ball_subset_closedBall) hq

/-- A genuine finite cone partition has total angle `2π` once each cone has
been geometrically identified with its closed circular arc. Arc coverage and
open-arc disjointness are conclusions, not additional supplied hypotheses. -/
theorem cone_partition_sum_width {ι : Type*} [Fintype ι]
    (cone : ι → Set ℂ) (center : ι → AddCircle (2 * Real.pi)) (width : ι → ℝ)
    (hcone : ∀ i, IsPositiveCone (cone i))
    (hwidth : ∀ i, 0 ≤ width i ∧ width i ≤ 2 * Real.pi)
    (htrace : ∀ i, angularTrace (cone i) = closedArc (center i) (width i))
    (hcover : ∀ z : ℂ, ∃ i, z ∈ cone i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (cone i)) (interior (cone j)))) :
    ∑ i, width i = 2 * Real.pi := by
  apply sum_width_eq_two_pi center width hwidth
  · apply eq_univ_of_forall
    intro q
    obtain ⟨i, hi⟩ := hcover (direction q)
    exact mem_iUnion.mpr ⟨i, (htrace i) ▸ hi⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro q hqi hqj
    have hi := openArc_subset_trace_interior (hcone i) (center i) (width i) (htrace i) hqi
    have hj := openArc_subset_trace_interior (hcone j) (center j) (width j) (htrace j) hqj
    exact Set.disjoint_left.mp (hdisjoint hij) hi hj

/-- The angular trace in an orthonormal coordinate system on any real plane. -/
def angularTraceWith {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (S : Set E) : Set (AddCircle (2 * Real.pi)) :=
  {q | e (direction q) ∈ S}

/-- Coordinate-invariant version for a genuine orthonormal normal plane. -/
theorem plane_cone_partition_sum_width
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (e : ℂ ≃ₗᵢ[ℝ] E) (cone : ι → Set E)
    (center : ι → AddCircle (2 * Real.pi)) (width : ι → ℝ)
    (hcone : ∀ i, IsPositiveCone (cone i))
    (hwidth : ∀ i, 0 ≤ width i ∧ width i ≤ 2 * Real.pi)
    (htrace : ∀ i, angularTraceWith e (cone i) = closedArc (center i) (width i))
    (hcover : ∀ z : E, ∃ i, z ∈ cone i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (cone i)) (interior (cone j)))) :
    ∑ i, width i = 2 * Real.pi := by
  apply cone_partition_sum_width (fun i => e ⁻¹' cone i) center width
  · intro i t ht z
    change e (t • z) ∈ cone i ↔ e z ∈ cone i
    rw [map_smul]
    exact hcone i t ht (e z)
  · exact hwidth
  · exact htrace
  · intro z
    exact hcover (e z)
  · intro i j hij
    change Disjoint (interior (e.toHomeomorph ⁻¹' cone i))
      (interior (e.toHomeomorph ⁻¹' cone j))
    rw [← e.toHomeomorph.preimage_interior, ← e.toHomeomorph.preimage_interior]
    exact (hdisjoint hij).preimage e

#print axioms direction_mem_interior_of_open_trace
#print axioms cone_partition_sum_width
#print axioms plane_cone_partition_sum_width

end SectorAngleSum
end SparseMonotiles
