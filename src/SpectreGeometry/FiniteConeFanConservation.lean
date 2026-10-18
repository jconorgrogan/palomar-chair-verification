module

public import SpectreGeometry.LocalConeGerm
public import SpectreGeometry.NormalPlaneSectorMeasure

@[expose] public section


/-! Generic scaling and angular conservation for finite actual local cone
families. Membership germs, homogeneity and physical coverage/packing are
explicit inputs; no angular sum or cone-interior packing is assumed. -/
namespace SpectreGeometry.FiniteConeFan
open Set MeasureTheory
open PhysicalRegistration.PlanarSectorMeasure
open scoped InnerProductSpace Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact membership on an open ball transports interior membership too. -/
theorem interior_iff_of_ball_germ (S C : Set E) (x : E) (r : ℝ)
    (heq : ∀ z, ‖z‖ < r → (x+z ∈ S ↔ z ∈ C))
    (z : E) (hz : ‖z‖ < r) : x+z ∈ interior S ↔ z ∈ interior C := by
  constructor
  · intro hi
    let U : Set E := {w | x+w ∈ interior S} ∩ Metric.ball 0 r
    have hU : IsOpen U :=
      (isOpen_interior.preimage (continuous_const.add continuous_id)).inter Metric.isOpen_ball
    have hzU : z ∈ U := ⟨hi,by simpa [Metric.mem_ball] using hz⟩
    apply interior_maximal (t := U) _ hU hzU
    intro w hw
    exact (heq w (by simpa [Metric.mem_ball] using hw.2)).mp (interior_subset hw.1)
  · intro hi
    let U : Set E := {y | y-x ∈ interior C} ∩ Metric.ball x r
    have hU : IsOpen U :=
      (isOpen_interior.preimage (continuous_id.sub continuous_const)).inter Metric.isOpen_ball
    have hzU : x+z ∈ U := ⟨by simpa using hi,
      by simpa [Metric.mem_ball,dist_eq_norm] using hz⟩
    apply interior_maximal (t := U) _ hU hzU
    intro y hy
    have h := (heq (y-x) (by simpa [Metric.mem_ball,dist_eq_norm] using hy.2)).mpr
      (interior_subset hy.1)
    simpa using h

theorem homogeneous_smul_mem_interior (C : Set E)
    (hom : ∀ t : ℝ, 0 < t → ∀ z, t • z ∈ C ↔ z ∈ C)
    (t : ℝ) (ht : 0 < t) {z : E} (hz : z ∈ interior C) : t • z ∈ interior C := by
  let U : Set E := {w | t⁻¹ • w ∈ interior C}
  have hU : IsOpen U := isOpen_interior.preimage (continuous_const_smul t⁻¹)
  have hzU : t • z ∈ U := by simpa [U,smul_smul,ht.ne'] using hz
  apply interior_maximal (t := U) _ hU hzU
  intro w hw
  have hh := (hom t ht (t⁻¹ • w)).mpr (interior_subset hw)
  simpa [smul_smul,ht.ne'] using hh

theorem exists_positive_small_smul (z : E) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ ‖t • z‖ < r := by
  obtain ⟨t,ht,htr⟩ := exists_pos_mul_lt hr ‖z‖
  exact ⟨t,ht,by simpa [norm_smul,Real.norm_eq_abs,abs_of_pos ht,mul_comm] using htr⟩

/-- A finite family of actual germs and local physical coverage yields a
full homogeneous cone cover with pairwise disjoint ambient interiors. -/
theorem finite_local_germs_fan {ι : Type*} [Fintype ι]
    (S C : ι → Set E) (x : E)
    (hg : ∀ i, LocalConeGerm (S i) x (C i))
    (hom : ∀ i (t : ℝ), 0 < t → ∀ z, t • z ∈ C i ↔ z ∈ C i)
    (hlocal : ∃ V : Set E, IsOpen V ∧ 0 ∈ V ∧ ∀ z ∈ V, ∃ i, x+z ∈ S i)
    (hd : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j))) :
    (∀ z, ∃ i, z ∈ C i) ∧
      Pairwise (fun i j => Disjoint (interior (C i)) (interior (C j))) := by
  classical
  choose U hU h0 heq using hg
  obtain ⟨V,hV,hV0,hcover⟩ := hlocal
  let W := V ∩ ⋂ i, U i
  have hW : IsOpen W := hV.inter (isOpen_iInter_of_finite hU)
  have hW0 : (0:E) ∈ W := ⟨hV0,mem_iInter.mpr h0⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW 0 hW0
  have hsmall (z : E) (hz : ‖z‖ < r) : z ∈ W :=
    hball (by simpa [Metric.mem_ball] using hz)
  have hcommon (i : ι) (z : E) (hz : ‖z‖ < r) : x+z ∈ S i ↔ z ∈ C i :=
    heq i z (mem_iInter.mp (hsmall z hz).2 i)
  constructor
  · intro z
    obtain ⟨t,ht,htz⟩ := exists_positive_small_smul z hr
    obtain ⟨i,hi⟩ := hcover (t • z) (hsmall _ htz).1
    exact ⟨i,(hom i t ht z).mp ((hcommon i _ htz).mp hi)⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨t,ht,htz⟩ := exists_positive_small_smul z hr
    have hi := homogeneous_smul_mem_interior (C i) (hom i) t ht hzi
    have hj := homogeneous_smul_mem_interior (C j) (hom j) t ht hzj
    have hi' := (interior_iff_of_ball_germ (S i) (C i) x r (hcommon i) _ htz).mpr hi
    have hj' := (interior_iff_of_ball_germ (S j) (C j) x r (hcommon j) _ htz).mpr hj
    exact Set.disjoint_left.mp (hd hij) hi' hj'

/-- Literal angular restriction in an arbitrary isometric normal chart. -/
def angularCone (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E) (C : Set E) : Set Real.Angle :=
  {θ | L (direction θ) ∈ C}

theorem finite_chart_normal_zeros (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E)
    (n : E) (hn : n ∈ Set.range L) (hne : n ≠ 0) :
    {θ : Real.Angle | inner ℝ n (L (direction θ)) = 0}.Finite := by
  obtain ⟨a,rfl⟩ := hn
  have ha : a ≠ 0 := by intro h; apply hne; rw [h,map_zero]
  simpa only [L.inner_map_map] using finite_normal_boundary ha

theorem measurableSet_angularCone (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E)
    (C : Set E) (hC : IsClosed C) : MeasurableSet (angularCone L C) := by
  have hd : Continuous direction := by
    unfold direction
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_cos
    · exact Real.Angle.continuous_sin
  exact (hC.preimage (L.continuous.comp hd)).measurableSet

/-- Full-turn conservation, with all exceptional directions proved finite
from the actual listed normals. No restriction on the number of normals. -/
theorem angular_mass_sum_real {ι : Type*} [Fintype ι]
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E) (C : ι → Set E) (N : ι → Finset E)
    (hclosed : ∀ i, IsClosed (C i))
    (hrange : ∀ i n, n ∈ N i → n ∈ Set.range L)
    (hoff : ∀ i z, z ∈ C i → (∀ n ∈ N i, n ≠ 0 → inner ℝ n z ≠ 0) → z ∈ interior (C i))
    (hd : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (hcover : ∀ z, ∃ i, z ∈ C i) :
    ∑ i, (volume (angularCone L (C i))).toReal = 2*Real.pi := by
  classical
  let X : Set Real.Angle := ⋃ i, ⋃ n ∈ N i,
    if n = 0 then ∅ else {θ | inner ℝ n (L (direction θ)) = 0}
  have hX : X.Finite := by
    apply Set.finite_iUnion
    intro i
    apply (N i).finite_toSet.biUnion
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simpa [hn0] using finite_chart_normal_zeros L n (hrange i n hn) hn0
  apply finite_sector_cover_total_except_real (fun i => angularCone L (C i)) X hX
  · intro i
    exact (measurableSet_angularCone L (C i) (hclosed i)).nullMeasurableSet
  · intro i j hij θ hθ
    by_contra hnot
    have hn (k : ι) : ∀ n ∈ N k, n ≠ 0 → inner ℝ n (L (direction θ)) ≠ 0 := by
      intro n hnk hn0 heq
      apply hnot
      exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨hnk,by simp [hn0,heq]⟩⟩⟩
    exact Set.disjoint_left.mp (hd hij) (hoff i _ hθ.1 (hn i)) (hoff j _ hθ.2 (hn j))
  · apply eq_univ_of_forall
    intro θ
    obtain ⟨i,hi⟩ := hcover (L (direction θ))
    exact mem_iUnion.mpr ⟨i,hi⟩

end
end SpectreGeometry.FiniteConeFan
