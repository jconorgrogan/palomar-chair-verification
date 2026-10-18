module

public import SpectreGeometry.EdgeNeighborhood
public import SpectreGeometry.EuclideanCarrier

@[expose] public section


/-! A genuine local noncrossing argument for linear half-planes. It is a
geometric lemma, not an edge-registration assumption: disjoint positive
sides in any open neighborhood force equal line kernels. -/
namespace SpectreGeometry
noncomputable section
open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_form_exists_positive (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) :
    ∃ v, 0 < A v := by
  have hex : ∃ v, A v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hA
    ext v
    exact h v
  obtain ⟨v,hv⟩ := hex
  rcases lt_or_gt_of_ne hv with hn | hp
  · exact ⟨-v,by simpa only [map_neg] using neg_pos.mpr hn⟩
  · exact ⟨v,hp⟩

/-- A local prohibition of simultaneous positive sides is scale-invariant. -/
theorem local_positive_disjoint_global (A B : E →ₗ[ℝ] ℝ) (x : E)
    (U : Set E) (hU : IsOpen U) (hx : x ∈ U)
    (hlocal : ∀ y ∈ U, ¬(0 < A (y-x) ∧ 0 < B (y-x))) :
    ∀ v, ¬(0 < A v ∧ 0 < B v) := by
  intro v hv
  let φ : ℝ → E := fun t => x+t • v
  have hφ : Continuous φ := by unfold φ; fun_prop
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ U := by
    have h0 : φ 0 ∈ U := by simpa [φ] using hx
    exact hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  obtain ⟨t,ht,hpt⟩ := hevent.exists_gt
  apply hlocal (φ t) hpt
  have he : φ t-x = t • v := by simp [φ]
  rw [he,map_smul,map_smul]
  exact ⟨mul_pos ht hv.1,mul_pos ht hv.2⟩

/-- Two nonzero real linear forms with disjoint positive sides have the
same kernel. No dimension restriction or angular discretization is used. -/
theorem positive_disjoint_same_kernel (A B : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdisjoint : ∀ v, ¬(0 < A v ∧ 0 < B v)) : ∀ v, A v = 0 ↔ B v = 0 := by
  have hincl : ∀ (C D : E →ₗ[ℝ] ℝ), C ≠ 0 →
      (∀ v, ¬(0 < C v ∧ 0 < D v)) → ∀ v, C v = 0 → D v = 0 := by
    intro C D hC hCD v hCv
    by_contra hDv
    obtain ⟨w,hw⟩ := linear_form_exists_positive C hC
    let z := w+((1-D w)/(D v)) • v
    have hCz : C z = C w := by simp [z,hCv]
    have hDz : D z = 1 := by
      simp only [z,map_add,map_smul,smul_eq_mul]
      field_simp
      ring
    exact hCD z ⟨hCz.symm ▸ hw,by rw [hDz]; norm_num⟩
  intro v
  exact ⟨hincl A B hA hdisjoint v,
    hincl B A hB (fun w hw => hdisjoint w ⟨hw.2,hw.1⟩) v⟩

/-- Local disjoint tile half-planes therefore share an actual supporting
line. Later placement lemmas supply these forms from the exact polygon. -/
theorem local_positive_disjoint_same_kernel (A B : E →ₗ[ℝ] ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (x : E)
    (U : Set E) (hU : IsOpen U) (hx : x ∈ U)
    (hlocal : ∀ y ∈ U, ¬(0 < A (y-x) ∧ 0 < B (y-x))) :
    ∀ v, A v = 0 ↔ B v = 0 :=
  positive_disjoint_same_kernel A B hA hB (local_positive_disjoint_global A B x U hU hx hlocal)

end
end SpectreGeometry
