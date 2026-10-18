module

public import SpectreGeometry.NormalPlaneSectorMeasure
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! Finite sign descriptions of actual linear cones. These generic facts use
arbitrary finite normal sets; they impose no bound on the number of normals. -/
namespace SpectreGeometry.FiniteConeFan
noncomputable section
open Set Filter
open scoped InnerProductSpace Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
local instance : DecidableEq E := Classical.decEq E
local instance : DecidableEq F := Classical.decEq F

/-- Cone membership depends only on the weak signs of the listed normals. -/
def SignDetermined (N : Finset E) (C : Set E) : Prop :=
  ∀ z w, (∀ n ∈ N,
    (inner ℝ n z ≤ 0 ↔ inner ℝ n w ≤ 0) ∧
    (0 ≤ inner ℝ n z ↔ 0 ≤ inner ℝ n w)) → (z ∈ C ↔ w ∈ C)

theorem SignDetermined.homogeneous {N : Finset E} {C : Set E}
    (hC : SignDetermined N C) (t : ℝ) (ht : 0 < t) (z : E) :
    t • z ∈ C ↔ z ∈ C := by
  apply hC
  intro n hn
  simp only [real_inner_smul_right]
  constructor <;> constructor <;> intro h <;> nlinarith

theorem SignDetermined.eventually_mem_iff {N : Finset E} {C : Set E}
    (hC : SignDetermined N C) (z : E)
    (hz : ∀ n ∈ N, n ≠ 0 → inner ℝ n z ≠ 0) :
    ∀ᶠ w in 𝓝 z, (w ∈ C ↔ z ∈ C) := by
  have hn (n : N) : ∀ᶠ w in 𝓝 z,
      (inner ℝ (n : E) w ≤ 0 ↔ inner ℝ (n : E) z ≤ 0) ∧
      (0 ≤ inner ℝ (n : E) w ↔ 0 ≤ inner ℝ (n : E) z) := by
    by_cases hn0 : (n : E) = 0
    · simp [hn0]
    have hne := hz n n.property hn0
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hh : ∀ᶠ w in 𝓝 z, inner ℝ (n : E) w < 0 :=
        (isOpen_lt (continuous_const.inner continuous_id) continuous_const).mem_nhds hneg
      filter_upwards [hh] with w hw
      exact ⟨iff_of_true hw.le hneg.le,
        iff_of_false (not_le_of_gt hw) (not_le_of_gt hneg)⟩
    · have hh : ∀ᶠ w in 𝓝 z, 0 < inner ℝ (n : E) w :=
        (isOpen_lt continuous_const (continuous_const.inner continuous_id)).mem_nhds hpos
      filter_upwards [hh] with w hw
      exact ⟨iff_of_false (not_le_of_gt hw) (not_le_of_gt hpos),
        iff_of_true hw.le hpos.le⟩
  have hall : ∀ᶠ w in 𝓝 z, ∀ n : N,
      (inner ℝ (n : E) w ≤ 0 ↔ inner ℝ (n : E) z ≤ 0) ∧
      (0 ≤ inner ℝ (n : E) w ↔ 0 ≤ inner ℝ (n : E) z) := eventually_all.mpr hn
  filter_upwards [hall] with w hw
  exact hC w z (fun n hn => hw ⟨n,hn⟩)

theorem SignDetermined.mem_interior_of_off_normals {N : Finset E} {C : Set E}
    (hC : SignDetermined N C) {z : E} (hzC : z ∈ C)
    (hz : ∀ n ∈ N, n ≠ 0 → inner ℝ n z ≠ 0) : z ∈ interior C := by
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hC.eventually_mem_iff z hz] with w hw
  exact hw.mpr hzC

theorem SignDetermined.mono {N M : Finset E} {C : Set E}
    (hC : SignDetermined N C) (hNM : N ⊆ M) : SignDetermined M C := by
  intro z w h
  exact hC z w (fun n hn => h n (hNM hn))

theorem signDetermined_halfspace (n : E) :
    SignDetermined {n} {z | inner ℝ n z ≤ 0} := by
  intro z w h
  exact (h n (Finset.mem_singleton_self n)).1

theorem SignDetermined.inter {N M : Finset E} {C D : Set E}
    (hC : SignDetermined N C) (hD : SignDetermined M D) :
    SignDetermined (N ∪ M) (C ∩ D) := by
  classical
  intro z w h
  exact and_congr (hC z w (fun n hn => h n (Finset.mem_union_left M hn)))
    (hD z w (fun n hn => h n (Finset.mem_union_right N hn)))

theorem SignDetermined.union {N M : Finset E} {C D : Set E}
    (hC : SignDetermined N C) (hD : SignDetermined M D) :
    SignDetermined (N ∪ M) (C ∪ D) := by
  classical
  intro z w h
  exact or_congr (hC z w (fun n hn => h n (Finset.mem_union_left M hn)))
    (hD z w (fun n hn => h n (Finset.mem_union_right N hn)))

theorem SignDetermined.image_linearIsometryEquiv {N : Finset E} {C : Set E}
    (hC : SignDetermined N C) (L : E ≃ₗᵢ[ℝ] F) :
    SignDetermined (N.image L) (L '' C) := by
  classical
  intro z w h
  have hsign : ∀ n ∈ N,
      (inner ℝ n (L.symm z) ≤ 0 ↔ inner ℝ n (L.symm w) ≤ 0) ∧
      (0 ≤ inner ℝ n (L.symm z) ↔ 0 ≤ inner ℝ n (L.symm w)) := by
    intro n hn
    have he := h (L n) (Finset.mem_image.mpr ⟨n,hn,rfl⟩)
    simpa only [← L.inner_map_map n (L.symm z), ← L.inner_map_map n (L.symm w),
      L.apply_symm_apply] using he
  have he := hC (L.symm z) (L.symm w) hsign
  have himage (v : F) : v ∈ L '' C ↔ L.symm v ∈ C := by
    constructor
    · rintro ⟨a,ha,rfl⟩; simpa using ha
    · intro hv; exact ⟨L.symm v,hv,L.apply_symm_apply v⟩
  exact (himage z).trans (he.trans (himage w).symm)

end
end SpectreGeometry.FiniteConeFan
