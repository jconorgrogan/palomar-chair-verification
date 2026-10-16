module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section


/-! A two-dimensional isometric normal plane cannot contain an independent
pair together with a nonzero vector orthogonal to both. No orientation,
coordinate splitting, registration, or finite-dimensional ambient-space
assumption is used. -/
namespace SpectreGeometry
noncomputable section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An independent pair in an isometric two-plane spans that entire plane,
so a vector in the same plane orthogonal to the pair must vanish. -/
theorem normal_plane_orthogonal_third_eq_zero
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E) {a b c : E}
    (hab : LinearIndependent ℝ ![a,b])
    (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (ha : a ∈ Set.range L) (hb : b ∈ Set.range L) (hc : c ∈ Set.range L) :
    c = 0 := by
  let S : Submodule ℝ E := Submodule.span ℝ ({a,b} : Set E)
  have hle : S ≤ LinearMap.range L.toLinearMap := by
    apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  have hrange : Set.range ![a,b] = ({a,b} : Set E) := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hdimS : Module.finrank ℝ S = 2 := by
    have hdim := finrank_span_eq_card hab
    change Module.finrank ℝ (Submodule.span ℝ (Set.range ![a,b])) = 2 at hdim
    rw [hrange] at hdim
    exact hdim
  have hdimL : Module.finrank ℝ (LinearMap.range L.toLinearMap) = 2 := by
    simpa using LinearMap.finrank_range_of_inj (f := L.toLinearMap) L.injective
  have heq : S = LinearMap.range L.toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hle (hdimS.trans hdimL.symm)
  have hcS : c ∈ S := by rw [heq]; exact hc
  obtain ⟨α,β,hcomb⟩ := Submodule.mem_span_pair.mp hcS
  have hcc : inner ℝ c c = 0 := by
    calc
      inner ℝ c c = inner ℝ (α • a + β • b) c :=
        congrArg (fun w : E => inner ℝ w c) hcomb.symm
      _ = 0 := by simp [inner_add_left, real_inner_smul_left, hac, hbc]
  exact inner_self_eq_zero.mp hcc

/-- Rank obstruction used when one polygon factor contributes two independent
boundary normals and an orthogonal factor contributes a nonzero third normal. -/
theorem normal_plane_rank_obstruction
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E) {a b c : E}
    (hab : LinearIndependent ℝ ![a,b]) (hc0 : c ≠ 0)
    (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (ha : a ∈ Set.range L) (hb : b ∈ Set.range L) (hc : c ∈ Set.range L) :
    False :=
  hc0 (normal_plane_orthogonal_third_eq_zero L hab hac hbc ha hb hc)

end
end SpectreGeometry
