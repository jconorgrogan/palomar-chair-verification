module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


/-! Every isometric two-plane in Euclidean four-space has an isometric
two-dimensional chart onto its orthogonal complement. No orientation or
coordinate alignment is prescribed. -/
namespace SpectreGeometry
noncomputable section

/-- A root tangent chart in four dimensions always admits a complementary
normal chart. The chart is obtained from an orthonormal basis of the actual
orthogonal complement, whose dimension is two. -/
theorem exists_complementary_normal_chart
    (H : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    ∃ N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4),
      LinearMap.range N.toLinearMap = (LinearMap.range H.toLinearMap)ᗮ := by
  let K := LinearMap.range H.toLinearMap
  have hdimK : Module.finrank ℝ K = 2 := by
    simpa [K] using LinearMap.finrank_range_of_inj (f := H.toLinearMap) H.injective
  have hdimN : Module.finrank ℝ Kᗮ = 2 :=
    Submodule.finrank_add_finrank_orthogonal' (by simp [hdimK])
  let b : OrthonormalBasis (Fin 2) ℝ Kᗮ :=
    (stdOrthonormalBasis ℝ Kᗮ).reindex (finCongr hdimN)
  let N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
    Kᗮ.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  refine ⟨N, ?_⟩
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact (b.repr.symm u).property
  · intro hz
    refine ⟨b.repr ⟨z, hz⟩, ?_⟩
    change (b.repr.symm (b.repr ⟨z, hz⟩) : EuclideanSpace ℝ (Fin 4)) = z
    simp

/-- In complementary charts, a vector is in the normal chart exactly when
it is orthogonal to every root tangent vector. This uses the normal-first
inner-product order of physical hyperplane equations. -/
theorem mem_range_complementary_normal_chart_iff
    (H N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (hN : LinearMap.range N.toLinearMap = (LinearMap.range H.toLinearMap)ᗮ)
    (n : EuclideanSpace ℝ (Fin 4)) :
    n ∈ Set.range N ↔ ∀ v, inner ℝ n (H v) = 0 := by
  change n ∈ LinearMap.range N.toLinearMap ↔ _
  rw [hN, Submodule.mem_orthogonal']
  constructor
  · intro hn v
    exact hn (H v) ⟨v, rfl⟩
  · intro hn w hw
    obtain ⟨v, rfl⟩ := hw
    exact hn v

end
end SpectreGeometry
