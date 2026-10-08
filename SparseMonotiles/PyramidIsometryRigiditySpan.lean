module

public import SparseMonotiles.PyramidIsometryRigidityMetric

@[expose] public section

/-! # Affine spanning by the corners and apex of a nondegenerate box pyramid -/
namespace SparseMonotiles

/-- A base corner, with the last coordinate equal to zero. -/
noncomputable def euclideanPyramidCorner {n : ℕ} (lo hi : Fin n → ℝ)
    (b : Fin n → Bool) : Point (n + 1) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm
    (Fin.lastCases 0 (fun i => if b i then hi i else lo i))

/-- The finite vertex family, without geometric assumptions baked into its index. -/
noncomputable def euclideanPyramidVertex {n : ℕ} (lo hi : Fin n → ℝ)
    (a : Point (n + 1)) : Option (Fin n → Bool) → Point (n + 1)
  | none => a
  | some b => euclideanPyramidCorner lo hi b

@[simp] theorem euclideanPyramidCorner_last {n : ℕ} (lo hi : Fin n → ℝ)
    (b : Fin n → Bool) : euclideanPyramidCorner lo hi b (Fin.last n) = 0 := by
  simp [euclideanPyramidCorner]

@[simp] theorem euclideanPyramidCorner_castSucc {n : ℕ} (lo hi : Fin n → ℝ)
    (b : Fin n → Bool) (i : Fin n) :
    euclideanPyramidCorner lo hi b i.castSucc = if b i then hi i else lo i := by
  simp [euclideanPyramidCorner]

/-- Coordinate evaluation commutes with finite sums of Euclidean points. -/
theorem point_sum_apply {ι : Type*} {d : ℕ} (s : Finset ι) (f : ι → Point d)
    (k : Fin d) : (∑ i ∈ s, f i) k = ∑ i ∈ s, f i k :=
  map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) k) f s

/-- Tangential coordinate axes together with one transverse difference span all space. -/
theorem affineSpan_eq_top_of_tangent_axes {n : ℕ} (s : Set (Point (n + 1)))
    (p a : Point (n + 1)) (hp : p ∈ s) (ha : a ∈ s)
    (hh : a (Fin.last n) - p (Fin.last n) ≠ 0)
    (ht : ∀ i : Fin n, EuclideanSpace.single i.castSucc (1 : ℝ) ∈
      (affineSpan ℝ s).direction) : affineSpan ℝ s = ⊤ := by
  classical
  let S := affineSpan ℝ s
  have hpS : p ∈ S := subset_affineSpan ℝ s hp
  have haS : a ∈ S := subset_affineSpan ℝ s ha
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨p, hpS⟩).mp
  apply top_unique
  intro x _
  let c : ℝ := x (Fin.last n) / (a (Fin.last n) - p (Fin.last n))
  have hx : c • (a - p) + ∑ i : Fin n,
      (x i.castSucc - c * (a i.castSucc - p i.castSucc)) •
        EuclideanSpace.single i.castSucc (1 : ℝ) ∈ S.direction :=
    S.direction.add_mem (S.direction.smul_mem c
      (AffineSubspace.vsub_mem_direction haS hpS))
      (S.direction.sum_mem (fun i _ => S.direction.smul_mem _ (ht i)))
  have heq : c • (a - p) + ∑ i : Fin n,
      (x i.castSucc - c * (a i.castSucc - p i.castSucc)) •
        EuclideanSpace.single i.castSucc (1 : ℝ) = x := by
    ext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · have hne : ∀ i : Fin n, Fin.last n ≠ i.castSucc :=
        fun i => (Fin.castSucc_ne_last i).symm
      simp [point_sum_apply, EuclideanSpace.single_apply, c, hh, hne]
    · simp [point_sum_apply, EuclideanSpace.single_apply]
  rwa [heq] at hx

/-- The base corner family supplies every tangential coordinate axis. -/
theorem euclideanPyramidVertex_tangent_mem_direction {n : ℕ}
    (lo hi : Fin n → ℝ) (a : Point (n + 1)) (hw : ∀ i, lo i ≠ hi i)
    (i : Fin n) : EuclideanSpace.single i.castSucc (1 : ℝ) ∈
      (affineSpan ℝ (Set.range (euclideanPyramidVertex lo hi a))).direction := by
  classical
  let S := affineSpan ℝ (Set.range (euclideanPyramidVertex lo hi a))
  let b : Fin n → Bool := fun _ => false
  have hp : euclideanPyramidCorner lo hi b ∈ S :=
    subset_affineSpan ℝ _ ⟨some b, rfl⟩
  have hq : euclideanPyramidCorner lo hi (Function.update b i true) ∈ S :=
    subset_affineSpan ℝ _ ⟨some (Function.update b i true), rfl⟩
  have hmem := S.direction.smul_mem ((hi i - lo i)⁻¹)
    (AffineSubspace.vsub_mem_direction hq hp)
  have hd : hi i - lo i ≠ 0 := sub_ne_zero.mpr (hw i).symm
  have heq : (hi i - lo i)⁻¹ •
      (euclideanPyramidCorner lo hi (Function.update b i true) -
        euclideanPyramidCorner lo hi b) = EuclideanSpace.single i.castSucc (1 : ℝ) := by
    ext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [EuclideanSpace.single_apply, (Fin.castSucc_ne_last i).symm]
    · by_cases hji : j = i
      · subst j
        simp [b, EuclideanSpace.single_apply, hd]
      · simp [b, Function.update_of_ne hji, EuclideanSpace.single_apply, hji]
  change (hi i - lo i)⁻¹ •
    (euclideanPyramidCorner lo hi (Function.update b i true) -
      euclideanPyramidCorner lo hi b) ∈ S.direction at hmem
  rwa [heq] at hmem

/-- A box with nonzero widths and an apex off its hyperplane has a spanning vertex set. -/
theorem affineSpan_euclideanPyramidVertex {n : ℕ} (lo hi : Fin n → ℝ)
    (a : Point (n + 1)) (hw : ∀ i, lo i ≠ hi i) (hh : a (Fin.last n) ≠ 0) :
    affineSpan ℝ (Set.range (euclideanPyramidVertex lo hi a)) = ⊤ := by
  apply affineSpan_eq_top_of_tangent_axes
    (Set.range (euclideanPyramidVertex lo hi a))
    (euclideanPyramidCorner lo hi (fun _ => false)) a
    ⟨some (fun _ => false), rfl⟩ ⟨none, rfl⟩
  · simpa using hh
  · exact euclideanPyramidVertex_tangent_mem_direction lo hi a hw

#print axioms affineSpan_euclideanPyramidVertex

end SparseMonotiles
