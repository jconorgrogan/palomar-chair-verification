module

public import SparseMonotiles.GenericFacePoints

@[expose] public section

/-!
# Selecting a ridge also in the all-face degeneracy

In ambient dimension at least two, the all-face alternative has an arbitrary
codimension-one subplane of the face through the selected point. Consequently
every generic face point admits a common codimension-two ambient ridge.
-/
namespace SparseMonotiles

open Set AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive-dimensional face contains a codimension-two ambient ridge
through each of its points. -/
theorem exists_ridge_through_face_point [FiniteDimensional ℝ E]
    (P : AffineSubspace ℝ E)
    (hcodim : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ E)
    (hdim : 2 ≤ Module.finrank ℝ E) (x : P) :
    ∃ R : AffineSubspace ℝ E, (x : E) ∈ R ∧ R ≤ P ∧
      Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E := by
  classical
  have hpos : 0 < Module.finrank ℝ P.direction := by omega
  let b := Module.finBasis ℝ P.direction
  let i : Fin (Module.finrank ℝ P.direction) := ⟨0,hpos⟩
  let l : P.direction →ₗ[ℝ] ℝ := b.coord i
  have hl : l ≠ 0 := by
    intro he
    have h := congrArg (fun f : P.direction →ₗ[ℝ] ℝ => f (b i)) he
    simpa [l] using h
  let K := LinearMap.ker l
  let M := K.map P.direction.subtype
  have hM : M ≤ P.direction := by
    rintro v ⟨w,hw,rfl⟩
    exact w.property
  refine ⟨mk' (x : E) M, self_mem_mk' _ _, ?_, ?_⟩
  · intro y hy
    have hd := hM (mem_mk'.mp hy)
    simpa using vadd_mem_of_mem_direction hd x.property
  · rw [direction_mk']
    have hrank : Module.finrank ℝ M = Module.finrank ℝ K :=
      Submodule.finrank_map_subtype_eq _ _
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hl
    change Module.finrank ℝ K + 1 = _ at hker
    omega

/-- Uniform common-ridge version of the face bridge: the all-face degeneracy
is discharged by constructing a subplane, rather than assuming a ridge. -/
theorem exists_genericFacePoints_common_ridge [FiniteDimensional ℝ E]
    {ι : Type*} [Countable ι] (P : AffineSubspace ℝ E)
    (hP : (P : Set E).Nonempty)
    (hcodim : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ E)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (f : ι → E →ᵃ[ℝ] ℝ) (c : ι → ℝ)
    (O : Set E) (hO : IsOpen (Subtype.val ⁻¹' O : Set P))
    (hconv : Convex ℝ O) (hne : (Subtype.val ⁻¹' O : Set P).Nonempty) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∀ x ∈ G, ∃ R : AffineSubspace ℝ E, (x : E) ∈ R ∧ R ≤ P ∧
        Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E ∧
        ∀ i, f i x = c i → R ≤ affineFormPlane (f i) (c i) := by
  obtain ⟨G,hGO,hpath,hclosure,hG⟩ :=
    exists_genericFacePoints P hP hcodim f c O hO hconv hne
  refine ⟨G,hGO,hpath,hclosure,?_⟩
  intro x hx
  rcases hG x hx with hall | hridge
  · obtain ⟨R,hxR,hRP,hrank⟩ := exists_ridge_through_face_point P hcodim hdim x
    exact ⟨R,hxR,hRP,hrank,fun i hi => hRP.trans (hall i hi)⟩
  · exact hridge

#print axioms exists_ridge_through_face_point
#print axioms exists_genericFacePoints_common_ridge

end SparseMonotiles
