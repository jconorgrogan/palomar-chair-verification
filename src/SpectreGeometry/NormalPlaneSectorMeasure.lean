module

public import PhysicalRegistration.PlanarSectorMeasure

@[expose] public section


/-! Angular measure of literal halfplanes restricted to an isometrically
embedded two-dimensional normal plane. Range, nonzero, and angle assumptions
are explicit. The chart need not be surjective onto the ambient space. -/
namespace SpectreGeometry
noncomputable section
open Set MeasureTheory
open PhysicalRegistration.PlanarSectorMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sectorHalfplane (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E) (n : E) : Set Real.Angle :=
  {θ | inner ℝ n (L (direction θ)) ≤ 0}

/-- A normal lying in the chart's image pulls back to the literal planar
halfplane determined by its preimage. -/
theorem sectorHalfplane_map (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E)
    (a : EuclideanSpace ℝ (Fin 2)) : sectorHalfplane L (L a) = halfplane a := by
  ext θ
  simp only [sectorHalfplane, halfplane, Set.mem_setOf_eq, L.inner_map_map]

theorem volume_sectorHalfplane (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E)
    {n : E} (hn0 : n ≠ 0) (hnRange : n ∈ Set.range L) :
    volume (sectorHalfplane L n) = ENNReal.ofReal Real.pi := by
  obtain ⟨a,rfl⟩ := hnRange
  have ha : a ≠ 0 := by
    intro he
    apply hn0
    rw [he, map_zero]
  rw [sectorHalfplane_map]
  exact volume_halfplane ha

theorem volume_sectorHalfplane_inter (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E)
    {n m : E} (hn0 : n ≠ 0) (hm0 : m ≠ 0)
    (hnRange : n ∈ Set.range L) (hmRange : m ∈ Set.range L)
    (hangle : InnerProductGeometry.angle n m < Real.pi) :
    volume (sectorHalfplane L n ∩ sectorHalfplane L m) =
      ENNReal.ofReal (Real.pi - InnerProductGeometry.angle n m) := by
  obtain ⟨a,rfl⟩ := hnRange
  obtain ⟨b,rfl⟩ := hmRange
  have ha : a ≠ 0 := by
    intro he
    apply hn0
    rw [he, map_zero]
  have hb : b ≠ 0 := by
    intro he
    apply hm0
    rw [he, map_zero]
  have hab : InnerProductGeometry.angle a b < Real.pi := by
    simpa only [L.angle_map] using hangle
  simpa only [sectorHalfplane_map, L.angle_map] using volume_halfplane_inter ha hb hab

theorem volume_sectorHalfplane_union (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E)
    {n m : E} (hn0 : n ≠ 0) (hm0 : m ≠ 0)
    (hnRange : n ∈ Set.range L) (hmRange : m ∈ Set.range L)
    (hangle : InnerProductGeometry.angle n m < Real.pi) :
    volume (sectorHalfplane L n ∪ sectorHalfplane L m) =
      ENNReal.ofReal (Real.pi + InnerProductGeometry.angle n m) := by
  obtain ⟨a,rfl⟩ := hnRange
  obtain ⟨b,rfl⟩ := hmRange
  have ha : a ≠ 0 := by
    intro he
    apply hn0
    rw [he, map_zero]
  have hb : b ≠ 0 := by
    intro he
    apply hm0
    rw [he, map_zero]
  have hab : InnerProductGeometry.angle a b < Real.pi := by
    simpa only [L.angle_map] using hangle
  simpa only [sectorHalfplane_map, L.angle_map] using volume_halfplane_union ha hb hab

/-- Two nonzero orthogonal normals in the same chart cut out a genuine
quarter-circle of angular measure π/2. -/
theorem volume_sectorHalfplane_orthogonal (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E)
    {n m : E} (hn0 : n ≠ 0) (hm0 : m ≠ 0)
    (hnRange : n ∈ Set.range L) (hmRange : m ∈ Set.range L)
    (horth : inner ℝ n m = 0) :
    volume (sectorHalfplane L n ∩ sectorHalfplane L m) =
      ENNReal.ofReal (Real.pi / 2) := by
  have hangle : InnerProductGeometry.angle n m = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two n m).mp horth
  have hlt : InnerProductGeometry.angle n m < Real.pi := by
    rw [hangle]
    linarith [Real.pi_pos]
  rw [volume_sectorHalfplane_inter L hn0 hm0 hnRange hmRange hlt, hangle]
  congr 1
  ring

end
end SpectreGeometry
