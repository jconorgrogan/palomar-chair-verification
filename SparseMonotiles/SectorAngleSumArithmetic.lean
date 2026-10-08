module

public import SparseMonotiles.SectorAngleSumPlaneGeometry
public import SparseMonotiles.SectorArithmetic

@[expose] public section

/-! # The actual companion-tile list and geometric K1/K2 arithmetic

One list entry is retained for every index other than the distinguished sector.
Equal widths are not deduplicated. Its complementary angle sum is derived from
the geometric partition theorem, never assumed.
-/

namespace SparseMonotiles
namespace SectorAngleSum

open Set

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

/-- One actual angle entry per companion index. -/
noncomputable def companionAngles (width : ι → ℝ) (i₀ : ι) : List ℝ :=
  (Finset.univ.erase i₀).toList.map width

@[simp] theorem companionAngles_length (width : ι → ℝ) (i₀ : ι) :
    (companionAngles width i₀).length = Fintype.card ι - 1 := by
  simp [companionAngles]

/-- Companion entries are exactly the actual other indexed sectors. -/
theorem mem_companionAngles (width : ι → ℝ) (i₀ : ι) (θ : ℝ) :
    θ ∈ companionAngles width i₀ ↔ ∃ i, i ≠ i₀ ∧ width i = θ := by
  simp [companionAngles]

/-- The list sum is the genuine complement of the distinguished sector. -/
theorem companionAngles_sum
    (hdim : Module.finrank ℝ E = 2) (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j))))
    (i₀ : ι) :
    (companionAngles width i₀).sum = 2*Real.pi-width i₀ := by
  have hsum := rank_two_geometric_sector_partition_sum hdim sector width hshape hcover hdisjoint
  have herase := Finset.sum_erase_add Finset.univ width (Finset.mem_univ i₀)
  simp only [companionAngles, Finset.sum_map_toList]
  linarith

/-- The arithmetic sector-partition predicate is now a geometric conclusion,
with the inventory provided separately for the actual companion tiles. -/
theorem companionAngles_sectorPartition
    (hdim : Module.finrank ℝ E = 2) (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j))))
    (i₀ : ι) (hinv : ∀ i, i ≠ i₀ → SectorArithmetic.InAngleInventory (width i)) :
    SectorArithmetic.SectorPartition (companionAngles width i₀) (2*Real.pi-width i₀) := by
  constructor
  · intro θ hθ
    obtain ⟨i,hi,rfl⟩ := (mem_companionAngles width i₀ θ).mp hθ
    exact hinv i hi
  · exact companionAngles_sum hdim sector width hshape hcover hdisjoint i₀

/-- Geometric K1 angle classification around a genuine flat sector. -/
theorem flat_sector_companions
    (hdim : Module.finrank ℝ E = 2) (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j))))
    (i₀ : ι) (hflat : width i₀ = Real.pi)
    (hinv : ∀ i, i ≠ i₀ → SectorArithmetic.InAngleInventory (width i)) :
    companionAngles width i₀ = [Real.pi] ∨
      companionAngles width i₀ = [Real.pi/2,Real.pi/2] := by
  have h := companionAngles_sectorPartition hdim sector width hshape hcover hdisjoint i₀ hinv
  rw [hflat, show 2*Real.pi-Real.pi = Real.pi by ring] at h
  exact SectorArithmetic.pi_sector_classification h

/-- Geometric K2: a key-crease sector has exactly one actual companion index,
whose angle is the complementary non-flat angle. -/
theorem key_sector_unique_companion
    (hdim : Module.finrank ℝ E = 2) (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j))))
    (i₀ : ι) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : width i₀ = Real.pi-δ ∨ width i₀ = Real.pi+δ)
    (hinv : ∀ i, i ≠ i₀ → SectorArithmetic.InAngleInventory (width i)) :
    companionAngles width i₀ = [2*Real.pi-width i₀] ∧
      2*Real.pi-width i₀ ≠ Real.pi ∧ Fintype.card ι = 2 := by
  have h := companionAngles_sectorPartition hdim sector width hshape hcover hdisjoint i₀ hinv
  obtain ⟨hc,hn⟩ := SectorArithmetic.key_crease_complement_classification hδ hδ' hkey h
  refine ⟨hc,hn,?_⟩
  have hl := companionAngles_length width i₀
  rw [hc] at hl
  simp only [List.length_singleton] at hl
  omega

#print axioms companionAngles_sum
#print axioms flat_sector_companions
#print axioms key_sector_unique_companion

end SectorAngleSum
end SparseMonotiles
