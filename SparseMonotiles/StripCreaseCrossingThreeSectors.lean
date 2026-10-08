module

public import SparseMonotiles.SectorAngleSumArithmetic

@[expose] public section

/-! # Name the actual two right-quadrant companions in the three-sector alternative -/
namespace SparseMonotiles
open Set SectorAngleSum

/-- The three-member alternative retains actual companion indices and their
right angles. No sectors are deduplicated by angle. -/
theorem flat_partition_three_actual_companions
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
    (hdim : Module.finrank ℝ E = 2) (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j))))
    (root : ι) (hflat : width root = Real.pi)
    (hinv : ∀ i, SectorArithmetic.InAngleInventory (width i))
    (hcard : Fintype.card ι = 3) :
    ∃ B C : ι, B ≠ root ∧ C ≠ root ∧ B ≠ C ∧
      (∀ A : ι, A = root ∨ A = B ∨ A = C) ∧
      HasSectorAngle (sector B) (Real.pi/2) ∧ HasSectorAngle (sector C) (Real.pi/2) := by
  have hs := flat_sector_companions hdim sector width hshape hcover hdisjoint root hflat (fun i _ => hinv i)
  have hl := companionAngles_length width root
  have hlist : companionAngles width root = [Real.pi/2,Real.pi/2] := by
    rcases hs with hs | hs
    · rw [hs,hcard] at hl
      norm_num at hl
    · exact hs
  have herase : (Finset.univ.erase root : Finset ι).card = 2 := by simp [hcard]
  obtain ⟨B,C,hBC,hset⟩ := Finset.card_eq_two.mp herase
  have hB : B ∈ Finset.univ.erase root := by rw [hset]; simp
  have hC : C ∈ Finset.univ.erase root := by rw [hset]; simp
  have hBne : B ≠ root := (Finset.mem_erase.mp hB).1
  have hCne : C ≠ root := (Finset.mem_erase.mp hC).1
  have hw (A : ι) (hA : A ≠ root) : width A = Real.pi/2 := by
    have hm : width A ∈ companionAngles width root :=
      (mem_companionAngles width root _).mpr ⟨A,hA,rfl⟩
    rw [hlist] at hm
    simpa using hm
  refine ⟨B,C,hBne,hCne,hBC,?_,?_,?_⟩
  · intro A
    by_cases hA : A = root
    · exact Or.inl hA
    · right
      have hm : A ∈ Finset.univ.erase root := Finset.mem_erase.mpr ⟨hA,Finset.mem_univ _⟩
      rw [hset] at hm
      simpa using hm
  · simpa only [hw B hBne] using hshape B
  · simpa only [hw C hCne] using hshape C

#print axioms flat_partition_three_actual_companions
end SparseMonotiles
