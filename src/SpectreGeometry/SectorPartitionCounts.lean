module

public import SpectreGeometry.PhysicalSectorStar

@[expose] public section


/-! Counting consequences of a genuine twelve-sector partition. No physical
registration is assumed. -/
namespace SpectreGeometry
noncomputable section
open scoped BigOperators

def rotatedSlotMask (k : Fin 12) (b : BoundarySlot) : Finset (Fin 12) :=
  Finset.univ.filter (fun d => slotSector b (directionAdd (directionInverse k) d))

theorem rotated_slot_card : ∀ (k : Fin 12) (b : BoundarySlot),
    (rotatedSlotMask k b).card = (slotSectorList b).length := by decide

theorem sector_partition_sum {ι : Type*} [Fintype ι]
    (k : ι → Fin 12) (b : ι → BoundarySlot)
    (hpartition : ∀ d : Fin 12, ∃! i, slotSector (b i) (directionAdd (directionInverse (k i)) d)) :
    ∑ i, (slotSectorList (b i)).length = 12 := by
  classical
  have hdisjoint : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => rotatedSlotMask (k i) (b i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro d hdi hdj
    have hi' := (Finset.mem_filter.mp hdi).2
    have hj' := (Finset.mem_filter.mp hdj).2
    obtain ⟨a,ha,hu⟩ := hpartition d
    exact hij ((hu i hi').trans (hu j hj').symm)
  have hunion : Finset.univ.biUnion (fun i => rotatedSlotMask (k i) (b i)) = Finset.univ := by
    ext d
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,iff_true]
    obtain ⟨i,hi,_⟩ := hpartition d
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ d,hi⟩⟩
  have hc := Finset.card_biUnion hdisjoint
  rw [hunion] at hc
  simp only [rotated_slot_card,Finset.card_univ,Fintype.card_fin] at hc
  exact hc.symm

theorem sector_partition_other_size {ι : Type*} [Fintype ι]
    (k : ι → Fin 12) (b : ι → BoundarySlot)
    (hpartition : ∀ d : Fin 12, ∃! i, slotSector (b i) (directionAdd (directionInverse (k i)) d))
    (root : ι) (hroot : (slotSectorList (b root)).length = 6)
    (i : ι) (hi : i ≠ root) :
    (slotSectorList (b i)).length = 3 ∨ (slotSectorList (b i)).length = 6 := by
  classical
  let s : Finset ι := Finset.univ.erase root
  let l : List Nat := s.toList.map (fun j => (slotSectorList (b j)).length)
  have hs : ∑ j ∈ s, (slotSectorList (b j)).length = 6 := by
    have he := Finset.sum_erase_add (Finset.univ (α := ι))
      (fun j => (slotSectorList (b j)).length) (Finset.mem_univ root)
    have ht := sector_partition_sum k b hpartition
    rw [hroot,ht] at he
    dsimp only [s]
    omega
  have hsum : l.sum = 6 := by simpa only [l,Finset.sum_map_toList] using hs
  have hmin : ∀ a ∈ l, 3 ≤ a := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact slot_sector_minimum (b j)
  have himem : (slotSectorList (b i)).length ∈ l := by
    apply List.mem_map.mpr
    exact ⟨i,Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩),rfl⟩
  rcases halfturn_partition l hmin hsum with h | h
  · rw [h] at himem
    exact Or.inr (by simpa using himem)
  · rw [h] at himem
    exact Or.inl (by simpa using himem)

end
end SpectreGeometry
