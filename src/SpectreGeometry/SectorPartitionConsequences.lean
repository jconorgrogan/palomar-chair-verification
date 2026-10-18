module

public import SpectreGeometry.SectorPartitionCounts

@[expose] public section


namespace SpectreGeometry
noncomputable section
open scoped BigOperators

theorem sector_partition_masks_disjoint {ι : Type*}
    (k : ι → Fin 12) (b : ι → BoundarySlot)
    (hpartition : ∀ d : Fin 12, ∃! i, slotSector (b i) (directionAdd (directionInverse (k i)) d))
    {i j : ι} (hij : i ≠ j) : Disjoint (rotatedSlotMask (k i) (b i)) (rotatedSlotMask (k j) (b j)) := by
  apply Finset.disjoint_left.mpr
  intro d hdi hdj
  obtain ⟨a,ha,hu⟩ := hpartition d
  exact hij ((hu i (Finset.mem_filter.mp hdi).2).trans (hu j (Finset.mem_filter.mp hdj).2).symm)

theorem sector_partition_two_sixes {ι : Type*}
    (k : ι → Fin 12) (b : ι → BoundarySlot)
    (hpartition : ∀ d : Fin 12, ∃! i, slotSector (b i) (directionAdd (directionInverse (k i)) d))
    (i j : ι) (hij : i ≠ j)
    (hi : (slotSectorList (b i)).length = 6) (hj : (slotSectorList (b j)).length = 6) :
    ∀ a, a = i ∨ a = j := by
  intro a
  have hd := sector_partition_masks_disjoint k b hpartition hij
  have hc : (rotatedSlotMask (k i) (b i) ∪ rotatedSlotMask (k j) (b j)).card = 12 := by
    rw [Finset.card_union_of_disjoint hd,rotated_slot_card,rotated_slot_card,hi,hj]
  have he : rotatedSlotMask (k i) (b i) ∪ rotatedSlotMask (k j) (b j) = Finset.univ :=
    Finset.eq_univ_of_card _ hc
  have hapos : 0 < (rotatedSlotMask (k a) (b a)).card := by
    rw [rotated_slot_card]
    exact lt_of_lt_of_le (by decide : 0 < 3) (slot_sector_minimum (b a))
  obtain ⟨d,hd⟩ := Finset.card_pos.mp hapos
  have hm : d ∈ rotatedSlotMask (k i) (b i) ∪ rotatedSlotMask (k j) (b j) := by
    rw [he]
    exact Finset.mem_univ d
  obtain ⟨v,hv,hu⟩ := hpartition d
  have ha := hu a (Finset.mem_filter.mp hd).2
  rcases Finset.mem_union.mp hm with hm | hm
  · exact Or.inl (ha.trans (hu i (Finset.mem_filter.mp hm).2).symm)
  · exact Or.inr (ha.trans (hu j (Finset.mem_filter.mp hm).2).symm)

end
end SpectreGeometry
