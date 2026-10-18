module

public import SpectreGeometry.SectorPartitionConsequences

@[expose] public section


namespace SpectreGeometry
noncomputable section
open scoped BigOperators

def AllowedSectorSize (a : Nat) : Prop := a = 3 ∨ a = 4 ∨ a = 6 ∨ a = 8 ∨ a = 9
instance (a : Nat) : Decidable (AllowedSectorSize a) := inferInstanceAs (Decidable (_ ∨ _))

theorem allowed_sector_list_sum (l : List Nat) (h : ∀ a ∈ l, AllowedSectorSize a) :
    l.sum ≠ 1 ∧ l.sum ≠ 2 ∧ l.sum ≠ 5 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := h a (by simp)
      have hl := ih (fun b hb => h b (by simp [hb]))
      simp only [List.sum_cons]
      unfold AllowedSectorSize at ha
      omega

theorem sector_partition_pair_sum {ι : Type*} [Fintype ι]
    (k : ι → Fin 12) (b : ι → BoundarySlot)
    (hpart : ∀ d : Fin 12, ∃! i, slotSector (b i) (directionAdd (directionInverse (k i)) d))
    (i j : ι) (hij : i ≠ j) :
    (slotSectorList (b i)).length + (slotSectorList (b j)).length = 6 ∨
    (slotSectorList (b i)).length + (slotSectorList (b j)).length = 8 ∨
    (slotSectorList (b i)).length + (slotSectorList (b j)).length = 9 ∨
    (slotSectorList (b i)).length + (slotSectorList (b j)).length = 12 := by
  classical
  let s : Finset ι := (Finset.univ.erase i).erase j
  let l := s.toList.map (fun a => (slotSectorList (b a)).length)
  have hsum : l.sum + (slotSectorList (b j)).length + (slotSectorList (b i)).length = 12 := by
    have h1 := Finset.sum_erase_add (Finset.univ (α := ι))
      (fun a => (slotSectorList (b a)).length) (Finset.mem_univ i)
    have h2 := Finset.sum_erase_add (Finset.univ.erase i)
      (fun a => (slotSectorList (b a)).length) (Finset.mem_erase.mpr ⟨Ne.symm hij,Finset.mem_univ j⟩)
    have ht := sector_partition_sum k b hpart
    rw [ht] at h1
    dsimp only [l]
    rw [Finset.sum_map_toList]
    dsimp only [s]
    omega
  have hsmall := allowed_sector_list_sum l (by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact slot_sector_sizes (b v))
  have hi := slot_sector_sizes (b i)
  have hj := slot_sector_sizes (b j)
  omega

end
end SpectreGeometry
