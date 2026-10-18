module

public import SpectreClusters.StageDRawHaloModel

@[expose] public section

namespace SpectreClusters.StageD.Raw

def haloRangeCheck (root order : List Cell) (start : Nat) : Bool :=
  (List.range 8).all fun j => haloCheckAt root order (root.getD (start+j) ⟨(0,0),0⟩)

theorem halo_subset_of_ranges (root order : List Cell) (hlen : root.length ≤ 80)
    (h : ∀ b : Fin 10, haloRangeCheck root order (b.val*8) = true) :
    ∀ c ∈ halo root, c ∈ order := by
  apply halo_subset_of_checks
  intro a ha
  have hi := List.idxOf_lt_length_of_mem ha
  have hb : root.idxOf a / 8 < 10 := by omega
  have hj : root.idxOf a % 8 < 8 := Nat.mod_lt _ (by decide)
  have hx := List.all_eq_true.mp (h ⟨root.idxOf a / 8,hb⟩) (root.idxOf a % 8)
    (List.mem_range.mpr hj)
  have he : (root.idxOf a / 8)*8+root.idxOf a%8 = root.idxOf a := by omega
  have hg : root.getD (root.idxOf a) ⟨(0,0),0⟩ = a := by
    simp [List.getD_eq_getElem?_getD,hi]
  simpa only [he,hg] using hx

def haloWitnessCheck (root : List Cell) (entry : Cell × Cell) : Bool :=
  root.any (cellEqB entry.2) && !(root.any (cellEqB entry.1)) &&
    (contacts entry.2).any (cellEqB entry.1)

theorem haloWitnessCheck_sound (root : List Cell) (c a : Cell)
    (h : haloWitnessCheck root (c,a) = true) : c ∈ halo root := by
  simp only [haloWitnessCheck,Bool.and_eq_true,List.any_eq_true,cellEqB_iff] at h
  obtain ⟨⟨⟨d,hd,had⟩,hout⟩,e,he,hce⟩ := h
  apply (mem_halo_iff root c).mpr
  refine ⟨?_,a,by simpa only [had] using hd,?_⟩
  · intro hc
    have hx : root.any (cellEqB c) = true := List.any_eq_true.mpr ⟨c,hc,(cellEqB_iff c c).mpr rfl⟩
    simp [hx] at hout
  · exact (mem_contacts_iff a c).mp (by simpa only [hce] using he)

theorem haloWitnesses_sound (root : List Cell) (entries : List (Cell × Cell))
    (h : entries.all (haloWitnessCheck root) = true) :
    ∀ c ∈ entries.map Prod.fst, c ∈ halo root := by
  intro c hc
  obtain ⟨⟨d,a⟩,hd,rfl⟩ := List.mem_map.mp hc
  exact haloWitnessCheck_sound root d a (List.all_eq_true.mp h (d,a) hd)

theorem interpretation_order_eq_reverse (k : ClusterKind) :
    StageD.haloOrder k = (haloOrder k).reverse := by cases k <;> rfl
end SpectreClusters.StageD.Raw
