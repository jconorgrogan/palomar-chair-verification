module

public import SpectreClusters.StageABindingCore
public import SpectreClusters.GridCoverModel

@[expose] public section

namespace SpectreClusters.StageA

set_option maxRecDepth 100000 in
theorem haloA_cover :
    (halo (htCells .hat)).all (fun c => (haloOrder .hat).any (cellEqB c)) = true := by rfl
set_option maxRecDepth 100000 in
theorem haloA_sound :
    (haloOrder .hat).all (fun c => (halo (htCells .hat)).any (cellEqB c)) = true := by rfl
set_option maxRecDepth 100000 in
theorem haloB_cover :
    (halo (htCells .turtle)).all (fun c => (haloOrder .turtle).any (cellEqB c)) = true := by rfl
set_option maxRecDepth 100000 in
theorem haloB_sound :
    (haloOrder .turtle).all (fun c => (halo (htCells .turtle)).any (cellEqB c)) = true := by rfl

theorem haloOrder_mem_iff (kind : HTKind) (c : Cell) :
    c ∈ haloOrder kind ↔ c ∈ halo (htCells kind) := by
  have hs : (haloOrder kind).all (fun c => (halo (htCells kind)).any (cellEqB c)) = true := by
    cases kind
    · exact haloA_sound
    · exact haloB_sound
  have hc : (halo (htCells kind)).all (fun c => (haloOrder kind).any (cellEqB c)) = true := by
    cases kind
    · exact haloA_cover
    · exact haloB_cover
  constructor
  · intro h
    obtain ⟨d,hd,hcd⟩ := List.any_eq_true.mp (List.all_eq_true.mp hs c h)
    simpa only [(cellEqB_iff c d).mp hcd] using hd
  · intro h
    obtain ⟨d,hd,hcd⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc c h)
    simpa only [(cellEqB_iff c d).mp hcd] using hd

set_option maxRecDepth 100000 in
theorem choicesA_bound : choicesTable .hat = (haloOrder .hat).map (indexedChoices .hat) := by rfl
set_option maxRecDepth 100000 in
theorem choicesB_bound : choicesTable .turtle = (haloOrder .turtle).map (indexedChoices .turtle) := by rfl

theorem choicesTable_bound (kind : HTKind) :
    choicesTable kind = (haloOrder kind).map (indexedChoices kind) := by
  cases kind
  · exact choicesA_bound
  · exact choicesB_bound

end SpectreClusters.StageA
