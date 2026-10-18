module

public import SpectreClusters.StageAActualSupport

@[expose] public section


/-! Every captured actual full-grid tiling contains an actual hat occurrence.
Three final turtle rows have no immediate hat, but candidate28 forces a hat
one ring farther out. No existence is inferred merely from a row label. -/
namespace SpectreClusters.StageA

def rowHasHatB (i : Nat) : Bool :=
  (neighbors .turtle i).any (fun p => p.kind == .hat)

set_option maxRecDepth 100000 in
theorem final_turtle_has_hat_or_exception_check :
    (keptIds 2 .turtle).all (fun i => rowHasHatB i || [219,229,248].contains i) = true := by rfl

set_option maxRecDepth 100000 in
theorem hat_presence_neighbor_check :
    [219,229,248].all (fun i => (rawWordAt .turtle i).contains 28 &&
      (keptIds 2 .turtle).all (fun j =>
        !(supportB .turtle (rawWordAt .turtle i) 28 (rawWordAt .turtle j)) ||
          rowHasHatB j)) = true := by rfl

theorem hat_presence_alignment : alignmentValidB .turtle 28 = true := by rfl
theorem hat_presence_candidate_kind : (candidateAt .turtle 28).kind = .turtle := by rfl

theorem row_has_hat_owned (f : Cell → HTPlacement) (hf : ValidGridField f)
    (hr : RootOwned f (canonicalRoot .turtle)) (i : Nat)
    (hword : rawWordAt .turtle i = wordOf f .turtle) (hh : rowHasHatB i = true) :
    ∃ p, RootOwned f p ∧ p.kind = .hat := by
  obtain ⟨p,hp,hk⟩ := List.any_eq_true.mp hh
  exact ⟨p,((row_neighbors_iff_fieldNeighbor f hf .turtle hr i hword p).mp hp).1,
    by simpa using hk⟩

theorem normalized_turtle_has_hat (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (hr : RootOwned f (canonicalRoot .turtle)) :
    ∃ p, RootOwned f p ∧ p.kind = .hat := by
  obtain ⟨i,hi,hword⟩ := hcaptures f hf .turtle hr
  change rawWordAt .turtle i = wordOf f .turtle at hword
  have hc := List.all_eq_true.mp final_turtle_has_hat_or_exception_check i hi
  have hd : rowHasHatB i = true ∨ i ∈ [219,229,248] := by simpa using hc
  rcases hd with hh | he
  · exact row_has_hat_owned f hf hr i hword hh
  · have hc := List.all_eq_true.mp hat_presence_neighbor_check i he
    simp only [Bool.and_eq_true] at hc
    have hn : 28 ∈ rawWordAt .turtle i := by simpa using hc.1
    obtain ⟨j,hj,hjword,hs⟩ := actual_neighbor_support hcaptures f hf .turtle hr i 28
      hword hn hat_presence_alignment
    change supportB .turtle (rawWordAt .turtle i) 28 (rawWordAt .turtle j) = true at hs
    have hj' : j ∈ keptIds 2 .turtle := by simpa only [hat_presence_candidate_kind] using hj
    have hcj := List.all_eq_true.mp hc.2 j hj'
    have hh : rowHasHatB j = true := by simpa [hs] using hcj
    let q := candidateAt .turtle 28
    have hq : RootOwned f q := GridReductionWindowBinding.represented_neighbor_owned f hf .turtle
      (field_mem_candidates f hf .turtle hr) 28 (show 28 ∈ wordOf f .turtle from hword ▸ hn)
    have hroot : RootOwned (normalizeField f q) (canonicalRoot .turtle) := by
      simpa only [q,hat_presence_candidate_kind,originRoot,canonicalRoot] using normalizeField_rootOwned f q hq
    have hw : rawWordAt .turtle j = wordOf (normalizeField f q) .turtle := by
      simpa only [q,hat_presence_candidate_kind] using hjword
    obtain ⟨p,hp,hpk⟩ := row_has_hat_owned (normalizeField f q) (normalizeField_valid f hf q)
      hroot j hw hh
    exact ⟨movePlacement q.turn q.center p,owned_of_normalized_owned f q p hp,hpk⟩

/-- This is a genuine owned occurrence, not only an abstract final-row label. -/
theorem exists_owned_hat (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ∃ p, RootOwned f p ∧ p.kind = .hat := by
  let c : Cell := ⟨(0,0),0⟩
  let root := f c
  have hr : RootOwned f root := GridReduction.field_rootOwned f hf c
  cases hk : root.kind with
  | hat => exact ⟨root,hr,hk⟩
  | turtle =>
    let g := normalizeField f root
    have hv : ValidGridField g := normalizeField_valid f hf root
    have hroot : RootOwned g (canonicalRoot .turtle) := by
      simpa only [hk,originRoot,canonicalRoot] using normalizeField_rootOwned f root hr
    obtain ⟨p,hp,hpk⟩ := normalized_turtle_has_hat hcaptures g hv hroot
    exact ⟨movePlacement root.turn root.center p,
      owned_of_normalized_owned f root p hp,hpk⟩

end SpectreClusters.StageA
