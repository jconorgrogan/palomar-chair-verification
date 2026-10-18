module

public import SpectreClusters.StageARegularHatCoverData

@[expose] public section


namespace SpectreClusters.StageA

theorem row_candidate_owned (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (canonicalRoot kind)) (i : Nat)
    (hword : rawWordAt kind i = wordOf f kind) (n : Nat)
    (hn : n ∈ rawWordAt kind i) : RootOwned f (candidateAt kind n) := by
  exact GridReductionWindowBinding.represented_neighbor_owned f hf kind
    (field_mem_candidates f hf kind hr) n (show n ∈ wordOf f kind from hword ▸ hn)

theorem up_neighbor_turtle_cover (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (hr : RootOwned f (canonicalRoot .hat)) (i : Nat)
    (hword : rawWordAt .hat i = wordOf f .hat)
    (hn : 2 ∈ rawWordAt .hat i) (hcheck : upSupportCheckB i = true) :
    ∃ t, RootOwned f t ∧ t.kind = .turtle ∧
      canonicalRoot .hat ∈ clusterPiecesAt .t8h t := by
  obtain ⟨j,hj,hjword,hs⟩ := actual_neighbor_support hcaptures f hf .hat hr i 2
    hword hn hat_up_alignment
  have ht := row_candidate_owned f hf .hat hr i hword 2 hn
  have hv := normalizeField_valid f hf (candidateAt .hat 2)
  have hr' : RootOwned (normalizeField f (candidateAt .hat 2)) (canonicalRoot .hat) :=
    normalizeField_rootOwned f (candidateAt .hat 2) ht
  change rawWordAt .hat j = wordOf (normalizeField f (candidateAt .hat 2)) .hat at hjword
  rcases up_support_of_check i j hcheck hj hs with rfl | rfl
  · have ho := row_candidate_owned (normalizeField f (candidateAt .hat 2)) hv .hat hr'
      8 hjword 33 up_row8_turtle_mem
    exact ⟨firstUpperTurtle,owned_of_normalized_owned f (candidateAt .hat 2)
      (candidateAt .hat 33) ho,firstUpperTurtle_kind,firstUpperTurtle_covers⟩
  · have ho := row_candidate_owned (normalizeField f (candidateAt .hat 2)) hv .hat hr'
      15 hjword 51 up_row15_turtle_mem
    exact ⟨secondUpperTurtle,owned_of_normalized_owned f (candidateAt .hat 2)
      (candidateAt .hat 51) ho,secondUpperTurtle_kind,secondUpperTurtle_covers⟩

/-- A regular genuine hat lies at a literal T8H piece position of an
actually present turtle, including hats outside every T6H core. This is a
cover statement; it does not assign shared extra hats to two clusters. -/
theorem regular_hat_has_turtle_cover (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (hr : RootOwned f (canonicalRoot .hat)) (i : Nat)
    (hi : i ∈ keptIds 2 .hat) (hne : i ≠ 210)
    (hword : rawWordAt .hat i = wordOf f .hat) :
    ∃ t, RootOwned f t ∧ t.kind = .turtle ∧
      canonicalRoot .hat ∈ clusterPiecesAt .t8h t := by
  rcases regular_hat_cover_alternatives i hi hne with ⟨n,hn,hkind,hcover⟩ | h16 | h27 | h38
  · exact ⟨candidateAt .hat n,row_candidate_owned f hf .hat hr i hword n hn,hkind,hcover⟩
  · subst i
    exact up_neighbor_turtle_cover hcaptures f hf hr 16 hword hat16_up_mem hat16_up_support_check
  · subst i
    exact up_neighbor_turtle_cover hcaptures f hf hr 27 hword hat27_up_mem hat27_up_support_check
  · subst i
    exact up_neighbor_turtle_cover hcaptures f hf hr 38 hword hat38_up_mem hat38_up_support_check

end SpectreClusters.StageA
