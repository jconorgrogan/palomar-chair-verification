module

public import SpectreClusters.StageDRawProbeRowsT7HPart0
public import SpectreClusters.StageDRawProbeRowsT7HPart1
public import SpectreClusters.StageDRawProbeRowsT7HPart2
public import SpectreClusters.StageDRawProbeRowsT7HPart3
public import SpectreClusters.StageDRawProbeRowsT7HPart4
public import SpectreClusters.StageDRawProbeT7HStep6

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT7H : List (List Nat × Nat) := probeRowWitnessesT7H0 ++ probeRowWitnessesT7H1 ++ probeRowWitnessesT7H2 ++ probeRowWitnessesT7H3 ++ probeRowWitnessesT7H4
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H_words : probeRowWitnessesT7H.map Prod.fst = probeSuffixT7H6 := by rfl
theorem probeRowWitnessesT7H_checked : probeRowWitnessesT7H.all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by
  simp only [probeRowWitnessesT7H,List.all_append,probeRowWitnessesT7H0_checked,probeRowWitnessesT7H1_checked,probeRowWitnessesT7H2_checked,probeRowWitnessesT7H3_checked,probeRowWitnessesT7H4_checked,Bool.and_self]

theorem probeSuffixT7H_covered (w : List Nat) (hw : w ∈ probeSuffixT7H6) :
    ∃ i, i < (rawNeighborIDs .t7h).length ∧
      ∀ j ∈ (rawNeighborIDs .t7h).getD i [], j ∈ w := by
  rw [←probeRowWitnessesT7H_words] at hw
  obtain ⟨⟨word,i⟩,hm,he⟩ := List.mem_map.mp hw
  change word = w at he
  obtain ⟨hi,hrow⟩ := wordCoversRowB_sound .t7h word i
    (List.all_eq_true.mp probeRowWitnessesT7H_checked (word,i) hm)
  exact ⟨i,hi,by simpa only [he] using hrow⟩
end SpectreClusters.StageD.Raw
