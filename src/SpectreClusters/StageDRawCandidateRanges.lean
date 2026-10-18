module

public import SpectreClusters.StageDRawData

@[expose] public section

namespace SpectreClusters.StageD.Raw

def alignedRangeChecks (root : List Cell) (candidates : List ClusterPlacement)
    (c : Cell) (witnesses : List CandidateWitness) (start count : Nat) : Bool :=
  (List.range count).all fun j =>
    witnessCheck root candidates ((alignedAt c).getD (start+j) fallback)
      (witnesses.getD (start+j) (.listed 0))

theorem alignedChecks_of_ranges (root : List Cell) (candidates : List ClusterPlacement)
    (c : Cell) (witnesses : List CandidateWitness)
    (hlen : (alignedAt c).length = 140)
    (h : ∀ b : Fin 2, alignedRangeChecks root candidates c witnesses (b.val*70) 70 = true) :
    alignedChecks root candidates c witnesses = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hib : i < 140 := by simpa only [List.mem_range,hlen] using hi
  have hb : i / 70 < 2 := by omega
  have hj : i % 70 < 70 := Nat.mod_lt _ (by decide)
  have hx := List.all_eq_true.mp (h ⟨i/70,hb⟩) (i%70) (List.mem_range.mpr hj)
  have he : (i / 70)*70 + i%70 = i := by omega
  simpa only [he] using hx
end SpectreClusters.StageD.Raw
