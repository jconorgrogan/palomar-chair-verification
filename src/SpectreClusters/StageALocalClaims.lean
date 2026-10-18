module

public import SpectreClusters.StageAWindowModel

@[expose] public section

namespace SpectreClusters.StageA

def oppositeCount (kind : HTKind) (i : Nat) : Nat :=
  (((rawWordAt kind i).eraseDups).filter fun n => !((candidateAt kind n).kind == kind)).length

def neighbors (kind : HTKind) (i : Nat) : List HTPlacement :=
  ((rawWordAt kind i).eraseDups).map (candidateAt kind)

set_option maxRecDepth 100000 in
theorem final_hat_count_check :
    (keptIds 2 .hat).all (fun i => oppositeCount .hat i ≤ 1 || i == 210) = true := by rfl
set_option maxRecDepth 100000 in
theorem final_turtle_count_check :
    (keptIds 2 .turtle).all (fun i => oppositeCount .turtle i ≤ 1 || i == 0) = true := by rfl

theorem final_hat_opposite_count (i : Nat) (hi : i ∈ keptIds 2 .hat) :
    oppositeCount .hat i ≤ 1 ∨ i = 210 := by
  have h := List.all_eq_true.mp final_hat_count_check i hi
  simpa using h

theorem final_turtle_opposite_count (i : Nat) (hi : i ∈ keptIds 2 .turtle) :
    oppositeCount .turtle i ≤ 1 ∨ i = 0 := by
  have h := List.all_eq_true.mp final_turtle_count_check i hi
  simpa using h

set_option maxRecDepth 100000 in
theorem turtle_special_six_hats : (neighbors .turtle 0).length = 6 ∧
    (neighbors .turtle 0).all (fun p => p.kind == .hat) = true := by decide
set_option maxRecDepth 100000 in
theorem hat_special_six_turtles : (neighbors .hat 210).length = 6 ∧
    (neighbors .hat 210).all (fun p => p.kind == .turtle) = true := by decide

set_option maxRecDepth 100000 in
theorem turtle_special_literal_check :
    (canonicalRoot .turtle :: neighbors .turtle 0).all
      (fun p => (clusterPieces .t6h).any (poseEqB p)) = true ∧
    (clusterPieces .t6h).all
      (fun p => (canonicalRoot .turtle :: neighbors .turtle 0).any (poseEqB p)) = true := by decide

/-- Exact occurrence-set equality for the exceptional turtle row. It is
not yet a claim that every physical turtle belongs to this row. -/
theorem turtle_special_literal (p : HTPlacement) :
    p ∈ (canonicalRoot .turtle :: neighbors .turtle 0) ↔ p ∈ clusterPieces .t6h := by
  constructor
  · intro hp
    obtain ⟨q,hq,hpq⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp turtle_special_literal_check.1 p hp)
    simpa only [(poseEqB_iff p q).mp hpq] using hq
  · intro hp
    obtain ⟨q,hq,hpq⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp turtle_special_literal_check.2 p hp)
    simpa only [(poseEqB_iff p q).mp hpq] using hq

end SpectreClusters.StageA
