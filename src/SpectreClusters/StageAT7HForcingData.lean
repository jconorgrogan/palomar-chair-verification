module

public import SpectreClusters.StageAForcingChecks

@[expose] public section


namespace SpectreClusters.StageA

def seventhHat : HTPlacement := ⟨.hat,0,(1,-2)⟩

set_option maxRecDepth 100000

theorem turtle_core_hat_mem : 3 ∈ rawWordAt .turtle 0 := by decide

theorem turtle_support6_extra_mem : 1 ∈ rawWordAt .hat 6 := by decide

theorem turtle_support8_extra_mem : 1 ∈ rawWordAt .hat 8 := by decide

theorem turtle_seventh_pose :
    movePlacement (candidateAt .turtle 3).turn (candidateAt .turtle 3).center
      (candidateAt .hat 1) = seventhHat := by rfl

theorem t7h_extra_check :
    (clusterPieces .t7h).all (fun p => (clusterPieces .t6h).contains p ||
      poseEqB p seventhHat) = true := by decide

theorem t7h_member_core_or_extra (p : HTPlacement) (hp : p ∈ clusterPieces .t7h) :
    p ∈ clusterPieces .t6h ∨ p = seventhHat := by
  have h := List.all_eq_true.mp t7h_extra_check p hp
  simpa only [Bool.or_eq_true,List.contains_iff_mem,poseEqB_iff] using h

end SpectreClusters.StageA
