module

public import SpectreClusters.StageAT7HForcingData

@[expose] public section


namespace SpectreClusters.StageA

def eighthHat : HTPlacement := ⟨.hat,2,(2,0)⟩

set_option maxRecDepth 100000

theorem turtle_upper_hat_alignment : alignmentValidB .turtle 11 = true := by rfl

theorem turtle_upper_hat_support_check :
    (keptIds 2 .hat).all (fun j =>
      !(supportB .turtle (rawWordAt .turtle 0) 11 (rawWordAt .hat j)) ||
        [13,15].contains j) = true := by rfl

theorem turtle_upper_hat_support (j : Nat) (hj : j ∈ keptIds 2 .hat)
    (hs : supportB .turtle (rawWordAt .turtle 0) 11 (rawWordAt .hat j) = true) :
    j = 13 ∨ j = 15 := by
  have h := List.all_eq_true.mp turtle_upper_hat_support_check j hj
  simpa [hs] using h

theorem turtle_upper_hat_mem : 11 ∈ rawWordAt .turtle 0 := by decide
theorem turtle_support13_extra_mem : 1 ∈ rawWordAt .hat 13 := by decide
theorem turtle_support15_extra_mem : 1 ∈ rawWordAt .hat 15 := by decide

theorem turtle_eighth_pose :
    movePlacement (candidateAt .turtle 11).turn (candidateAt .turtle 11).center
      (candidateAt .hat 1) = eighthHat := by rfl

theorem t8h_extra_check :
    (clusterPieces .t8h).all (fun p => (clusterPieces .t7h).contains p ||
      poseEqB p eighthHat) = true := by decide

theorem t8h_member_core_or_extra (p : HTPlacement) (hp : p ∈ clusterPieces .t8h) :
    p ∈ clusterPieces .t7h ∨ p = eighthHat := by
  have h := List.all_eq_true.mp t8h_extra_check p hp
  simpa only [Bool.or_eq_true,List.contains_iff_mem,poseEqB_iff] using h

theorem t7h_mem_t8h (p : HTPlacement) (hp : p ∈ clusterPieces .t7h) :
    p ∈ clusterPieces .t8h := by
  have h : (clusterPieces .t7h).all (clusterPieces .t8h).contains = true := by decide
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h p hp)

theorem eighthHat_mem_t8h : eighthHat ∈ clusterPieces .t8h := by decide

end SpectreClusters.StageA
