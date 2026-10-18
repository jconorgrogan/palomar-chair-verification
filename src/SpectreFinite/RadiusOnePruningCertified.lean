module

public import SpectreFinite.RadiusOnePruningRounds
public import SpectreFinite.RadiusOnePruningInitialGamma
public import SpectreFinite.RadiusOnePruningInitialDelta
public import SpectreFinite.RadiusOnePruningInitialTheta
public import SpectreFinite.RadiusOnePruningInitialLambda
public import SpectreFinite.RadiusOnePruningInitialXi
public import SpectreFinite.RadiusOnePruningInitialPi
public import SpectreFinite.RadiusOnePruningInitialSigma
public import SpectreFinite.RadiusOnePruningInitialPhi
public import SpectreFinite.RadiusOnePruningInitialPsi

@[expose] public section

/-! Concrete occurrence-complete 306-window family for globally matching
discrete marked-hexagon fields. No field existence, listed-parent forcing,
exact filter/fixed-point equality, or physical correspondence is asserted. -/
namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem blockPatch_mem (block : List Verdict) (hb : block ∈ chunks0) (p : Patch)
    (hp : p ∈ (block.map Verdict.window).map windowPatch) :
    p ∈ (rows0.map Verdict.window).map windowPatch := by
  obtain ⟨w,hw,he⟩ := List.mem_map.mp hp
  obtain ⟨v,hv,hvw⟩ := List.mem_map.mp hw
  apply List.mem_map.mpr
  refine ⟨w,?_,he⟩
  apply List.mem_map.mpr
  exact ⟨v,List.mem_flatten.mpr ⟨block,hb,hv⟩,hvw⟩

theorem raw_rotated_mem_initial : ∀ k : TileKind, ∀ t : Fin 6, ∀ p : Patch,
    p ∈ (RadiusOne.assignments (k,0)).map (rotatePatch t RadiusOne.positions) →
      p ∈ (rows0.map Verdict.window).map windowPatch := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i)))))))))
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (0,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (0,0) = RadiusOne.gammaStage6 := RadiusOne.gammaStage6_exact
      rw [hr, initial0_0] at hp
      exact blockPatch_mem rows0_0_0 (List.getElem_mem (l := chunks0) (n := 0) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (0,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (0,0) = RadiusOne.gammaStage6 := RadiusOne.gammaStage6_exact
      rw [hr, initial0_1] at hp
      exact blockPatch_mem rows0_0_1 (List.getElem_mem (l := chunks0) (n := 1) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (0,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (0,0) = RadiusOne.gammaStage6 := RadiusOne.gammaStage6_exact
      rw [hr, initial0_2] at hp
      exact blockPatch_mem rows0_0_2 (List.getElem_mem (l := chunks0) (n := 2) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (0,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (0,0) = RadiusOne.gammaStage6 := RadiusOne.gammaStage6_exact
      rw [hr, initial0_3] at hp
      exact blockPatch_mem rows0_0_3 (List.getElem_mem (l := chunks0) (n := 3) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (0,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (0,0) = RadiusOne.gammaStage6 := RadiusOne.gammaStage6_exact
      rw [hr, initial0_4] at hp
      exact blockPatch_mem rows0_0_4 (List.getElem_mem (l := chunks0) (n := 4) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (0,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (0,0) = RadiusOne.gammaStage6 := RadiusOne.gammaStage6_exact
      rw [hr, initial0_5] at hp
      exact blockPatch_mem rows0_0_5 (List.getElem_mem (l := chunks0) (n := 5) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (1,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (1,0) = RadiusOne.deltaStage6 := RadiusOne.deltaStage6_exact
      rw [hr, initial1_0] at hp
      exact blockPatch_mem rows0_1_0 (List.getElem_mem (l := chunks0) (n := 6) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (1,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (1,0) = RadiusOne.deltaStage6 := RadiusOne.deltaStage6_exact
      rw [hr, initial1_1] at hp
      exact blockPatch_mem rows0_1_1 (List.getElem_mem (l := chunks0) (n := 7) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (1,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (1,0) = RadiusOne.deltaStage6 := RadiusOne.deltaStage6_exact
      rw [hr, initial1_2] at hp
      exact blockPatch_mem rows0_1_2 (List.getElem_mem (l := chunks0) (n := 8) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (1,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (1,0) = RadiusOne.deltaStage6 := RadiusOne.deltaStage6_exact
      rw [hr, initial1_3] at hp
      exact blockPatch_mem rows0_1_3 (List.getElem_mem (l := chunks0) (n := 9) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (1,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (1,0) = RadiusOne.deltaStage6 := RadiusOne.deltaStage6_exact
      rw [hr, initial1_4] at hp
      exact blockPatch_mem rows0_1_4 (List.getElem_mem (l := chunks0) (n := 10) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (1,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (1,0) = RadiusOne.deltaStage6 := RadiusOne.deltaStage6_exact
      rw [hr, initial1_5] at hp
      exact blockPatch_mem rows0_1_5 (List.getElem_mem (l := chunks0) (n := 11) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (2,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (2,0) = RadiusOne.thetaStage6 := RadiusOne.thetaStage6_exact
      rw [hr, initial2_0] at hp
      exact blockPatch_mem rows0_2_0 (List.getElem_mem (l := chunks0) (n := 12) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (2,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (2,0) = RadiusOne.thetaStage6 := RadiusOne.thetaStage6_exact
      rw [hr, initial2_1] at hp
      exact blockPatch_mem rows0_2_1 (List.getElem_mem (l := chunks0) (n := 13) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (2,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (2,0) = RadiusOne.thetaStage6 := RadiusOne.thetaStage6_exact
      rw [hr, initial2_2] at hp
      exact blockPatch_mem rows0_2_2 (List.getElem_mem (l := chunks0) (n := 14) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (2,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (2,0) = RadiusOne.thetaStage6 := RadiusOne.thetaStage6_exact
      rw [hr, initial2_3] at hp
      exact blockPatch_mem rows0_2_3 (List.getElem_mem (l := chunks0) (n := 15) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (2,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (2,0) = RadiusOne.thetaStage6 := RadiusOne.thetaStage6_exact
      rw [hr, initial2_4] at hp
      exact blockPatch_mem rows0_2_4 (List.getElem_mem (l := chunks0) (n := 16) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (2,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (2,0) = RadiusOne.thetaStage6 := RadiusOne.thetaStage6_exact
      rw [hr, initial2_5] at hp
      exact blockPatch_mem rows0_2_5 (List.getElem_mem (l := chunks0) (n := 17) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (3,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (3,0) = RadiusOne.lambdaStage6 := RadiusOne.lambdaStage6_exact
      rw [hr, initial3_0] at hp
      exact blockPatch_mem rows0_3_0 (List.getElem_mem (l := chunks0) (n := 18) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (3,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (3,0) = RadiusOne.lambdaStage6 := RadiusOne.lambdaStage6_exact
      rw [hr, initial3_1] at hp
      exact blockPatch_mem rows0_3_1 (List.getElem_mem (l := chunks0) (n := 19) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (3,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (3,0) = RadiusOne.lambdaStage6 := RadiusOne.lambdaStage6_exact
      rw [hr, initial3_2] at hp
      exact blockPatch_mem rows0_3_2 (List.getElem_mem (l := chunks0) (n := 20) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (3,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (3,0) = RadiusOne.lambdaStage6 := RadiusOne.lambdaStage6_exact
      rw [hr, initial3_3] at hp
      exact blockPatch_mem rows0_3_3 (List.getElem_mem (l := chunks0) (n := 21) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (3,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (3,0) = RadiusOne.lambdaStage6 := RadiusOne.lambdaStage6_exact
      rw [hr, initial3_4] at hp
      exact blockPatch_mem rows0_3_4 (List.getElem_mem (l := chunks0) (n := 22) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (3,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (3,0) = RadiusOne.lambdaStage6 := RadiusOne.lambdaStage6_exact
      rw [hr, initial3_5] at hp
      exact blockPatch_mem rows0_3_5 (List.getElem_mem (l := chunks0) (n := 23) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (4,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (4,0) = RadiusOne.xiStage6 := RadiusOne.xiStage6_exact
      rw [hr, initial4_0] at hp
      exact blockPatch_mem rows0_4_0 (List.getElem_mem (l := chunks0) (n := 24) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (4,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (4,0) = RadiusOne.xiStage6 := RadiusOne.xiStage6_exact
      rw [hr, initial4_1] at hp
      exact blockPatch_mem rows0_4_1 (List.getElem_mem (l := chunks0) (n := 25) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (4,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (4,0) = RadiusOne.xiStage6 := RadiusOne.xiStage6_exact
      rw [hr, initial4_2] at hp
      exact blockPatch_mem rows0_4_2 (List.getElem_mem (l := chunks0) (n := 26) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (4,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (4,0) = RadiusOne.xiStage6 := RadiusOne.xiStage6_exact
      rw [hr, initial4_3] at hp
      exact blockPatch_mem rows0_4_3 (List.getElem_mem (l := chunks0) (n := 27) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (4,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (4,0) = RadiusOne.xiStage6 := RadiusOne.xiStage6_exact
      rw [hr, initial4_4] at hp
      exact blockPatch_mem rows0_4_4 (List.getElem_mem (l := chunks0) (n := 28) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (4,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (4,0) = RadiusOne.xiStage6 := RadiusOne.xiStage6_exact
      rw [hr, initial4_5] at hp
      exact blockPatch_mem rows0_4_5 (List.getElem_mem (l := chunks0) (n := 29) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (5,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (5,0) = RadiusOne.piStage6 := RadiusOne.piStage6_exact
      rw [hr, initial5_0] at hp
      exact blockPatch_mem rows0_5_0 (List.getElem_mem (l := chunks0) (n := 30) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (5,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (5,0) = RadiusOne.piStage6 := RadiusOne.piStage6_exact
      rw [hr, initial5_1] at hp
      exact blockPatch_mem rows0_5_1 (List.getElem_mem (l := chunks0) (n := 31) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (5,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (5,0) = RadiusOne.piStage6 := RadiusOne.piStage6_exact
      rw [hr, initial5_2] at hp
      exact blockPatch_mem rows0_5_2 (List.getElem_mem (l := chunks0) (n := 32) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (5,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (5,0) = RadiusOne.piStage6 := RadiusOne.piStage6_exact
      rw [hr, initial5_3] at hp
      exact blockPatch_mem rows0_5_3 (List.getElem_mem (l := chunks0) (n := 33) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (5,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (5,0) = RadiusOne.piStage6 := RadiusOne.piStage6_exact
      rw [hr, initial5_4] at hp
      exact blockPatch_mem rows0_5_4 (List.getElem_mem (l := chunks0) (n := 34) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (5,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (5,0) = RadiusOne.piStage6 := RadiusOne.piStage6_exact
      rw [hr, initial5_5] at hp
      exact blockPatch_mem rows0_5_5 (List.getElem_mem (l := chunks0) (n := 35) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (6,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (6,0) = RadiusOne.sigmaStage6 := RadiusOne.sigmaStage6_exact
      rw [hr, initial6_0] at hp
      exact blockPatch_mem rows0_6_0 (List.getElem_mem (l := chunks0) (n := 36) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (6,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (6,0) = RadiusOne.sigmaStage6 := RadiusOne.sigmaStage6_exact
      rw [hr, initial6_1] at hp
      exact blockPatch_mem rows0_6_1 (List.getElem_mem (l := chunks0) (n := 37) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (6,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (6,0) = RadiusOne.sigmaStage6 := RadiusOne.sigmaStage6_exact
      rw [hr, initial6_2] at hp
      exact blockPatch_mem rows0_6_2 (List.getElem_mem (l := chunks0) (n := 38) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (6,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (6,0) = RadiusOne.sigmaStage6 := RadiusOne.sigmaStage6_exact
      rw [hr, initial6_3] at hp
      exact blockPatch_mem rows0_6_3 (List.getElem_mem (l := chunks0) (n := 39) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (6,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (6,0) = RadiusOne.sigmaStage6 := RadiusOne.sigmaStage6_exact
      rw [hr, initial6_4] at hp
      exact blockPatch_mem rows0_6_4 (List.getElem_mem (l := chunks0) (n := 40) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (6,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (6,0) = RadiusOne.sigmaStage6 := RadiusOne.sigmaStage6_exact
      rw [hr, initial6_5] at hp
      exact blockPatch_mem rows0_6_5 (List.getElem_mem (l := chunks0) (n := 41) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (7,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (7,0) = RadiusOne.phiStage6 := RadiusOne.phiStage6_exact
      rw [hr, initial7_0] at hp
      exact blockPatch_mem rows0_7_0 (List.getElem_mem (l := chunks0) (n := 42) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (7,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (7,0) = RadiusOne.phiStage6 := RadiusOne.phiStage6_exact
      rw [hr, initial7_1] at hp
      exact blockPatch_mem rows0_7_1 (List.getElem_mem (l := chunks0) (n := 43) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (7,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (7,0) = RadiusOne.phiStage6 := RadiusOne.phiStage6_exact
      rw [hr, initial7_2] at hp
      exact blockPatch_mem rows0_7_2 (List.getElem_mem (l := chunks0) (n := 44) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (7,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (7,0) = RadiusOne.phiStage6 := RadiusOne.phiStage6_exact
      rw [hr, initial7_3] at hp
      exact blockPatch_mem rows0_7_3 (List.getElem_mem (l := chunks0) (n := 45) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (7,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (7,0) = RadiusOne.phiStage6 := RadiusOne.phiStage6_exact
      rw [hr, initial7_4] at hp
      exact blockPatch_mem rows0_7_4 (List.getElem_mem (l := chunks0) (n := 46) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (7,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (7,0) = RadiusOne.phiStage6 := RadiusOne.phiStage6_exact
      rw [hr, initial7_5] at hp
      exact blockPatch_mem rows0_7_5 (List.getElem_mem (l := chunks0) (n := 47) (by decide)) p hp
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
    · intro p hp
      change p ∈ (RadiusOne.assignments (8,0)).map (rotatePatch 0 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (8,0) = RadiusOne.psiStage6 := RadiusOne.psiStage6_exact
      rw [hr, initial8_0] at hp
      exact blockPatch_mem rows0_8_0 (List.getElem_mem (l := chunks0) (n := 48) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (8,0)).map (rotatePatch 1 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (8,0) = RadiusOne.psiStage6 := RadiusOne.psiStage6_exact
      rw [hr, initial8_1] at hp
      exact blockPatch_mem rows0_8_1 (List.getElem_mem (l := chunks0) (n := 49) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (8,0)).map (rotatePatch 2 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (8,0) = RadiusOne.psiStage6 := RadiusOne.psiStage6_exact
      rw [hr, initial8_2] at hp
      exact blockPatch_mem rows0_8_2 (List.getElem_mem (l := chunks0) (n := 50) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (8,0)).map (rotatePatch 3 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (8,0) = RadiusOne.psiStage6 := RadiusOne.psiStage6_exact
      rw [hr, initial8_3] at hp
      exact blockPatch_mem rows0_8_3 (List.getElem_mem (l := chunks0) (n := 51) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (8,0)).map (rotatePatch 4 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (8,0) = RadiusOne.psiStage6 := RadiusOne.psiStage6_exact
      rw [hr, initial8_4] at hp
      exact blockPatch_mem rows0_8_4 (List.getElem_mem (l := chunks0) (n := 52) (by decide)) p hp
    · intro p hp
      change p ∈ (RadiusOne.assignments (8,0)).map (rotatePatch 5 RadiusOne.positions) at hp
      have hr : RadiusOne.assignments (8,0) = RadiusOne.psiStage6 := RadiusOne.psiStage6_exact
      rw [hr, initial8_5] at hp
      exact blockPatch_mem rows0_8_5 (List.getElem_mem (l := chunks0) (n := 53) (by decide)) p hp

/-- The concrete initial rows cover the complete rotation-normalized search. -/
theorem initial_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) :
    OccurrenceComplete f RadiusOne.positions ((rows0.map Verdict.window).map windowPatch) := by
  intro center
  have h := allTurnRadiusOne_occurrenceComplete f hf center
  obtain ⟨k,hk,hkpatch⟩ := List.mem_flatMap.mp h
  obtain ⟨t,ht,htpatch⟩ := List.mem_flatMap.mp hkpatch
  exact raw_rotated_mem_initial k t _ htpatch

/-- All real field windows lie in this particular kernel-certified family. -/
theorem certifiedFamily_occurrenceComplete (f : Position → State) (hf : GloballyLegal f) :
    OccurrenceComplete f RadiusOne.positions certifiedFamily :=
  rounds_occurrenceComplete f (initial_occurrenceComplete f hf)

theorem extract_mem_certifiedFamily (f : Position → State) (hf : GloballyLegal f)
    (center : Position) : extract f center RadiusOne.positions ∈ certifiedFamily :=
  certifiedFamily_occurrenceComplete f hf center

#print axioms certifiedFamily_occurrenceComplete
#print axioms extract_mem_certifiedFamily
end SpectreFinite.HexSearch.SignaturePruning
