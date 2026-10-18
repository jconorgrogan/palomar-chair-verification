module

public import SpectreClusters.StageAPhaseAPart0
public import SpectreClusters.StageAPhaseAPart1
public import SpectreClusters.StageAPhaseAPart2
public import SpectreClusters.StageAPhaseAPart3
public import SpectreClusters.StageAPhaseAPart4
public import SpectreClusters.StageAPhaseAPart5
public import SpectreClusters.StageAPhaseBPart0
public import SpectreClusters.StageAPhaseBPart1
public import SpectreClusters.StageAPhaseBPart2
public import SpectreClusters.StageAPhaseBPart3
public import SpectreClusters.StageAPhaseBPart4
public import SpectreClusters.StageAPhaseBPart5

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
theorem phaseA_all : (keptIds 2 .hat).all (phaseCompatibleB .hat) = true := by
  simp only [keptIds,List.all_cons,List.all_nil,phaseA_0, phaseA_2, phaseA_6, phaseA_8, phaseA_13, phaseA_15, phaseA_16, phaseA_17, phaseA_21, phaseA_22, phaseA_23, phaseA_24, phaseA_27, phaseA_28, phaseA_31, phaseA_32, phaseA_35, phaseA_38, phaseA_39, phaseA_79, phaseA_81, phaseA_89, phaseA_210] <;> rfl
theorem phaseB_all : (keptIds 2 .turtle).all (phaseCompatibleB .turtle) = true := by
  simp only [keptIds,List.all_cons,List.all_nil,phaseB_0, phaseB_163, phaseB_171, phaseB_179, phaseB_201, phaseB_203, phaseB_205, phaseB_212, phaseB_214, phaseB_215, phaseB_219, phaseB_221, phaseB_222, phaseB_223, phaseB_226, phaseB_227, phaseB_229, phaseB_231, phaseB_240, phaseB_242, phaseB_246, phaseB_248, phaseB_250] <;> rfl
theorem final_phase_checked (kind : HTKind) (i : Nat) (hi : i ∈ keptIds 2 kind) :
    phaseCompatibleB kind i = true := by
  cases kind
  · exact List.all_eq_true.mp phaseA_all i hi
  · exact List.all_eq_true.mp phaseB_all i hi
end SpectreClusters.StageA
