module

public import SpectreClusters.StageDReductionGeometryData0
public import SpectreClusters.StageDReductionGeometryData1

@[expose] public section


namespace SpectreClusters.StageD.Reduction

def geometryChunks : Array (Array BlockGeometry) := #[geometryData0,geometryData1]
def geometryAt (i : Nat) : BlockGeometry :=
  (((geometryChunks[i / 512]?).getD #[])[i % 512]?).getD ⟨.t7h,0,0,0,⟨(0,0),0⟩⟩
def geometryCount : Nat := 933
end SpectreClusters.StageD.Reduction
