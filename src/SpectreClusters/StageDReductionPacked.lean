module

public import SpectreClusters.StageDReductionModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

structure PackedCertificate where
  neighbor : Nat
  mask : Nat
  refs : Nat
  hit : Nat

def unpackCertificate (p : PackedCertificate) : RejectCertificate :=
  ⟨p.neighbor,p.mask,(List.range 41).toArray.map (fun m => (p.refs >>> (10*m)) % 1024),p.hit⟩

end SpectreClusters.StageD.Reduction
