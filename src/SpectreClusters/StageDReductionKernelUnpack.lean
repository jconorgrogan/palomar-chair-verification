module

public import SpectreClusters.StageDReductionData

@[expose] public section


/-! Proof-preserving structural decoder for kernel certificate reduction. -/
namespace SpectreClusters.StageD.Reduction

def unpackStructural (p : PackedCertificate) : RejectCertificate :=
  ⟨p.neighbor,p.mask,((List.range 41).map (fun m => (p.refs / 2^(10*m)) % 1024)).toArray,p.hit⟩

theorem unpackStructural_eq (p : PackedCertificate) :
    unpackStructural p = unpackCertificate p := by
  simp only [unpackStructural,unpackCertificate,List.map_toArray,Nat.shiftRight_eq_div_pow]

def kernelCertificateAt (s : Nat) (k : ClusterKind) (i : Nat) : RejectCertificate :=
  unpackStructural (packedAt (match s,k with
    | 0,.t7h => (initialCertificatet7h[i]?).getD 0
    | 0,.t8h => (initialCertificatet8h[i]?).getD 0
    | 1,.t7h => if i = 127 then 1875 else if i = 134 then 1876 else if i = 136 then 1877 else if i = 143 then 1878 else 0
    | 1,.t8h => if i = 1269 then 1879 else if i = 1277 then 1880 else if i = 1325 then 1881 else if i = 1331 then 1882 else if i = 1629 then 1883 else if i = 1653 then 1884 else if i = 1717 then 1885 else if i = 1733 then 1886 else if i = 1749 then 1887 else if i = 1757 then 1888 else 0
    | 2,.t8h => if i = 1289 then 1889 else 0
    | _,_ => 0))

theorem kernelCertificateAt_eq : kernelCertificateAt = certificateAt := by
  funext s k i
  unfold kernelCertificateAt certificateAt
  exact unpackStructural_eq _

def kernelTables : Tables where
  kept := kept
  geometryCount := geometryCount
  geometryAt := geometryAt
  hitCount := hitCount
  hitAt := hitAt
  certificate := kernelCertificateAt

theorem kernelTables_eq : kernelTables = tables := by
  unfold kernelTables tables
  rw [kernelCertificateAt_eq]

end SpectreClusters.StageD.Reduction
