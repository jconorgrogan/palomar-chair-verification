module

public import SpectreClusters.ReverseClusterCocycleData

@[expose] public section


namespace SpectreClusters.ReverseExistence
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem pair_certificate_4 : PairCertificate 4 := by
  unfold PairCertificate
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))
end SpectreClusters.ReverseExistence
