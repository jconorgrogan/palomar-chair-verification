module

public import SpectreClusters.ReverseClusterDeltaBoundsData

@[expose] public section


namespace SpectreClusters.ReverseExistence
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem delta_bound_certificate_1 : DeltaBoundCertificate 1 := by
  unfold DeltaBoundCertificate
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))
end SpectreClusters.ReverseExistence
