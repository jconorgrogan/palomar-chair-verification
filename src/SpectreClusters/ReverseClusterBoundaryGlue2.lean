module

public import SpectreClusters.ReverseClusterBoundaryGlueData

@[expose] public section

namespace SpectreClusters.ReverseExistence
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem boundary_glue_certificate_2 : BoundaryGlueCertificate 2 := by
  unfold BoundaryGlueCertificate
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))
end SpectreClusters.ReverseExistence
