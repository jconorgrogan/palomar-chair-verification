module

public import SpectreClusters.StageDReductionGeometryData
public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionCertificateData

@[expose] public section


namespace SpectreClusters.StageD.Reduction

def tables : Tables where
  kept := kept
  geometryCount := geometryCount
  geometryAt := geometryAt
  hitCount := hitCount
  hitAt := hitAt
  certificate := certificateAt

end SpectreClusters.StageD.Reduction
