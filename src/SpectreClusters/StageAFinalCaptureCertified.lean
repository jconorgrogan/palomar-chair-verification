module

public import SpectreClusters.StageAComplete
public import SpectreClusters.StageAActualSupport

@[expose] public section


namespace SpectreClusters.StageA

/-- The checked discrete Stage A endpoint in the exact downstream interface. -/
theorem finalCaptures_certified : FinalCaptures := captures_two

end SpectreClusters.StageA
