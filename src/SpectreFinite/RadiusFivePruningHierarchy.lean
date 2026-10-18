module

public import SpectreFinite.NativeCoarsening
public import SpectreFinite.RadiusFiveParentCoverage

@[expose] public section


namespace SpectreFinite.HexSearch.RadiusFivePruning

/-- The checked radius-five pruning and parent-family inclusion discharge the
exact universal occurrence premise used by the repeatable native hierarchy. -/
theorem certifiedParentOccurrenceTheorem : NativeHierarchy.ParentOccurrenceTheorem :=
  RadiusFiveParentBinding.parentFamily_occurrenceComplete

#print axioms certifiedParentOccurrenceTheorem

end SpectreFinite.HexSearch.RadiusFivePruning
