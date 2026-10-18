module

public import SpectreGeometry.ReverseClusterTriangulationSource02Cover06

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex2Node120 : CoverTree := .split (29242,16729,2876918862) sourceHex2Node121 sourceHex2Node132
theorem sourceHex2Node120_checked : checkTree [(2,1,330000),(1,2,330000),(-1,1,330000),(-2,-1,330000),(-1,-2,330000),(1,-1,330000),(0,0,1),(-228439,-151514,-154176000),(-3429,-1000,-229438000)] (familyFacets sourceFamily2) sourceHex2Node120 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex2Node121_checked,sourceHex2Node132_checked⟩

def sourceHex2Node100 : CoverTree := .split (3429,1000,229438000) sourceHex2Node101 sourceHex2Node120
theorem sourceHex2Node100_checked : checkTree [(2,1,330000),(1,2,330000),(-1,1,330000),(-2,-1,330000),(-1,-2,330000),(1,-1,330000),(0,0,1),(-228439,-151514,-154176000)] (familyFacets sourceFamily2) sourceHex2Node100 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex2Node101_checked,sourceHex2Node120_checked⟩

def sourceHex2Node0 : CoverTree := .split (228439,151514,154176000) sourceHex2Node1 sourceHex2Node100
theorem sourceHex2Node0_checked : checkTree [(2,1,330000),(1,2,330000),(-1,1,330000),(-2,-1,330000),(-1,-2,330000),(1,-1,330000),(0,0,1)] (familyFacets sourceFamily2) sourceHex2Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex2Node1_checked,sourceHex2Node100_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
