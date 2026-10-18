module

public import SpectreGeometry.ReverseClusterTriangulationSource04Cover06

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex4Node148 : CoverTree := .split (-1550608,-154951,-4871998824000) sourceHex4Node149 sourceHex4Node170
theorem sourceHex4Node148_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-6399893,-4249060,-97215888000),(-45688,214315,54583669070)] (familyFacets sourceFamily4) sourceHex4Node148 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex4Node149_checked,sourceHex4Node170_checked⟩

def sourceHex4Node102 : CoverTree := .split (45688,-214315,-54583669070) sourceHex4Node103 sourceHex4Node148
theorem sourceHex4Node102_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-6399893,-4249060,-97215888000)] (familyFacets sourceFamily4) sourceHex4Node102 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex4Node103_checked,sourceHex4Node148_checked⟩

def sourceHex4Node0 : CoverTree := .split (6399893,4249060,97215888000) sourceHex4Node1 sourceHex4Node102
theorem sourceHex4Node0_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1)] (familyFacets sourceFamily4) sourceHex4Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex4Node1_checked,sourceHex4Node102_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
