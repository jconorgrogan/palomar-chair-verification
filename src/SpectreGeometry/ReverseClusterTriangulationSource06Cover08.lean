module

public import SpectreGeometry.ReverseClusterTriangulationSource06Cover07

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex6Node110 : CoverTree := .split (-6717774,-859937,-54712914480000) sourceHex6Node111 sourceHex6Node192
theorem sourceHex6Node110_checked : checkTree [(2,1,25200000),(1,2,25200000),(-1,1,25200000),(-2,-1,25200000),(-1,-2,25200000),(1,-1,25200000),(0,0,1),(-19021259,-12475417,-3105985680000),(-11943098,-3531827,-61598690160000)] (familyFacets sourceFamily6) sourceHex6Node110 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex6Node111_checked,sourceHex6Node192_checked⟩

def sourceHex6Node94 : CoverTree := .split (11943098,3531827,61598690160000) sourceHex6Node95 sourceHex6Node110
theorem sourceHex6Node94_checked : checkTree [(2,1,25200000),(1,2,25200000),(-1,1,25200000),(-2,-1,25200000),(-1,-2,25200000),(1,-1,25200000),(0,0,1),(-19021259,-12475417,-3105985680000)] (familyFacets sourceFamily6) sourceHex6Node94 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex6Node95_checked,sourceHex6Node110_checked⟩

def sourceHex6Node0 : CoverTree := .split (19021259,12475417,3105985680000) sourceHex6Node1 sourceHex6Node94
theorem sourceHex6Node0_checked : checkTree [(2,1,25200000),(1,2,25200000),(-1,1,25200000),(-2,-1,25200000),(-1,-2,25200000),(1,-1,25200000),(0,0,1)] (familyFacets sourceFamily6) sourceHex6Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex6Node1_checked,sourceHex6Node94_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
