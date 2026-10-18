module

public import SpectreGeometry.ReverseClusterTriangulationSource05Cover05

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex5Node127 : CoverTree := .split (3397771,-236722,14846034720000) sourceHex5Node128 sourceHex5Node133
theorem sourceHex5Node127_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3494855,-2300253,-164381448000),(-63515,288351,68832078862),(-4651364,-465313,-14611746072000)] (familyFacets sourceFamily5) sourceHex5Node127 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex5Node128_checked,sourceHex5Node133_checked⟩

def sourceHex5Node148 : CoverTree := .split (-3023061,-1250068,-4242856464000) (.split (-6236667,-1635083,-13985821080000) (.split (1585303,1169770,4077438979441) (.leaf 127 [⟨1,[(9,1)]⟩,⟨1,[(12,1)]⟩,⟨1,[(11,1)]⟩]) (.leaf 128 [⟨4703363971441,[(9,4076321580559),(12,2784743808000)]⟩,⟨531421646903,[(8,4076321580559),(12,341967321138)]⟩,⟨1,[(12,1)]⟩])) (.leaf 132 [⟨1,[(10,1)]⟩,⟨1,[(11,1)]⟩,⟨1,[(8,1)]⟩])) (.split (7398821,3899460,5727436176000) (.split (-6426883,-3915241,-2047663464000) (.leaf 143 [⟨1,[(12,1)]⟩,⟨1,[(11,1)]⟩,⟨1153845503400,[(7,279256964023),(8,2290855607069),(6,150167973038890519443922)]⟩]) (.leaf 144 [⟨1,[(12,1)]⟩,⟨131367167003,[(8,137532164543),(12,12863520922),(6,27461488660597811091998)]⟩,⟨1,[(7,1)]⟩])) (.leaf 138 [⟨1,[(10,1)]⟩,⟨951100731431,[(8,2539276077232),(10,478930173209)]⟩,⟨1,[(11,1)]⟩]))
theorem sourceHex5Node148_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3494855,-2300253,-164381448000),(-63515,288351,68832078862),(4651364,465313,14611746072000)] (familyFacets sourceFamily5) sourceHex5Node148 = true := by decide

def sourceHex5Node126 : CoverTree := .split (-4651364,-465313,-14611746072000) sourceHex5Node127 sourceHex5Node148
theorem sourceHex5Node126_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3494855,-2300253,-164381448000),(-63515,288351,68832078862)] (familyFacets sourceFamily5) sourceHex5Node126 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex5Node127_checked,sourceHex5Node148_checked⟩

def sourceHex5Node88 : CoverTree := .split (63515,-288351,-68832078862) sourceHex5Node89 sourceHex5Node126
theorem sourceHex5Node88_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3494855,-2300253,-164381448000)] (familyFacets sourceFamily5) sourceHex5Node88 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex5Node89_checked,sourceHex5Node126_checked⟩

def sourceHex5Node0 : CoverTree := .split (3494855,2300253,164381448000) sourceHex5Node1 sourceHex5Node88
theorem sourceHex5Node0_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1)] (familyFacets sourceFamily5) sourceHex5Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex5Node1_checked,sourceHex5Node88_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
