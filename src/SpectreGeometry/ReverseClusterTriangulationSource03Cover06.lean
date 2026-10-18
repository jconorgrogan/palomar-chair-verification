module

public import SpectreGeometry.ReverseClusterTriangulationSource03Cover05

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex3Node137 : CoverTree := .split (1616389,-95494,8581061412000) sourceHex3Node138 sourceHex3Node143
theorem sourceHex3Node137_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000),(-4234063,-1222473,-7879486384000),(-1636269,-938119,-4502854269190),(-679851,1523489,-1993048288000),(-1691447,572379,-8688036280000)] (familyFacets sourceFamily3) sourceHex3Node137 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex3Node138_checked,sourceHex3Node143_checked⟩

def sourceHex3Node151 : CoverTree := .split (1808628,-509993,8355861360000) (.split (2424628,-201993,10330568248000) (.split (-108508,-383377,247417737200) (.leaf 125 [⟨1,[(12,1)]⟩,⟨1,[(15,1)]⟩,⟨1,[(14,1)]⟩]) (.leaf 126 [⟨313061896281,[(9,21791492800),(12,365613578119)]⟩,⟨1414307,[(13,404698),(14,1876995)]⟩,⟨1,[(15,1)]⟩])) (.leaf 124 [⟨1,[(0,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(13,1)]⟩])) (.split (2307447,-264379,10660405140000) (.split (-2415019,424593,-11157387780000) (.split (53786,-80107,419114087935) (.leaf 120 [⟨1,[(15,1)]⟩,⟨1,[(16,1)]⟩,⟨1,[(14,1)]⟩]) (.split (-3128981,499407,-14333426184000) (.leaf 121 [⟨1,[(17,1)]⟩,⟨2836205,[(11,2163519),(14,2392276)]⟩,⟨1,[(16,1)]⟩]) (.leaf 122 [⟨1,[(17,1)]⟩,⟨122466036000,[(15,570050887537),(17,463711996463)]⟩,⟨181534269317,[(9,276961664302),(16,4181650265151),(6,76788838491548780268565)]⟩]))) (.split (-606391,-85400,-2337814423537) (.leaf 123 [⟨1,[(15,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(16,1)]⟩]) (.split (-3735372,414007,-16101189720000) (.leaf 122 [⟨463711996463,[(15,570050887537),(16,122466036000)]⟩,⟨1,[(16,1)]⟩,⟨1,[(17,1)]⟩]) (.leaf 126 [⟨313061896281,[(9,21791492800),(12,365613578119)]⟩,⟨1,[(17,1)]⟩,⟨2890572300,[(13,3692446957),(17,1871811743)]⟩])))) (.leaf 119 [⟨1,[(0,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(11,1)]⟩]))
theorem sourceHex3Node151_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000),(-4234063,-1222473,-7879486384000),(-1636269,-938119,-4502854269190),(-679851,1523489,-1993048288000),(1691447,-572379,8688036280000),(-231612,58537,-962652152000)] (familyFacets sourceFamily3) sourceHex3Node151 = true := by decide

def sourceHex3Node152 : CoverTree := .leaf 128 [⟨1,[(12,1)]⟩,⟨1,[(10,1)]⟩,⟨1,[(9,1)]⟩]
theorem sourceHex3Node152_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000),(-4234063,-1222473,-7879486384000),(-1636269,-938119,-4502854269190),(-679851,1523489,-1993048288000),(1691447,-572379,8688036280000),(231612,-58537,962652152000)] (familyFacets sourceFamily3) sourceHex3Node152 = true := by decide

def sourceHex3Node150 : CoverTree := .split (-231612,58537,-962652152000) sourceHex3Node151 sourceHex3Node152
theorem sourceHex3Node150_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000),(-4234063,-1222473,-7879486384000),(-1636269,-938119,-4502854269190),(-679851,1523489,-1993048288000),(1691447,-572379,8688036280000)] (familyFacets sourceFamily3) sourceHex3Node150 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex3Node151_checked,sourceHex3Node152_checked⟩

def sourceHex3Node136 : CoverTree := .split (-1691447,572379,-8688036280000) sourceHex3Node137 sourceHex3Node150
theorem sourceHex3Node136_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000),(-4234063,-1222473,-7879486384000),(-1636269,-938119,-4502854269190),(-679851,1523489,-1993048288000)] (familyFacets sourceFamily3) sourceHex3Node136 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex3Node137_checked,sourceHex3Node150_checked⟩

def sourceHex3Node114 : CoverTree := .split (679851,-1523489,1993048288000) sourceHex3Node115 sourceHex3Node136
theorem sourceHex3Node114_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000),(-4234063,-1222473,-7879486384000),(-1636269,-938119,-4502854269190)] (familyFacets sourceFamily3) sourceHex3Node114 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex3Node115_checked,sourceHex3Node136_checked⟩

def sourceHex3Node102 : CoverTree := .split (1636269,938119,4502854269190) sourceHex3Node103 sourceHex3Node114
theorem sourceHex3Node102_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000),(-4234063,-1222473,-7879486384000)] (familyFacets sourceFamily3) sourceHex3Node102 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex3Node103_checked,sourceHex3Node114_checked⟩

def sourceHex3Node86 : CoverTree := .split (4234063,1222473,7879486384000) sourceHex3Node87 sourceHex3Node102
theorem sourceHex3Node86_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1),(-3487969,-2287529,-209472648000)] (familyFacets sourceFamily3) sourceHex3Node86 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex3Node87_checked,sourceHex3Node102_checked⟩

def sourceHex3Node0 : CoverTree := .split (3487969,2287529,209472648000) sourceHex3Node1 sourceHex3Node86
theorem sourceHex3Node0_checked : checkTree [(2,1,9240000),(1,2,9240000),(-1,1,9240000),(-2,-1,9240000),(-1,-2,9240000),(1,-1,9240000),(0,0,1)] (familyFacets sourceFamily3) sourceHex3Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex3Node1_checked,sourceHex3Node86_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
