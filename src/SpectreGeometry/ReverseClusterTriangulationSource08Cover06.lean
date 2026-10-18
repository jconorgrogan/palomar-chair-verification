module

public import SpectreGeometry.ReverseClusterTriangulationSource08Cover05

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex8Node148 : CoverTree := .split (-78062,21215,-40015598722) sourceHex8Node149 sourceHex8Node150
theorem sourceHex8Node148_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000),(-17323,78641,1706455782),(-422851,-42301,-120758232000),(-38611,2690,-15336800000),(-3623,-27782,4656948103),(-182825,16711,-81111440000)] (familyFacets sourceFamily8) sourceHex8Node148 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex8Node149_checked,sourceHex8Node150_checked⟩

def sourceHex8Node151 : CoverTree := .split (-36142,-1681,-14524040000) (.split (68426,-14957,30705720000) (.leaf 109 [⟨1,[(0,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(14,1)]⟩]) (.split (-45973,-13203,-16517906722) (.leaf 108 [⟨1,[(12,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(15,1)]⟩]) (.leaf 107 [⟨1229387417,[(11,4411434722),(15,6369171897)]⟩,⟨1,[(15,1)]⟩,⟨163900,[(13,352251),(14,138683)]⟩]))) (.split (-253435,4859,-101179640000) (.split (36583,-14945,17645229278) (.leaf 110 [⟨1,[(14,1)]⟩,⟨1,[(15,1)]⟩,⟨1,[(13,1)]⟩]) (.split (135574,-9043,57196272000) (.split (-234565,3141,-93356648000) (.leaf 111 [⟨1,[(17,1)]⟩,⟨1,[(16,1)]⟩,⟨1,[(15,1)]⟩]) (.leaf 113 [⟨1,[(17,1)]⟩,⟨42964000,[(14,466738699),(17,494129301)]⟩,⟨135304584,[(10,76986041),(11,15684875),(6,22618613548845875)]⟩])) (.leaf 107 [⟨332668927,[(11,503122071),(13,2123057299),(6,849015312195902687)]⟩,⟨554732000,[(13,2205717361),(16,399902213)]⟩,⟨1,[(16,1)]⟩]))) (.split (55453,-16661,25467794408) (.leaf 114 [⟨1,[(14,1)]⟩,⟨1,[(10,1)]⟩,⟨1,[(15,1)]⟩]) (.leaf 113 [⟨494129301,[(14,466738699),(15,42964000)]⟩,⟨1,[(15,1)]⟩,⟨135304584,[(10,76986041),(11,15684875),(6,22618613548845875)]⟩])))
theorem sourceHex8Node151_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000),(-17323,78641,1706455782),(-422851,-42301,-120758232000),(-38611,2690,-15336800000),(-3623,-27782,4656948103),(182825,-16711,81111440000)] (familyFacets sourceFamily8) sourceHex8Node151 = true := by decide

def sourceHex8Node147 : CoverTree := .split (-182825,16711,-81111440000) sourceHex8Node148 sourceHex8Node151
theorem sourceHex8Node147_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000),(-17323,78641,1706455782),(-422851,-42301,-120758232000),(-38611,2690,-15336800000),(-3623,-27782,4656948103)] (familyFacets sourceFamily8) sourceHex8Node147 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex8Node148_checked,sourceHex8Node151_checked⟩

def sourceHex8Node137 : CoverTree := .split (3623,27782,-4656948103) sourceHex8Node138 sourceHex8Node147
theorem sourceHex8Node137_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000),(-17323,78641,1706455782),(-422851,-42301,-120758232000),(-38611,2690,-15336800000)] (familyFacets sourceFamily8) sourceHex8Node137 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex8Node138_checked,sourceHex8Node147_checked⟩

def sourceHex8Node131 : CoverTree := .split (38611,-2690,15336800000) sourceHex8Node132 sourceHex8Node137
theorem sourceHex8Node131_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000),(-17323,78641,1706455782),(-422851,-42301,-120758232000)] (familyFacets sourceFamily8) sourceHex8Node131 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex8Node132_checked,sourceHex8Node137_checked⟩

def sourceHex8Node152 : CoverTree := .split (-549647,-227285,-70129752000) (.split (-94495,-24774,-19264224000) (.split (144119,106343,33697978074) (.leaf 127 [⟨1,[(9,1)]⟩,⟨1,[(12,1)]⟩,⟨1,[(11,1)]⟩]) (.leaf 128 [⟨19435433037,[(9,1531304633),(12,1046104000)]⟩,⟨7860341297,[(8,7964488000),(11,4239192109)]⟩,⟨1,[(12,1)]⟩])) (.leaf 132 [⟨1,[(10,1)]⟩,⟨1,[(11,1)]⟩,⟨1,[(8,1)]⟩])) (.split (168155,88624,11833584000) (.split (-584262,-355931,-16922808000) (.leaf 143 [⟨1,[(12,1)]⟩,⟨1,[(11,1)]⟩,⟨4767971416,[(7,2307900991),(8,3155469067),(6,5128768507807452094)]⟩]) (.leaf 144 [⟨1,[(12,1)]⟩,⟨52112740655,[(8,18186204268),(12,5102916337),(6,90034311856509781964)]⟩,⟨1,[(7,1)]⟩])) (.leaf 138 [⟨1,[(10,1)]⟩,⟨23581023891,[(8,20985613106),(10,5937197923)]⟩,⟨1,[(11,1)]⟩]))
theorem sourceHex8Node152_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000),(-17323,78641,1706455782),(422851,42301,120758232000)] (familyFacets sourceFamily8) sourceHex8Node152 = true := by decide

def sourceHex8Node130 : CoverTree := .split (-422851,-42301,-120758232000) sourceHex8Node131 sourceHex8Node152
theorem sourceHex8Node130_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000),(-17323,78641,1706455782)] (familyFacets sourceFamily8) sourceHex8Node130 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex8Node131_checked,sourceHex8Node152_checked⟩

def sourceHex8Node92 : CoverTree := .split (17323,-78641,-1706455782) sourceHex8Node93 sourceHex8Node130
theorem sourceHex8Node92_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1),(-158857,-104557,-679224000)] (familyFacets sourceFamily8) sourceHex8Node92 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex8Node93_checked,sourceHex8Node130_checked⟩

def sourceHex8Node0 : CoverTree := .split (158857,104557,679224000) sourceHex8Node1 sourceHex8Node92
theorem sourceHex8Node0_checked : checkTree [(2,1,840000),(1,2,840000),(-1,1,840000),(-2,-1,840000),(-1,-2,840000),(1,-1,840000),(0,0,1)] (familyFacets sourceFamily8) sourceHex8Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex8Node1_checked,sourceHex8Node92_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
