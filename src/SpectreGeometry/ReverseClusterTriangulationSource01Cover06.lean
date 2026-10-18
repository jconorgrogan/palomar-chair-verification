module

public import SpectreGeometry.ReverseClusterTriangulationSource01Cover05

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex1Node139 : CoverTree := .split (-591631,-199094,743674995000) sourceHex1Node140 sourceHex1Node141
theorem sourceHex1Node139_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(863320,1048049,-369322695000),(819262,466875,-849140775000),(-60647,-155212,47688410419)] (familyFacets sourceFamily1) sourceHex1Node139 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node140_checked,sourceHex1Node141_checked⟩

def sourceHex1Node129 : CoverTree := .split (60647,155212,-47688410419) sourceHex1Node130 sourceHex1Node139
theorem sourceHex1Node129_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(863320,1048049,-369322695000),(819262,466875,-849140775000)] (familyFacets sourceFamily1) sourceHex1Node129 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node130_checked,sourceHex1Node139_checked⟩

def sourceHex1Node127 : CoverTree := .split (-819262,-466875,849140775000) sourceHex1Node128 sourceHex1Node129
theorem sourceHex1Node127_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(863320,1048049,-369322695000)] (familyFacets sourceFamily1) sourceHex1Node127 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node128_checked,sourceHex1Node129_checked⟩

def sourceHex1Node152 : CoverTree := .split (1020398,854869,-208566540000) (.split (-915398,-959869,140869575000) (.leaf 157 [⟨1,[(2,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(12,1)]⟩]) (.split (66677,42037,-16940770413) (.leaf 158 [⟨1,[(10,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(13,1)]⟩]) (.leaf 159 [⟨1215266647,[(10,520114451),(14,6435000)]⟩,⟨5625801,[(12,564131),(13,490780)]⟩,⟨1,[(14,1)]⟩]))) (.split (-19233,-32699,-42861275) (.leaf 156 [⟨1,[(11,1)]⟩,⟨1,[(12,1)]⟩,⟨1,[(13,1)]⟩]) (.split (-182178,-169459,33203240000) (.split (1543437,1361636,-177640960000) (.leaf 155 [⟨1,[(15,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(14,1)]⟩]) (.leaf 154 [⟨1,[(15,1)]⟩,⟨1,[(7,1)]⟩,⟨12857075000,[(11,43208087453),(15,34012727547)]⟩])) (.leaf 159 [⟨2453748353,[(10,1041865549),(12,2145000),(6,90769726392345000)]⟩,⟨1,[(14,1)]⟩,⟨2453900000,[(12,520114451),(14,2015089941)]⟩])))
theorem sourceHex1Node152_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(-863320,-1048049,369322695000),(-159347,-155140,38321955000),(1116563,1018364,-123730740000)] (familyFacets sourceFamily1) sourceHex1Node152 = true := by decide

def sourceHex1Node153 : CoverTree := .split (392927,419294,33222420000) (.split (330709,179776,-54124669812) (.leaf 153 [⟨1,[(11,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(12,1)]⟩]) (.leaf 154 [⟨34012727547,[(11,43208087453),(13,12857075000)]⟩,⟨1,[(7,1)]⟩,⟨1,[(13,1)]⟩])) (.split (44187,100208,70586460000) (.split (653293,537964,-20232030972) (.leaf 152 [⟨1,[(13,1)]⟩,⟨1,[(12,1)]⟩,⟨1,[(14,1)]⟩]) (.leaf 151 [⟨10423542419,[(13,10423455081),(14,2526912500)]⟩,⟨1,[(14,1)]⟩,⟨2573654,[(7,2436663),(12,2549683)]⟩])) (.split (-22805,76953,125695080000) (.split (178171,146718,-5517386094) (.leaf 66 [⟨1,[(13,1)]⟩,⟨1,[(15,1)]⟩,⟨1,[(14,1)]⟩]) (.split (114187,30208,-75490590000) (.leaf 67 [⟨1,[(16,1)]⟩,⟨5685565651,[(14,5685549349),(15,1895180000)]⟩,⟨1,[(15,1)]⟩]) (.leaf 151 [⟨1,[(16,1)]⟩,⟨2526912500,[(13,10423455081),(16,10423542419)]⟩,⟨2573654,[(7,2436663),(12,2549683)]⟩]))) (.split (29695,24453,-919380000) (.leaf 65 [⟨1,[(2,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(15,1)]⟩]) (.split (82195,-28047,-127533840000) (.leaf 64 [⟨1,[(2,1)]⟩,⟨1,[(15,1)]⟩,⟨1,[(16,1)]⟩]) (.leaf 67 [⟨89686528899,[(7,9475925651),(14,59697504838),(6,1012417354600019270000)]⟩,⟨1,[(16,1)]⟩,⟨947590000,[(15,5685549349),(16,8151)]⟩])))))
theorem sourceHex1Node153_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(-863320,-1048049,369322695000),(-159347,-155140,38321955000),(-1116563,-1018364,123730740000)] (familyFacets sourceFamily1) sourceHex1Node153 = true := by decide

def sourceHex1Node151 : CoverTree := .split (1116563,1018364,-123730740000) sourceHex1Node152 sourceHex1Node153
theorem sourceHex1Node151_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(-863320,-1048049,369322695000),(-159347,-155140,38321955000)] (familyFacets sourceFamily1) sourceHex1Node151 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node152_checked,sourceHex1Node153_checked⟩

def sourceHex1Node155 : CoverTree := .split (-886318,-1004051,248633910000) (.split (991318,899051,-314745165000) (.leaf 162 [⟨1,[(2,1)]⟩,⟨1,[(12,1)]⟩,⟨1,[(13,1)]⟩]) (.split (-124111,-186929,27232483761) (.leaf 161 [⟨1,[(10,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(14,1)]⟩]) (.split (68551,66620,-16490880000) (.leaf 160 [⟨1,[(15,1)]⟩,⟨1,[(14,1)]⟩,⟨630123,[(12,528095),(13,521782)]⟩]) (.leaf 159 [⟨1,[(15,1)]⟩,⟨3212734311,[(10,4674491588),(12,180044521),(6,27697294668539790000)]⟩,⟨6435000,[(10,520114451),(15,1215266647)]⟩])))) (.split (189841,130224,-67140899341) (.leaf 163 [⟨1,[(11,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(12,1)]⟩]) (.split (1563682,1585949,-469004760000) (.split (-1373841,-1455725,499313080000) (.leaf 164 [⟨1,[(15,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(13,1)]⟩]) (.leaf 165 [⟨1,[(15,1)]⟩,⟨8278060000,[(11,105730190791),(15,83470499209)]⟩,⟨12362526647,[(9,17101218353),(13,18718215000),(6,416654534046802950000)]⟩])) (.leaf 160 [⟨25848629414,[(8,1086910549),(12,1866787545),(6,57347205005355678142)]⟩,⟨2608910000,[(12,1515298353),(14,651821647)]⟩,⟨1,[(14,1)]⟩])))
theorem sourceHex1Node155_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(-863320,-1048049,369322695000),(159347,155140,-38321955000),(-1076159,-1134275,390964980000)] (familyFacets sourceFamily1) sourceHex1Node155 = true := by decide

def sourceHex1Node156 : CoverTree := .split (968320,943049,-433228950000) (.leaf 167 [⟨1,[(2,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(12,1)]⟩]) (.split (-107839,-191226,41206529209) (.leaf 166 [⟨1,[(11,1)]⟩,⟨1,[(12,1)]⟩,⟨1,[(13,1)]⟩]) (.leaf 165 [⟨83470499209,[(11,105730190791),(13,8278060000)]⟩,⟨1,[(13,1)]⟩,⟨1911369,[(9,1880750),(12,1247881)]⟩]))
theorem sourceHex1Node156_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(-863320,-1048049,369322695000),(159347,155140,-38321955000),(1076159,1134275,-390964980000)] (familyFacets sourceFamily1) sourceHex1Node156 = true := by decide

def sourceHex1Node154 : CoverTree := .split (-1076159,-1134275,390964980000) sourceHex1Node155 sourceHex1Node156
theorem sourceHex1Node154_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(-863320,-1048049,369322695000),(159347,155140,-38321955000)] (familyFacets sourceFamily1) sourceHex1Node154 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node155_checked,sourceHex1Node156_checked⟩

def sourceHex1Node150 : CoverTree := .split (-159347,-155140,38321955000) sourceHex1Node151 sourceHex1Node154
theorem sourceHex1Node150_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758),(-863320,-1048049,369322695000)] (familyFacets sourceFamily1) sourceHex1Node150 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node151_checked,sourceHex1Node154_checked⟩

def sourceHex1Node126 : CoverTree := .split (863320,1048049,-369322695000) sourceHex1Node127 sourceHex1Node150
theorem sourceHex1Node126_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000),(107996,-140135,-17910548758)] (familyFacets sourceFamily1) sourceHex1Node126 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node127_checked,sourceHex1Node150_checked⟩

def sourceHex1Node70 : CoverTree := .split (-107996,140135,17910548758) sourceHex1Node71 sourceHex1Node126
theorem sourceHex1Node70_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1),(937073,770706,-29466640000)] (familyFacets sourceFamily1) sourceHex1Node70 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node71_checked,sourceHex1Node126_checked⟩

def sourceHex1Node0 : CoverTree := .split (-937073,-770706,29466640000) sourceHex1Node1 sourceHex1Node70
theorem sourceHex1Node0_checked : checkTree [(2,1,2520000),(1,2,2520000),(-1,1,2520000),(-2,-1,2520000),(-1,-2,2520000),(1,-1,2520000),(0,0,1)] (familyFacets sourceFamily1) sourceHex1Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex1Node1_checked,sourceHex1Node70_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
