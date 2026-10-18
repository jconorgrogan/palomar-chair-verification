module

public import SpectreGeometry.ReverseClusterTriangulationSource07Cover05

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sourceHex7Node152 : CoverTree := .split (-8498,793,-671224000) (.split (498,-4793,231560000) (.leaf 92 [⟨1,[(0,1)]⟩,⟨1,[(15,1)]⟩,⟨1,[(16,1)]⟩]) (.leaf 91 [⟨1,[(5,1)]⟩,⟨1,[(16,1)]⟩,⟨5042,[(15,4295),(16,2663)]⟩])) (.split (115,-183,16059939) (.split (-9993,3172,-860972000) (.leaf 93 [⟨1,[(17,1)]⟩,⟨1,[(16,1)]⟩,⟨1,[(15,1)]⟩]) (.split (-15472,7893,-1428448000) (.leaf 98 [⟨1,[(17,1)]⟩,⟨1,[(18,1)]⟩,⟨308000,[(14,851359),(17,680641)]⟩]) (.leaf 99 [⟨1,[(13,1)]⟩,⟨5179,[(5,5150249),(14,1873),(6,21850169926)]⟩,⟨1,[(18,1)]⟩]))) (.split (7502,-3207,694080000) (.leaf 94 [⟨1,[(14,1)]⟩,⟨1,[(17,1)]⟩,⟨1,[(16,1)]⟩]) (.leaf 91 [⟨1,[(5,1)]⟩,⟨2663,[(15,4295),(17,5042)]⟩,⟨1,[(17,1)]⟩])))
theorem sourceHex7Node152_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(-21967,7433,-1465352000),(-2624,155,-180912000),(-13116,9283,-1293872000),(-6007,828,-472248000)] (familyFacets sourceFamily7) sourceHex7Node152 = true := by decide

def sourceHex7Node150 : CoverTree := .split (6007,-828,472248000) sourceHex7Node151 sourceHex7Node152
theorem sourceHex7Node150_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(-21967,7433,-1465352000),(-2624,155,-180912000),(-13116,9283,-1293872000)] (familyFacets sourceFamily7) sourceHex7Node150 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node151_checked,sourceHex7Node152_checked⟩

def sourceHex7Node154 : CoverTree := .split (208,-385,28128000) (.split (4535,5397,171956000) (.leaf 103 [⟨1,[(16,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(15,1)]⟩]) (.split (7134,4349,403016000) (.leaf 48 [⟨1,[(16,1)]⟩,⟨1,[(17,1)]⟩,⟨9835032,[(14,18779483),(16,523)]⟩]) (.leaf 45 [⟨1,[(0,1)]⟩,⟨1967111,[(14,1251200),(17,89),(6,654377600)]⟩,⟨1,[(17,1)]⟩]))) (.split (-8124,43,-543948896) (.leaf 102 [⟨1,[(13,1)]⟩,⟨1,[(15,1)]⟩,⟨1,[(16,1)]⟩]) (.leaf 101 [⟨2339097,[(13,2695403),(16,1085500)]⟩,⟨1,[(16,1)]⟩,⟨163,[(12,170),(15,501)]⟩]))
theorem sourceHex7Node154_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(-21967,7433,-1465352000),(-2624,155,-180912000),(13116,-9283,1293872000),(-1361,549,-111168968)] (familyFacets sourceFamily7) sourceHex7Node154 = true := by decide

def sourceHex7Node155 : CoverTree := .split (11465,2603,737972000) (.leaf 104 [⟨1,[(15,1)]⟩,⟨1,[(12,1)]⟩,⟨1,[(14,1)]⟩]) (.split (8866,3651,544472000) (.split (2599,-1048,212280517) (.leaf 47 [⟨1,[(15,1)]⟩,⟨1,[(17,1)]⟩,⟨1,[(16,1)]⟩]) (.leaf 48 [⟨523,[(14,18779483),(17,9835032)]⟩,⟨18780517,[(16,18779483),(17,12512000)]⟩,⟨1,[(17,1)]⟩])) (.split (866,-349,70728000) (.leaf 46 [⟨1,[(0,1)]⟩,⟨1,[(16,1)]⟩,⟨1,[(17,1)]⟩]) (.split (-7134,-4349,-403016000) (.leaf 45 [⟨1,[(0,1)]⟩,⟨1,[(17,1)]⟩,⟨1,[(18,1)]⟩]) (.leaf 48 [⟨445,[(14,6256517),(17,9835032),(6,5084711544)]⟩,⟨1,[(18,1)]⟩,⟨6256000,[(17,18779483),(18,517)]⟩]))))
theorem sourceHex7Node155_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(-21967,7433,-1465352000),(-2624,155,-180912000),(13116,-9283,1293872000),(1361,-549,111168968)] (familyFacets sourceFamily7) sourceHex7Node155 = true := by decide

def sourceHex7Node153 : CoverTree := .split (-1361,549,-111168968) sourceHex7Node154 sourceHex7Node155
theorem sourceHex7Node153_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(-21967,7433,-1465352000),(-2624,155,-180912000),(13116,-9283,1293872000)] (familyFacets sourceFamily7) sourceHex7Node153 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node154_checked,sourceHex7Node155_checked⟩

def sourceHex7Node149 : CoverTree := .split (-13116,9283,-1293872000) sourceHex7Node150 sourceHex7Node153
theorem sourceHex7Node149_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(-21967,7433,-1465352000),(-2624,155,-180912000)] (familyFacets sourceFamily7) sourceHex7Node149 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node150_checked,sourceHex7Node153_checked⟩

def sourceHex7Node143 : CoverTree := .split (2624,-155,180912000) sourceHex7Node144 sourceHex7Node149
theorem sourceHex7Node143_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(-21967,7433,-1465352000)] (familyFacets sourceFamily7) sourceHex7Node143 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node144_checked,sourceHex7Node149_checked⟩

def sourceHex7Node157 : CoverTree := .split (23489,-6623,1409340000) (.split (31489,-2623,1742400000) (.split (-1410,-4979,41690161) (.leaf 125 [⟨1,[(12,1)]⟩,⟨1,[(15,1)]⟩,⟨1,[(14,1)]⟩]) (.leaf 126 [⟨18858037,[(9,26252000),(12,154173741)]⟩,⟨12245,[(13,3506),(14,16249)]⟩,⟨1,[(15,1)]⟩])) (.leaf 124 [⟨1,[(0,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(13,1)]⟩])) (.split (29967,-3433,1798020000) (.split (-15682,2757,-940920000) (.split (1397,-2081,141385426) (.leaf 120 [⟨1,[(15,1)]⟩,⟨1,[(16,1)]⟩,⟨1,[(14,1)]⟩]) (.split (-20318,3243,-1208760000) (.leaf 121 [⟨1,[(17,1)]⟩,⟨36833,[(11,28107),(14,31060)]⟩,⟨1,[(16,1)]⟩]) (.leaf 122 [⟨1,[(17,1)]⟩,⟨5160000,[(15,48071287),(17,39102713)]⟩,⟨30621149,[(9,93439722),(16,352659637),(6,2185192658074366)]⟩]))) (.split (-7875,-1109,-394294574) (.leaf 123 [⟨1,[(15,1)]⟩,⟨1,[(13,1)]⟩,⟨1,[(16,1)]⟩]) (.split (-48511,5377,-2715672000) (.leaf 122 [⟨39102713,[(15,48071287),(16,5160000)]⟩,⟨1,[(16,1)]⟩,⟨1,[(17,1)]⟩]) (.leaf 126 [⟨18858037,[(9,26252000),(12,154173741)]⟩,⟨1,[(17,1)]⟩,⟨78205426,[(13,37645935),(16,126290161)]⟩])))) (.leaf 119 [⟨1,[(0,1)]⟩,⟨1,[(14,1)]⟩,⟨1,[(11,1)]⟩]))
theorem sourceHex7Node157_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(21967,-7433,1465352000),(-4297,1086,-231944000)] (familyFacets sourceFamily7) sourceHex7Node157 = true := by decide

def sourceHex7Node158 : CoverTree := .leaf 128 [⟨1,[(12,1)]⟩,⟨1,[(10,1)]⟩,⟨1,[(9,1)]⟩]
theorem sourceHex7Node158_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(21967,-7433,1465352000),(4297,-1086,231944000)] (familyFacets sourceFamily7) sourceHex7Node158 = true := by decide

def sourceHex7Node156 : CoverTree := .split (-4297,1086,-231944000) sourceHex7Node157 sourceHex7Node158
theorem sourceHex7Node156_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000),(21967,-7433,1465352000)] (familyFacets sourceFamily7) sourceHex7Node156 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node157_checked,sourceHex7Node158_checked⟩

def sourceHex7Node142 : CoverTree := .split (-21967,7433,-1465352000) sourceHex7Node143 sourceHex7Node156
theorem sourceHex7Node142_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482),(-8829,19786,-336136000)] (familyFacets sourceFamily7) sourceHex7Node142 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node143_checked,sourceHex7Node156_checked⟩

def sourceHex7Node120 : CoverTree := .split (8829,-19786,336136000) sourceHex7Node121 sourceHex7Node142
theorem sourceHex7Node120_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000),(-10625,-6092,-379723482)] (familyFacets sourceFamily7) sourceHex7Node120 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node121_checked,sourceHex7Node142_checked⟩

def sourceHex7Node108 : CoverTree := .split (10625,6092,379723482) sourceHex7Node109 sourceHex7Node120
theorem sourceHex7Node108_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000),(-13747,-3969,-332240000)] (familyFacets sourceFamily7) sourceHex7Node108 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node109_checked,sourceHex7Node120_checked⟩

def sourceHex7Node92 : CoverTree := .split (13747,3969,332240000) sourceHex7Node93 sourceHex7Node108
theorem sourceHex7Node92_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1),(-90597,-59416,-70704000)] (familyFacets sourceFamily7) sourceHex7Node92 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node93_checked,sourceHex7Node108_checked⟩

def sourceHex7Node0 : CoverTree := .split (90597,59416,70704000) sourceHex7Node1 sourceHex7Node92
theorem sourceHex7Node0_checked : checkTree [(2,1,120000),(1,2,120000),(-1,1,120000),(-2,-1,120000),(-1,-2,120000),(1,-1,120000),(0,0,1)] (familyFacets sourceFamily7) sourceHex7Node0 = true := by
  exact Bool.and_eq_true_iff.mpr ⟨sourceHex7Node1_checked,sourceHex7Node92_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
