module

public import SpectreGeometry.ReverseClusterTriangulationSource01Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource01Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source1Family_length : sourceFamily1.length = 218 := by decide

theorem source1FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+0) default)
      (sourceFamily1.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes0,source1FaceRow0_checked⟩ (Fin.cases ⟨source1FaceCodes1,source1FaceRow1_checked⟩ (Fin.cases ⟨source1FaceCodes2,source1FaceRow2_checked⟩ (Fin.cases ⟨source1FaceCodes3,source1FaceRow3_checked⟩ (Fin.cases ⟨source1FaceCodes4,source1FaceRow4_checked⟩ (Fin.cases ⟨source1FaceCodes5,source1FaceRow5_checked⟩ (Fin.cases ⟨source1FaceCodes6,source1FaceRow6_checked⟩ (Fin.cases ⟨source1FaceCodes7,source1FaceRow7_checked⟩ (Fin.cases ⟨source1FaceCodes8,source1FaceRow8_checked⟩ (Fin.cases ⟨source1FaceCodes9,source1FaceRow9_checked⟩ (Fin.cases ⟨source1FaceCodes10,source1FaceRow10_checked⟩ (Fin.cases ⟨source1FaceCodes11,source1FaceRow11_checked⟩ (Fin.cases ⟨source1FaceCodes12,source1FaceRow12_checked⟩ (Fin.cases ⟨source1FaceCodes13,source1FaceRow13_checked⟩ (Fin.cases ⟨source1FaceCodes14,source1FaceRow14_checked⟩ (Fin.cases ⟨source1FaceCodes15,source1FaceRow15_checked⟩ (Fin.cases ⟨source1FaceCodes16,source1FaceRow16_checked⟩ (Fin.cases ⟨source1FaceCodes17,source1FaceRow17_checked⟩ (Fin.cases ⟨source1FaceCodes18,source1FaceRow18_checked⟩ (Fin.cases ⟨source1FaceCodes19,source1FaceRow19_checked⟩ (Fin.cases ⟨source1FaceCodes20,source1FaceRow20_checked⟩ (Fin.cases ⟨source1FaceCodes21,source1FaceRow21_checked⟩ (Fin.cases ⟨source1FaceCodes22,source1FaceRow22_checked⟩ (Fin.cases ⟨source1FaceCodes23,source1FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+24) default)
      (sourceFamily1.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes24,source1FaceRow24_checked⟩ (Fin.cases ⟨source1FaceCodes25,source1FaceRow25_checked⟩ (Fin.cases ⟨source1FaceCodes26,source1FaceRow26_checked⟩ (Fin.cases ⟨source1FaceCodes27,source1FaceRow27_checked⟩ (Fin.cases ⟨source1FaceCodes28,source1FaceRow28_checked⟩ (Fin.cases ⟨source1FaceCodes29,source1FaceRow29_checked⟩ (Fin.cases ⟨source1FaceCodes30,source1FaceRow30_checked⟩ (Fin.cases ⟨source1FaceCodes31,source1FaceRow31_checked⟩ (Fin.cases ⟨source1FaceCodes32,source1FaceRow32_checked⟩ (Fin.cases ⟨source1FaceCodes33,source1FaceRow33_checked⟩ (Fin.cases ⟨source1FaceCodes34,source1FaceRow34_checked⟩ (Fin.cases ⟨source1FaceCodes35,source1FaceRow35_checked⟩ (Fin.cases ⟨source1FaceCodes36,source1FaceRow36_checked⟩ (Fin.cases ⟨source1FaceCodes37,source1FaceRow37_checked⟩ (Fin.cases ⟨source1FaceCodes38,source1FaceRow38_checked⟩ (Fin.cases ⟨source1FaceCodes39,source1FaceRow39_checked⟩ (Fin.cases ⟨source1FaceCodes40,source1FaceRow40_checked⟩ (Fin.cases ⟨source1FaceCodes41,source1FaceRow41_checked⟩ (Fin.cases ⟨source1FaceCodes42,source1FaceRow42_checked⟩ (Fin.cases ⟨source1FaceCodes43,source1FaceRow43_checked⟩ (Fin.cases ⟨source1FaceCodes44,source1FaceRow44_checked⟩ (Fin.cases ⟨source1FaceCodes45,source1FaceRow45_checked⟩ (Fin.cases ⟨source1FaceCodes46,source1FaceRow46_checked⟩ (Fin.cases ⟨source1FaceCodes47,source1FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+48) default)
      (sourceFamily1.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes48,source1FaceRow48_checked⟩ (Fin.cases ⟨source1FaceCodes49,source1FaceRow49_checked⟩ (Fin.cases ⟨source1FaceCodes50,source1FaceRow50_checked⟩ (Fin.cases ⟨source1FaceCodes51,source1FaceRow51_checked⟩ (Fin.cases ⟨source1FaceCodes52,source1FaceRow52_checked⟩ (Fin.cases ⟨source1FaceCodes53,source1FaceRow53_checked⟩ (Fin.cases ⟨source1FaceCodes54,source1FaceRow54_checked⟩ (Fin.cases ⟨source1FaceCodes55,source1FaceRow55_checked⟩ (Fin.cases ⟨source1FaceCodes56,source1FaceRow56_checked⟩ (Fin.cases ⟨source1FaceCodes57,source1FaceRow57_checked⟩ (Fin.cases ⟨source1FaceCodes58,source1FaceRow58_checked⟩ (Fin.cases ⟨source1FaceCodes59,source1FaceRow59_checked⟩ (Fin.cases ⟨source1FaceCodes60,source1FaceRow60_checked⟩ (Fin.cases ⟨source1FaceCodes61,source1FaceRow61_checked⟩ (Fin.cases ⟨source1FaceCodes62,source1FaceRow62_checked⟩ (Fin.cases ⟨source1FaceCodes63,source1FaceRow63_checked⟩ (Fin.cases ⟨source1FaceCodes64,source1FaceRow64_checked⟩ (Fin.cases ⟨source1FaceCodes65,source1FaceRow65_checked⟩ (Fin.cases ⟨source1FaceCodes66,source1FaceRow66_checked⟩ (Fin.cases ⟨source1FaceCodes67,source1FaceRow67_checked⟩ (Fin.cases ⟨source1FaceCodes68,source1FaceRow68_checked⟩ (Fin.cases ⟨source1FaceCodes69,source1FaceRow69_checked⟩ (Fin.cases ⟨source1FaceCodes70,source1FaceRow70_checked⟩ (Fin.cases ⟨source1FaceCodes71,source1FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+72) default)
      (sourceFamily1.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes72,source1FaceRow72_checked⟩ (Fin.cases ⟨source1FaceCodes73,source1FaceRow73_checked⟩ (Fin.cases ⟨source1FaceCodes74,source1FaceRow74_checked⟩ (Fin.cases ⟨source1FaceCodes75,source1FaceRow75_checked⟩ (Fin.cases ⟨source1FaceCodes76,source1FaceRow76_checked⟩ (Fin.cases ⟨source1FaceCodes77,source1FaceRow77_checked⟩ (Fin.cases ⟨source1FaceCodes78,source1FaceRow78_checked⟩ (Fin.cases ⟨source1FaceCodes79,source1FaceRow79_checked⟩ (Fin.cases ⟨source1FaceCodes80,source1FaceRow80_checked⟩ (Fin.cases ⟨source1FaceCodes81,source1FaceRow81_checked⟩ (Fin.cases ⟨source1FaceCodes82,source1FaceRow82_checked⟩ (Fin.cases ⟨source1FaceCodes83,source1FaceRow83_checked⟩ (Fin.cases ⟨source1FaceCodes84,source1FaceRow84_checked⟩ (Fin.cases ⟨source1FaceCodes85,source1FaceRow85_checked⟩ (Fin.cases ⟨source1FaceCodes86,source1FaceRow86_checked⟩ (Fin.cases ⟨source1FaceCodes87,source1FaceRow87_checked⟩ (Fin.cases ⟨source1FaceCodes88,source1FaceRow88_checked⟩ (Fin.cases ⟨source1FaceCodes89,source1FaceRow89_checked⟩ (Fin.cases ⟨source1FaceCodes90,source1FaceRow90_checked⟩ (Fin.cases ⟨source1FaceCodes91,source1FaceRow91_checked⟩ (Fin.cases ⟨source1FaceCodes92,source1FaceRow92_checked⟩ (Fin.cases ⟨source1FaceCodes93,source1FaceRow93_checked⟩ (Fin.cases ⟨source1FaceCodes94,source1FaceRow94_checked⟩ (Fin.cases ⟨source1FaceCodes95,source1FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+96) default)
      (sourceFamily1.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes96,source1FaceRow96_checked⟩ (Fin.cases ⟨source1FaceCodes97,source1FaceRow97_checked⟩ (Fin.cases ⟨source1FaceCodes98,source1FaceRow98_checked⟩ (Fin.cases ⟨source1FaceCodes99,source1FaceRow99_checked⟩ (Fin.cases ⟨source1FaceCodes100,source1FaceRow100_checked⟩ (Fin.cases ⟨source1FaceCodes101,source1FaceRow101_checked⟩ (Fin.cases ⟨source1FaceCodes102,source1FaceRow102_checked⟩ (Fin.cases ⟨source1FaceCodes103,source1FaceRow103_checked⟩ (Fin.cases ⟨source1FaceCodes104,source1FaceRow104_checked⟩ (Fin.cases ⟨source1FaceCodes105,source1FaceRow105_checked⟩ (Fin.cases ⟨source1FaceCodes106,source1FaceRow106_checked⟩ (Fin.cases ⟨source1FaceCodes107,source1FaceRow107_checked⟩ (Fin.cases ⟨source1FaceCodes108,source1FaceRow108_checked⟩ (Fin.cases ⟨source1FaceCodes109,source1FaceRow109_checked⟩ (Fin.cases ⟨source1FaceCodes110,source1FaceRow110_checked⟩ (Fin.cases ⟨source1FaceCodes111,source1FaceRow111_checked⟩ (Fin.cases ⟨source1FaceCodes112,source1FaceRow112_checked⟩ (Fin.cases ⟨source1FaceCodes113,source1FaceRow113_checked⟩ (Fin.cases ⟨source1FaceCodes114,source1FaceRow114_checked⟩ (Fin.cases ⟨source1FaceCodes115,source1FaceRow115_checked⟩ (Fin.cases ⟨source1FaceCodes116,source1FaceRow116_checked⟩ (Fin.cases ⟨source1FaceCodes117,source1FaceRow117_checked⟩ (Fin.cases ⟨source1FaceCodes118,source1FaceRow118_checked⟩ (Fin.cases ⟨source1FaceCodes119,source1FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+120) default)
      (sourceFamily1.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes120,source1FaceRow120_checked⟩ (Fin.cases ⟨source1FaceCodes121,source1FaceRow121_checked⟩ (Fin.cases ⟨source1FaceCodes122,source1FaceRow122_checked⟩ (Fin.cases ⟨source1FaceCodes123,source1FaceRow123_checked⟩ (Fin.cases ⟨source1FaceCodes124,source1FaceRow124_checked⟩ (Fin.cases ⟨source1FaceCodes125,source1FaceRow125_checked⟩ (Fin.cases ⟨source1FaceCodes126,source1FaceRow126_checked⟩ (Fin.cases ⟨source1FaceCodes127,source1FaceRow127_checked⟩ (Fin.cases ⟨source1FaceCodes128,source1FaceRow128_checked⟩ (Fin.cases ⟨source1FaceCodes129,source1FaceRow129_checked⟩ (Fin.cases ⟨source1FaceCodes130,source1FaceRow130_checked⟩ (Fin.cases ⟨source1FaceCodes131,source1FaceRow131_checked⟩ (Fin.cases ⟨source1FaceCodes132,source1FaceRow132_checked⟩ (Fin.cases ⟨source1FaceCodes133,source1FaceRow133_checked⟩ (Fin.cases ⟨source1FaceCodes134,source1FaceRow134_checked⟩ (Fin.cases ⟨source1FaceCodes135,source1FaceRow135_checked⟩ (Fin.cases ⟨source1FaceCodes136,source1FaceRow136_checked⟩ (Fin.cases ⟨source1FaceCodes137,source1FaceRow137_checked⟩ (Fin.cases ⟨source1FaceCodes138,source1FaceRow138_checked⟩ (Fin.cases ⟨source1FaceCodes139,source1FaceRow139_checked⟩ (Fin.cases ⟨source1FaceCodes140,source1FaceRow140_checked⟩ (Fin.cases ⟨source1FaceCodes141,source1FaceRow141_checked⟩ (Fin.cases ⟨source1FaceCodes142,source1FaceRow142_checked⟩ (Fin.cases ⟨source1FaceCodes143,source1FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+144) default)
      (sourceFamily1.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes144,source1FaceRow144_checked⟩ (Fin.cases ⟨source1FaceCodes145,source1FaceRow145_checked⟩ (Fin.cases ⟨source1FaceCodes146,source1FaceRow146_checked⟩ (Fin.cases ⟨source1FaceCodes147,source1FaceRow147_checked⟩ (Fin.cases ⟨source1FaceCodes148,source1FaceRow148_checked⟩ (Fin.cases ⟨source1FaceCodes149,source1FaceRow149_checked⟩ (Fin.cases ⟨source1FaceCodes150,source1FaceRow150_checked⟩ (Fin.cases ⟨source1FaceCodes151,source1FaceRow151_checked⟩ (Fin.cases ⟨source1FaceCodes152,source1FaceRow152_checked⟩ (Fin.cases ⟨source1FaceCodes153,source1FaceRow153_checked⟩ (Fin.cases ⟨source1FaceCodes154,source1FaceRow154_checked⟩ (Fin.cases ⟨source1FaceCodes155,source1FaceRow155_checked⟩ (Fin.cases ⟨source1FaceCodes156,source1FaceRow156_checked⟩ (Fin.cases ⟨source1FaceCodes157,source1FaceRow157_checked⟩ (Fin.cases ⟨source1FaceCodes158,source1FaceRow158_checked⟩ (Fin.cases ⟨source1FaceCodes159,source1FaceRow159_checked⟩ (Fin.cases ⟨source1FaceCodes160,source1FaceRow160_checked⟩ (Fin.cases ⟨source1FaceCodes161,source1FaceRow161_checked⟩ (Fin.cases ⟨source1FaceCodes162,source1FaceRow162_checked⟩ (Fin.cases ⟨source1FaceCodes163,source1FaceRow163_checked⟩ (Fin.cases ⟨source1FaceCodes164,source1FaceRow164_checked⟩ (Fin.cases ⟨source1FaceCodes165,source1FaceRow165_checked⟩ (Fin.cases ⟨source1FaceCodes166,source1FaceRow166_checked⟩ (Fin.cases ⟨source1FaceCodes167,source1FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+168) default)
      (sourceFamily1.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes168,source1FaceRow168_checked⟩ (Fin.cases ⟨source1FaceCodes169,source1FaceRow169_checked⟩ (Fin.cases ⟨source1FaceCodes170,source1FaceRow170_checked⟩ (Fin.cases ⟨source1FaceCodes171,source1FaceRow171_checked⟩ (Fin.cases ⟨source1FaceCodes172,source1FaceRow172_checked⟩ (Fin.cases ⟨source1FaceCodes173,source1FaceRow173_checked⟩ (Fin.cases ⟨source1FaceCodes174,source1FaceRow174_checked⟩ (Fin.cases ⟨source1FaceCodes175,source1FaceRow175_checked⟩ (Fin.cases ⟨source1FaceCodes176,source1FaceRow176_checked⟩ (Fin.cases ⟨source1FaceCodes177,source1FaceRow177_checked⟩ (Fin.cases ⟨source1FaceCodes178,source1FaceRow178_checked⟩ (Fin.cases ⟨source1FaceCodes179,source1FaceRow179_checked⟩ (Fin.cases ⟨source1FaceCodes180,source1FaceRow180_checked⟩ (Fin.cases ⟨source1FaceCodes181,source1FaceRow181_checked⟩ (Fin.cases ⟨source1FaceCodes182,source1FaceRow182_checked⟩ (Fin.cases ⟨source1FaceCodes183,source1FaceRow183_checked⟩ (Fin.cases ⟨source1FaceCodes184,source1FaceRow184_checked⟩ (Fin.cases ⟨source1FaceCodes185,source1FaceRow185_checked⟩ (Fin.cases ⟨source1FaceCodes186,source1FaceRow186_checked⟩ (Fin.cases ⟨source1FaceCodes187,source1FaceRow187_checked⟩ (Fin.cases ⟨source1FaceCodes188,source1FaceRow188_checked⟩ (Fin.cases ⟨source1FaceCodes189,source1FaceRow189_checked⟩ (Fin.cases ⟨source1FaceCodes190,source1FaceRow190_checked⟩ (Fin.cases ⟨source1FaceCodes191,source1FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+192) default)
      (sourceFamily1.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes192,source1FaceRow192_checked⟩ (Fin.cases ⟨source1FaceCodes193,source1FaceRow193_checked⟩ (Fin.cases ⟨source1FaceCodes194,source1FaceRow194_checked⟩ (Fin.cases ⟨source1FaceCodes195,source1FaceRow195_checked⟩ (Fin.cases ⟨source1FaceCodes196,source1FaceRow196_checked⟩ (Fin.cases ⟨source1FaceCodes197,source1FaceRow197_checked⟩ (Fin.cases ⟨source1FaceCodes198,source1FaceRow198_checked⟩ (Fin.cases ⟨source1FaceCodes199,source1FaceRow199_checked⟩ (Fin.cases ⟨source1FaceCodes200,source1FaceRow200_checked⟩ (Fin.cases ⟨source1FaceCodes201,source1FaceRow201_checked⟩ (Fin.cases ⟨source1FaceCodes202,source1FaceRow202_checked⟩ (Fin.cases ⟨source1FaceCodes203,source1FaceRow203_checked⟩ (Fin.cases ⟨source1FaceCodes204,source1FaceRow204_checked⟩ (Fin.cases ⟨source1FaceCodes205,source1FaceRow205_checked⟩ (Fin.cases ⟨source1FaceCodes206,source1FaceRow206_checked⟩ (Fin.cases ⟨source1FaceCodes207,source1FaceRow207_checked⟩ (Fin.cases ⟨source1FaceCodes208,source1FaceRow208_checked⟩ (Fin.cases ⟨source1FaceCodes209,source1FaceRow209_checked⟩ (Fin.cases ⟨source1FaceCodes210,source1FaceRow210_checked⟩ (Fin.cases ⟨source1FaceCodes211,source1FaceRow211_checked⟩ (Fin.cases ⟨source1FaceCodes212,source1FaceRow212_checked⟩ (Fin.cases ⟨source1FaceCodes213,source1FaceRow213_checked⟩ (Fin.cases ⟨source1FaceCodes214,source1FaceRow214_checked⟩ (Fin.cases ⟨source1FaceCodes215,source1FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source1FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily1.getD (j.val+216) default)
      (sourceFamily1.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source1FaceCodes216,source1FaceRow216_checked⟩ (Fin.cases ⟨source1FaceCodes217,source1FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source1AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily1.getD i.val default)
      (sourceFamily1.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source1FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
