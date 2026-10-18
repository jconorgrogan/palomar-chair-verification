module

public import SpectreGeometry.ReverseClusterTriangulationSource02Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource02Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source2Family_length : sourceFamily2.length = 218 := by decide

theorem source2FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+0) default)
      (sourceFamily2.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes0,source2FaceRow0_checked⟩ (Fin.cases ⟨source2FaceCodes1,source2FaceRow1_checked⟩ (Fin.cases ⟨source2FaceCodes2,source2FaceRow2_checked⟩ (Fin.cases ⟨source2FaceCodes3,source2FaceRow3_checked⟩ (Fin.cases ⟨source2FaceCodes4,source2FaceRow4_checked⟩ (Fin.cases ⟨source2FaceCodes5,source2FaceRow5_checked⟩ (Fin.cases ⟨source2FaceCodes6,source2FaceRow6_checked⟩ (Fin.cases ⟨source2FaceCodes7,source2FaceRow7_checked⟩ (Fin.cases ⟨source2FaceCodes8,source2FaceRow8_checked⟩ (Fin.cases ⟨source2FaceCodes9,source2FaceRow9_checked⟩ (Fin.cases ⟨source2FaceCodes10,source2FaceRow10_checked⟩ (Fin.cases ⟨source2FaceCodes11,source2FaceRow11_checked⟩ (Fin.cases ⟨source2FaceCodes12,source2FaceRow12_checked⟩ (Fin.cases ⟨source2FaceCodes13,source2FaceRow13_checked⟩ (Fin.cases ⟨source2FaceCodes14,source2FaceRow14_checked⟩ (Fin.cases ⟨source2FaceCodes15,source2FaceRow15_checked⟩ (Fin.cases ⟨source2FaceCodes16,source2FaceRow16_checked⟩ (Fin.cases ⟨source2FaceCodes17,source2FaceRow17_checked⟩ (Fin.cases ⟨source2FaceCodes18,source2FaceRow18_checked⟩ (Fin.cases ⟨source2FaceCodes19,source2FaceRow19_checked⟩ (Fin.cases ⟨source2FaceCodes20,source2FaceRow20_checked⟩ (Fin.cases ⟨source2FaceCodes21,source2FaceRow21_checked⟩ (Fin.cases ⟨source2FaceCodes22,source2FaceRow22_checked⟩ (Fin.cases ⟨source2FaceCodes23,source2FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+24) default)
      (sourceFamily2.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes24,source2FaceRow24_checked⟩ (Fin.cases ⟨source2FaceCodes25,source2FaceRow25_checked⟩ (Fin.cases ⟨source2FaceCodes26,source2FaceRow26_checked⟩ (Fin.cases ⟨source2FaceCodes27,source2FaceRow27_checked⟩ (Fin.cases ⟨source2FaceCodes28,source2FaceRow28_checked⟩ (Fin.cases ⟨source2FaceCodes29,source2FaceRow29_checked⟩ (Fin.cases ⟨source2FaceCodes30,source2FaceRow30_checked⟩ (Fin.cases ⟨source2FaceCodes31,source2FaceRow31_checked⟩ (Fin.cases ⟨source2FaceCodes32,source2FaceRow32_checked⟩ (Fin.cases ⟨source2FaceCodes33,source2FaceRow33_checked⟩ (Fin.cases ⟨source2FaceCodes34,source2FaceRow34_checked⟩ (Fin.cases ⟨source2FaceCodes35,source2FaceRow35_checked⟩ (Fin.cases ⟨source2FaceCodes36,source2FaceRow36_checked⟩ (Fin.cases ⟨source2FaceCodes37,source2FaceRow37_checked⟩ (Fin.cases ⟨source2FaceCodes38,source2FaceRow38_checked⟩ (Fin.cases ⟨source2FaceCodes39,source2FaceRow39_checked⟩ (Fin.cases ⟨source2FaceCodes40,source2FaceRow40_checked⟩ (Fin.cases ⟨source2FaceCodes41,source2FaceRow41_checked⟩ (Fin.cases ⟨source2FaceCodes42,source2FaceRow42_checked⟩ (Fin.cases ⟨source2FaceCodes43,source2FaceRow43_checked⟩ (Fin.cases ⟨source2FaceCodes44,source2FaceRow44_checked⟩ (Fin.cases ⟨source2FaceCodes45,source2FaceRow45_checked⟩ (Fin.cases ⟨source2FaceCodes46,source2FaceRow46_checked⟩ (Fin.cases ⟨source2FaceCodes47,source2FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+48) default)
      (sourceFamily2.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes48,source2FaceRow48_checked⟩ (Fin.cases ⟨source2FaceCodes49,source2FaceRow49_checked⟩ (Fin.cases ⟨source2FaceCodes50,source2FaceRow50_checked⟩ (Fin.cases ⟨source2FaceCodes51,source2FaceRow51_checked⟩ (Fin.cases ⟨source2FaceCodes52,source2FaceRow52_checked⟩ (Fin.cases ⟨source2FaceCodes53,source2FaceRow53_checked⟩ (Fin.cases ⟨source2FaceCodes54,source2FaceRow54_checked⟩ (Fin.cases ⟨source2FaceCodes55,source2FaceRow55_checked⟩ (Fin.cases ⟨source2FaceCodes56,source2FaceRow56_checked⟩ (Fin.cases ⟨source2FaceCodes57,source2FaceRow57_checked⟩ (Fin.cases ⟨source2FaceCodes58,source2FaceRow58_checked⟩ (Fin.cases ⟨source2FaceCodes59,source2FaceRow59_checked⟩ (Fin.cases ⟨source2FaceCodes60,source2FaceRow60_checked⟩ (Fin.cases ⟨source2FaceCodes61,source2FaceRow61_checked⟩ (Fin.cases ⟨source2FaceCodes62,source2FaceRow62_checked⟩ (Fin.cases ⟨source2FaceCodes63,source2FaceRow63_checked⟩ (Fin.cases ⟨source2FaceCodes64,source2FaceRow64_checked⟩ (Fin.cases ⟨source2FaceCodes65,source2FaceRow65_checked⟩ (Fin.cases ⟨source2FaceCodes66,source2FaceRow66_checked⟩ (Fin.cases ⟨source2FaceCodes67,source2FaceRow67_checked⟩ (Fin.cases ⟨source2FaceCodes68,source2FaceRow68_checked⟩ (Fin.cases ⟨source2FaceCodes69,source2FaceRow69_checked⟩ (Fin.cases ⟨source2FaceCodes70,source2FaceRow70_checked⟩ (Fin.cases ⟨source2FaceCodes71,source2FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+72) default)
      (sourceFamily2.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes72,source2FaceRow72_checked⟩ (Fin.cases ⟨source2FaceCodes73,source2FaceRow73_checked⟩ (Fin.cases ⟨source2FaceCodes74,source2FaceRow74_checked⟩ (Fin.cases ⟨source2FaceCodes75,source2FaceRow75_checked⟩ (Fin.cases ⟨source2FaceCodes76,source2FaceRow76_checked⟩ (Fin.cases ⟨source2FaceCodes77,source2FaceRow77_checked⟩ (Fin.cases ⟨source2FaceCodes78,source2FaceRow78_checked⟩ (Fin.cases ⟨source2FaceCodes79,source2FaceRow79_checked⟩ (Fin.cases ⟨source2FaceCodes80,source2FaceRow80_checked⟩ (Fin.cases ⟨source2FaceCodes81,source2FaceRow81_checked⟩ (Fin.cases ⟨source2FaceCodes82,source2FaceRow82_checked⟩ (Fin.cases ⟨source2FaceCodes83,source2FaceRow83_checked⟩ (Fin.cases ⟨source2FaceCodes84,source2FaceRow84_checked⟩ (Fin.cases ⟨source2FaceCodes85,source2FaceRow85_checked⟩ (Fin.cases ⟨source2FaceCodes86,source2FaceRow86_checked⟩ (Fin.cases ⟨source2FaceCodes87,source2FaceRow87_checked⟩ (Fin.cases ⟨source2FaceCodes88,source2FaceRow88_checked⟩ (Fin.cases ⟨source2FaceCodes89,source2FaceRow89_checked⟩ (Fin.cases ⟨source2FaceCodes90,source2FaceRow90_checked⟩ (Fin.cases ⟨source2FaceCodes91,source2FaceRow91_checked⟩ (Fin.cases ⟨source2FaceCodes92,source2FaceRow92_checked⟩ (Fin.cases ⟨source2FaceCodes93,source2FaceRow93_checked⟩ (Fin.cases ⟨source2FaceCodes94,source2FaceRow94_checked⟩ (Fin.cases ⟨source2FaceCodes95,source2FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+96) default)
      (sourceFamily2.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes96,source2FaceRow96_checked⟩ (Fin.cases ⟨source2FaceCodes97,source2FaceRow97_checked⟩ (Fin.cases ⟨source2FaceCodes98,source2FaceRow98_checked⟩ (Fin.cases ⟨source2FaceCodes99,source2FaceRow99_checked⟩ (Fin.cases ⟨source2FaceCodes100,source2FaceRow100_checked⟩ (Fin.cases ⟨source2FaceCodes101,source2FaceRow101_checked⟩ (Fin.cases ⟨source2FaceCodes102,source2FaceRow102_checked⟩ (Fin.cases ⟨source2FaceCodes103,source2FaceRow103_checked⟩ (Fin.cases ⟨source2FaceCodes104,source2FaceRow104_checked⟩ (Fin.cases ⟨source2FaceCodes105,source2FaceRow105_checked⟩ (Fin.cases ⟨source2FaceCodes106,source2FaceRow106_checked⟩ (Fin.cases ⟨source2FaceCodes107,source2FaceRow107_checked⟩ (Fin.cases ⟨source2FaceCodes108,source2FaceRow108_checked⟩ (Fin.cases ⟨source2FaceCodes109,source2FaceRow109_checked⟩ (Fin.cases ⟨source2FaceCodes110,source2FaceRow110_checked⟩ (Fin.cases ⟨source2FaceCodes111,source2FaceRow111_checked⟩ (Fin.cases ⟨source2FaceCodes112,source2FaceRow112_checked⟩ (Fin.cases ⟨source2FaceCodes113,source2FaceRow113_checked⟩ (Fin.cases ⟨source2FaceCodes114,source2FaceRow114_checked⟩ (Fin.cases ⟨source2FaceCodes115,source2FaceRow115_checked⟩ (Fin.cases ⟨source2FaceCodes116,source2FaceRow116_checked⟩ (Fin.cases ⟨source2FaceCodes117,source2FaceRow117_checked⟩ (Fin.cases ⟨source2FaceCodes118,source2FaceRow118_checked⟩ (Fin.cases ⟨source2FaceCodes119,source2FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+120) default)
      (sourceFamily2.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes120,source2FaceRow120_checked⟩ (Fin.cases ⟨source2FaceCodes121,source2FaceRow121_checked⟩ (Fin.cases ⟨source2FaceCodes122,source2FaceRow122_checked⟩ (Fin.cases ⟨source2FaceCodes123,source2FaceRow123_checked⟩ (Fin.cases ⟨source2FaceCodes124,source2FaceRow124_checked⟩ (Fin.cases ⟨source2FaceCodes125,source2FaceRow125_checked⟩ (Fin.cases ⟨source2FaceCodes126,source2FaceRow126_checked⟩ (Fin.cases ⟨source2FaceCodes127,source2FaceRow127_checked⟩ (Fin.cases ⟨source2FaceCodes128,source2FaceRow128_checked⟩ (Fin.cases ⟨source2FaceCodes129,source2FaceRow129_checked⟩ (Fin.cases ⟨source2FaceCodes130,source2FaceRow130_checked⟩ (Fin.cases ⟨source2FaceCodes131,source2FaceRow131_checked⟩ (Fin.cases ⟨source2FaceCodes132,source2FaceRow132_checked⟩ (Fin.cases ⟨source2FaceCodes133,source2FaceRow133_checked⟩ (Fin.cases ⟨source2FaceCodes134,source2FaceRow134_checked⟩ (Fin.cases ⟨source2FaceCodes135,source2FaceRow135_checked⟩ (Fin.cases ⟨source2FaceCodes136,source2FaceRow136_checked⟩ (Fin.cases ⟨source2FaceCodes137,source2FaceRow137_checked⟩ (Fin.cases ⟨source2FaceCodes138,source2FaceRow138_checked⟩ (Fin.cases ⟨source2FaceCodes139,source2FaceRow139_checked⟩ (Fin.cases ⟨source2FaceCodes140,source2FaceRow140_checked⟩ (Fin.cases ⟨source2FaceCodes141,source2FaceRow141_checked⟩ (Fin.cases ⟨source2FaceCodes142,source2FaceRow142_checked⟩ (Fin.cases ⟨source2FaceCodes143,source2FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+144) default)
      (sourceFamily2.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes144,source2FaceRow144_checked⟩ (Fin.cases ⟨source2FaceCodes145,source2FaceRow145_checked⟩ (Fin.cases ⟨source2FaceCodes146,source2FaceRow146_checked⟩ (Fin.cases ⟨source2FaceCodes147,source2FaceRow147_checked⟩ (Fin.cases ⟨source2FaceCodes148,source2FaceRow148_checked⟩ (Fin.cases ⟨source2FaceCodes149,source2FaceRow149_checked⟩ (Fin.cases ⟨source2FaceCodes150,source2FaceRow150_checked⟩ (Fin.cases ⟨source2FaceCodes151,source2FaceRow151_checked⟩ (Fin.cases ⟨source2FaceCodes152,source2FaceRow152_checked⟩ (Fin.cases ⟨source2FaceCodes153,source2FaceRow153_checked⟩ (Fin.cases ⟨source2FaceCodes154,source2FaceRow154_checked⟩ (Fin.cases ⟨source2FaceCodes155,source2FaceRow155_checked⟩ (Fin.cases ⟨source2FaceCodes156,source2FaceRow156_checked⟩ (Fin.cases ⟨source2FaceCodes157,source2FaceRow157_checked⟩ (Fin.cases ⟨source2FaceCodes158,source2FaceRow158_checked⟩ (Fin.cases ⟨source2FaceCodes159,source2FaceRow159_checked⟩ (Fin.cases ⟨source2FaceCodes160,source2FaceRow160_checked⟩ (Fin.cases ⟨source2FaceCodes161,source2FaceRow161_checked⟩ (Fin.cases ⟨source2FaceCodes162,source2FaceRow162_checked⟩ (Fin.cases ⟨source2FaceCodes163,source2FaceRow163_checked⟩ (Fin.cases ⟨source2FaceCodes164,source2FaceRow164_checked⟩ (Fin.cases ⟨source2FaceCodes165,source2FaceRow165_checked⟩ (Fin.cases ⟨source2FaceCodes166,source2FaceRow166_checked⟩ (Fin.cases ⟨source2FaceCodes167,source2FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+168) default)
      (sourceFamily2.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes168,source2FaceRow168_checked⟩ (Fin.cases ⟨source2FaceCodes169,source2FaceRow169_checked⟩ (Fin.cases ⟨source2FaceCodes170,source2FaceRow170_checked⟩ (Fin.cases ⟨source2FaceCodes171,source2FaceRow171_checked⟩ (Fin.cases ⟨source2FaceCodes172,source2FaceRow172_checked⟩ (Fin.cases ⟨source2FaceCodes173,source2FaceRow173_checked⟩ (Fin.cases ⟨source2FaceCodes174,source2FaceRow174_checked⟩ (Fin.cases ⟨source2FaceCodes175,source2FaceRow175_checked⟩ (Fin.cases ⟨source2FaceCodes176,source2FaceRow176_checked⟩ (Fin.cases ⟨source2FaceCodes177,source2FaceRow177_checked⟩ (Fin.cases ⟨source2FaceCodes178,source2FaceRow178_checked⟩ (Fin.cases ⟨source2FaceCodes179,source2FaceRow179_checked⟩ (Fin.cases ⟨source2FaceCodes180,source2FaceRow180_checked⟩ (Fin.cases ⟨source2FaceCodes181,source2FaceRow181_checked⟩ (Fin.cases ⟨source2FaceCodes182,source2FaceRow182_checked⟩ (Fin.cases ⟨source2FaceCodes183,source2FaceRow183_checked⟩ (Fin.cases ⟨source2FaceCodes184,source2FaceRow184_checked⟩ (Fin.cases ⟨source2FaceCodes185,source2FaceRow185_checked⟩ (Fin.cases ⟨source2FaceCodes186,source2FaceRow186_checked⟩ (Fin.cases ⟨source2FaceCodes187,source2FaceRow187_checked⟩ (Fin.cases ⟨source2FaceCodes188,source2FaceRow188_checked⟩ (Fin.cases ⟨source2FaceCodes189,source2FaceRow189_checked⟩ (Fin.cases ⟨source2FaceCodes190,source2FaceRow190_checked⟩ (Fin.cases ⟨source2FaceCodes191,source2FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+192) default)
      (sourceFamily2.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes192,source2FaceRow192_checked⟩ (Fin.cases ⟨source2FaceCodes193,source2FaceRow193_checked⟩ (Fin.cases ⟨source2FaceCodes194,source2FaceRow194_checked⟩ (Fin.cases ⟨source2FaceCodes195,source2FaceRow195_checked⟩ (Fin.cases ⟨source2FaceCodes196,source2FaceRow196_checked⟩ (Fin.cases ⟨source2FaceCodes197,source2FaceRow197_checked⟩ (Fin.cases ⟨source2FaceCodes198,source2FaceRow198_checked⟩ (Fin.cases ⟨source2FaceCodes199,source2FaceRow199_checked⟩ (Fin.cases ⟨source2FaceCodes200,source2FaceRow200_checked⟩ (Fin.cases ⟨source2FaceCodes201,source2FaceRow201_checked⟩ (Fin.cases ⟨source2FaceCodes202,source2FaceRow202_checked⟩ (Fin.cases ⟨source2FaceCodes203,source2FaceRow203_checked⟩ (Fin.cases ⟨source2FaceCodes204,source2FaceRow204_checked⟩ (Fin.cases ⟨source2FaceCodes205,source2FaceRow205_checked⟩ (Fin.cases ⟨source2FaceCodes206,source2FaceRow206_checked⟩ (Fin.cases ⟨source2FaceCodes207,source2FaceRow207_checked⟩ (Fin.cases ⟨source2FaceCodes208,source2FaceRow208_checked⟩ (Fin.cases ⟨source2FaceCodes209,source2FaceRow209_checked⟩ (Fin.cases ⟨source2FaceCodes210,source2FaceRow210_checked⟩ (Fin.cases ⟨source2FaceCodes211,source2FaceRow211_checked⟩ (Fin.cases ⟨source2FaceCodes212,source2FaceRow212_checked⟩ (Fin.cases ⟨source2FaceCodes213,source2FaceRow213_checked⟩ (Fin.cases ⟨source2FaceCodes214,source2FaceRow214_checked⟩ (Fin.cases ⟨source2FaceCodes215,source2FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source2FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily2.getD (j.val+216) default)
      (sourceFamily2.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source2FaceCodes216,source2FaceRow216_checked⟩ (Fin.cases ⟨source2FaceCodes217,source2FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source2AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily2.getD i.val default)
      (sourceFamily2.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source2FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
