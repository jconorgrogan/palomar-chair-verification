module

public import SpectreGeometry.ReverseClusterTriangulationSource05Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource05Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source5Family_length : sourceFamily5.length = 218 := by decide

theorem source5FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+0) default)
      (sourceFamily5.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes0,source5FaceRow0_checked⟩ (Fin.cases ⟨source5FaceCodes1,source5FaceRow1_checked⟩ (Fin.cases ⟨source5FaceCodes2,source5FaceRow2_checked⟩ (Fin.cases ⟨source5FaceCodes3,source5FaceRow3_checked⟩ (Fin.cases ⟨source5FaceCodes4,source5FaceRow4_checked⟩ (Fin.cases ⟨source5FaceCodes5,source5FaceRow5_checked⟩ (Fin.cases ⟨source5FaceCodes6,source5FaceRow6_checked⟩ (Fin.cases ⟨source5FaceCodes7,source5FaceRow7_checked⟩ (Fin.cases ⟨source5FaceCodes8,source5FaceRow8_checked⟩ (Fin.cases ⟨source5FaceCodes9,source5FaceRow9_checked⟩ (Fin.cases ⟨source5FaceCodes10,source5FaceRow10_checked⟩ (Fin.cases ⟨source5FaceCodes11,source5FaceRow11_checked⟩ (Fin.cases ⟨source5FaceCodes12,source5FaceRow12_checked⟩ (Fin.cases ⟨source5FaceCodes13,source5FaceRow13_checked⟩ (Fin.cases ⟨source5FaceCodes14,source5FaceRow14_checked⟩ (Fin.cases ⟨source5FaceCodes15,source5FaceRow15_checked⟩ (Fin.cases ⟨source5FaceCodes16,source5FaceRow16_checked⟩ (Fin.cases ⟨source5FaceCodes17,source5FaceRow17_checked⟩ (Fin.cases ⟨source5FaceCodes18,source5FaceRow18_checked⟩ (Fin.cases ⟨source5FaceCodes19,source5FaceRow19_checked⟩ (Fin.cases ⟨source5FaceCodes20,source5FaceRow20_checked⟩ (Fin.cases ⟨source5FaceCodes21,source5FaceRow21_checked⟩ (Fin.cases ⟨source5FaceCodes22,source5FaceRow22_checked⟩ (Fin.cases ⟨source5FaceCodes23,source5FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+24) default)
      (sourceFamily5.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes24,source5FaceRow24_checked⟩ (Fin.cases ⟨source5FaceCodes25,source5FaceRow25_checked⟩ (Fin.cases ⟨source5FaceCodes26,source5FaceRow26_checked⟩ (Fin.cases ⟨source5FaceCodes27,source5FaceRow27_checked⟩ (Fin.cases ⟨source5FaceCodes28,source5FaceRow28_checked⟩ (Fin.cases ⟨source5FaceCodes29,source5FaceRow29_checked⟩ (Fin.cases ⟨source5FaceCodes30,source5FaceRow30_checked⟩ (Fin.cases ⟨source5FaceCodes31,source5FaceRow31_checked⟩ (Fin.cases ⟨source5FaceCodes32,source5FaceRow32_checked⟩ (Fin.cases ⟨source5FaceCodes33,source5FaceRow33_checked⟩ (Fin.cases ⟨source5FaceCodes34,source5FaceRow34_checked⟩ (Fin.cases ⟨source5FaceCodes35,source5FaceRow35_checked⟩ (Fin.cases ⟨source5FaceCodes36,source5FaceRow36_checked⟩ (Fin.cases ⟨source5FaceCodes37,source5FaceRow37_checked⟩ (Fin.cases ⟨source5FaceCodes38,source5FaceRow38_checked⟩ (Fin.cases ⟨source5FaceCodes39,source5FaceRow39_checked⟩ (Fin.cases ⟨source5FaceCodes40,source5FaceRow40_checked⟩ (Fin.cases ⟨source5FaceCodes41,source5FaceRow41_checked⟩ (Fin.cases ⟨source5FaceCodes42,source5FaceRow42_checked⟩ (Fin.cases ⟨source5FaceCodes43,source5FaceRow43_checked⟩ (Fin.cases ⟨source5FaceCodes44,source5FaceRow44_checked⟩ (Fin.cases ⟨source5FaceCodes45,source5FaceRow45_checked⟩ (Fin.cases ⟨source5FaceCodes46,source5FaceRow46_checked⟩ (Fin.cases ⟨source5FaceCodes47,source5FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+48) default)
      (sourceFamily5.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes48,source5FaceRow48_checked⟩ (Fin.cases ⟨source5FaceCodes49,source5FaceRow49_checked⟩ (Fin.cases ⟨source5FaceCodes50,source5FaceRow50_checked⟩ (Fin.cases ⟨source5FaceCodes51,source5FaceRow51_checked⟩ (Fin.cases ⟨source5FaceCodes52,source5FaceRow52_checked⟩ (Fin.cases ⟨source5FaceCodes53,source5FaceRow53_checked⟩ (Fin.cases ⟨source5FaceCodes54,source5FaceRow54_checked⟩ (Fin.cases ⟨source5FaceCodes55,source5FaceRow55_checked⟩ (Fin.cases ⟨source5FaceCodes56,source5FaceRow56_checked⟩ (Fin.cases ⟨source5FaceCodes57,source5FaceRow57_checked⟩ (Fin.cases ⟨source5FaceCodes58,source5FaceRow58_checked⟩ (Fin.cases ⟨source5FaceCodes59,source5FaceRow59_checked⟩ (Fin.cases ⟨source5FaceCodes60,source5FaceRow60_checked⟩ (Fin.cases ⟨source5FaceCodes61,source5FaceRow61_checked⟩ (Fin.cases ⟨source5FaceCodes62,source5FaceRow62_checked⟩ (Fin.cases ⟨source5FaceCodes63,source5FaceRow63_checked⟩ (Fin.cases ⟨source5FaceCodes64,source5FaceRow64_checked⟩ (Fin.cases ⟨source5FaceCodes65,source5FaceRow65_checked⟩ (Fin.cases ⟨source5FaceCodes66,source5FaceRow66_checked⟩ (Fin.cases ⟨source5FaceCodes67,source5FaceRow67_checked⟩ (Fin.cases ⟨source5FaceCodes68,source5FaceRow68_checked⟩ (Fin.cases ⟨source5FaceCodes69,source5FaceRow69_checked⟩ (Fin.cases ⟨source5FaceCodes70,source5FaceRow70_checked⟩ (Fin.cases ⟨source5FaceCodes71,source5FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+72) default)
      (sourceFamily5.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes72,source5FaceRow72_checked⟩ (Fin.cases ⟨source5FaceCodes73,source5FaceRow73_checked⟩ (Fin.cases ⟨source5FaceCodes74,source5FaceRow74_checked⟩ (Fin.cases ⟨source5FaceCodes75,source5FaceRow75_checked⟩ (Fin.cases ⟨source5FaceCodes76,source5FaceRow76_checked⟩ (Fin.cases ⟨source5FaceCodes77,source5FaceRow77_checked⟩ (Fin.cases ⟨source5FaceCodes78,source5FaceRow78_checked⟩ (Fin.cases ⟨source5FaceCodes79,source5FaceRow79_checked⟩ (Fin.cases ⟨source5FaceCodes80,source5FaceRow80_checked⟩ (Fin.cases ⟨source5FaceCodes81,source5FaceRow81_checked⟩ (Fin.cases ⟨source5FaceCodes82,source5FaceRow82_checked⟩ (Fin.cases ⟨source5FaceCodes83,source5FaceRow83_checked⟩ (Fin.cases ⟨source5FaceCodes84,source5FaceRow84_checked⟩ (Fin.cases ⟨source5FaceCodes85,source5FaceRow85_checked⟩ (Fin.cases ⟨source5FaceCodes86,source5FaceRow86_checked⟩ (Fin.cases ⟨source5FaceCodes87,source5FaceRow87_checked⟩ (Fin.cases ⟨source5FaceCodes88,source5FaceRow88_checked⟩ (Fin.cases ⟨source5FaceCodes89,source5FaceRow89_checked⟩ (Fin.cases ⟨source5FaceCodes90,source5FaceRow90_checked⟩ (Fin.cases ⟨source5FaceCodes91,source5FaceRow91_checked⟩ (Fin.cases ⟨source5FaceCodes92,source5FaceRow92_checked⟩ (Fin.cases ⟨source5FaceCodes93,source5FaceRow93_checked⟩ (Fin.cases ⟨source5FaceCodes94,source5FaceRow94_checked⟩ (Fin.cases ⟨source5FaceCodes95,source5FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+96) default)
      (sourceFamily5.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes96,source5FaceRow96_checked⟩ (Fin.cases ⟨source5FaceCodes97,source5FaceRow97_checked⟩ (Fin.cases ⟨source5FaceCodes98,source5FaceRow98_checked⟩ (Fin.cases ⟨source5FaceCodes99,source5FaceRow99_checked⟩ (Fin.cases ⟨source5FaceCodes100,source5FaceRow100_checked⟩ (Fin.cases ⟨source5FaceCodes101,source5FaceRow101_checked⟩ (Fin.cases ⟨source5FaceCodes102,source5FaceRow102_checked⟩ (Fin.cases ⟨source5FaceCodes103,source5FaceRow103_checked⟩ (Fin.cases ⟨source5FaceCodes104,source5FaceRow104_checked⟩ (Fin.cases ⟨source5FaceCodes105,source5FaceRow105_checked⟩ (Fin.cases ⟨source5FaceCodes106,source5FaceRow106_checked⟩ (Fin.cases ⟨source5FaceCodes107,source5FaceRow107_checked⟩ (Fin.cases ⟨source5FaceCodes108,source5FaceRow108_checked⟩ (Fin.cases ⟨source5FaceCodes109,source5FaceRow109_checked⟩ (Fin.cases ⟨source5FaceCodes110,source5FaceRow110_checked⟩ (Fin.cases ⟨source5FaceCodes111,source5FaceRow111_checked⟩ (Fin.cases ⟨source5FaceCodes112,source5FaceRow112_checked⟩ (Fin.cases ⟨source5FaceCodes113,source5FaceRow113_checked⟩ (Fin.cases ⟨source5FaceCodes114,source5FaceRow114_checked⟩ (Fin.cases ⟨source5FaceCodes115,source5FaceRow115_checked⟩ (Fin.cases ⟨source5FaceCodes116,source5FaceRow116_checked⟩ (Fin.cases ⟨source5FaceCodes117,source5FaceRow117_checked⟩ (Fin.cases ⟨source5FaceCodes118,source5FaceRow118_checked⟩ (Fin.cases ⟨source5FaceCodes119,source5FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+120) default)
      (sourceFamily5.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes120,source5FaceRow120_checked⟩ (Fin.cases ⟨source5FaceCodes121,source5FaceRow121_checked⟩ (Fin.cases ⟨source5FaceCodes122,source5FaceRow122_checked⟩ (Fin.cases ⟨source5FaceCodes123,source5FaceRow123_checked⟩ (Fin.cases ⟨source5FaceCodes124,source5FaceRow124_checked⟩ (Fin.cases ⟨source5FaceCodes125,source5FaceRow125_checked⟩ (Fin.cases ⟨source5FaceCodes126,source5FaceRow126_checked⟩ (Fin.cases ⟨source5FaceCodes127,source5FaceRow127_checked⟩ (Fin.cases ⟨source5FaceCodes128,source5FaceRow128_checked⟩ (Fin.cases ⟨source5FaceCodes129,source5FaceRow129_checked⟩ (Fin.cases ⟨source5FaceCodes130,source5FaceRow130_checked⟩ (Fin.cases ⟨source5FaceCodes131,source5FaceRow131_checked⟩ (Fin.cases ⟨source5FaceCodes132,source5FaceRow132_checked⟩ (Fin.cases ⟨source5FaceCodes133,source5FaceRow133_checked⟩ (Fin.cases ⟨source5FaceCodes134,source5FaceRow134_checked⟩ (Fin.cases ⟨source5FaceCodes135,source5FaceRow135_checked⟩ (Fin.cases ⟨source5FaceCodes136,source5FaceRow136_checked⟩ (Fin.cases ⟨source5FaceCodes137,source5FaceRow137_checked⟩ (Fin.cases ⟨source5FaceCodes138,source5FaceRow138_checked⟩ (Fin.cases ⟨source5FaceCodes139,source5FaceRow139_checked⟩ (Fin.cases ⟨source5FaceCodes140,source5FaceRow140_checked⟩ (Fin.cases ⟨source5FaceCodes141,source5FaceRow141_checked⟩ (Fin.cases ⟨source5FaceCodes142,source5FaceRow142_checked⟩ (Fin.cases ⟨source5FaceCodes143,source5FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+144) default)
      (sourceFamily5.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes144,source5FaceRow144_checked⟩ (Fin.cases ⟨source5FaceCodes145,source5FaceRow145_checked⟩ (Fin.cases ⟨source5FaceCodes146,source5FaceRow146_checked⟩ (Fin.cases ⟨source5FaceCodes147,source5FaceRow147_checked⟩ (Fin.cases ⟨source5FaceCodes148,source5FaceRow148_checked⟩ (Fin.cases ⟨source5FaceCodes149,source5FaceRow149_checked⟩ (Fin.cases ⟨source5FaceCodes150,source5FaceRow150_checked⟩ (Fin.cases ⟨source5FaceCodes151,source5FaceRow151_checked⟩ (Fin.cases ⟨source5FaceCodes152,source5FaceRow152_checked⟩ (Fin.cases ⟨source5FaceCodes153,source5FaceRow153_checked⟩ (Fin.cases ⟨source5FaceCodes154,source5FaceRow154_checked⟩ (Fin.cases ⟨source5FaceCodes155,source5FaceRow155_checked⟩ (Fin.cases ⟨source5FaceCodes156,source5FaceRow156_checked⟩ (Fin.cases ⟨source5FaceCodes157,source5FaceRow157_checked⟩ (Fin.cases ⟨source5FaceCodes158,source5FaceRow158_checked⟩ (Fin.cases ⟨source5FaceCodes159,source5FaceRow159_checked⟩ (Fin.cases ⟨source5FaceCodes160,source5FaceRow160_checked⟩ (Fin.cases ⟨source5FaceCodes161,source5FaceRow161_checked⟩ (Fin.cases ⟨source5FaceCodes162,source5FaceRow162_checked⟩ (Fin.cases ⟨source5FaceCodes163,source5FaceRow163_checked⟩ (Fin.cases ⟨source5FaceCodes164,source5FaceRow164_checked⟩ (Fin.cases ⟨source5FaceCodes165,source5FaceRow165_checked⟩ (Fin.cases ⟨source5FaceCodes166,source5FaceRow166_checked⟩ (Fin.cases ⟨source5FaceCodes167,source5FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+168) default)
      (sourceFamily5.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes168,source5FaceRow168_checked⟩ (Fin.cases ⟨source5FaceCodes169,source5FaceRow169_checked⟩ (Fin.cases ⟨source5FaceCodes170,source5FaceRow170_checked⟩ (Fin.cases ⟨source5FaceCodes171,source5FaceRow171_checked⟩ (Fin.cases ⟨source5FaceCodes172,source5FaceRow172_checked⟩ (Fin.cases ⟨source5FaceCodes173,source5FaceRow173_checked⟩ (Fin.cases ⟨source5FaceCodes174,source5FaceRow174_checked⟩ (Fin.cases ⟨source5FaceCodes175,source5FaceRow175_checked⟩ (Fin.cases ⟨source5FaceCodes176,source5FaceRow176_checked⟩ (Fin.cases ⟨source5FaceCodes177,source5FaceRow177_checked⟩ (Fin.cases ⟨source5FaceCodes178,source5FaceRow178_checked⟩ (Fin.cases ⟨source5FaceCodes179,source5FaceRow179_checked⟩ (Fin.cases ⟨source5FaceCodes180,source5FaceRow180_checked⟩ (Fin.cases ⟨source5FaceCodes181,source5FaceRow181_checked⟩ (Fin.cases ⟨source5FaceCodes182,source5FaceRow182_checked⟩ (Fin.cases ⟨source5FaceCodes183,source5FaceRow183_checked⟩ (Fin.cases ⟨source5FaceCodes184,source5FaceRow184_checked⟩ (Fin.cases ⟨source5FaceCodes185,source5FaceRow185_checked⟩ (Fin.cases ⟨source5FaceCodes186,source5FaceRow186_checked⟩ (Fin.cases ⟨source5FaceCodes187,source5FaceRow187_checked⟩ (Fin.cases ⟨source5FaceCodes188,source5FaceRow188_checked⟩ (Fin.cases ⟨source5FaceCodes189,source5FaceRow189_checked⟩ (Fin.cases ⟨source5FaceCodes190,source5FaceRow190_checked⟩ (Fin.cases ⟨source5FaceCodes191,source5FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+192) default)
      (sourceFamily5.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes192,source5FaceRow192_checked⟩ (Fin.cases ⟨source5FaceCodes193,source5FaceRow193_checked⟩ (Fin.cases ⟨source5FaceCodes194,source5FaceRow194_checked⟩ (Fin.cases ⟨source5FaceCodes195,source5FaceRow195_checked⟩ (Fin.cases ⟨source5FaceCodes196,source5FaceRow196_checked⟩ (Fin.cases ⟨source5FaceCodes197,source5FaceRow197_checked⟩ (Fin.cases ⟨source5FaceCodes198,source5FaceRow198_checked⟩ (Fin.cases ⟨source5FaceCodes199,source5FaceRow199_checked⟩ (Fin.cases ⟨source5FaceCodes200,source5FaceRow200_checked⟩ (Fin.cases ⟨source5FaceCodes201,source5FaceRow201_checked⟩ (Fin.cases ⟨source5FaceCodes202,source5FaceRow202_checked⟩ (Fin.cases ⟨source5FaceCodes203,source5FaceRow203_checked⟩ (Fin.cases ⟨source5FaceCodes204,source5FaceRow204_checked⟩ (Fin.cases ⟨source5FaceCodes205,source5FaceRow205_checked⟩ (Fin.cases ⟨source5FaceCodes206,source5FaceRow206_checked⟩ (Fin.cases ⟨source5FaceCodes207,source5FaceRow207_checked⟩ (Fin.cases ⟨source5FaceCodes208,source5FaceRow208_checked⟩ (Fin.cases ⟨source5FaceCodes209,source5FaceRow209_checked⟩ (Fin.cases ⟨source5FaceCodes210,source5FaceRow210_checked⟩ (Fin.cases ⟨source5FaceCodes211,source5FaceRow211_checked⟩ (Fin.cases ⟨source5FaceCodes212,source5FaceRow212_checked⟩ (Fin.cases ⟨source5FaceCodes213,source5FaceRow213_checked⟩ (Fin.cases ⟨source5FaceCodes214,source5FaceRow214_checked⟩ (Fin.cases ⟨source5FaceCodes215,source5FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source5FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily5.getD (j.val+216) default)
      (sourceFamily5.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source5FaceCodes216,source5FaceRow216_checked⟩ (Fin.cases ⟨source5FaceCodes217,source5FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source5AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily5.getD i.val default)
      (sourceFamily5.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source5FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
