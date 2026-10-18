module

public import SpectreGeometry.ReverseClusterTriangulationSource07Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource07Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source7Family_length : sourceFamily7.length = 218 := by decide

theorem source7FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+0) default)
      (sourceFamily7.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes0,source7FaceRow0_checked⟩ (Fin.cases ⟨source7FaceCodes1,source7FaceRow1_checked⟩ (Fin.cases ⟨source7FaceCodes2,source7FaceRow2_checked⟩ (Fin.cases ⟨source7FaceCodes3,source7FaceRow3_checked⟩ (Fin.cases ⟨source7FaceCodes4,source7FaceRow4_checked⟩ (Fin.cases ⟨source7FaceCodes5,source7FaceRow5_checked⟩ (Fin.cases ⟨source7FaceCodes6,source7FaceRow6_checked⟩ (Fin.cases ⟨source7FaceCodes7,source7FaceRow7_checked⟩ (Fin.cases ⟨source7FaceCodes8,source7FaceRow8_checked⟩ (Fin.cases ⟨source7FaceCodes9,source7FaceRow9_checked⟩ (Fin.cases ⟨source7FaceCodes10,source7FaceRow10_checked⟩ (Fin.cases ⟨source7FaceCodes11,source7FaceRow11_checked⟩ (Fin.cases ⟨source7FaceCodes12,source7FaceRow12_checked⟩ (Fin.cases ⟨source7FaceCodes13,source7FaceRow13_checked⟩ (Fin.cases ⟨source7FaceCodes14,source7FaceRow14_checked⟩ (Fin.cases ⟨source7FaceCodes15,source7FaceRow15_checked⟩ (Fin.cases ⟨source7FaceCodes16,source7FaceRow16_checked⟩ (Fin.cases ⟨source7FaceCodes17,source7FaceRow17_checked⟩ (Fin.cases ⟨source7FaceCodes18,source7FaceRow18_checked⟩ (Fin.cases ⟨source7FaceCodes19,source7FaceRow19_checked⟩ (Fin.cases ⟨source7FaceCodes20,source7FaceRow20_checked⟩ (Fin.cases ⟨source7FaceCodes21,source7FaceRow21_checked⟩ (Fin.cases ⟨source7FaceCodes22,source7FaceRow22_checked⟩ (Fin.cases ⟨source7FaceCodes23,source7FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+24) default)
      (sourceFamily7.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes24,source7FaceRow24_checked⟩ (Fin.cases ⟨source7FaceCodes25,source7FaceRow25_checked⟩ (Fin.cases ⟨source7FaceCodes26,source7FaceRow26_checked⟩ (Fin.cases ⟨source7FaceCodes27,source7FaceRow27_checked⟩ (Fin.cases ⟨source7FaceCodes28,source7FaceRow28_checked⟩ (Fin.cases ⟨source7FaceCodes29,source7FaceRow29_checked⟩ (Fin.cases ⟨source7FaceCodes30,source7FaceRow30_checked⟩ (Fin.cases ⟨source7FaceCodes31,source7FaceRow31_checked⟩ (Fin.cases ⟨source7FaceCodes32,source7FaceRow32_checked⟩ (Fin.cases ⟨source7FaceCodes33,source7FaceRow33_checked⟩ (Fin.cases ⟨source7FaceCodes34,source7FaceRow34_checked⟩ (Fin.cases ⟨source7FaceCodes35,source7FaceRow35_checked⟩ (Fin.cases ⟨source7FaceCodes36,source7FaceRow36_checked⟩ (Fin.cases ⟨source7FaceCodes37,source7FaceRow37_checked⟩ (Fin.cases ⟨source7FaceCodes38,source7FaceRow38_checked⟩ (Fin.cases ⟨source7FaceCodes39,source7FaceRow39_checked⟩ (Fin.cases ⟨source7FaceCodes40,source7FaceRow40_checked⟩ (Fin.cases ⟨source7FaceCodes41,source7FaceRow41_checked⟩ (Fin.cases ⟨source7FaceCodes42,source7FaceRow42_checked⟩ (Fin.cases ⟨source7FaceCodes43,source7FaceRow43_checked⟩ (Fin.cases ⟨source7FaceCodes44,source7FaceRow44_checked⟩ (Fin.cases ⟨source7FaceCodes45,source7FaceRow45_checked⟩ (Fin.cases ⟨source7FaceCodes46,source7FaceRow46_checked⟩ (Fin.cases ⟨source7FaceCodes47,source7FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+48) default)
      (sourceFamily7.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes48,source7FaceRow48_checked⟩ (Fin.cases ⟨source7FaceCodes49,source7FaceRow49_checked⟩ (Fin.cases ⟨source7FaceCodes50,source7FaceRow50_checked⟩ (Fin.cases ⟨source7FaceCodes51,source7FaceRow51_checked⟩ (Fin.cases ⟨source7FaceCodes52,source7FaceRow52_checked⟩ (Fin.cases ⟨source7FaceCodes53,source7FaceRow53_checked⟩ (Fin.cases ⟨source7FaceCodes54,source7FaceRow54_checked⟩ (Fin.cases ⟨source7FaceCodes55,source7FaceRow55_checked⟩ (Fin.cases ⟨source7FaceCodes56,source7FaceRow56_checked⟩ (Fin.cases ⟨source7FaceCodes57,source7FaceRow57_checked⟩ (Fin.cases ⟨source7FaceCodes58,source7FaceRow58_checked⟩ (Fin.cases ⟨source7FaceCodes59,source7FaceRow59_checked⟩ (Fin.cases ⟨source7FaceCodes60,source7FaceRow60_checked⟩ (Fin.cases ⟨source7FaceCodes61,source7FaceRow61_checked⟩ (Fin.cases ⟨source7FaceCodes62,source7FaceRow62_checked⟩ (Fin.cases ⟨source7FaceCodes63,source7FaceRow63_checked⟩ (Fin.cases ⟨source7FaceCodes64,source7FaceRow64_checked⟩ (Fin.cases ⟨source7FaceCodes65,source7FaceRow65_checked⟩ (Fin.cases ⟨source7FaceCodes66,source7FaceRow66_checked⟩ (Fin.cases ⟨source7FaceCodes67,source7FaceRow67_checked⟩ (Fin.cases ⟨source7FaceCodes68,source7FaceRow68_checked⟩ (Fin.cases ⟨source7FaceCodes69,source7FaceRow69_checked⟩ (Fin.cases ⟨source7FaceCodes70,source7FaceRow70_checked⟩ (Fin.cases ⟨source7FaceCodes71,source7FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+72) default)
      (sourceFamily7.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes72,source7FaceRow72_checked⟩ (Fin.cases ⟨source7FaceCodes73,source7FaceRow73_checked⟩ (Fin.cases ⟨source7FaceCodes74,source7FaceRow74_checked⟩ (Fin.cases ⟨source7FaceCodes75,source7FaceRow75_checked⟩ (Fin.cases ⟨source7FaceCodes76,source7FaceRow76_checked⟩ (Fin.cases ⟨source7FaceCodes77,source7FaceRow77_checked⟩ (Fin.cases ⟨source7FaceCodes78,source7FaceRow78_checked⟩ (Fin.cases ⟨source7FaceCodes79,source7FaceRow79_checked⟩ (Fin.cases ⟨source7FaceCodes80,source7FaceRow80_checked⟩ (Fin.cases ⟨source7FaceCodes81,source7FaceRow81_checked⟩ (Fin.cases ⟨source7FaceCodes82,source7FaceRow82_checked⟩ (Fin.cases ⟨source7FaceCodes83,source7FaceRow83_checked⟩ (Fin.cases ⟨source7FaceCodes84,source7FaceRow84_checked⟩ (Fin.cases ⟨source7FaceCodes85,source7FaceRow85_checked⟩ (Fin.cases ⟨source7FaceCodes86,source7FaceRow86_checked⟩ (Fin.cases ⟨source7FaceCodes87,source7FaceRow87_checked⟩ (Fin.cases ⟨source7FaceCodes88,source7FaceRow88_checked⟩ (Fin.cases ⟨source7FaceCodes89,source7FaceRow89_checked⟩ (Fin.cases ⟨source7FaceCodes90,source7FaceRow90_checked⟩ (Fin.cases ⟨source7FaceCodes91,source7FaceRow91_checked⟩ (Fin.cases ⟨source7FaceCodes92,source7FaceRow92_checked⟩ (Fin.cases ⟨source7FaceCodes93,source7FaceRow93_checked⟩ (Fin.cases ⟨source7FaceCodes94,source7FaceRow94_checked⟩ (Fin.cases ⟨source7FaceCodes95,source7FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+96) default)
      (sourceFamily7.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes96,source7FaceRow96_checked⟩ (Fin.cases ⟨source7FaceCodes97,source7FaceRow97_checked⟩ (Fin.cases ⟨source7FaceCodes98,source7FaceRow98_checked⟩ (Fin.cases ⟨source7FaceCodes99,source7FaceRow99_checked⟩ (Fin.cases ⟨source7FaceCodes100,source7FaceRow100_checked⟩ (Fin.cases ⟨source7FaceCodes101,source7FaceRow101_checked⟩ (Fin.cases ⟨source7FaceCodes102,source7FaceRow102_checked⟩ (Fin.cases ⟨source7FaceCodes103,source7FaceRow103_checked⟩ (Fin.cases ⟨source7FaceCodes104,source7FaceRow104_checked⟩ (Fin.cases ⟨source7FaceCodes105,source7FaceRow105_checked⟩ (Fin.cases ⟨source7FaceCodes106,source7FaceRow106_checked⟩ (Fin.cases ⟨source7FaceCodes107,source7FaceRow107_checked⟩ (Fin.cases ⟨source7FaceCodes108,source7FaceRow108_checked⟩ (Fin.cases ⟨source7FaceCodes109,source7FaceRow109_checked⟩ (Fin.cases ⟨source7FaceCodes110,source7FaceRow110_checked⟩ (Fin.cases ⟨source7FaceCodes111,source7FaceRow111_checked⟩ (Fin.cases ⟨source7FaceCodes112,source7FaceRow112_checked⟩ (Fin.cases ⟨source7FaceCodes113,source7FaceRow113_checked⟩ (Fin.cases ⟨source7FaceCodes114,source7FaceRow114_checked⟩ (Fin.cases ⟨source7FaceCodes115,source7FaceRow115_checked⟩ (Fin.cases ⟨source7FaceCodes116,source7FaceRow116_checked⟩ (Fin.cases ⟨source7FaceCodes117,source7FaceRow117_checked⟩ (Fin.cases ⟨source7FaceCodes118,source7FaceRow118_checked⟩ (Fin.cases ⟨source7FaceCodes119,source7FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+120) default)
      (sourceFamily7.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes120,source7FaceRow120_checked⟩ (Fin.cases ⟨source7FaceCodes121,source7FaceRow121_checked⟩ (Fin.cases ⟨source7FaceCodes122,source7FaceRow122_checked⟩ (Fin.cases ⟨source7FaceCodes123,source7FaceRow123_checked⟩ (Fin.cases ⟨source7FaceCodes124,source7FaceRow124_checked⟩ (Fin.cases ⟨source7FaceCodes125,source7FaceRow125_checked⟩ (Fin.cases ⟨source7FaceCodes126,source7FaceRow126_checked⟩ (Fin.cases ⟨source7FaceCodes127,source7FaceRow127_checked⟩ (Fin.cases ⟨source7FaceCodes128,source7FaceRow128_checked⟩ (Fin.cases ⟨source7FaceCodes129,source7FaceRow129_checked⟩ (Fin.cases ⟨source7FaceCodes130,source7FaceRow130_checked⟩ (Fin.cases ⟨source7FaceCodes131,source7FaceRow131_checked⟩ (Fin.cases ⟨source7FaceCodes132,source7FaceRow132_checked⟩ (Fin.cases ⟨source7FaceCodes133,source7FaceRow133_checked⟩ (Fin.cases ⟨source7FaceCodes134,source7FaceRow134_checked⟩ (Fin.cases ⟨source7FaceCodes135,source7FaceRow135_checked⟩ (Fin.cases ⟨source7FaceCodes136,source7FaceRow136_checked⟩ (Fin.cases ⟨source7FaceCodes137,source7FaceRow137_checked⟩ (Fin.cases ⟨source7FaceCodes138,source7FaceRow138_checked⟩ (Fin.cases ⟨source7FaceCodes139,source7FaceRow139_checked⟩ (Fin.cases ⟨source7FaceCodes140,source7FaceRow140_checked⟩ (Fin.cases ⟨source7FaceCodes141,source7FaceRow141_checked⟩ (Fin.cases ⟨source7FaceCodes142,source7FaceRow142_checked⟩ (Fin.cases ⟨source7FaceCodes143,source7FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+144) default)
      (sourceFamily7.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes144,source7FaceRow144_checked⟩ (Fin.cases ⟨source7FaceCodes145,source7FaceRow145_checked⟩ (Fin.cases ⟨source7FaceCodes146,source7FaceRow146_checked⟩ (Fin.cases ⟨source7FaceCodes147,source7FaceRow147_checked⟩ (Fin.cases ⟨source7FaceCodes148,source7FaceRow148_checked⟩ (Fin.cases ⟨source7FaceCodes149,source7FaceRow149_checked⟩ (Fin.cases ⟨source7FaceCodes150,source7FaceRow150_checked⟩ (Fin.cases ⟨source7FaceCodes151,source7FaceRow151_checked⟩ (Fin.cases ⟨source7FaceCodes152,source7FaceRow152_checked⟩ (Fin.cases ⟨source7FaceCodes153,source7FaceRow153_checked⟩ (Fin.cases ⟨source7FaceCodes154,source7FaceRow154_checked⟩ (Fin.cases ⟨source7FaceCodes155,source7FaceRow155_checked⟩ (Fin.cases ⟨source7FaceCodes156,source7FaceRow156_checked⟩ (Fin.cases ⟨source7FaceCodes157,source7FaceRow157_checked⟩ (Fin.cases ⟨source7FaceCodes158,source7FaceRow158_checked⟩ (Fin.cases ⟨source7FaceCodes159,source7FaceRow159_checked⟩ (Fin.cases ⟨source7FaceCodes160,source7FaceRow160_checked⟩ (Fin.cases ⟨source7FaceCodes161,source7FaceRow161_checked⟩ (Fin.cases ⟨source7FaceCodes162,source7FaceRow162_checked⟩ (Fin.cases ⟨source7FaceCodes163,source7FaceRow163_checked⟩ (Fin.cases ⟨source7FaceCodes164,source7FaceRow164_checked⟩ (Fin.cases ⟨source7FaceCodes165,source7FaceRow165_checked⟩ (Fin.cases ⟨source7FaceCodes166,source7FaceRow166_checked⟩ (Fin.cases ⟨source7FaceCodes167,source7FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+168) default)
      (sourceFamily7.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes168,source7FaceRow168_checked⟩ (Fin.cases ⟨source7FaceCodes169,source7FaceRow169_checked⟩ (Fin.cases ⟨source7FaceCodes170,source7FaceRow170_checked⟩ (Fin.cases ⟨source7FaceCodes171,source7FaceRow171_checked⟩ (Fin.cases ⟨source7FaceCodes172,source7FaceRow172_checked⟩ (Fin.cases ⟨source7FaceCodes173,source7FaceRow173_checked⟩ (Fin.cases ⟨source7FaceCodes174,source7FaceRow174_checked⟩ (Fin.cases ⟨source7FaceCodes175,source7FaceRow175_checked⟩ (Fin.cases ⟨source7FaceCodes176,source7FaceRow176_checked⟩ (Fin.cases ⟨source7FaceCodes177,source7FaceRow177_checked⟩ (Fin.cases ⟨source7FaceCodes178,source7FaceRow178_checked⟩ (Fin.cases ⟨source7FaceCodes179,source7FaceRow179_checked⟩ (Fin.cases ⟨source7FaceCodes180,source7FaceRow180_checked⟩ (Fin.cases ⟨source7FaceCodes181,source7FaceRow181_checked⟩ (Fin.cases ⟨source7FaceCodes182,source7FaceRow182_checked⟩ (Fin.cases ⟨source7FaceCodes183,source7FaceRow183_checked⟩ (Fin.cases ⟨source7FaceCodes184,source7FaceRow184_checked⟩ (Fin.cases ⟨source7FaceCodes185,source7FaceRow185_checked⟩ (Fin.cases ⟨source7FaceCodes186,source7FaceRow186_checked⟩ (Fin.cases ⟨source7FaceCodes187,source7FaceRow187_checked⟩ (Fin.cases ⟨source7FaceCodes188,source7FaceRow188_checked⟩ (Fin.cases ⟨source7FaceCodes189,source7FaceRow189_checked⟩ (Fin.cases ⟨source7FaceCodes190,source7FaceRow190_checked⟩ (Fin.cases ⟨source7FaceCodes191,source7FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+192) default)
      (sourceFamily7.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes192,source7FaceRow192_checked⟩ (Fin.cases ⟨source7FaceCodes193,source7FaceRow193_checked⟩ (Fin.cases ⟨source7FaceCodes194,source7FaceRow194_checked⟩ (Fin.cases ⟨source7FaceCodes195,source7FaceRow195_checked⟩ (Fin.cases ⟨source7FaceCodes196,source7FaceRow196_checked⟩ (Fin.cases ⟨source7FaceCodes197,source7FaceRow197_checked⟩ (Fin.cases ⟨source7FaceCodes198,source7FaceRow198_checked⟩ (Fin.cases ⟨source7FaceCodes199,source7FaceRow199_checked⟩ (Fin.cases ⟨source7FaceCodes200,source7FaceRow200_checked⟩ (Fin.cases ⟨source7FaceCodes201,source7FaceRow201_checked⟩ (Fin.cases ⟨source7FaceCodes202,source7FaceRow202_checked⟩ (Fin.cases ⟨source7FaceCodes203,source7FaceRow203_checked⟩ (Fin.cases ⟨source7FaceCodes204,source7FaceRow204_checked⟩ (Fin.cases ⟨source7FaceCodes205,source7FaceRow205_checked⟩ (Fin.cases ⟨source7FaceCodes206,source7FaceRow206_checked⟩ (Fin.cases ⟨source7FaceCodes207,source7FaceRow207_checked⟩ (Fin.cases ⟨source7FaceCodes208,source7FaceRow208_checked⟩ (Fin.cases ⟨source7FaceCodes209,source7FaceRow209_checked⟩ (Fin.cases ⟨source7FaceCodes210,source7FaceRow210_checked⟩ (Fin.cases ⟨source7FaceCodes211,source7FaceRow211_checked⟩ (Fin.cases ⟨source7FaceCodes212,source7FaceRow212_checked⟩ (Fin.cases ⟨source7FaceCodes213,source7FaceRow213_checked⟩ (Fin.cases ⟨source7FaceCodes214,source7FaceRow214_checked⟩ (Fin.cases ⟨source7FaceCodes215,source7FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source7FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily7.getD (j.val+216) default)
      (sourceFamily7.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source7FaceCodes216,source7FaceRow216_checked⟩ (Fin.cases ⟨source7FaceCodes217,source7FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source7AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily7.getD i.val default)
      (sourceFamily7.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source7FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
