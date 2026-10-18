module

public import SpectreGeometry.ReverseClusterTriangulationSource04Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource04Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source4Family_length : sourceFamily4.length = 218 := by decide

theorem source4FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+0) default)
      (sourceFamily4.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes0,source4FaceRow0_checked⟩ (Fin.cases ⟨source4FaceCodes1,source4FaceRow1_checked⟩ (Fin.cases ⟨source4FaceCodes2,source4FaceRow2_checked⟩ (Fin.cases ⟨source4FaceCodes3,source4FaceRow3_checked⟩ (Fin.cases ⟨source4FaceCodes4,source4FaceRow4_checked⟩ (Fin.cases ⟨source4FaceCodes5,source4FaceRow5_checked⟩ (Fin.cases ⟨source4FaceCodes6,source4FaceRow6_checked⟩ (Fin.cases ⟨source4FaceCodes7,source4FaceRow7_checked⟩ (Fin.cases ⟨source4FaceCodes8,source4FaceRow8_checked⟩ (Fin.cases ⟨source4FaceCodes9,source4FaceRow9_checked⟩ (Fin.cases ⟨source4FaceCodes10,source4FaceRow10_checked⟩ (Fin.cases ⟨source4FaceCodes11,source4FaceRow11_checked⟩ (Fin.cases ⟨source4FaceCodes12,source4FaceRow12_checked⟩ (Fin.cases ⟨source4FaceCodes13,source4FaceRow13_checked⟩ (Fin.cases ⟨source4FaceCodes14,source4FaceRow14_checked⟩ (Fin.cases ⟨source4FaceCodes15,source4FaceRow15_checked⟩ (Fin.cases ⟨source4FaceCodes16,source4FaceRow16_checked⟩ (Fin.cases ⟨source4FaceCodes17,source4FaceRow17_checked⟩ (Fin.cases ⟨source4FaceCodes18,source4FaceRow18_checked⟩ (Fin.cases ⟨source4FaceCodes19,source4FaceRow19_checked⟩ (Fin.cases ⟨source4FaceCodes20,source4FaceRow20_checked⟩ (Fin.cases ⟨source4FaceCodes21,source4FaceRow21_checked⟩ (Fin.cases ⟨source4FaceCodes22,source4FaceRow22_checked⟩ (Fin.cases ⟨source4FaceCodes23,source4FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+24) default)
      (sourceFamily4.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes24,source4FaceRow24_checked⟩ (Fin.cases ⟨source4FaceCodes25,source4FaceRow25_checked⟩ (Fin.cases ⟨source4FaceCodes26,source4FaceRow26_checked⟩ (Fin.cases ⟨source4FaceCodes27,source4FaceRow27_checked⟩ (Fin.cases ⟨source4FaceCodes28,source4FaceRow28_checked⟩ (Fin.cases ⟨source4FaceCodes29,source4FaceRow29_checked⟩ (Fin.cases ⟨source4FaceCodes30,source4FaceRow30_checked⟩ (Fin.cases ⟨source4FaceCodes31,source4FaceRow31_checked⟩ (Fin.cases ⟨source4FaceCodes32,source4FaceRow32_checked⟩ (Fin.cases ⟨source4FaceCodes33,source4FaceRow33_checked⟩ (Fin.cases ⟨source4FaceCodes34,source4FaceRow34_checked⟩ (Fin.cases ⟨source4FaceCodes35,source4FaceRow35_checked⟩ (Fin.cases ⟨source4FaceCodes36,source4FaceRow36_checked⟩ (Fin.cases ⟨source4FaceCodes37,source4FaceRow37_checked⟩ (Fin.cases ⟨source4FaceCodes38,source4FaceRow38_checked⟩ (Fin.cases ⟨source4FaceCodes39,source4FaceRow39_checked⟩ (Fin.cases ⟨source4FaceCodes40,source4FaceRow40_checked⟩ (Fin.cases ⟨source4FaceCodes41,source4FaceRow41_checked⟩ (Fin.cases ⟨source4FaceCodes42,source4FaceRow42_checked⟩ (Fin.cases ⟨source4FaceCodes43,source4FaceRow43_checked⟩ (Fin.cases ⟨source4FaceCodes44,source4FaceRow44_checked⟩ (Fin.cases ⟨source4FaceCodes45,source4FaceRow45_checked⟩ (Fin.cases ⟨source4FaceCodes46,source4FaceRow46_checked⟩ (Fin.cases ⟨source4FaceCodes47,source4FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+48) default)
      (sourceFamily4.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes48,source4FaceRow48_checked⟩ (Fin.cases ⟨source4FaceCodes49,source4FaceRow49_checked⟩ (Fin.cases ⟨source4FaceCodes50,source4FaceRow50_checked⟩ (Fin.cases ⟨source4FaceCodes51,source4FaceRow51_checked⟩ (Fin.cases ⟨source4FaceCodes52,source4FaceRow52_checked⟩ (Fin.cases ⟨source4FaceCodes53,source4FaceRow53_checked⟩ (Fin.cases ⟨source4FaceCodes54,source4FaceRow54_checked⟩ (Fin.cases ⟨source4FaceCodes55,source4FaceRow55_checked⟩ (Fin.cases ⟨source4FaceCodes56,source4FaceRow56_checked⟩ (Fin.cases ⟨source4FaceCodes57,source4FaceRow57_checked⟩ (Fin.cases ⟨source4FaceCodes58,source4FaceRow58_checked⟩ (Fin.cases ⟨source4FaceCodes59,source4FaceRow59_checked⟩ (Fin.cases ⟨source4FaceCodes60,source4FaceRow60_checked⟩ (Fin.cases ⟨source4FaceCodes61,source4FaceRow61_checked⟩ (Fin.cases ⟨source4FaceCodes62,source4FaceRow62_checked⟩ (Fin.cases ⟨source4FaceCodes63,source4FaceRow63_checked⟩ (Fin.cases ⟨source4FaceCodes64,source4FaceRow64_checked⟩ (Fin.cases ⟨source4FaceCodes65,source4FaceRow65_checked⟩ (Fin.cases ⟨source4FaceCodes66,source4FaceRow66_checked⟩ (Fin.cases ⟨source4FaceCodes67,source4FaceRow67_checked⟩ (Fin.cases ⟨source4FaceCodes68,source4FaceRow68_checked⟩ (Fin.cases ⟨source4FaceCodes69,source4FaceRow69_checked⟩ (Fin.cases ⟨source4FaceCodes70,source4FaceRow70_checked⟩ (Fin.cases ⟨source4FaceCodes71,source4FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+72) default)
      (sourceFamily4.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes72,source4FaceRow72_checked⟩ (Fin.cases ⟨source4FaceCodes73,source4FaceRow73_checked⟩ (Fin.cases ⟨source4FaceCodes74,source4FaceRow74_checked⟩ (Fin.cases ⟨source4FaceCodes75,source4FaceRow75_checked⟩ (Fin.cases ⟨source4FaceCodes76,source4FaceRow76_checked⟩ (Fin.cases ⟨source4FaceCodes77,source4FaceRow77_checked⟩ (Fin.cases ⟨source4FaceCodes78,source4FaceRow78_checked⟩ (Fin.cases ⟨source4FaceCodes79,source4FaceRow79_checked⟩ (Fin.cases ⟨source4FaceCodes80,source4FaceRow80_checked⟩ (Fin.cases ⟨source4FaceCodes81,source4FaceRow81_checked⟩ (Fin.cases ⟨source4FaceCodes82,source4FaceRow82_checked⟩ (Fin.cases ⟨source4FaceCodes83,source4FaceRow83_checked⟩ (Fin.cases ⟨source4FaceCodes84,source4FaceRow84_checked⟩ (Fin.cases ⟨source4FaceCodes85,source4FaceRow85_checked⟩ (Fin.cases ⟨source4FaceCodes86,source4FaceRow86_checked⟩ (Fin.cases ⟨source4FaceCodes87,source4FaceRow87_checked⟩ (Fin.cases ⟨source4FaceCodes88,source4FaceRow88_checked⟩ (Fin.cases ⟨source4FaceCodes89,source4FaceRow89_checked⟩ (Fin.cases ⟨source4FaceCodes90,source4FaceRow90_checked⟩ (Fin.cases ⟨source4FaceCodes91,source4FaceRow91_checked⟩ (Fin.cases ⟨source4FaceCodes92,source4FaceRow92_checked⟩ (Fin.cases ⟨source4FaceCodes93,source4FaceRow93_checked⟩ (Fin.cases ⟨source4FaceCodes94,source4FaceRow94_checked⟩ (Fin.cases ⟨source4FaceCodes95,source4FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+96) default)
      (sourceFamily4.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes96,source4FaceRow96_checked⟩ (Fin.cases ⟨source4FaceCodes97,source4FaceRow97_checked⟩ (Fin.cases ⟨source4FaceCodes98,source4FaceRow98_checked⟩ (Fin.cases ⟨source4FaceCodes99,source4FaceRow99_checked⟩ (Fin.cases ⟨source4FaceCodes100,source4FaceRow100_checked⟩ (Fin.cases ⟨source4FaceCodes101,source4FaceRow101_checked⟩ (Fin.cases ⟨source4FaceCodes102,source4FaceRow102_checked⟩ (Fin.cases ⟨source4FaceCodes103,source4FaceRow103_checked⟩ (Fin.cases ⟨source4FaceCodes104,source4FaceRow104_checked⟩ (Fin.cases ⟨source4FaceCodes105,source4FaceRow105_checked⟩ (Fin.cases ⟨source4FaceCodes106,source4FaceRow106_checked⟩ (Fin.cases ⟨source4FaceCodes107,source4FaceRow107_checked⟩ (Fin.cases ⟨source4FaceCodes108,source4FaceRow108_checked⟩ (Fin.cases ⟨source4FaceCodes109,source4FaceRow109_checked⟩ (Fin.cases ⟨source4FaceCodes110,source4FaceRow110_checked⟩ (Fin.cases ⟨source4FaceCodes111,source4FaceRow111_checked⟩ (Fin.cases ⟨source4FaceCodes112,source4FaceRow112_checked⟩ (Fin.cases ⟨source4FaceCodes113,source4FaceRow113_checked⟩ (Fin.cases ⟨source4FaceCodes114,source4FaceRow114_checked⟩ (Fin.cases ⟨source4FaceCodes115,source4FaceRow115_checked⟩ (Fin.cases ⟨source4FaceCodes116,source4FaceRow116_checked⟩ (Fin.cases ⟨source4FaceCodes117,source4FaceRow117_checked⟩ (Fin.cases ⟨source4FaceCodes118,source4FaceRow118_checked⟩ (Fin.cases ⟨source4FaceCodes119,source4FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+120) default)
      (sourceFamily4.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes120,source4FaceRow120_checked⟩ (Fin.cases ⟨source4FaceCodes121,source4FaceRow121_checked⟩ (Fin.cases ⟨source4FaceCodes122,source4FaceRow122_checked⟩ (Fin.cases ⟨source4FaceCodes123,source4FaceRow123_checked⟩ (Fin.cases ⟨source4FaceCodes124,source4FaceRow124_checked⟩ (Fin.cases ⟨source4FaceCodes125,source4FaceRow125_checked⟩ (Fin.cases ⟨source4FaceCodes126,source4FaceRow126_checked⟩ (Fin.cases ⟨source4FaceCodes127,source4FaceRow127_checked⟩ (Fin.cases ⟨source4FaceCodes128,source4FaceRow128_checked⟩ (Fin.cases ⟨source4FaceCodes129,source4FaceRow129_checked⟩ (Fin.cases ⟨source4FaceCodes130,source4FaceRow130_checked⟩ (Fin.cases ⟨source4FaceCodes131,source4FaceRow131_checked⟩ (Fin.cases ⟨source4FaceCodes132,source4FaceRow132_checked⟩ (Fin.cases ⟨source4FaceCodes133,source4FaceRow133_checked⟩ (Fin.cases ⟨source4FaceCodes134,source4FaceRow134_checked⟩ (Fin.cases ⟨source4FaceCodes135,source4FaceRow135_checked⟩ (Fin.cases ⟨source4FaceCodes136,source4FaceRow136_checked⟩ (Fin.cases ⟨source4FaceCodes137,source4FaceRow137_checked⟩ (Fin.cases ⟨source4FaceCodes138,source4FaceRow138_checked⟩ (Fin.cases ⟨source4FaceCodes139,source4FaceRow139_checked⟩ (Fin.cases ⟨source4FaceCodes140,source4FaceRow140_checked⟩ (Fin.cases ⟨source4FaceCodes141,source4FaceRow141_checked⟩ (Fin.cases ⟨source4FaceCodes142,source4FaceRow142_checked⟩ (Fin.cases ⟨source4FaceCodes143,source4FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+144) default)
      (sourceFamily4.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes144,source4FaceRow144_checked⟩ (Fin.cases ⟨source4FaceCodes145,source4FaceRow145_checked⟩ (Fin.cases ⟨source4FaceCodes146,source4FaceRow146_checked⟩ (Fin.cases ⟨source4FaceCodes147,source4FaceRow147_checked⟩ (Fin.cases ⟨source4FaceCodes148,source4FaceRow148_checked⟩ (Fin.cases ⟨source4FaceCodes149,source4FaceRow149_checked⟩ (Fin.cases ⟨source4FaceCodes150,source4FaceRow150_checked⟩ (Fin.cases ⟨source4FaceCodes151,source4FaceRow151_checked⟩ (Fin.cases ⟨source4FaceCodes152,source4FaceRow152_checked⟩ (Fin.cases ⟨source4FaceCodes153,source4FaceRow153_checked⟩ (Fin.cases ⟨source4FaceCodes154,source4FaceRow154_checked⟩ (Fin.cases ⟨source4FaceCodes155,source4FaceRow155_checked⟩ (Fin.cases ⟨source4FaceCodes156,source4FaceRow156_checked⟩ (Fin.cases ⟨source4FaceCodes157,source4FaceRow157_checked⟩ (Fin.cases ⟨source4FaceCodes158,source4FaceRow158_checked⟩ (Fin.cases ⟨source4FaceCodes159,source4FaceRow159_checked⟩ (Fin.cases ⟨source4FaceCodes160,source4FaceRow160_checked⟩ (Fin.cases ⟨source4FaceCodes161,source4FaceRow161_checked⟩ (Fin.cases ⟨source4FaceCodes162,source4FaceRow162_checked⟩ (Fin.cases ⟨source4FaceCodes163,source4FaceRow163_checked⟩ (Fin.cases ⟨source4FaceCodes164,source4FaceRow164_checked⟩ (Fin.cases ⟨source4FaceCodes165,source4FaceRow165_checked⟩ (Fin.cases ⟨source4FaceCodes166,source4FaceRow166_checked⟩ (Fin.cases ⟨source4FaceCodes167,source4FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+168) default)
      (sourceFamily4.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes168,source4FaceRow168_checked⟩ (Fin.cases ⟨source4FaceCodes169,source4FaceRow169_checked⟩ (Fin.cases ⟨source4FaceCodes170,source4FaceRow170_checked⟩ (Fin.cases ⟨source4FaceCodes171,source4FaceRow171_checked⟩ (Fin.cases ⟨source4FaceCodes172,source4FaceRow172_checked⟩ (Fin.cases ⟨source4FaceCodes173,source4FaceRow173_checked⟩ (Fin.cases ⟨source4FaceCodes174,source4FaceRow174_checked⟩ (Fin.cases ⟨source4FaceCodes175,source4FaceRow175_checked⟩ (Fin.cases ⟨source4FaceCodes176,source4FaceRow176_checked⟩ (Fin.cases ⟨source4FaceCodes177,source4FaceRow177_checked⟩ (Fin.cases ⟨source4FaceCodes178,source4FaceRow178_checked⟩ (Fin.cases ⟨source4FaceCodes179,source4FaceRow179_checked⟩ (Fin.cases ⟨source4FaceCodes180,source4FaceRow180_checked⟩ (Fin.cases ⟨source4FaceCodes181,source4FaceRow181_checked⟩ (Fin.cases ⟨source4FaceCodes182,source4FaceRow182_checked⟩ (Fin.cases ⟨source4FaceCodes183,source4FaceRow183_checked⟩ (Fin.cases ⟨source4FaceCodes184,source4FaceRow184_checked⟩ (Fin.cases ⟨source4FaceCodes185,source4FaceRow185_checked⟩ (Fin.cases ⟨source4FaceCodes186,source4FaceRow186_checked⟩ (Fin.cases ⟨source4FaceCodes187,source4FaceRow187_checked⟩ (Fin.cases ⟨source4FaceCodes188,source4FaceRow188_checked⟩ (Fin.cases ⟨source4FaceCodes189,source4FaceRow189_checked⟩ (Fin.cases ⟨source4FaceCodes190,source4FaceRow190_checked⟩ (Fin.cases ⟨source4FaceCodes191,source4FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+192) default)
      (sourceFamily4.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes192,source4FaceRow192_checked⟩ (Fin.cases ⟨source4FaceCodes193,source4FaceRow193_checked⟩ (Fin.cases ⟨source4FaceCodes194,source4FaceRow194_checked⟩ (Fin.cases ⟨source4FaceCodes195,source4FaceRow195_checked⟩ (Fin.cases ⟨source4FaceCodes196,source4FaceRow196_checked⟩ (Fin.cases ⟨source4FaceCodes197,source4FaceRow197_checked⟩ (Fin.cases ⟨source4FaceCodes198,source4FaceRow198_checked⟩ (Fin.cases ⟨source4FaceCodes199,source4FaceRow199_checked⟩ (Fin.cases ⟨source4FaceCodes200,source4FaceRow200_checked⟩ (Fin.cases ⟨source4FaceCodes201,source4FaceRow201_checked⟩ (Fin.cases ⟨source4FaceCodes202,source4FaceRow202_checked⟩ (Fin.cases ⟨source4FaceCodes203,source4FaceRow203_checked⟩ (Fin.cases ⟨source4FaceCodes204,source4FaceRow204_checked⟩ (Fin.cases ⟨source4FaceCodes205,source4FaceRow205_checked⟩ (Fin.cases ⟨source4FaceCodes206,source4FaceRow206_checked⟩ (Fin.cases ⟨source4FaceCodes207,source4FaceRow207_checked⟩ (Fin.cases ⟨source4FaceCodes208,source4FaceRow208_checked⟩ (Fin.cases ⟨source4FaceCodes209,source4FaceRow209_checked⟩ (Fin.cases ⟨source4FaceCodes210,source4FaceRow210_checked⟩ (Fin.cases ⟨source4FaceCodes211,source4FaceRow211_checked⟩ (Fin.cases ⟨source4FaceCodes212,source4FaceRow212_checked⟩ (Fin.cases ⟨source4FaceCodes213,source4FaceRow213_checked⟩ (Fin.cases ⟨source4FaceCodes214,source4FaceRow214_checked⟩ (Fin.cases ⟨source4FaceCodes215,source4FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source4FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily4.getD (j.val+216) default)
      (sourceFamily4.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source4FaceCodes216,source4FaceRow216_checked⟩ (Fin.cases ⟨source4FaceCodes217,source4FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source4AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily4.getD i.val default)
      (sourceFamily4.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source4FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
