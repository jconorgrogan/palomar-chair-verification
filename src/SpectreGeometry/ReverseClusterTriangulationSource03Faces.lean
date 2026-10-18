module

public import SpectreGeometry.ReverseClusterTriangulationSource03Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource03Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source3Family_length : sourceFamily3.length = 218 := by decide

theorem source3FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+0) default)
      (sourceFamily3.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes0,source3FaceRow0_checked⟩ (Fin.cases ⟨source3FaceCodes1,source3FaceRow1_checked⟩ (Fin.cases ⟨source3FaceCodes2,source3FaceRow2_checked⟩ (Fin.cases ⟨source3FaceCodes3,source3FaceRow3_checked⟩ (Fin.cases ⟨source3FaceCodes4,source3FaceRow4_checked⟩ (Fin.cases ⟨source3FaceCodes5,source3FaceRow5_checked⟩ (Fin.cases ⟨source3FaceCodes6,source3FaceRow6_checked⟩ (Fin.cases ⟨source3FaceCodes7,source3FaceRow7_checked⟩ (Fin.cases ⟨source3FaceCodes8,source3FaceRow8_checked⟩ (Fin.cases ⟨source3FaceCodes9,source3FaceRow9_checked⟩ (Fin.cases ⟨source3FaceCodes10,source3FaceRow10_checked⟩ (Fin.cases ⟨source3FaceCodes11,source3FaceRow11_checked⟩ (Fin.cases ⟨source3FaceCodes12,source3FaceRow12_checked⟩ (Fin.cases ⟨source3FaceCodes13,source3FaceRow13_checked⟩ (Fin.cases ⟨source3FaceCodes14,source3FaceRow14_checked⟩ (Fin.cases ⟨source3FaceCodes15,source3FaceRow15_checked⟩ (Fin.cases ⟨source3FaceCodes16,source3FaceRow16_checked⟩ (Fin.cases ⟨source3FaceCodes17,source3FaceRow17_checked⟩ (Fin.cases ⟨source3FaceCodes18,source3FaceRow18_checked⟩ (Fin.cases ⟨source3FaceCodes19,source3FaceRow19_checked⟩ (Fin.cases ⟨source3FaceCodes20,source3FaceRow20_checked⟩ (Fin.cases ⟨source3FaceCodes21,source3FaceRow21_checked⟩ (Fin.cases ⟨source3FaceCodes22,source3FaceRow22_checked⟩ (Fin.cases ⟨source3FaceCodes23,source3FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+24) default)
      (sourceFamily3.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes24,source3FaceRow24_checked⟩ (Fin.cases ⟨source3FaceCodes25,source3FaceRow25_checked⟩ (Fin.cases ⟨source3FaceCodes26,source3FaceRow26_checked⟩ (Fin.cases ⟨source3FaceCodes27,source3FaceRow27_checked⟩ (Fin.cases ⟨source3FaceCodes28,source3FaceRow28_checked⟩ (Fin.cases ⟨source3FaceCodes29,source3FaceRow29_checked⟩ (Fin.cases ⟨source3FaceCodes30,source3FaceRow30_checked⟩ (Fin.cases ⟨source3FaceCodes31,source3FaceRow31_checked⟩ (Fin.cases ⟨source3FaceCodes32,source3FaceRow32_checked⟩ (Fin.cases ⟨source3FaceCodes33,source3FaceRow33_checked⟩ (Fin.cases ⟨source3FaceCodes34,source3FaceRow34_checked⟩ (Fin.cases ⟨source3FaceCodes35,source3FaceRow35_checked⟩ (Fin.cases ⟨source3FaceCodes36,source3FaceRow36_checked⟩ (Fin.cases ⟨source3FaceCodes37,source3FaceRow37_checked⟩ (Fin.cases ⟨source3FaceCodes38,source3FaceRow38_checked⟩ (Fin.cases ⟨source3FaceCodes39,source3FaceRow39_checked⟩ (Fin.cases ⟨source3FaceCodes40,source3FaceRow40_checked⟩ (Fin.cases ⟨source3FaceCodes41,source3FaceRow41_checked⟩ (Fin.cases ⟨source3FaceCodes42,source3FaceRow42_checked⟩ (Fin.cases ⟨source3FaceCodes43,source3FaceRow43_checked⟩ (Fin.cases ⟨source3FaceCodes44,source3FaceRow44_checked⟩ (Fin.cases ⟨source3FaceCodes45,source3FaceRow45_checked⟩ (Fin.cases ⟨source3FaceCodes46,source3FaceRow46_checked⟩ (Fin.cases ⟨source3FaceCodes47,source3FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+48) default)
      (sourceFamily3.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes48,source3FaceRow48_checked⟩ (Fin.cases ⟨source3FaceCodes49,source3FaceRow49_checked⟩ (Fin.cases ⟨source3FaceCodes50,source3FaceRow50_checked⟩ (Fin.cases ⟨source3FaceCodes51,source3FaceRow51_checked⟩ (Fin.cases ⟨source3FaceCodes52,source3FaceRow52_checked⟩ (Fin.cases ⟨source3FaceCodes53,source3FaceRow53_checked⟩ (Fin.cases ⟨source3FaceCodes54,source3FaceRow54_checked⟩ (Fin.cases ⟨source3FaceCodes55,source3FaceRow55_checked⟩ (Fin.cases ⟨source3FaceCodes56,source3FaceRow56_checked⟩ (Fin.cases ⟨source3FaceCodes57,source3FaceRow57_checked⟩ (Fin.cases ⟨source3FaceCodes58,source3FaceRow58_checked⟩ (Fin.cases ⟨source3FaceCodes59,source3FaceRow59_checked⟩ (Fin.cases ⟨source3FaceCodes60,source3FaceRow60_checked⟩ (Fin.cases ⟨source3FaceCodes61,source3FaceRow61_checked⟩ (Fin.cases ⟨source3FaceCodes62,source3FaceRow62_checked⟩ (Fin.cases ⟨source3FaceCodes63,source3FaceRow63_checked⟩ (Fin.cases ⟨source3FaceCodes64,source3FaceRow64_checked⟩ (Fin.cases ⟨source3FaceCodes65,source3FaceRow65_checked⟩ (Fin.cases ⟨source3FaceCodes66,source3FaceRow66_checked⟩ (Fin.cases ⟨source3FaceCodes67,source3FaceRow67_checked⟩ (Fin.cases ⟨source3FaceCodes68,source3FaceRow68_checked⟩ (Fin.cases ⟨source3FaceCodes69,source3FaceRow69_checked⟩ (Fin.cases ⟨source3FaceCodes70,source3FaceRow70_checked⟩ (Fin.cases ⟨source3FaceCodes71,source3FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+72) default)
      (sourceFamily3.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes72,source3FaceRow72_checked⟩ (Fin.cases ⟨source3FaceCodes73,source3FaceRow73_checked⟩ (Fin.cases ⟨source3FaceCodes74,source3FaceRow74_checked⟩ (Fin.cases ⟨source3FaceCodes75,source3FaceRow75_checked⟩ (Fin.cases ⟨source3FaceCodes76,source3FaceRow76_checked⟩ (Fin.cases ⟨source3FaceCodes77,source3FaceRow77_checked⟩ (Fin.cases ⟨source3FaceCodes78,source3FaceRow78_checked⟩ (Fin.cases ⟨source3FaceCodes79,source3FaceRow79_checked⟩ (Fin.cases ⟨source3FaceCodes80,source3FaceRow80_checked⟩ (Fin.cases ⟨source3FaceCodes81,source3FaceRow81_checked⟩ (Fin.cases ⟨source3FaceCodes82,source3FaceRow82_checked⟩ (Fin.cases ⟨source3FaceCodes83,source3FaceRow83_checked⟩ (Fin.cases ⟨source3FaceCodes84,source3FaceRow84_checked⟩ (Fin.cases ⟨source3FaceCodes85,source3FaceRow85_checked⟩ (Fin.cases ⟨source3FaceCodes86,source3FaceRow86_checked⟩ (Fin.cases ⟨source3FaceCodes87,source3FaceRow87_checked⟩ (Fin.cases ⟨source3FaceCodes88,source3FaceRow88_checked⟩ (Fin.cases ⟨source3FaceCodes89,source3FaceRow89_checked⟩ (Fin.cases ⟨source3FaceCodes90,source3FaceRow90_checked⟩ (Fin.cases ⟨source3FaceCodes91,source3FaceRow91_checked⟩ (Fin.cases ⟨source3FaceCodes92,source3FaceRow92_checked⟩ (Fin.cases ⟨source3FaceCodes93,source3FaceRow93_checked⟩ (Fin.cases ⟨source3FaceCodes94,source3FaceRow94_checked⟩ (Fin.cases ⟨source3FaceCodes95,source3FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+96) default)
      (sourceFamily3.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes96,source3FaceRow96_checked⟩ (Fin.cases ⟨source3FaceCodes97,source3FaceRow97_checked⟩ (Fin.cases ⟨source3FaceCodes98,source3FaceRow98_checked⟩ (Fin.cases ⟨source3FaceCodes99,source3FaceRow99_checked⟩ (Fin.cases ⟨source3FaceCodes100,source3FaceRow100_checked⟩ (Fin.cases ⟨source3FaceCodes101,source3FaceRow101_checked⟩ (Fin.cases ⟨source3FaceCodes102,source3FaceRow102_checked⟩ (Fin.cases ⟨source3FaceCodes103,source3FaceRow103_checked⟩ (Fin.cases ⟨source3FaceCodes104,source3FaceRow104_checked⟩ (Fin.cases ⟨source3FaceCodes105,source3FaceRow105_checked⟩ (Fin.cases ⟨source3FaceCodes106,source3FaceRow106_checked⟩ (Fin.cases ⟨source3FaceCodes107,source3FaceRow107_checked⟩ (Fin.cases ⟨source3FaceCodes108,source3FaceRow108_checked⟩ (Fin.cases ⟨source3FaceCodes109,source3FaceRow109_checked⟩ (Fin.cases ⟨source3FaceCodes110,source3FaceRow110_checked⟩ (Fin.cases ⟨source3FaceCodes111,source3FaceRow111_checked⟩ (Fin.cases ⟨source3FaceCodes112,source3FaceRow112_checked⟩ (Fin.cases ⟨source3FaceCodes113,source3FaceRow113_checked⟩ (Fin.cases ⟨source3FaceCodes114,source3FaceRow114_checked⟩ (Fin.cases ⟨source3FaceCodes115,source3FaceRow115_checked⟩ (Fin.cases ⟨source3FaceCodes116,source3FaceRow116_checked⟩ (Fin.cases ⟨source3FaceCodes117,source3FaceRow117_checked⟩ (Fin.cases ⟨source3FaceCodes118,source3FaceRow118_checked⟩ (Fin.cases ⟨source3FaceCodes119,source3FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+120) default)
      (sourceFamily3.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes120,source3FaceRow120_checked⟩ (Fin.cases ⟨source3FaceCodes121,source3FaceRow121_checked⟩ (Fin.cases ⟨source3FaceCodes122,source3FaceRow122_checked⟩ (Fin.cases ⟨source3FaceCodes123,source3FaceRow123_checked⟩ (Fin.cases ⟨source3FaceCodes124,source3FaceRow124_checked⟩ (Fin.cases ⟨source3FaceCodes125,source3FaceRow125_checked⟩ (Fin.cases ⟨source3FaceCodes126,source3FaceRow126_checked⟩ (Fin.cases ⟨source3FaceCodes127,source3FaceRow127_checked⟩ (Fin.cases ⟨source3FaceCodes128,source3FaceRow128_checked⟩ (Fin.cases ⟨source3FaceCodes129,source3FaceRow129_checked⟩ (Fin.cases ⟨source3FaceCodes130,source3FaceRow130_checked⟩ (Fin.cases ⟨source3FaceCodes131,source3FaceRow131_checked⟩ (Fin.cases ⟨source3FaceCodes132,source3FaceRow132_checked⟩ (Fin.cases ⟨source3FaceCodes133,source3FaceRow133_checked⟩ (Fin.cases ⟨source3FaceCodes134,source3FaceRow134_checked⟩ (Fin.cases ⟨source3FaceCodes135,source3FaceRow135_checked⟩ (Fin.cases ⟨source3FaceCodes136,source3FaceRow136_checked⟩ (Fin.cases ⟨source3FaceCodes137,source3FaceRow137_checked⟩ (Fin.cases ⟨source3FaceCodes138,source3FaceRow138_checked⟩ (Fin.cases ⟨source3FaceCodes139,source3FaceRow139_checked⟩ (Fin.cases ⟨source3FaceCodes140,source3FaceRow140_checked⟩ (Fin.cases ⟨source3FaceCodes141,source3FaceRow141_checked⟩ (Fin.cases ⟨source3FaceCodes142,source3FaceRow142_checked⟩ (Fin.cases ⟨source3FaceCodes143,source3FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+144) default)
      (sourceFamily3.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes144,source3FaceRow144_checked⟩ (Fin.cases ⟨source3FaceCodes145,source3FaceRow145_checked⟩ (Fin.cases ⟨source3FaceCodes146,source3FaceRow146_checked⟩ (Fin.cases ⟨source3FaceCodes147,source3FaceRow147_checked⟩ (Fin.cases ⟨source3FaceCodes148,source3FaceRow148_checked⟩ (Fin.cases ⟨source3FaceCodes149,source3FaceRow149_checked⟩ (Fin.cases ⟨source3FaceCodes150,source3FaceRow150_checked⟩ (Fin.cases ⟨source3FaceCodes151,source3FaceRow151_checked⟩ (Fin.cases ⟨source3FaceCodes152,source3FaceRow152_checked⟩ (Fin.cases ⟨source3FaceCodes153,source3FaceRow153_checked⟩ (Fin.cases ⟨source3FaceCodes154,source3FaceRow154_checked⟩ (Fin.cases ⟨source3FaceCodes155,source3FaceRow155_checked⟩ (Fin.cases ⟨source3FaceCodes156,source3FaceRow156_checked⟩ (Fin.cases ⟨source3FaceCodes157,source3FaceRow157_checked⟩ (Fin.cases ⟨source3FaceCodes158,source3FaceRow158_checked⟩ (Fin.cases ⟨source3FaceCodes159,source3FaceRow159_checked⟩ (Fin.cases ⟨source3FaceCodes160,source3FaceRow160_checked⟩ (Fin.cases ⟨source3FaceCodes161,source3FaceRow161_checked⟩ (Fin.cases ⟨source3FaceCodes162,source3FaceRow162_checked⟩ (Fin.cases ⟨source3FaceCodes163,source3FaceRow163_checked⟩ (Fin.cases ⟨source3FaceCodes164,source3FaceRow164_checked⟩ (Fin.cases ⟨source3FaceCodes165,source3FaceRow165_checked⟩ (Fin.cases ⟨source3FaceCodes166,source3FaceRow166_checked⟩ (Fin.cases ⟨source3FaceCodes167,source3FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+168) default)
      (sourceFamily3.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes168,source3FaceRow168_checked⟩ (Fin.cases ⟨source3FaceCodes169,source3FaceRow169_checked⟩ (Fin.cases ⟨source3FaceCodes170,source3FaceRow170_checked⟩ (Fin.cases ⟨source3FaceCodes171,source3FaceRow171_checked⟩ (Fin.cases ⟨source3FaceCodes172,source3FaceRow172_checked⟩ (Fin.cases ⟨source3FaceCodes173,source3FaceRow173_checked⟩ (Fin.cases ⟨source3FaceCodes174,source3FaceRow174_checked⟩ (Fin.cases ⟨source3FaceCodes175,source3FaceRow175_checked⟩ (Fin.cases ⟨source3FaceCodes176,source3FaceRow176_checked⟩ (Fin.cases ⟨source3FaceCodes177,source3FaceRow177_checked⟩ (Fin.cases ⟨source3FaceCodes178,source3FaceRow178_checked⟩ (Fin.cases ⟨source3FaceCodes179,source3FaceRow179_checked⟩ (Fin.cases ⟨source3FaceCodes180,source3FaceRow180_checked⟩ (Fin.cases ⟨source3FaceCodes181,source3FaceRow181_checked⟩ (Fin.cases ⟨source3FaceCodes182,source3FaceRow182_checked⟩ (Fin.cases ⟨source3FaceCodes183,source3FaceRow183_checked⟩ (Fin.cases ⟨source3FaceCodes184,source3FaceRow184_checked⟩ (Fin.cases ⟨source3FaceCodes185,source3FaceRow185_checked⟩ (Fin.cases ⟨source3FaceCodes186,source3FaceRow186_checked⟩ (Fin.cases ⟨source3FaceCodes187,source3FaceRow187_checked⟩ (Fin.cases ⟨source3FaceCodes188,source3FaceRow188_checked⟩ (Fin.cases ⟨source3FaceCodes189,source3FaceRow189_checked⟩ (Fin.cases ⟨source3FaceCodes190,source3FaceRow190_checked⟩ (Fin.cases ⟨source3FaceCodes191,source3FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+192) default)
      (sourceFamily3.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes192,source3FaceRow192_checked⟩ (Fin.cases ⟨source3FaceCodes193,source3FaceRow193_checked⟩ (Fin.cases ⟨source3FaceCodes194,source3FaceRow194_checked⟩ (Fin.cases ⟨source3FaceCodes195,source3FaceRow195_checked⟩ (Fin.cases ⟨source3FaceCodes196,source3FaceRow196_checked⟩ (Fin.cases ⟨source3FaceCodes197,source3FaceRow197_checked⟩ (Fin.cases ⟨source3FaceCodes198,source3FaceRow198_checked⟩ (Fin.cases ⟨source3FaceCodes199,source3FaceRow199_checked⟩ (Fin.cases ⟨source3FaceCodes200,source3FaceRow200_checked⟩ (Fin.cases ⟨source3FaceCodes201,source3FaceRow201_checked⟩ (Fin.cases ⟨source3FaceCodes202,source3FaceRow202_checked⟩ (Fin.cases ⟨source3FaceCodes203,source3FaceRow203_checked⟩ (Fin.cases ⟨source3FaceCodes204,source3FaceRow204_checked⟩ (Fin.cases ⟨source3FaceCodes205,source3FaceRow205_checked⟩ (Fin.cases ⟨source3FaceCodes206,source3FaceRow206_checked⟩ (Fin.cases ⟨source3FaceCodes207,source3FaceRow207_checked⟩ (Fin.cases ⟨source3FaceCodes208,source3FaceRow208_checked⟩ (Fin.cases ⟨source3FaceCodes209,source3FaceRow209_checked⟩ (Fin.cases ⟨source3FaceCodes210,source3FaceRow210_checked⟩ (Fin.cases ⟨source3FaceCodes211,source3FaceRow211_checked⟩ (Fin.cases ⟨source3FaceCodes212,source3FaceRow212_checked⟩ (Fin.cases ⟨source3FaceCodes213,source3FaceRow213_checked⟩ (Fin.cases ⟨source3FaceCodes214,source3FaceRow214_checked⟩ (Fin.cases ⟨source3FaceCodes215,source3FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source3FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily3.getD (j.val+216) default)
      (sourceFamily3.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source3FaceCodes216,source3FaceRow216_checked⟩ (Fin.cases ⟨source3FaceCodes217,source3FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source3AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily3.getD i.val default)
      (sourceFamily3.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source3FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
