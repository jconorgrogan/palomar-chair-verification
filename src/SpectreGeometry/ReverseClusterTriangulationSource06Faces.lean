module

public import SpectreGeometry.ReverseClusterTriangulationSource06Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource06Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source6Family_length : sourceFamily6.length = 218 := by decide

theorem source6FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+0) default)
      (sourceFamily6.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes0,source6FaceRow0_checked⟩ (Fin.cases ⟨source6FaceCodes1,source6FaceRow1_checked⟩ (Fin.cases ⟨source6FaceCodes2,source6FaceRow2_checked⟩ (Fin.cases ⟨source6FaceCodes3,source6FaceRow3_checked⟩ (Fin.cases ⟨source6FaceCodes4,source6FaceRow4_checked⟩ (Fin.cases ⟨source6FaceCodes5,source6FaceRow5_checked⟩ (Fin.cases ⟨source6FaceCodes6,source6FaceRow6_checked⟩ (Fin.cases ⟨source6FaceCodes7,source6FaceRow7_checked⟩ (Fin.cases ⟨source6FaceCodes8,source6FaceRow8_checked⟩ (Fin.cases ⟨source6FaceCodes9,source6FaceRow9_checked⟩ (Fin.cases ⟨source6FaceCodes10,source6FaceRow10_checked⟩ (Fin.cases ⟨source6FaceCodes11,source6FaceRow11_checked⟩ (Fin.cases ⟨source6FaceCodes12,source6FaceRow12_checked⟩ (Fin.cases ⟨source6FaceCodes13,source6FaceRow13_checked⟩ (Fin.cases ⟨source6FaceCodes14,source6FaceRow14_checked⟩ (Fin.cases ⟨source6FaceCodes15,source6FaceRow15_checked⟩ (Fin.cases ⟨source6FaceCodes16,source6FaceRow16_checked⟩ (Fin.cases ⟨source6FaceCodes17,source6FaceRow17_checked⟩ (Fin.cases ⟨source6FaceCodes18,source6FaceRow18_checked⟩ (Fin.cases ⟨source6FaceCodes19,source6FaceRow19_checked⟩ (Fin.cases ⟨source6FaceCodes20,source6FaceRow20_checked⟩ (Fin.cases ⟨source6FaceCodes21,source6FaceRow21_checked⟩ (Fin.cases ⟨source6FaceCodes22,source6FaceRow22_checked⟩ (Fin.cases ⟨source6FaceCodes23,source6FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+24) default)
      (sourceFamily6.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes24,source6FaceRow24_checked⟩ (Fin.cases ⟨source6FaceCodes25,source6FaceRow25_checked⟩ (Fin.cases ⟨source6FaceCodes26,source6FaceRow26_checked⟩ (Fin.cases ⟨source6FaceCodes27,source6FaceRow27_checked⟩ (Fin.cases ⟨source6FaceCodes28,source6FaceRow28_checked⟩ (Fin.cases ⟨source6FaceCodes29,source6FaceRow29_checked⟩ (Fin.cases ⟨source6FaceCodes30,source6FaceRow30_checked⟩ (Fin.cases ⟨source6FaceCodes31,source6FaceRow31_checked⟩ (Fin.cases ⟨source6FaceCodes32,source6FaceRow32_checked⟩ (Fin.cases ⟨source6FaceCodes33,source6FaceRow33_checked⟩ (Fin.cases ⟨source6FaceCodes34,source6FaceRow34_checked⟩ (Fin.cases ⟨source6FaceCodes35,source6FaceRow35_checked⟩ (Fin.cases ⟨source6FaceCodes36,source6FaceRow36_checked⟩ (Fin.cases ⟨source6FaceCodes37,source6FaceRow37_checked⟩ (Fin.cases ⟨source6FaceCodes38,source6FaceRow38_checked⟩ (Fin.cases ⟨source6FaceCodes39,source6FaceRow39_checked⟩ (Fin.cases ⟨source6FaceCodes40,source6FaceRow40_checked⟩ (Fin.cases ⟨source6FaceCodes41,source6FaceRow41_checked⟩ (Fin.cases ⟨source6FaceCodes42,source6FaceRow42_checked⟩ (Fin.cases ⟨source6FaceCodes43,source6FaceRow43_checked⟩ (Fin.cases ⟨source6FaceCodes44,source6FaceRow44_checked⟩ (Fin.cases ⟨source6FaceCodes45,source6FaceRow45_checked⟩ (Fin.cases ⟨source6FaceCodes46,source6FaceRow46_checked⟩ (Fin.cases ⟨source6FaceCodes47,source6FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+48) default)
      (sourceFamily6.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes48,source6FaceRow48_checked⟩ (Fin.cases ⟨source6FaceCodes49,source6FaceRow49_checked⟩ (Fin.cases ⟨source6FaceCodes50,source6FaceRow50_checked⟩ (Fin.cases ⟨source6FaceCodes51,source6FaceRow51_checked⟩ (Fin.cases ⟨source6FaceCodes52,source6FaceRow52_checked⟩ (Fin.cases ⟨source6FaceCodes53,source6FaceRow53_checked⟩ (Fin.cases ⟨source6FaceCodes54,source6FaceRow54_checked⟩ (Fin.cases ⟨source6FaceCodes55,source6FaceRow55_checked⟩ (Fin.cases ⟨source6FaceCodes56,source6FaceRow56_checked⟩ (Fin.cases ⟨source6FaceCodes57,source6FaceRow57_checked⟩ (Fin.cases ⟨source6FaceCodes58,source6FaceRow58_checked⟩ (Fin.cases ⟨source6FaceCodes59,source6FaceRow59_checked⟩ (Fin.cases ⟨source6FaceCodes60,source6FaceRow60_checked⟩ (Fin.cases ⟨source6FaceCodes61,source6FaceRow61_checked⟩ (Fin.cases ⟨source6FaceCodes62,source6FaceRow62_checked⟩ (Fin.cases ⟨source6FaceCodes63,source6FaceRow63_checked⟩ (Fin.cases ⟨source6FaceCodes64,source6FaceRow64_checked⟩ (Fin.cases ⟨source6FaceCodes65,source6FaceRow65_checked⟩ (Fin.cases ⟨source6FaceCodes66,source6FaceRow66_checked⟩ (Fin.cases ⟨source6FaceCodes67,source6FaceRow67_checked⟩ (Fin.cases ⟨source6FaceCodes68,source6FaceRow68_checked⟩ (Fin.cases ⟨source6FaceCodes69,source6FaceRow69_checked⟩ (Fin.cases ⟨source6FaceCodes70,source6FaceRow70_checked⟩ (Fin.cases ⟨source6FaceCodes71,source6FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+72) default)
      (sourceFamily6.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes72,source6FaceRow72_checked⟩ (Fin.cases ⟨source6FaceCodes73,source6FaceRow73_checked⟩ (Fin.cases ⟨source6FaceCodes74,source6FaceRow74_checked⟩ (Fin.cases ⟨source6FaceCodes75,source6FaceRow75_checked⟩ (Fin.cases ⟨source6FaceCodes76,source6FaceRow76_checked⟩ (Fin.cases ⟨source6FaceCodes77,source6FaceRow77_checked⟩ (Fin.cases ⟨source6FaceCodes78,source6FaceRow78_checked⟩ (Fin.cases ⟨source6FaceCodes79,source6FaceRow79_checked⟩ (Fin.cases ⟨source6FaceCodes80,source6FaceRow80_checked⟩ (Fin.cases ⟨source6FaceCodes81,source6FaceRow81_checked⟩ (Fin.cases ⟨source6FaceCodes82,source6FaceRow82_checked⟩ (Fin.cases ⟨source6FaceCodes83,source6FaceRow83_checked⟩ (Fin.cases ⟨source6FaceCodes84,source6FaceRow84_checked⟩ (Fin.cases ⟨source6FaceCodes85,source6FaceRow85_checked⟩ (Fin.cases ⟨source6FaceCodes86,source6FaceRow86_checked⟩ (Fin.cases ⟨source6FaceCodes87,source6FaceRow87_checked⟩ (Fin.cases ⟨source6FaceCodes88,source6FaceRow88_checked⟩ (Fin.cases ⟨source6FaceCodes89,source6FaceRow89_checked⟩ (Fin.cases ⟨source6FaceCodes90,source6FaceRow90_checked⟩ (Fin.cases ⟨source6FaceCodes91,source6FaceRow91_checked⟩ (Fin.cases ⟨source6FaceCodes92,source6FaceRow92_checked⟩ (Fin.cases ⟨source6FaceCodes93,source6FaceRow93_checked⟩ (Fin.cases ⟨source6FaceCodes94,source6FaceRow94_checked⟩ (Fin.cases ⟨source6FaceCodes95,source6FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+96) default)
      (sourceFamily6.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes96,source6FaceRow96_checked⟩ (Fin.cases ⟨source6FaceCodes97,source6FaceRow97_checked⟩ (Fin.cases ⟨source6FaceCodes98,source6FaceRow98_checked⟩ (Fin.cases ⟨source6FaceCodes99,source6FaceRow99_checked⟩ (Fin.cases ⟨source6FaceCodes100,source6FaceRow100_checked⟩ (Fin.cases ⟨source6FaceCodes101,source6FaceRow101_checked⟩ (Fin.cases ⟨source6FaceCodes102,source6FaceRow102_checked⟩ (Fin.cases ⟨source6FaceCodes103,source6FaceRow103_checked⟩ (Fin.cases ⟨source6FaceCodes104,source6FaceRow104_checked⟩ (Fin.cases ⟨source6FaceCodes105,source6FaceRow105_checked⟩ (Fin.cases ⟨source6FaceCodes106,source6FaceRow106_checked⟩ (Fin.cases ⟨source6FaceCodes107,source6FaceRow107_checked⟩ (Fin.cases ⟨source6FaceCodes108,source6FaceRow108_checked⟩ (Fin.cases ⟨source6FaceCodes109,source6FaceRow109_checked⟩ (Fin.cases ⟨source6FaceCodes110,source6FaceRow110_checked⟩ (Fin.cases ⟨source6FaceCodes111,source6FaceRow111_checked⟩ (Fin.cases ⟨source6FaceCodes112,source6FaceRow112_checked⟩ (Fin.cases ⟨source6FaceCodes113,source6FaceRow113_checked⟩ (Fin.cases ⟨source6FaceCodes114,source6FaceRow114_checked⟩ (Fin.cases ⟨source6FaceCodes115,source6FaceRow115_checked⟩ (Fin.cases ⟨source6FaceCodes116,source6FaceRow116_checked⟩ (Fin.cases ⟨source6FaceCodes117,source6FaceRow117_checked⟩ (Fin.cases ⟨source6FaceCodes118,source6FaceRow118_checked⟩ (Fin.cases ⟨source6FaceCodes119,source6FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+120) default)
      (sourceFamily6.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes120,source6FaceRow120_checked⟩ (Fin.cases ⟨source6FaceCodes121,source6FaceRow121_checked⟩ (Fin.cases ⟨source6FaceCodes122,source6FaceRow122_checked⟩ (Fin.cases ⟨source6FaceCodes123,source6FaceRow123_checked⟩ (Fin.cases ⟨source6FaceCodes124,source6FaceRow124_checked⟩ (Fin.cases ⟨source6FaceCodes125,source6FaceRow125_checked⟩ (Fin.cases ⟨source6FaceCodes126,source6FaceRow126_checked⟩ (Fin.cases ⟨source6FaceCodes127,source6FaceRow127_checked⟩ (Fin.cases ⟨source6FaceCodes128,source6FaceRow128_checked⟩ (Fin.cases ⟨source6FaceCodes129,source6FaceRow129_checked⟩ (Fin.cases ⟨source6FaceCodes130,source6FaceRow130_checked⟩ (Fin.cases ⟨source6FaceCodes131,source6FaceRow131_checked⟩ (Fin.cases ⟨source6FaceCodes132,source6FaceRow132_checked⟩ (Fin.cases ⟨source6FaceCodes133,source6FaceRow133_checked⟩ (Fin.cases ⟨source6FaceCodes134,source6FaceRow134_checked⟩ (Fin.cases ⟨source6FaceCodes135,source6FaceRow135_checked⟩ (Fin.cases ⟨source6FaceCodes136,source6FaceRow136_checked⟩ (Fin.cases ⟨source6FaceCodes137,source6FaceRow137_checked⟩ (Fin.cases ⟨source6FaceCodes138,source6FaceRow138_checked⟩ (Fin.cases ⟨source6FaceCodes139,source6FaceRow139_checked⟩ (Fin.cases ⟨source6FaceCodes140,source6FaceRow140_checked⟩ (Fin.cases ⟨source6FaceCodes141,source6FaceRow141_checked⟩ (Fin.cases ⟨source6FaceCodes142,source6FaceRow142_checked⟩ (Fin.cases ⟨source6FaceCodes143,source6FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+144) default)
      (sourceFamily6.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes144,source6FaceRow144_checked⟩ (Fin.cases ⟨source6FaceCodes145,source6FaceRow145_checked⟩ (Fin.cases ⟨source6FaceCodes146,source6FaceRow146_checked⟩ (Fin.cases ⟨source6FaceCodes147,source6FaceRow147_checked⟩ (Fin.cases ⟨source6FaceCodes148,source6FaceRow148_checked⟩ (Fin.cases ⟨source6FaceCodes149,source6FaceRow149_checked⟩ (Fin.cases ⟨source6FaceCodes150,source6FaceRow150_checked⟩ (Fin.cases ⟨source6FaceCodes151,source6FaceRow151_checked⟩ (Fin.cases ⟨source6FaceCodes152,source6FaceRow152_checked⟩ (Fin.cases ⟨source6FaceCodes153,source6FaceRow153_checked⟩ (Fin.cases ⟨source6FaceCodes154,source6FaceRow154_checked⟩ (Fin.cases ⟨source6FaceCodes155,source6FaceRow155_checked⟩ (Fin.cases ⟨source6FaceCodes156,source6FaceRow156_checked⟩ (Fin.cases ⟨source6FaceCodes157,source6FaceRow157_checked⟩ (Fin.cases ⟨source6FaceCodes158,source6FaceRow158_checked⟩ (Fin.cases ⟨source6FaceCodes159,source6FaceRow159_checked⟩ (Fin.cases ⟨source6FaceCodes160,source6FaceRow160_checked⟩ (Fin.cases ⟨source6FaceCodes161,source6FaceRow161_checked⟩ (Fin.cases ⟨source6FaceCodes162,source6FaceRow162_checked⟩ (Fin.cases ⟨source6FaceCodes163,source6FaceRow163_checked⟩ (Fin.cases ⟨source6FaceCodes164,source6FaceRow164_checked⟩ (Fin.cases ⟨source6FaceCodes165,source6FaceRow165_checked⟩ (Fin.cases ⟨source6FaceCodes166,source6FaceRow166_checked⟩ (Fin.cases ⟨source6FaceCodes167,source6FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+168) default)
      (sourceFamily6.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes168,source6FaceRow168_checked⟩ (Fin.cases ⟨source6FaceCodes169,source6FaceRow169_checked⟩ (Fin.cases ⟨source6FaceCodes170,source6FaceRow170_checked⟩ (Fin.cases ⟨source6FaceCodes171,source6FaceRow171_checked⟩ (Fin.cases ⟨source6FaceCodes172,source6FaceRow172_checked⟩ (Fin.cases ⟨source6FaceCodes173,source6FaceRow173_checked⟩ (Fin.cases ⟨source6FaceCodes174,source6FaceRow174_checked⟩ (Fin.cases ⟨source6FaceCodes175,source6FaceRow175_checked⟩ (Fin.cases ⟨source6FaceCodes176,source6FaceRow176_checked⟩ (Fin.cases ⟨source6FaceCodes177,source6FaceRow177_checked⟩ (Fin.cases ⟨source6FaceCodes178,source6FaceRow178_checked⟩ (Fin.cases ⟨source6FaceCodes179,source6FaceRow179_checked⟩ (Fin.cases ⟨source6FaceCodes180,source6FaceRow180_checked⟩ (Fin.cases ⟨source6FaceCodes181,source6FaceRow181_checked⟩ (Fin.cases ⟨source6FaceCodes182,source6FaceRow182_checked⟩ (Fin.cases ⟨source6FaceCodes183,source6FaceRow183_checked⟩ (Fin.cases ⟨source6FaceCodes184,source6FaceRow184_checked⟩ (Fin.cases ⟨source6FaceCodes185,source6FaceRow185_checked⟩ (Fin.cases ⟨source6FaceCodes186,source6FaceRow186_checked⟩ (Fin.cases ⟨source6FaceCodes187,source6FaceRow187_checked⟩ (Fin.cases ⟨source6FaceCodes188,source6FaceRow188_checked⟩ (Fin.cases ⟨source6FaceCodes189,source6FaceRow189_checked⟩ (Fin.cases ⟨source6FaceCodes190,source6FaceRow190_checked⟩ (Fin.cases ⟨source6FaceCodes191,source6FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+192) default)
      (sourceFamily6.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes192,source6FaceRow192_checked⟩ (Fin.cases ⟨source6FaceCodes193,source6FaceRow193_checked⟩ (Fin.cases ⟨source6FaceCodes194,source6FaceRow194_checked⟩ (Fin.cases ⟨source6FaceCodes195,source6FaceRow195_checked⟩ (Fin.cases ⟨source6FaceCodes196,source6FaceRow196_checked⟩ (Fin.cases ⟨source6FaceCodes197,source6FaceRow197_checked⟩ (Fin.cases ⟨source6FaceCodes198,source6FaceRow198_checked⟩ (Fin.cases ⟨source6FaceCodes199,source6FaceRow199_checked⟩ (Fin.cases ⟨source6FaceCodes200,source6FaceRow200_checked⟩ (Fin.cases ⟨source6FaceCodes201,source6FaceRow201_checked⟩ (Fin.cases ⟨source6FaceCodes202,source6FaceRow202_checked⟩ (Fin.cases ⟨source6FaceCodes203,source6FaceRow203_checked⟩ (Fin.cases ⟨source6FaceCodes204,source6FaceRow204_checked⟩ (Fin.cases ⟨source6FaceCodes205,source6FaceRow205_checked⟩ (Fin.cases ⟨source6FaceCodes206,source6FaceRow206_checked⟩ (Fin.cases ⟨source6FaceCodes207,source6FaceRow207_checked⟩ (Fin.cases ⟨source6FaceCodes208,source6FaceRow208_checked⟩ (Fin.cases ⟨source6FaceCodes209,source6FaceRow209_checked⟩ (Fin.cases ⟨source6FaceCodes210,source6FaceRow210_checked⟩ (Fin.cases ⟨source6FaceCodes211,source6FaceRow211_checked⟩ (Fin.cases ⟨source6FaceCodes212,source6FaceRow212_checked⟩ (Fin.cases ⟨source6FaceCodes213,source6FaceRow213_checked⟩ (Fin.cases ⟨source6FaceCodes214,source6FaceRow214_checked⟩ (Fin.cases ⟨source6FaceCodes215,source6FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source6FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily6.getD (j.val+216) default)
      (sourceFamily6.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source6FaceCodes216,source6FaceRow216_checked⟩ (Fin.cases ⟨source6FaceCodes217,source6FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source6AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily6.getD i.val default)
      (sourceFamily6.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source6FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
