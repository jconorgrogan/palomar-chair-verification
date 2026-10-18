module

public import SpectreGeometry.ReverseClusterTriangulationSource08Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces08
public import SpectreGeometry.ReverseClusterTriangulationSource08Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source8Family_length : sourceFamily8.length = 218 := by decide

theorem source8FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+0) default)
      (sourceFamily8.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes0,source8FaceRow0_checked⟩ (Fin.cases ⟨source8FaceCodes1,source8FaceRow1_checked⟩ (Fin.cases ⟨source8FaceCodes2,source8FaceRow2_checked⟩ (Fin.cases ⟨source8FaceCodes3,source8FaceRow3_checked⟩ (Fin.cases ⟨source8FaceCodes4,source8FaceRow4_checked⟩ (Fin.cases ⟨source8FaceCodes5,source8FaceRow5_checked⟩ (Fin.cases ⟨source8FaceCodes6,source8FaceRow6_checked⟩ (Fin.cases ⟨source8FaceCodes7,source8FaceRow7_checked⟩ (Fin.cases ⟨source8FaceCodes8,source8FaceRow8_checked⟩ (Fin.cases ⟨source8FaceCodes9,source8FaceRow9_checked⟩ (Fin.cases ⟨source8FaceCodes10,source8FaceRow10_checked⟩ (Fin.cases ⟨source8FaceCodes11,source8FaceRow11_checked⟩ (Fin.cases ⟨source8FaceCodes12,source8FaceRow12_checked⟩ (Fin.cases ⟨source8FaceCodes13,source8FaceRow13_checked⟩ (Fin.cases ⟨source8FaceCodes14,source8FaceRow14_checked⟩ (Fin.cases ⟨source8FaceCodes15,source8FaceRow15_checked⟩ (Fin.cases ⟨source8FaceCodes16,source8FaceRow16_checked⟩ (Fin.cases ⟨source8FaceCodes17,source8FaceRow17_checked⟩ (Fin.cases ⟨source8FaceCodes18,source8FaceRow18_checked⟩ (Fin.cases ⟨source8FaceCodes19,source8FaceRow19_checked⟩ (Fin.cases ⟨source8FaceCodes20,source8FaceRow20_checked⟩ (Fin.cases ⟨source8FaceCodes21,source8FaceRow21_checked⟩ (Fin.cases ⟨source8FaceCodes22,source8FaceRow22_checked⟩ (Fin.cases ⟨source8FaceCodes23,source8FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+24) default)
      (sourceFamily8.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes24,source8FaceRow24_checked⟩ (Fin.cases ⟨source8FaceCodes25,source8FaceRow25_checked⟩ (Fin.cases ⟨source8FaceCodes26,source8FaceRow26_checked⟩ (Fin.cases ⟨source8FaceCodes27,source8FaceRow27_checked⟩ (Fin.cases ⟨source8FaceCodes28,source8FaceRow28_checked⟩ (Fin.cases ⟨source8FaceCodes29,source8FaceRow29_checked⟩ (Fin.cases ⟨source8FaceCodes30,source8FaceRow30_checked⟩ (Fin.cases ⟨source8FaceCodes31,source8FaceRow31_checked⟩ (Fin.cases ⟨source8FaceCodes32,source8FaceRow32_checked⟩ (Fin.cases ⟨source8FaceCodes33,source8FaceRow33_checked⟩ (Fin.cases ⟨source8FaceCodes34,source8FaceRow34_checked⟩ (Fin.cases ⟨source8FaceCodes35,source8FaceRow35_checked⟩ (Fin.cases ⟨source8FaceCodes36,source8FaceRow36_checked⟩ (Fin.cases ⟨source8FaceCodes37,source8FaceRow37_checked⟩ (Fin.cases ⟨source8FaceCodes38,source8FaceRow38_checked⟩ (Fin.cases ⟨source8FaceCodes39,source8FaceRow39_checked⟩ (Fin.cases ⟨source8FaceCodes40,source8FaceRow40_checked⟩ (Fin.cases ⟨source8FaceCodes41,source8FaceRow41_checked⟩ (Fin.cases ⟨source8FaceCodes42,source8FaceRow42_checked⟩ (Fin.cases ⟨source8FaceCodes43,source8FaceRow43_checked⟩ (Fin.cases ⟨source8FaceCodes44,source8FaceRow44_checked⟩ (Fin.cases ⟨source8FaceCodes45,source8FaceRow45_checked⟩ (Fin.cases ⟨source8FaceCodes46,source8FaceRow46_checked⟩ (Fin.cases ⟨source8FaceCodes47,source8FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+48) default)
      (sourceFamily8.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes48,source8FaceRow48_checked⟩ (Fin.cases ⟨source8FaceCodes49,source8FaceRow49_checked⟩ (Fin.cases ⟨source8FaceCodes50,source8FaceRow50_checked⟩ (Fin.cases ⟨source8FaceCodes51,source8FaceRow51_checked⟩ (Fin.cases ⟨source8FaceCodes52,source8FaceRow52_checked⟩ (Fin.cases ⟨source8FaceCodes53,source8FaceRow53_checked⟩ (Fin.cases ⟨source8FaceCodes54,source8FaceRow54_checked⟩ (Fin.cases ⟨source8FaceCodes55,source8FaceRow55_checked⟩ (Fin.cases ⟨source8FaceCodes56,source8FaceRow56_checked⟩ (Fin.cases ⟨source8FaceCodes57,source8FaceRow57_checked⟩ (Fin.cases ⟨source8FaceCodes58,source8FaceRow58_checked⟩ (Fin.cases ⟨source8FaceCodes59,source8FaceRow59_checked⟩ (Fin.cases ⟨source8FaceCodes60,source8FaceRow60_checked⟩ (Fin.cases ⟨source8FaceCodes61,source8FaceRow61_checked⟩ (Fin.cases ⟨source8FaceCodes62,source8FaceRow62_checked⟩ (Fin.cases ⟨source8FaceCodes63,source8FaceRow63_checked⟩ (Fin.cases ⟨source8FaceCodes64,source8FaceRow64_checked⟩ (Fin.cases ⟨source8FaceCodes65,source8FaceRow65_checked⟩ (Fin.cases ⟨source8FaceCodes66,source8FaceRow66_checked⟩ (Fin.cases ⟨source8FaceCodes67,source8FaceRow67_checked⟩ (Fin.cases ⟨source8FaceCodes68,source8FaceRow68_checked⟩ (Fin.cases ⟨source8FaceCodes69,source8FaceRow69_checked⟩ (Fin.cases ⟨source8FaceCodes70,source8FaceRow70_checked⟩ (Fin.cases ⟨source8FaceCodes71,source8FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+72) default)
      (sourceFamily8.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes72,source8FaceRow72_checked⟩ (Fin.cases ⟨source8FaceCodes73,source8FaceRow73_checked⟩ (Fin.cases ⟨source8FaceCodes74,source8FaceRow74_checked⟩ (Fin.cases ⟨source8FaceCodes75,source8FaceRow75_checked⟩ (Fin.cases ⟨source8FaceCodes76,source8FaceRow76_checked⟩ (Fin.cases ⟨source8FaceCodes77,source8FaceRow77_checked⟩ (Fin.cases ⟨source8FaceCodes78,source8FaceRow78_checked⟩ (Fin.cases ⟨source8FaceCodes79,source8FaceRow79_checked⟩ (Fin.cases ⟨source8FaceCodes80,source8FaceRow80_checked⟩ (Fin.cases ⟨source8FaceCodes81,source8FaceRow81_checked⟩ (Fin.cases ⟨source8FaceCodes82,source8FaceRow82_checked⟩ (Fin.cases ⟨source8FaceCodes83,source8FaceRow83_checked⟩ (Fin.cases ⟨source8FaceCodes84,source8FaceRow84_checked⟩ (Fin.cases ⟨source8FaceCodes85,source8FaceRow85_checked⟩ (Fin.cases ⟨source8FaceCodes86,source8FaceRow86_checked⟩ (Fin.cases ⟨source8FaceCodes87,source8FaceRow87_checked⟩ (Fin.cases ⟨source8FaceCodes88,source8FaceRow88_checked⟩ (Fin.cases ⟨source8FaceCodes89,source8FaceRow89_checked⟩ (Fin.cases ⟨source8FaceCodes90,source8FaceRow90_checked⟩ (Fin.cases ⟨source8FaceCodes91,source8FaceRow91_checked⟩ (Fin.cases ⟨source8FaceCodes92,source8FaceRow92_checked⟩ (Fin.cases ⟨source8FaceCodes93,source8FaceRow93_checked⟩ (Fin.cases ⟨source8FaceCodes94,source8FaceRow94_checked⟩ (Fin.cases ⟨source8FaceCodes95,source8FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+96) default)
      (sourceFamily8.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes96,source8FaceRow96_checked⟩ (Fin.cases ⟨source8FaceCodes97,source8FaceRow97_checked⟩ (Fin.cases ⟨source8FaceCodes98,source8FaceRow98_checked⟩ (Fin.cases ⟨source8FaceCodes99,source8FaceRow99_checked⟩ (Fin.cases ⟨source8FaceCodes100,source8FaceRow100_checked⟩ (Fin.cases ⟨source8FaceCodes101,source8FaceRow101_checked⟩ (Fin.cases ⟨source8FaceCodes102,source8FaceRow102_checked⟩ (Fin.cases ⟨source8FaceCodes103,source8FaceRow103_checked⟩ (Fin.cases ⟨source8FaceCodes104,source8FaceRow104_checked⟩ (Fin.cases ⟨source8FaceCodes105,source8FaceRow105_checked⟩ (Fin.cases ⟨source8FaceCodes106,source8FaceRow106_checked⟩ (Fin.cases ⟨source8FaceCodes107,source8FaceRow107_checked⟩ (Fin.cases ⟨source8FaceCodes108,source8FaceRow108_checked⟩ (Fin.cases ⟨source8FaceCodes109,source8FaceRow109_checked⟩ (Fin.cases ⟨source8FaceCodes110,source8FaceRow110_checked⟩ (Fin.cases ⟨source8FaceCodes111,source8FaceRow111_checked⟩ (Fin.cases ⟨source8FaceCodes112,source8FaceRow112_checked⟩ (Fin.cases ⟨source8FaceCodes113,source8FaceRow113_checked⟩ (Fin.cases ⟨source8FaceCodes114,source8FaceRow114_checked⟩ (Fin.cases ⟨source8FaceCodes115,source8FaceRow115_checked⟩ (Fin.cases ⟨source8FaceCodes116,source8FaceRow116_checked⟩ (Fin.cases ⟨source8FaceCodes117,source8FaceRow117_checked⟩ (Fin.cases ⟨source8FaceCodes118,source8FaceRow118_checked⟩ (Fin.cases ⟨source8FaceCodes119,source8FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+120) default)
      (sourceFamily8.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes120,source8FaceRow120_checked⟩ (Fin.cases ⟨source8FaceCodes121,source8FaceRow121_checked⟩ (Fin.cases ⟨source8FaceCodes122,source8FaceRow122_checked⟩ (Fin.cases ⟨source8FaceCodes123,source8FaceRow123_checked⟩ (Fin.cases ⟨source8FaceCodes124,source8FaceRow124_checked⟩ (Fin.cases ⟨source8FaceCodes125,source8FaceRow125_checked⟩ (Fin.cases ⟨source8FaceCodes126,source8FaceRow126_checked⟩ (Fin.cases ⟨source8FaceCodes127,source8FaceRow127_checked⟩ (Fin.cases ⟨source8FaceCodes128,source8FaceRow128_checked⟩ (Fin.cases ⟨source8FaceCodes129,source8FaceRow129_checked⟩ (Fin.cases ⟨source8FaceCodes130,source8FaceRow130_checked⟩ (Fin.cases ⟨source8FaceCodes131,source8FaceRow131_checked⟩ (Fin.cases ⟨source8FaceCodes132,source8FaceRow132_checked⟩ (Fin.cases ⟨source8FaceCodes133,source8FaceRow133_checked⟩ (Fin.cases ⟨source8FaceCodes134,source8FaceRow134_checked⟩ (Fin.cases ⟨source8FaceCodes135,source8FaceRow135_checked⟩ (Fin.cases ⟨source8FaceCodes136,source8FaceRow136_checked⟩ (Fin.cases ⟨source8FaceCodes137,source8FaceRow137_checked⟩ (Fin.cases ⟨source8FaceCodes138,source8FaceRow138_checked⟩ (Fin.cases ⟨source8FaceCodes139,source8FaceRow139_checked⟩ (Fin.cases ⟨source8FaceCodes140,source8FaceRow140_checked⟩ (Fin.cases ⟨source8FaceCodes141,source8FaceRow141_checked⟩ (Fin.cases ⟨source8FaceCodes142,source8FaceRow142_checked⟩ (Fin.cases ⟨source8FaceCodes143,source8FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+144) default)
      (sourceFamily8.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes144,source8FaceRow144_checked⟩ (Fin.cases ⟨source8FaceCodes145,source8FaceRow145_checked⟩ (Fin.cases ⟨source8FaceCodes146,source8FaceRow146_checked⟩ (Fin.cases ⟨source8FaceCodes147,source8FaceRow147_checked⟩ (Fin.cases ⟨source8FaceCodes148,source8FaceRow148_checked⟩ (Fin.cases ⟨source8FaceCodes149,source8FaceRow149_checked⟩ (Fin.cases ⟨source8FaceCodes150,source8FaceRow150_checked⟩ (Fin.cases ⟨source8FaceCodes151,source8FaceRow151_checked⟩ (Fin.cases ⟨source8FaceCodes152,source8FaceRow152_checked⟩ (Fin.cases ⟨source8FaceCodes153,source8FaceRow153_checked⟩ (Fin.cases ⟨source8FaceCodes154,source8FaceRow154_checked⟩ (Fin.cases ⟨source8FaceCodes155,source8FaceRow155_checked⟩ (Fin.cases ⟨source8FaceCodes156,source8FaceRow156_checked⟩ (Fin.cases ⟨source8FaceCodes157,source8FaceRow157_checked⟩ (Fin.cases ⟨source8FaceCodes158,source8FaceRow158_checked⟩ (Fin.cases ⟨source8FaceCodes159,source8FaceRow159_checked⟩ (Fin.cases ⟨source8FaceCodes160,source8FaceRow160_checked⟩ (Fin.cases ⟨source8FaceCodes161,source8FaceRow161_checked⟩ (Fin.cases ⟨source8FaceCodes162,source8FaceRow162_checked⟩ (Fin.cases ⟨source8FaceCodes163,source8FaceRow163_checked⟩ (Fin.cases ⟨source8FaceCodes164,source8FaceRow164_checked⟩ (Fin.cases ⟨source8FaceCodes165,source8FaceRow165_checked⟩ (Fin.cases ⟨source8FaceCodes166,source8FaceRow166_checked⟩ (Fin.cases ⟨source8FaceCodes167,source8FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+168) default)
      (sourceFamily8.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes168,source8FaceRow168_checked⟩ (Fin.cases ⟨source8FaceCodes169,source8FaceRow169_checked⟩ (Fin.cases ⟨source8FaceCodes170,source8FaceRow170_checked⟩ (Fin.cases ⟨source8FaceCodes171,source8FaceRow171_checked⟩ (Fin.cases ⟨source8FaceCodes172,source8FaceRow172_checked⟩ (Fin.cases ⟨source8FaceCodes173,source8FaceRow173_checked⟩ (Fin.cases ⟨source8FaceCodes174,source8FaceRow174_checked⟩ (Fin.cases ⟨source8FaceCodes175,source8FaceRow175_checked⟩ (Fin.cases ⟨source8FaceCodes176,source8FaceRow176_checked⟩ (Fin.cases ⟨source8FaceCodes177,source8FaceRow177_checked⟩ (Fin.cases ⟨source8FaceCodes178,source8FaceRow178_checked⟩ (Fin.cases ⟨source8FaceCodes179,source8FaceRow179_checked⟩ (Fin.cases ⟨source8FaceCodes180,source8FaceRow180_checked⟩ (Fin.cases ⟨source8FaceCodes181,source8FaceRow181_checked⟩ (Fin.cases ⟨source8FaceCodes182,source8FaceRow182_checked⟩ (Fin.cases ⟨source8FaceCodes183,source8FaceRow183_checked⟩ (Fin.cases ⟨source8FaceCodes184,source8FaceRow184_checked⟩ (Fin.cases ⟨source8FaceCodes185,source8FaceRow185_checked⟩ (Fin.cases ⟨source8FaceCodes186,source8FaceRow186_checked⟩ (Fin.cases ⟨source8FaceCodes187,source8FaceRow187_checked⟩ (Fin.cases ⟨source8FaceCodes188,source8FaceRow188_checked⟩ (Fin.cases ⟨source8FaceCodes189,source8FaceRow189_checked⟩ (Fin.cases ⟨source8FaceCodes190,source8FaceRow190_checked⟩ (Fin.cases ⟨source8FaceCodes191,source8FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+192) default)
      (sourceFamily8.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes192,source8FaceRow192_checked⟩ (Fin.cases ⟨source8FaceCodes193,source8FaceRow193_checked⟩ (Fin.cases ⟨source8FaceCodes194,source8FaceRow194_checked⟩ (Fin.cases ⟨source8FaceCodes195,source8FaceRow195_checked⟩ (Fin.cases ⟨source8FaceCodes196,source8FaceRow196_checked⟩ (Fin.cases ⟨source8FaceCodes197,source8FaceRow197_checked⟩ (Fin.cases ⟨source8FaceCodes198,source8FaceRow198_checked⟩ (Fin.cases ⟨source8FaceCodes199,source8FaceRow199_checked⟩ (Fin.cases ⟨source8FaceCodes200,source8FaceRow200_checked⟩ (Fin.cases ⟨source8FaceCodes201,source8FaceRow201_checked⟩ (Fin.cases ⟨source8FaceCodes202,source8FaceRow202_checked⟩ (Fin.cases ⟨source8FaceCodes203,source8FaceRow203_checked⟩ (Fin.cases ⟨source8FaceCodes204,source8FaceRow204_checked⟩ (Fin.cases ⟨source8FaceCodes205,source8FaceRow205_checked⟩ (Fin.cases ⟨source8FaceCodes206,source8FaceRow206_checked⟩ (Fin.cases ⟨source8FaceCodes207,source8FaceRow207_checked⟩ (Fin.cases ⟨source8FaceCodes208,source8FaceRow208_checked⟩ (Fin.cases ⟨source8FaceCodes209,source8FaceRow209_checked⟩ (Fin.cases ⟨source8FaceCodes210,source8FaceRow210_checked⟩ (Fin.cases ⟨source8FaceCodes211,source8FaceRow211_checked⟩ (Fin.cases ⟨source8FaceCodes212,source8FaceRow212_checked⟩ (Fin.cases ⟨source8FaceCodes213,source8FaceRow213_checked⟩ (Fin.cases ⟨source8FaceCodes214,source8FaceRow214_checked⟩ (Fin.cases ⟨source8FaceCodes215,source8FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source8FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (sourceFamily8.getD (j.val+216) default)
      (sourceFamily8.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨source8FaceCodes216,source8FaceRow216_checked⟩ (Fin.cases ⟨source8FaceCodes217,source8FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem source8AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (sourceFamily8.getD i.val default)
      (sourceFamily8.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source8FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
