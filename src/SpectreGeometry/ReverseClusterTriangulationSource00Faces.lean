module

public import SpectreGeometry.ReverseClusterTriangulationSource00Faces00
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces01
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces02
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces03
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces04
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces05
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces06
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces07
public import SpectreGeometry.ReverseClusterTriangulationSource00Faces08

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem source0Family_length : sourceFamily0.length = 208 := by decide

theorem source0FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+0) default)
      (sourceFamily0.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes0,source0FaceRow0_checked⟩ (Fin.cases ⟨source0FaceCodes1,source0FaceRow1_checked⟩ (Fin.cases ⟨source0FaceCodes2,source0FaceRow2_checked⟩ (Fin.cases ⟨source0FaceCodes3,source0FaceRow3_checked⟩ (Fin.cases ⟨source0FaceCodes4,source0FaceRow4_checked⟩ (Fin.cases ⟨source0FaceCodes5,source0FaceRow5_checked⟩ (Fin.cases ⟨source0FaceCodes6,source0FaceRow6_checked⟩ (Fin.cases ⟨source0FaceCodes7,source0FaceRow7_checked⟩ (Fin.cases ⟨source0FaceCodes8,source0FaceRow8_checked⟩ (Fin.cases ⟨source0FaceCodes9,source0FaceRow9_checked⟩ (Fin.cases ⟨source0FaceCodes10,source0FaceRow10_checked⟩ (Fin.cases ⟨source0FaceCodes11,source0FaceRow11_checked⟩ (Fin.cases ⟨source0FaceCodes12,source0FaceRow12_checked⟩ (Fin.cases ⟨source0FaceCodes13,source0FaceRow13_checked⟩ (Fin.cases ⟨source0FaceCodes14,source0FaceRow14_checked⟩ (Fin.cases ⟨source0FaceCodes15,source0FaceRow15_checked⟩ (Fin.cases ⟨source0FaceCodes16,source0FaceRow16_checked⟩ (Fin.cases ⟨source0FaceCodes17,source0FaceRow17_checked⟩ (Fin.cases ⟨source0FaceCodes18,source0FaceRow18_checked⟩ (Fin.cases ⟨source0FaceCodes19,source0FaceRow19_checked⟩ (Fin.cases ⟨source0FaceCodes20,source0FaceRow20_checked⟩ (Fin.cases ⟨source0FaceCodes21,source0FaceRow21_checked⟩ (Fin.cases ⟨source0FaceCodes22,source0FaceRow22_checked⟩ (Fin.cases ⟨source0FaceCodes23,source0FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+24) default)
      (sourceFamily0.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes24,source0FaceRow24_checked⟩ (Fin.cases ⟨source0FaceCodes25,source0FaceRow25_checked⟩ (Fin.cases ⟨source0FaceCodes26,source0FaceRow26_checked⟩ (Fin.cases ⟨source0FaceCodes27,source0FaceRow27_checked⟩ (Fin.cases ⟨source0FaceCodes28,source0FaceRow28_checked⟩ (Fin.cases ⟨source0FaceCodes29,source0FaceRow29_checked⟩ (Fin.cases ⟨source0FaceCodes30,source0FaceRow30_checked⟩ (Fin.cases ⟨source0FaceCodes31,source0FaceRow31_checked⟩ (Fin.cases ⟨source0FaceCodes32,source0FaceRow32_checked⟩ (Fin.cases ⟨source0FaceCodes33,source0FaceRow33_checked⟩ (Fin.cases ⟨source0FaceCodes34,source0FaceRow34_checked⟩ (Fin.cases ⟨source0FaceCodes35,source0FaceRow35_checked⟩ (Fin.cases ⟨source0FaceCodes36,source0FaceRow36_checked⟩ (Fin.cases ⟨source0FaceCodes37,source0FaceRow37_checked⟩ (Fin.cases ⟨source0FaceCodes38,source0FaceRow38_checked⟩ (Fin.cases ⟨source0FaceCodes39,source0FaceRow39_checked⟩ (Fin.cases ⟨source0FaceCodes40,source0FaceRow40_checked⟩ (Fin.cases ⟨source0FaceCodes41,source0FaceRow41_checked⟩ (Fin.cases ⟨source0FaceCodes42,source0FaceRow42_checked⟩ (Fin.cases ⟨source0FaceCodes43,source0FaceRow43_checked⟩ (Fin.cases ⟨source0FaceCodes44,source0FaceRow44_checked⟩ (Fin.cases ⟨source0FaceCodes45,source0FaceRow45_checked⟩ (Fin.cases ⟨source0FaceCodes46,source0FaceRow46_checked⟩ (Fin.cases ⟨source0FaceCodes47,source0FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+48) default)
      (sourceFamily0.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes48,source0FaceRow48_checked⟩ (Fin.cases ⟨source0FaceCodes49,source0FaceRow49_checked⟩ (Fin.cases ⟨source0FaceCodes50,source0FaceRow50_checked⟩ (Fin.cases ⟨source0FaceCodes51,source0FaceRow51_checked⟩ (Fin.cases ⟨source0FaceCodes52,source0FaceRow52_checked⟩ (Fin.cases ⟨source0FaceCodes53,source0FaceRow53_checked⟩ (Fin.cases ⟨source0FaceCodes54,source0FaceRow54_checked⟩ (Fin.cases ⟨source0FaceCodes55,source0FaceRow55_checked⟩ (Fin.cases ⟨source0FaceCodes56,source0FaceRow56_checked⟩ (Fin.cases ⟨source0FaceCodes57,source0FaceRow57_checked⟩ (Fin.cases ⟨source0FaceCodes58,source0FaceRow58_checked⟩ (Fin.cases ⟨source0FaceCodes59,source0FaceRow59_checked⟩ (Fin.cases ⟨source0FaceCodes60,source0FaceRow60_checked⟩ (Fin.cases ⟨source0FaceCodes61,source0FaceRow61_checked⟩ (Fin.cases ⟨source0FaceCodes62,source0FaceRow62_checked⟩ (Fin.cases ⟨source0FaceCodes63,source0FaceRow63_checked⟩ (Fin.cases ⟨source0FaceCodes64,source0FaceRow64_checked⟩ (Fin.cases ⟨source0FaceCodes65,source0FaceRow65_checked⟩ (Fin.cases ⟨source0FaceCodes66,source0FaceRow66_checked⟩ (Fin.cases ⟨source0FaceCodes67,source0FaceRow67_checked⟩ (Fin.cases ⟨source0FaceCodes68,source0FaceRow68_checked⟩ (Fin.cases ⟨source0FaceCodes69,source0FaceRow69_checked⟩ (Fin.cases ⟨source0FaceCodes70,source0FaceRow70_checked⟩ (Fin.cases ⟨source0FaceCodes71,source0FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+72) default)
      (sourceFamily0.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes72,source0FaceRow72_checked⟩ (Fin.cases ⟨source0FaceCodes73,source0FaceRow73_checked⟩ (Fin.cases ⟨source0FaceCodes74,source0FaceRow74_checked⟩ (Fin.cases ⟨source0FaceCodes75,source0FaceRow75_checked⟩ (Fin.cases ⟨source0FaceCodes76,source0FaceRow76_checked⟩ (Fin.cases ⟨source0FaceCodes77,source0FaceRow77_checked⟩ (Fin.cases ⟨source0FaceCodes78,source0FaceRow78_checked⟩ (Fin.cases ⟨source0FaceCodes79,source0FaceRow79_checked⟩ (Fin.cases ⟨source0FaceCodes80,source0FaceRow80_checked⟩ (Fin.cases ⟨source0FaceCodes81,source0FaceRow81_checked⟩ (Fin.cases ⟨source0FaceCodes82,source0FaceRow82_checked⟩ (Fin.cases ⟨source0FaceCodes83,source0FaceRow83_checked⟩ (Fin.cases ⟨source0FaceCodes84,source0FaceRow84_checked⟩ (Fin.cases ⟨source0FaceCodes85,source0FaceRow85_checked⟩ (Fin.cases ⟨source0FaceCodes86,source0FaceRow86_checked⟩ (Fin.cases ⟨source0FaceCodes87,source0FaceRow87_checked⟩ (Fin.cases ⟨source0FaceCodes88,source0FaceRow88_checked⟩ (Fin.cases ⟨source0FaceCodes89,source0FaceRow89_checked⟩ (Fin.cases ⟨source0FaceCodes90,source0FaceRow90_checked⟩ (Fin.cases ⟨source0FaceCodes91,source0FaceRow91_checked⟩ (Fin.cases ⟨source0FaceCodes92,source0FaceRow92_checked⟩ (Fin.cases ⟨source0FaceCodes93,source0FaceRow93_checked⟩ (Fin.cases ⟨source0FaceCodes94,source0FaceRow94_checked⟩ (Fin.cases ⟨source0FaceCodes95,source0FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+96) default)
      (sourceFamily0.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes96,source0FaceRow96_checked⟩ (Fin.cases ⟨source0FaceCodes97,source0FaceRow97_checked⟩ (Fin.cases ⟨source0FaceCodes98,source0FaceRow98_checked⟩ (Fin.cases ⟨source0FaceCodes99,source0FaceRow99_checked⟩ (Fin.cases ⟨source0FaceCodes100,source0FaceRow100_checked⟩ (Fin.cases ⟨source0FaceCodes101,source0FaceRow101_checked⟩ (Fin.cases ⟨source0FaceCodes102,source0FaceRow102_checked⟩ (Fin.cases ⟨source0FaceCodes103,source0FaceRow103_checked⟩ (Fin.cases ⟨source0FaceCodes104,source0FaceRow104_checked⟩ (Fin.cases ⟨source0FaceCodes105,source0FaceRow105_checked⟩ (Fin.cases ⟨source0FaceCodes106,source0FaceRow106_checked⟩ (Fin.cases ⟨source0FaceCodes107,source0FaceRow107_checked⟩ (Fin.cases ⟨source0FaceCodes108,source0FaceRow108_checked⟩ (Fin.cases ⟨source0FaceCodes109,source0FaceRow109_checked⟩ (Fin.cases ⟨source0FaceCodes110,source0FaceRow110_checked⟩ (Fin.cases ⟨source0FaceCodes111,source0FaceRow111_checked⟩ (Fin.cases ⟨source0FaceCodes112,source0FaceRow112_checked⟩ (Fin.cases ⟨source0FaceCodes113,source0FaceRow113_checked⟩ (Fin.cases ⟨source0FaceCodes114,source0FaceRow114_checked⟩ (Fin.cases ⟨source0FaceCodes115,source0FaceRow115_checked⟩ (Fin.cases ⟨source0FaceCodes116,source0FaceRow116_checked⟩ (Fin.cases ⟨source0FaceCodes117,source0FaceRow117_checked⟩ (Fin.cases ⟨source0FaceCodes118,source0FaceRow118_checked⟩ (Fin.cases ⟨source0FaceCodes119,source0FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+120) default)
      (sourceFamily0.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes120,source0FaceRow120_checked⟩ (Fin.cases ⟨source0FaceCodes121,source0FaceRow121_checked⟩ (Fin.cases ⟨source0FaceCodes122,source0FaceRow122_checked⟩ (Fin.cases ⟨source0FaceCodes123,source0FaceRow123_checked⟩ (Fin.cases ⟨source0FaceCodes124,source0FaceRow124_checked⟩ (Fin.cases ⟨source0FaceCodes125,source0FaceRow125_checked⟩ (Fin.cases ⟨source0FaceCodes126,source0FaceRow126_checked⟩ (Fin.cases ⟨source0FaceCodes127,source0FaceRow127_checked⟩ (Fin.cases ⟨source0FaceCodes128,source0FaceRow128_checked⟩ (Fin.cases ⟨source0FaceCodes129,source0FaceRow129_checked⟩ (Fin.cases ⟨source0FaceCodes130,source0FaceRow130_checked⟩ (Fin.cases ⟨source0FaceCodes131,source0FaceRow131_checked⟩ (Fin.cases ⟨source0FaceCodes132,source0FaceRow132_checked⟩ (Fin.cases ⟨source0FaceCodes133,source0FaceRow133_checked⟩ (Fin.cases ⟨source0FaceCodes134,source0FaceRow134_checked⟩ (Fin.cases ⟨source0FaceCodes135,source0FaceRow135_checked⟩ (Fin.cases ⟨source0FaceCodes136,source0FaceRow136_checked⟩ (Fin.cases ⟨source0FaceCodes137,source0FaceRow137_checked⟩ (Fin.cases ⟨source0FaceCodes138,source0FaceRow138_checked⟩ (Fin.cases ⟨source0FaceCodes139,source0FaceRow139_checked⟩ (Fin.cases ⟨source0FaceCodes140,source0FaceRow140_checked⟩ (Fin.cases ⟨source0FaceCodes141,source0FaceRow141_checked⟩ (Fin.cases ⟨source0FaceCodes142,source0FaceRow142_checked⟩ (Fin.cases ⟨source0FaceCodes143,source0FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+144) default)
      (sourceFamily0.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes144,source0FaceRow144_checked⟩ (Fin.cases ⟨source0FaceCodes145,source0FaceRow145_checked⟩ (Fin.cases ⟨source0FaceCodes146,source0FaceRow146_checked⟩ (Fin.cases ⟨source0FaceCodes147,source0FaceRow147_checked⟩ (Fin.cases ⟨source0FaceCodes148,source0FaceRow148_checked⟩ (Fin.cases ⟨source0FaceCodes149,source0FaceRow149_checked⟩ (Fin.cases ⟨source0FaceCodes150,source0FaceRow150_checked⟩ (Fin.cases ⟨source0FaceCodes151,source0FaceRow151_checked⟩ (Fin.cases ⟨source0FaceCodes152,source0FaceRow152_checked⟩ (Fin.cases ⟨source0FaceCodes153,source0FaceRow153_checked⟩ (Fin.cases ⟨source0FaceCodes154,source0FaceRow154_checked⟩ (Fin.cases ⟨source0FaceCodes155,source0FaceRow155_checked⟩ (Fin.cases ⟨source0FaceCodes156,source0FaceRow156_checked⟩ (Fin.cases ⟨source0FaceCodes157,source0FaceRow157_checked⟩ (Fin.cases ⟨source0FaceCodes158,source0FaceRow158_checked⟩ (Fin.cases ⟨source0FaceCodes159,source0FaceRow159_checked⟩ (Fin.cases ⟨source0FaceCodes160,source0FaceRow160_checked⟩ (Fin.cases ⟨source0FaceCodes161,source0FaceRow161_checked⟩ (Fin.cases ⟨source0FaceCodes162,source0FaceRow162_checked⟩ (Fin.cases ⟨source0FaceCodes163,source0FaceRow163_checked⟩ (Fin.cases ⟨source0FaceCodes164,source0FaceRow164_checked⟩ (Fin.cases ⟨source0FaceCodes165,source0FaceRow165_checked⟩ (Fin.cases ⟨source0FaceCodes166,source0FaceRow166_checked⟩ (Fin.cases ⟨source0FaceCodes167,source0FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+168) default)
      (sourceFamily0.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes168,source0FaceRow168_checked⟩ (Fin.cases ⟨source0FaceCodes169,source0FaceRow169_checked⟩ (Fin.cases ⟨source0FaceCodes170,source0FaceRow170_checked⟩ (Fin.cases ⟨source0FaceCodes171,source0FaceRow171_checked⟩ (Fin.cases ⟨source0FaceCodes172,source0FaceRow172_checked⟩ (Fin.cases ⟨source0FaceCodes173,source0FaceRow173_checked⟩ (Fin.cases ⟨source0FaceCodes174,source0FaceRow174_checked⟩ (Fin.cases ⟨source0FaceCodes175,source0FaceRow175_checked⟩ (Fin.cases ⟨source0FaceCodes176,source0FaceRow176_checked⟩ (Fin.cases ⟨source0FaceCodes177,source0FaceRow177_checked⟩ (Fin.cases ⟨source0FaceCodes178,source0FaceRow178_checked⟩ (Fin.cases ⟨source0FaceCodes179,source0FaceRow179_checked⟩ (Fin.cases ⟨source0FaceCodes180,source0FaceRow180_checked⟩ (Fin.cases ⟨source0FaceCodes181,source0FaceRow181_checked⟩ (Fin.cases ⟨source0FaceCodes182,source0FaceRow182_checked⟩ (Fin.cases ⟨source0FaceCodes183,source0FaceRow183_checked⟩ (Fin.cases ⟨source0FaceCodes184,source0FaceRow184_checked⟩ (Fin.cases ⟨source0FaceCodes185,source0FaceRow185_checked⟩ (Fin.cases ⟨source0FaceCodes186,source0FaceRow186_checked⟩ (Fin.cases ⟨source0FaceCodes187,source0FaceRow187_checked⟩ (Fin.cases ⟨source0FaceCodes188,source0FaceRow188_checked⟩ (Fin.cases ⟨source0FaceCodes189,source0FaceRow189_checked⟩ (Fin.cases ⟨source0FaceCodes190,source0FaceRow190_checked⟩ (Fin.cases ⟨source0FaceCodes191,source0FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem source0FaceRowsBlock8 : ∀ j : Fin 16,
    ∃ codes, packetFaceRowB (sourceFamily0.getD (j.val+192) default)
      (sourceFamily0.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨source0FaceCodes192,source0FaceRow192_checked⟩ (Fin.cases ⟨source0FaceCodes193,source0FaceRow193_checked⟩ (Fin.cases ⟨source0FaceCodes194,source0FaceRow194_checked⟩ (Fin.cases ⟨source0FaceCodes195,source0FaceRow195_checked⟩ (Fin.cases ⟨source0FaceCodes196,source0FaceRow196_checked⟩ (Fin.cases ⟨source0FaceCodes197,source0FaceRow197_checked⟩ (Fin.cases ⟨source0FaceCodes198,source0FaceRow198_checked⟩ (Fin.cases ⟨source0FaceCodes199,source0FaceRow199_checked⟩ (Fin.cases ⟨source0FaceCodes200,source0FaceRow200_checked⟩ (Fin.cases ⟨source0FaceCodes201,source0FaceRow201_checked⟩ (Fin.cases ⟨source0FaceCodes202,source0FaceRow202_checked⟩ (Fin.cases ⟨source0FaceCodes203,source0FaceRow203_checked⟩ (Fin.cases ⟨source0FaceCodes204,source0FaceRow204_checked⟩ (Fin.cases ⟨source0FaceCodes205,source0FaceRow205_checked⟩ (Fin.cases ⟨source0FaceCodes206,source0FaceRow206_checked⟩ (Fin.cases ⟨source0FaceCodes207,source0FaceRow207_checked⟩ (fun i => Fin.elim0 i))))))))))))))))

theorem source0AllFaceRows : ∀ i : Fin 208,
    ∃ codes, packetFaceRowB (sourceFamily0.getD i.val default)
      (sourceFamily0.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  have hs : 192 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using source0FaceRowsBlock8
    ⟨i.val-192,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
