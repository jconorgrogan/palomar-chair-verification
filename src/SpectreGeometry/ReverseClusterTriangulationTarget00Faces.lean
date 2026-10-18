module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces00
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces01
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces02
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces03
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces04
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces05
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces06
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces07
public import SpectreGeometry.ReverseClusterTriangulationTarget00Faces08

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem target0Family_length : targetMeshFamily0.length = 208 := by decide

theorem target0FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+0) default)
      (targetMeshFamily0.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes0,target0FaceRow0_checked⟩ (Fin.cases ⟨target0FaceCodes1,target0FaceRow1_checked⟩ (Fin.cases ⟨target0FaceCodes2,target0FaceRow2_checked⟩ (Fin.cases ⟨target0FaceCodes3,target0FaceRow3_checked⟩ (Fin.cases ⟨target0FaceCodes4,target0FaceRow4_checked⟩ (Fin.cases ⟨target0FaceCodes5,target0FaceRow5_checked⟩ (Fin.cases ⟨target0FaceCodes6,target0FaceRow6_checked⟩ (Fin.cases ⟨target0FaceCodes7,target0FaceRow7_checked⟩ (Fin.cases ⟨target0FaceCodes8,target0FaceRow8_checked⟩ (Fin.cases ⟨target0FaceCodes9,target0FaceRow9_checked⟩ (Fin.cases ⟨target0FaceCodes10,target0FaceRow10_checked⟩ (Fin.cases ⟨target0FaceCodes11,target0FaceRow11_checked⟩ (Fin.cases ⟨target0FaceCodes12,target0FaceRow12_checked⟩ (Fin.cases ⟨target0FaceCodes13,target0FaceRow13_checked⟩ (Fin.cases ⟨target0FaceCodes14,target0FaceRow14_checked⟩ (Fin.cases ⟨target0FaceCodes15,target0FaceRow15_checked⟩ (Fin.cases ⟨target0FaceCodes16,target0FaceRow16_checked⟩ (Fin.cases ⟨target0FaceCodes17,target0FaceRow17_checked⟩ (Fin.cases ⟨target0FaceCodes18,target0FaceRow18_checked⟩ (Fin.cases ⟨target0FaceCodes19,target0FaceRow19_checked⟩ (Fin.cases ⟨target0FaceCodes20,target0FaceRow20_checked⟩ (Fin.cases ⟨target0FaceCodes21,target0FaceRow21_checked⟩ (Fin.cases ⟨target0FaceCodes22,target0FaceRow22_checked⟩ (Fin.cases ⟨target0FaceCodes23,target0FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+24) default)
      (targetMeshFamily0.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes24,target0FaceRow24_checked⟩ (Fin.cases ⟨target0FaceCodes25,target0FaceRow25_checked⟩ (Fin.cases ⟨target0FaceCodes26,target0FaceRow26_checked⟩ (Fin.cases ⟨target0FaceCodes27,target0FaceRow27_checked⟩ (Fin.cases ⟨target0FaceCodes28,target0FaceRow28_checked⟩ (Fin.cases ⟨target0FaceCodes29,target0FaceRow29_checked⟩ (Fin.cases ⟨target0FaceCodes30,target0FaceRow30_checked⟩ (Fin.cases ⟨target0FaceCodes31,target0FaceRow31_checked⟩ (Fin.cases ⟨target0FaceCodes32,target0FaceRow32_checked⟩ (Fin.cases ⟨target0FaceCodes33,target0FaceRow33_checked⟩ (Fin.cases ⟨target0FaceCodes34,target0FaceRow34_checked⟩ (Fin.cases ⟨target0FaceCodes35,target0FaceRow35_checked⟩ (Fin.cases ⟨target0FaceCodes36,target0FaceRow36_checked⟩ (Fin.cases ⟨target0FaceCodes37,target0FaceRow37_checked⟩ (Fin.cases ⟨target0FaceCodes38,target0FaceRow38_checked⟩ (Fin.cases ⟨target0FaceCodes39,target0FaceRow39_checked⟩ (Fin.cases ⟨target0FaceCodes40,target0FaceRow40_checked⟩ (Fin.cases ⟨target0FaceCodes41,target0FaceRow41_checked⟩ (Fin.cases ⟨target0FaceCodes42,target0FaceRow42_checked⟩ (Fin.cases ⟨target0FaceCodes43,target0FaceRow43_checked⟩ (Fin.cases ⟨target0FaceCodes44,target0FaceRow44_checked⟩ (Fin.cases ⟨target0FaceCodes45,target0FaceRow45_checked⟩ (Fin.cases ⟨target0FaceCodes46,target0FaceRow46_checked⟩ (Fin.cases ⟨target0FaceCodes47,target0FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+48) default)
      (targetMeshFamily0.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes48,target0FaceRow48_checked⟩ (Fin.cases ⟨target0FaceCodes49,target0FaceRow49_checked⟩ (Fin.cases ⟨target0FaceCodes50,target0FaceRow50_checked⟩ (Fin.cases ⟨target0FaceCodes51,target0FaceRow51_checked⟩ (Fin.cases ⟨target0FaceCodes52,target0FaceRow52_checked⟩ (Fin.cases ⟨target0FaceCodes53,target0FaceRow53_checked⟩ (Fin.cases ⟨target0FaceCodes54,target0FaceRow54_checked⟩ (Fin.cases ⟨target0FaceCodes55,target0FaceRow55_checked⟩ (Fin.cases ⟨target0FaceCodes56,target0FaceRow56_checked⟩ (Fin.cases ⟨target0FaceCodes57,target0FaceRow57_checked⟩ (Fin.cases ⟨target0FaceCodes58,target0FaceRow58_checked⟩ (Fin.cases ⟨target0FaceCodes59,target0FaceRow59_checked⟩ (Fin.cases ⟨target0FaceCodes60,target0FaceRow60_checked⟩ (Fin.cases ⟨target0FaceCodes61,target0FaceRow61_checked⟩ (Fin.cases ⟨target0FaceCodes62,target0FaceRow62_checked⟩ (Fin.cases ⟨target0FaceCodes63,target0FaceRow63_checked⟩ (Fin.cases ⟨target0FaceCodes64,target0FaceRow64_checked⟩ (Fin.cases ⟨target0FaceCodes65,target0FaceRow65_checked⟩ (Fin.cases ⟨target0FaceCodes66,target0FaceRow66_checked⟩ (Fin.cases ⟨target0FaceCodes67,target0FaceRow67_checked⟩ (Fin.cases ⟨target0FaceCodes68,target0FaceRow68_checked⟩ (Fin.cases ⟨target0FaceCodes69,target0FaceRow69_checked⟩ (Fin.cases ⟨target0FaceCodes70,target0FaceRow70_checked⟩ (Fin.cases ⟨target0FaceCodes71,target0FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+72) default)
      (targetMeshFamily0.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes72,target0FaceRow72_checked⟩ (Fin.cases ⟨target0FaceCodes73,target0FaceRow73_checked⟩ (Fin.cases ⟨target0FaceCodes74,target0FaceRow74_checked⟩ (Fin.cases ⟨target0FaceCodes75,target0FaceRow75_checked⟩ (Fin.cases ⟨target0FaceCodes76,target0FaceRow76_checked⟩ (Fin.cases ⟨target0FaceCodes77,target0FaceRow77_checked⟩ (Fin.cases ⟨target0FaceCodes78,target0FaceRow78_checked⟩ (Fin.cases ⟨target0FaceCodes79,target0FaceRow79_checked⟩ (Fin.cases ⟨target0FaceCodes80,target0FaceRow80_checked⟩ (Fin.cases ⟨target0FaceCodes81,target0FaceRow81_checked⟩ (Fin.cases ⟨target0FaceCodes82,target0FaceRow82_checked⟩ (Fin.cases ⟨target0FaceCodes83,target0FaceRow83_checked⟩ (Fin.cases ⟨target0FaceCodes84,target0FaceRow84_checked⟩ (Fin.cases ⟨target0FaceCodes85,target0FaceRow85_checked⟩ (Fin.cases ⟨target0FaceCodes86,target0FaceRow86_checked⟩ (Fin.cases ⟨target0FaceCodes87,target0FaceRow87_checked⟩ (Fin.cases ⟨target0FaceCodes88,target0FaceRow88_checked⟩ (Fin.cases ⟨target0FaceCodes89,target0FaceRow89_checked⟩ (Fin.cases ⟨target0FaceCodes90,target0FaceRow90_checked⟩ (Fin.cases ⟨target0FaceCodes91,target0FaceRow91_checked⟩ (Fin.cases ⟨target0FaceCodes92,target0FaceRow92_checked⟩ (Fin.cases ⟨target0FaceCodes93,target0FaceRow93_checked⟩ (Fin.cases ⟨target0FaceCodes94,target0FaceRow94_checked⟩ (Fin.cases ⟨target0FaceCodes95,target0FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+96) default)
      (targetMeshFamily0.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes96,target0FaceRow96_checked⟩ (Fin.cases ⟨target0FaceCodes97,target0FaceRow97_checked⟩ (Fin.cases ⟨target0FaceCodes98,target0FaceRow98_checked⟩ (Fin.cases ⟨target0FaceCodes99,target0FaceRow99_checked⟩ (Fin.cases ⟨target0FaceCodes100,target0FaceRow100_checked⟩ (Fin.cases ⟨target0FaceCodes101,target0FaceRow101_checked⟩ (Fin.cases ⟨target0FaceCodes102,target0FaceRow102_checked⟩ (Fin.cases ⟨target0FaceCodes103,target0FaceRow103_checked⟩ (Fin.cases ⟨target0FaceCodes104,target0FaceRow104_checked⟩ (Fin.cases ⟨target0FaceCodes105,target0FaceRow105_checked⟩ (Fin.cases ⟨target0FaceCodes106,target0FaceRow106_checked⟩ (Fin.cases ⟨target0FaceCodes107,target0FaceRow107_checked⟩ (Fin.cases ⟨target0FaceCodes108,target0FaceRow108_checked⟩ (Fin.cases ⟨target0FaceCodes109,target0FaceRow109_checked⟩ (Fin.cases ⟨target0FaceCodes110,target0FaceRow110_checked⟩ (Fin.cases ⟨target0FaceCodes111,target0FaceRow111_checked⟩ (Fin.cases ⟨target0FaceCodes112,target0FaceRow112_checked⟩ (Fin.cases ⟨target0FaceCodes113,target0FaceRow113_checked⟩ (Fin.cases ⟨target0FaceCodes114,target0FaceRow114_checked⟩ (Fin.cases ⟨target0FaceCodes115,target0FaceRow115_checked⟩ (Fin.cases ⟨target0FaceCodes116,target0FaceRow116_checked⟩ (Fin.cases ⟨target0FaceCodes117,target0FaceRow117_checked⟩ (Fin.cases ⟨target0FaceCodes118,target0FaceRow118_checked⟩ (Fin.cases ⟨target0FaceCodes119,target0FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+120) default)
      (targetMeshFamily0.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes120,target0FaceRow120_checked⟩ (Fin.cases ⟨target0FaceCodes121,target0FaceRow121_checked⟩ (Fin.cases ⟨target0FaceCodes122,target0FaceRow122_checked⟩ (Fin.cases ⟨target0FaceCodes123,target0FaceRow123_checked⟩ (Fin.cases ⟨target0FaceCodes124,target0FaceRow124_checked⟩ (Fin.cases ⟨target0FaceCodes125,target0FaceRow125_checked⟩ (Fin.cases ⟨target0FaceCodes126,target0FaceRow126_checked⟩ (Fin.cases ⟨target0FaceCodes127,target0FaceRow127_checked⟩ (Fin.cases ⟨target0FaceCodes128,target0FaceRow128_checked⟩ (Fin.cases ⟨target0FaceCodes129,target0FaceRow129_checked⟩ (Fin.cases ⟨target0FaceCodes130,target0FaceRow130_checked⟩ (Fin.cases ⟨target0FaceCodes131,target0FaceRow131_checked⟩ (Fin.cases ⟨target0FaceCodes132,target0FaceRow132_checked⟩ (Fin.cases ⟨target0FaceCodes133,target0FaceRow133_checked⟩ (Fin.cases ⟨target0FaceCodes134,target0FaceRow134_checked⟩ (Fin.cases ⟨target0FaceCodes135,target0FaceRow135_checked⟩ (Fin.cases ⟨target0FaceCodes136,target0FaceRow136_checked⟩ (Fin.cases ⟨target0FaceCodes137,target0FaceRow137_checked⟩ (Fin.cases ⟨target0FaceCodes138,target0FaceRow138_checked⟩ (Fin.cases ⟨target0FaceCodes139,target0FaceRow139_checked⟩ (Fin.cases ⟨target0FaceCodes140,target0FaceRow140_checked⟩ (Fin.cases ⟨target0FaceCodes141,target0FaceRow141_checked⟩ (Fin.cases ⟨target0FaceCodes142,target0FaceRow142_checked⟩ (Fin.cases ⟨target0FaceCodes143,target0FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+144) default)
      (targetMeshFamily0.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes144,target0FaceRow144_checked⟩ (Fin.cases ⟨target0FaceCodes145,target0FaceRow145_checked⟩ (Fin.cases ⟨target0FaceCodes146,target0FaceRow146_checked⟩ (Fin.cases ⟨target0FaceCodes147,target0FaceRow147_checked⟩ (Fin.cases ⟨target0FaceCodes148,target0FaceRow148_checked⟩ (Fin.cases ⟨target0FaceCodes149,target0FaceRow149_checked⟩ (Fin.cases ⟨target0FaceCodes150,target0FaceRow150_checked⟩ (Fin.cases ⟨target0FaceCodes151,target0FaceRow151_checked⟩ (Fin.cases ⟨target0FaceCodes152,target0FaceRow152_checked⟩ (Fin.cases ⟨target0FaceCodes153,target0FaceRow153_checked⟩ (Fin.cases ⟨target0FaceCodes154,target0FaceRow154_checked⟩ (Fin.cases ⟨target0FaceCodes155,target0FaceRow155_checked⟩ (Fin.cases ⟨target0FaceCodes156,target0FaceRow156_checked⟩ (Fin.cases ⟨target0FaceCodes157,target0FaceRow157_checked⟩ (Fin.cases ⟨target0FaceCodes158,target0FaceRow158_checked⟩ (Fin.cases ⟨target0FaceCodes159,target0FaceRow159_checked⟩ (Fin.cases ⟨target0FaceCodes160,target0FaceRow160_checked⟩ (Fin.cases ⟨target0FaceCodes161,target0FaceRow161_checked⟩ (Fin.cases ⟨target0FaceCodes162,target0FaceRow162_checked⟩ (Fin.cases ⟨target0FaceCodes163,target0FaceRow163_checked⟩ (Fin.cases ⟨target0FaceCodes164,target0FaceRow164_checked⟩ (Fin.cases ⟨target0FaceCodes165,target0FaceRow165_checked⟩ (Fin.cases ⟨target0FaceCodes166,target0FaceRow166_checked⟩ (Fin.cases ⟨target0FaceCodes167,target0FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+168) default)
      (targetMeshFamily0.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes168,target0FaceRow168_checked⟩ (Fin.cases ⟨target0FaceCodes169,target0FaceRow169_checked⟩ (Fin.cases ⟨target0FaceCodes170,target0FaceRow170_checked⟩ (Fin.cases ⟨target0FaceCodes171,target0FaceRow171_checked⟩ (Fin.cases ⟨target0FaceCodes172,target0FaceRow172_checked⟩ (Fin.cases ⟨target0FaceCodes173,target0FaceRow173_checked⟩ (Fin.cases ⟨target0FaceCodes174,target0FaceRow174_checked⟩ (Fin.cases ⟨target0FaceCodes175,target0FaceRow175_checked⟩ (Fin.cases ⟨target0FaceCodes176,target0FaceRow176_checked⟩ (Fin.cases ⟨target0FaceCodes177,target0FaceRow177_checked⟩ (Fin.cases ⟨target0FaceCodes178,target0FaceRow178_checked⟩ (Fin.cases ⟨target0FaceCodes179,target0FaceRow179_checked⟩ (Fin.cases ⟨target0FaceCodes180,target0FaceRow180_checked⟩ (Fin.cases ⟨target0FaceCodes181,target0FaceRow181_checked⟩ (Fin.cases ⟨target0FaceCodes182,target0FaceRow182_checked⟩ (Fin.cases ⟨target0FaceCodes183,target0FaceRow183_checked⟩ (Fin.cases ⟨target0FaceCodes184,target0FaceRow184_checked⟩ (Fin.cases ⟨target0FaceCodes185,target0FaceRow185_checked⟩ (Fin.cases ⟨target0FaceCodes186,target0FaceRow186_checked⟩ (Fin.cases ⟨target0FaceCodes187,target0FaceRow187_checked⟩ (Fin.cases ⟨target0FaceCodes188,target0FaceRow188_checked⟩ (Fin.cases ⟨target0FaceCodes189,target0FaceRow189_checked⟩ (Fin.cases ⟨target0FaceCodes190,target0FaceRow190_checked⟩ (Fin.cases ⟨target0FaceCodes191,target0FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target0FaceRowsBlock8 : ∀ j : Fin 16,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD (j.val+192) default)
      (targetMeshFamily0.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨target0FaceCodes192,target0FaceRow192_checked⟩ (Fin.cases ⟨target0FaceCodes193,target0FaceRow193_checked⟩ (Fin.cases ⟨target0FaceCodes194,target0FaceRow194_checked⟩ (Fin.cases ⟨target0FaceCodes195,target0FaceRow195_checked⟩ (Fin.cases ⟨target0FaceCodes196,target0FaceRow196_checked⟩ (Fin.cases ⟨target0FaceCodes197,target0FaceRow197_checked⟩ (Fin.cases ⟨target0FaceCodes198,target0FaceRow198_checked⟩ (Fin.cases ⟨target0FaceCodes199,target0FaceRow199_checked⟩ (Fin.cases ⟨target0FaceCodes200,target0FaceRow200_checked⟩ (Fin.cases ⟨target0FaceCodes201,target0FaceRow201_checked⟩ (Fin.cases ⟨target0FaceCodes202,target0FaceRow202_checked⟩ (Fin.cases ⟨target0FaceCodes203,target0FaceRow203_checked⟩ (Fin.cases ⟨target0FaceCodes204,target0FaceRow204_checked⟩ (Fin.cases ⟨target0FaceCodes205,target0FaceRow205_checked⟩ (Fin.cases ⟨target0FaceCodes206,target0FaceRow206_checked⟩ (Fin.cases ⟨target0FaceCodes207,target0FaceRow207_checked⟩ (fun i => Fin.elim0 i))))))))))))))))

theorem target0AllFaceRows : ∀ i : Fin 208,
    ∃ codes, packetFaceRowB (targetMeshFamily0.getD i.val default)
      (targetMeshFamily0.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  have hs : 192 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using target0FaceRowsBlock8
    ⟨i.val-192,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
