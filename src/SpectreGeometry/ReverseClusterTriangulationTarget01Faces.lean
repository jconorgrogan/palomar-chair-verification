module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces00
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces01
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces02
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces03
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces04
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces05
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces06
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces07
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces08
public import SpectreGeometry.ReverseClusterTriangulationTarget01Faces09

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem target1Family_length : targetMeshFamily1.length = 218 := by decide

theorem target1FaceRowsBlock0 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+0) default)
      (targetMeshFamily1.take (j.val+0)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes0,target1FaceRow0_checked⟩ (Fin.cases ⟨target1FaceCodes1,target1FaceRow1_checked⟩ (Fin.cases ⟨target1FaceCodes2,target1FaceRow2_checked⟩ (Fin.cases ⟨target1FaceCodes3,target1FaceRow3_checked⟩ (Fin.cases ⟨target1FaceCodes4,target1FaceRow4_checked⟩ (Fin.cases ⟨target1FaceCodes5,target1FaceRow5_checked⟩ (Fin.cases ⟨target1FaceCodes6,target1FaceRow6_checked⟩ (Fin.cases ⟨target1FaceCodes7,target1FaceRow7_checked⟩ (Fin.cases ⟨target1FaceCodes8,target1FaceRow8_checked⟩ (Fin.cases ⟨target1FaceCodes9,target1FaceRow9_checked⟩ (Fin.cases ⟨target1FaceCodes10,target1FaceRow10_checked⟩ (Fin.cases ⟨target1FaceCodes11,target1FaceRow11_checked⟩ (Fin.cases ⟨target1FaceCodes12,target1FaceRow12_checked⟩ (Fin.cases ⟨target1FaceCodes13,target1FaceRow13_checked⟩ (Fin.cases ⟨target1FaceCodes14,target1FaceRow14_checked⟩ (Fin.cases ⟨target1FaceCodes15,target1FaceRow15_checked⟩ (Fin.cases ⟨target1FaceCodes16,target1FaceRow16_checked⟩ (Fin.cases ⟨target1FaceCodes17,target1FaceRow17_checked⟩ (Fin.cases ⟨target1FaceCodes18,target1FaceRow18_checked⟩ (Fin.cases ⟨target1FaceCodes19,target1FaceRow19_checked⟩ (Fin.cases ⟨target1FaceCodes20,target1FaceRow20_checked⟩ (Fin.cases ⟨target1FaceCodes21,target1FaceRow21_checked⟩ (Fin.cases ⟨target1FaceCodes22,target1FaceRow22_checked⟩ (Fin.cases ⟨target1FaceCodes23,target1FaceRow23_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock1 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+24) default)
      (targetMeshFamily1.take (j.val+24)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes24,target1FaceRow24_checked⟩ (Fin.cases ⟨target1FaceCodes25,target1FaceRow25_checked⟩ (Fin.cases ⟨target1FaceCodes26,target1FaceRow26_checked⟩ (Fin.cases ⟨target1FaceCodes27,target1FaceRow27_checked⟩ (Fin.cases ⟨target1FaceCodes28,target1FaceRow28_checked⟩ (Fin.cases ⟨target1FaceCodes29,target1FaceRow29_checked⟩ (Fin.cases ⟨target1FaceCodes30,target1FaceRow30_checked⟩ (Fin.cases ⟨target1FaceCodes31,target1FaceRow31_checked⟩ (Fin.cases ⟨target1FaceCodes32,target1FaceRow32_checked⟩ (Fin.cases ⟨target1FaceCodes33,target1FaceRow33_checked⟩ (Fin.cases ⟨target1FaceCodes34,target1FaceRow34_checked⟩ (Fin.cases ⟨target1FaceCodes35,target1FaceRow35_checked⟩ (Fin.cases ⟨target1FaceCodes36,target1FaceRow36_checked⟩ (Fin.cases ⟨target1FaceCodes37,target1FaceRow37_checked⟩ (Fin.cases ⟨target1FaceCodes38,target1FaceRow38_checked⟩ (Fin.cases ⟨target1FaceCodes39,target1FaceRow39_checked⟩ (Fin.cases ⟨target1FaceCodes40,target1FaceRow40_checked⟩ (Fin.cases ⟨target1FaceCodes41,target1FaceRow41_checked⟩ (Fin.cases ⟨target1FaceCodes42,target1FaceRow42_checked⟩ (Fin.cases ⟨target1FaceCodes43,target1FaceRow43_checked⟩ (Fin.cases ⟨target1FaceCodes44,target1FaceRow44_checked⟩ (Fin.cases ⟨target1FaceCodes45,target1FaceRow45_checked⟩ (Fin.cases ⟨target1FaceCodes46,target1FaceRow46_checked⟩ (Fin.cases ⟨target1FaceCodes47,target1FaceRow47_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock2 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+48) default)
      (targetMeshFamily1.take (j.val+48)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes48,target1FaceRow48_checked⟩ (Fin.cases ⟨target1FaceCodes49,target1FaceRow49_checked⟩ (Fin.cases ⟨target1FaceCodes50,target1FaceRow50_checked⟩ (Fin.cases ⟨target1FaceCodes51,target1FaceRow51_checked⟩ (Fin.cases ⟨target1FaceCodes52,target1FaceRow52_checked⟩ (Fin.cases ⟨target1FaceCodes53,target1FaceRow53_checked⟩ (Fin.cases ⟨target1FaceCodes54,target1FaceRow54_checked⟩ (Fin.cases ⟨target1FaceCodes55,target1FaceRow55_checked⟩ (Fin.cases ⟨target1FaceCodes56,target1FaceRow56_checked⟩ (Fin.cases ⟨target1FaceCodes57,target1FaceRow57_checked⟩ (Fin.cases ⟨target1FaceCodes58,target1FaceRow58_checked⟩ (Fin.cases ⟨target1FaceCodes59,target1FaceRow59_checked⟩ (Fin.cases ⟨target1FaceCodes60,target1FaceRow60_checked⟩ (Fin.cases ⟨target1FaceCodes61,target1FaceRow61_checked⟩ (Fin.cases ⟨target1FaceCodes62,target1FaceRow62_checked⟩ (Fin.cases ⟨target1FaceCodes63,target1FaceRow63_checked⟩ (Fin.cases ⟨target1FaceCodes64,target1FaceRow64_checked⟩ (Fin.cases ⟨target1FaceCodes65,target1FaceRow65_checked⟩ (Fin.cases ⟨target1FaceCodes66,target1FaceRow66_checked⟩ (Fin.cases ⟨target1FaceCodes67,target1FaceRow67_checked⟩ (Fin.cases ⟨target1FaceCodes68,target1FaceRow68_checked⟩ (Fin.cases ⟨target1FaceCodes69,target1FaceRow69_checked⟩ (Fin.cases ⟨target1FaceCodes70,target1FaceRow70_checked⟩ (Fin.cases ⟨target1FaceCodes71,target1FaceRow71_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock3 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+72) default)
      (targetMeshFamily1.take (j.val+72)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes72,target1FaceRow72_checked⟩ (Fin.cases ⟨target1FaceCodes73,target1FaceRow73_checked⟩ (Fin.cases ⟨target1FaceCodes74,target1FaceRow74_checked⟩ (Fin.cases ⟨target1FaceCodes75,target1FaceRow75_checked⟩ (Fin.cases ⟨target1FaceCodes76,target1FaceRow76_checked⟩ (Fin.cases ⟨target1FaceCodes77,target1FaceRow77_checked⟩ (Fin.cases ⟨target1FaceCodes78,target1FaceRow78_checked⟩ (Fin.cases ⟨target1FaceCodes79,target1FaceRow79_checked⟩ (Fin.cases ⟨target1FaceCodes80,target1FaceRow80_checked⟩ (Fin.cases ⟨target1FaceCodes81,target1FaceRow81_checked⟩ (Fin.cases ⟨target1FaceCodes82,target1FaceRow82_checked⟩ (Fin.cases ⟨target1FaceCodes83,target1FaceRow83_checked⟩ (Fin.cases ⟨target1FaceCodes84,target1FaceRow84_checked⟩ (Fin.cases ⟨target1FaceCodes85,target1FaceRow85_checked⟩ (Fin.cases ⟨target1FaceCodes86,target1FaceRow86_checked⟩ (Fin.cases ⟨target1FaceCodes87,target1FaceRow87_checked⟩ (Fin.cases ⟨target1FaceCodes88,target1FaceRow88_checked⟩ (Fin.cases ⟨target1FaceCodes89,target1FaceRow89_checked⟩ (Fin.cases ⟨target1FaceCodes90,target1FaceRow90_checked⟩ (Fin.cases ⟨target1FaceCodes91,target1FaceRow91_checked⟩ (Fin.cases ⟨target1FaceCodes92,target1FaceRow92_checked⟩ (Fin.cases ⟨target1FaceCodes93,target1FaceRow93_checked⟩ (Fin.cases ⟨target1FaceCodes94,target1FaceRow94_checked⟩ (Fin.cases ⟨target1FaceCodes95,target1FaceRow95_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock4 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+96) default)
      (targetMeshFamily1.take (j.val+96)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes96,target1FaceRow96_checked⟩ (Fin.cases ⟨target1FaceCodes97,target1FaceRow97_checked⟩ (Fin.cases ⟨target1FaceCodes98,target1FaceRow98_checked⟩ (Fin.cases ⟨target1FaceCodes99,target1FaceRow99_checked⟩ (Fin.cases ⟨target1FaceCodes100,target1FaceRow100_checked⟩ (Fin.cases ⟨target1FaceCodes101,target1FaceRow101_checked⟩ (Fin.cases ⟨target1FaceCodes102,target1FaceRow102_checked⟩ (Fin.cases ⟨target1FaceCodes103,target1FaceRow103_checked⟩ (Fin.cases ⟨target1FaceCodes104,target1FaceRow104_checked⟩ (Fin.cases ⟨target1FaceCodes105,target1FaceRow105_checked⟩ (Fin.cases ⟨target1FaceCodes106,target1FaceRow106_checked⟩ (Fin.cases ⟨target1FaceCodes107,target1FaceRow107_checked⟩ (Fin.cases ⟨target1FaceCodes108,target1FaceRow108_checked⟩ (Fin.cases ⟨target1FaceCodes109,target1FaceRow109_checked⟩ (Fin.cases ⟨target1FaceCodes110,target1FaceRow110_checked⟩ (Fin.cases ⟨target1FaceCodes111,target1FaceRow111_checked⟩ (Fin.cases ⟨target1FaceCodes112,target1FaceRow112_checked⟩ (Fin.cases ⟨target1FaceCodes113,target1FaceRow113_checked⟩ (Fin.cases ⟨target1FaceCodes114,target1FaceRow114_checked⟩ (Fin.cases ⟨target1FaceCodes115,target1FaceRow115_checked⟩ (Fin.cases ⟨target1FaceCodes116,target1FaceRow116_checked⟩ (Fin.cases ⟨target1FaceCodes117,target1FaceRow117_checked⟩ (Fin.cases ⟨target1FaceCodes118,target1FaceRow118_checked⟩ (Fin.cases ⟨target1FaceCodes119,target1FaceRow119_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock5 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+120) default)
      (targetMeshFamily1.take (j.val+120)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes120,target1FaceRow120_checked⟩ (Fin.cases ⟨target1FaceCodes121,target1FaceRow121_checked⟩ (Fin.cases ⟨target1FaceCodes122,target1FaceRow122_checked⟩ (Fin.cases ⟨target1FaceCodes123,target1FaceRow123_checked⟩ (Fin.cases ⟨target1FaceCodes124,target1FaceRow124_checked⟩ (Fin.cases ⟨target1FaceCodes125,target1FaceRow125_checked⟩ (Fin.cases ⟨target1FaceCodes126,target1FaceRow126_checked⟩ (Fin.cases ⟨target1FaceCodes127,target1FaceRow127_checked⟩ (Fin.cases ⟨target1FaceCodes128,target1FaceRow128_checked⟩ (Fin.cases ⟨target1FaceCodes129,target1FaceRow129_checked⟩ (Fin.cases ⟨target1FaceCodes130,target1FaceRow130_checked⟩ (Fin.cases ⟨target1FaceCodes131,target1FaceRow131_checked⟩ (Fin.cases ⟨target1FaceCodes132,target1FaceRow132_checked⟩ (Fin.cases ⟨target1FaceCodes133,target1FaceRow133_checked⟩ (Fin.cases ⟨target1FaceCodes134,target1FaceRow134_checked⟩ (Fin.cases ⟨target1FaceCodes135,target1FaceRow135_checked⟩ (Fin.cases ⟨target1FaceCodes136,target1FaceRow136_checked⟩ (Fin.cases ⟨target1FaceCodes137,target1FaceRow137_checked⟩ (Fin.cases ⟨target1FaceCodes138,target1FaceRow138_checked⟩ (Fin.cases ⟨target1FaceCodes139,target1FaceRow139_checked⟩ (Fin.cases ⟨target1FaceCodes140,target1FaceRow140_checked⟩ (Fin.cases ⟨target1FaceCodes141,target1FaceRow141_checked⟩ (Fin.cases ⟨target1FaceCodes142,target1FaceRow142_checked⟩ (Fin.cases ⟨target1FaceCodes143,target1FaceRow143_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock6 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+144) default)
      (targetMeshFamily1.take (j.val+144)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes144,target1FaceRow144_checked⟩ (Fin.cases ⟨target1FaceCodes145,target1FaceRow145_checked⟩ (Fin.cases ⟨target1FaceCodes146,target1FaceRow146_checked⟩ (Fin.cases ⟨target1FaceCodes147,target1FaceRow147_checked⟩ (Fin.cases ⟨target1FaceCodes148,target1FaceRow148_checked⟩ (Fin.cases ⟨target1FaceCodes149,target1FaceRow149_checked⟩ (Fin.cases ⟨target1FaceCodes150,target1FaceRow150_checked⟩ (Fin.cases ⟨target1FaceCodes151,target1FaceRow151_checked⟩ (Fin.cases ⟨target1FaceCodes152,target1FaceRow152_checked⟩ (Fin.cases ⟨target1FaceCodes153,target1FaceRow153_checked⟩ (Fin.cases ⟨target1FaceCodes154,target1FaceRow154_checked⟩ (Fin.cases ⟨target1FaceCodes155,target1FaceRow155_checked⟩ (Fin.cases ⟨target1FaceCodes156,target1FaceRow156_checked⟩ (Fin.cases ⟨target1FaceCodes157,target1FaceRow157_checked⟩ (Fin.cases ⟨target1FaceCodes158,target1FaceRow158_checked⟩ (Fin.cases ⟨target1FaceCodes159,target1FaceRow159_checked⟩ (Fin.cases ⟨target1FaceCodes160,target1FaceRow160_checked⟩ (Fin.cases ⟨target1FaceCodes161,target1FaceRow161_checked⟩ (Fin.cases ⟨target1FaceCodes162,target1FaceRow162_checked⟩ (Fin.cases ⟨target1FaceCodes163,target1FaceRow163_checked⟩ (Fin.cases ⟨target1FaceCodes164,target1FaceRow164_checked⟩ (Fin.cases ⟨target1FaceCodes165,target1FaceRow165_checked⟩ (Fin.cases ⟨target1FaceCodes166,target1FaceRow166_checked⟩ (Fin.cases ⟨target1FaceCodes167,target1FaceRow167_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock7 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+168) default)
      (targetMeshFamily1.take (j.val+168)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes168,target1FaceRow168_checked⟩ (Fin.cases ⟨target1FaceCodes169,target1FaceRow169_checked⟩ (Fin.cases ⟨target1FaceCodes170,target1FaceRow170_checked⟩ (Fin.cases ⟨target1FaceCodes171,target1FaceRow171_checked⟩ (Fin.cases ⟨target1FaceCodes172,target1FaceRow172_checked⟩ (Fin.cases ⟨target1FaceCodes173,target1FaceRow173_checked⟩ (Fin.cases ⟨target1FaceCodes174,target1FaceRow174_checked⟩ (Fin.cases ⟨target1FaceCodes175,target1FaceRow175_checked⟩ (Fin.cases ⟨target1FaceCodes176,target1FaceRow176_checked⟩ (Fin.cases ⟨target1FaceCodes177,target1FaceRow177_checked⟩ (Fin.cases ⟨target1FaceCodes178,target1FaceRow178_checked⟩ (Fin.cases ⟨target1FaceCodes179,target1FaceRow179_checked⟩ (Fin.cases ⟨target1FaceCodes180,target1FaceRow180_checked⟩ (Fin.cases ⟨target1FaceCodes181,target1FaceRow181_checked⟩ (Fin.cases ⟨target1FaceCodes182,target1FaceRow182_checked⟩ (Fin.cases ⟨target1FaceCodes183,target1FaceRow183_checked⟩ (Fin.cases ⟨target1FaceCodes184,target1FaceRow184_checked⟩ (Fin.cases ⟨target1FaceCodes185,target1FaceRow185_checked⟩ (Fin.cases ⟨target1FaceCodes186,target1FaceRow186_checked⟩ (Fin.cases ⟨target1FaceCodes187,target1FaceRow187_checked⟩ (Fin.cases ⟨target1FaceCodes188,target1FaceRow188_checked⟩ (Fin.cases ⟨target1FaceCodes189,target1FaceRow189_checked⟩ (Fin.cases ⟨target1FaceCodes190,target1FaceRow190_checked⟩ (Fin.cases ⟨target1FaceCodes191,target1FaceRow191_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock8 : ∀ j : Fin 24,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+192) default)
      (targetMeshFamily1.take (j.val+192)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes192,target1FaceRow192_checked⟩ (Fin.cases ⟨target1FaceCodes193,target1FaceRow193_checked⟩ (Fin.cases ⟨target1FaceCodes194,target1FaceRow194_checked⟩ (Fin.cases ⟨target1FaceCodes195,target1FaceRow195_checked⟩ (Fin.cases ⟨target1FaceCodes196,target1FaceRow196_checked⟩ (Fin.cases ⟨target1FaceCodes197,target1FaceRow197_checked⟩ (Fin.cases ⟨target1FaceCodes198,target1FaceRow198_checked⟩ (Fin.cases ⟨target1FaceCodes199,target1FaceRow199_checked⟩ (Fin.cases ⟨target1FaceCodes200,target1FaceRow200_checked⟩ (Fin.cases ⟨target1FaceCodes201,target1FaceRow201_checked⟩ (Fin.cases ⟨target1FaceCodes202,target1FaceRow202_checked⟩ (Fin.cases ⟨target1FaceCodes203,target1FaceRow203_checked⟩ (Fin.cases ⟨target1FaceCodes204,target1FaceRow204_checked⟩ (Fin.cases ⟨target1FaceCodes205,target1FaceRow205_checked⟩ (Fin.cases ⟨target1FaceCodes206,target1FaceRow206_checked⟩ (Fin.cases ⟨target1FaceCodes207,target1FaceRow207_checked⟩ (Fin.cases ⟨target1FaceCodes208,target1FaceRow208_checked⟩ (Fin.cases ⟨target1FaceCodes209,target1FaceRow209_checked⟩ (Fin.cases ⟨target1FaceCodes210,target1FaceRow210_checked⟩ (Fin.cases ⟨target1FaceCodes211,target1FaceRow211_checked⟩ (Fin.cases ⟨target1FaceCodes212,target1FaceRow212_checked⟩ (Fin.cases ⟨target1FaceCodes213,target1FaceRow213_checked⟩ (Fin.cases ⟨target1FaceCodes214,target1FaceRow214_checked⟩ (Fin.cases ⟨target1FaceCodes215,target1FaceRow215_checked⟩ (fun i => Fin.elim0 i))))))))))))))))))))))))

theorem target1FaceRowsBlock9 : ∀ j : Fin 2,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD (j.val+216) default)
      (targetMeshFamily1.take (j.val+216)) codes = true := by
  exact Fin.cases ⟨target1FaceCodes216,target1FaceRow216_checked⟩ (Fin.cases ⟨target1FaceCodes217,target1FaceRow217_checked⟩ (fun i => Fin.elim0 i))

theorem target1AllFaceRows : ∀ i : Fin 218,
    ∃ codes, packetFaceRowB (targetMeshFamily1.getD i.val default)
      (targetMeshFamily1.take i.val) codes = true := by
  intro i
  by_cases h0 : i.val < 24
  · have hs : 0 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock0
      ⟨i.val-0,by omega⟩
  by_cases h1 : i.val < 48
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock1
      ⟨i.val-24,by omega⟩
  by_cases h2 : i.val < 72
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock2
      ⟨i.val-48,by omega⟩
  by_cases h3 : i.val < 96
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock3
      ⟨i.val-72,by omega⟩
  by_cases h4 : i.val < 120
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock4
      ⟨i.val-96,by omega⟩
  by_cases h5 : i.val < 144
  · have hs : 120 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock5
      ⟨i.val-120,by omega⟩
  by_cases h6 : i.val < 168
  · have hs : 144 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock6
      ⟨i.val-144,by omega⟩
  by_cases h7 : i.val < 192
  · have hs : 168 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock7
      ⟨i.val-168,by omega⟩
  by_cases h8 : i.val < 216
  · have hs : 192 ≤ i.val := by omega
    simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock8
      ⟨i.val-192,by omega⟩
  have hs : 216 ≤ i.val := by omega
  simpa only [Nat.sub_add_cancel hs] using target1FaceRowsBlock9
    ⟨i.val-216,by omega⟩

end SpectreGeometry.ReverseClusterTriangulation
