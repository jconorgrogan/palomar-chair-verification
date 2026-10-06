module

public import SparseMonotiles.AtlasReverseChunks.Tile5Keys3
public import SparseMonotiles.AtlasReverseChunks.Tile5Keys4
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
open Contact.IndexedData5

theorem atlasFacet5_64_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 64) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key100, key101, key102, key103} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_100_mem
  · exact indexedKey5_101_mem
  · exact indexedKey5_102_mem
  · exact indexedKey5_103_mem

theorem atlasFacet5_65_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 65) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key104} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_104_mem

theorem atlasFacet5_66_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 66) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key105} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_105_mem

theorem atlasFacet5_67_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 67) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key106} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_106_mem

theorem atlasFacet5_68_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 68) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key107} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_107_mem

theorem atlasFacet5_69_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 69) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key108, key109, key110, key111} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_108_mem
  · exact indexedKey5_109_mem
  · exact indexedKey5_110_mem
  · exact indexedKey5_111_mem

theorem atlasFacet5_70_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 70) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key112} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_112_mem

theorem atlasFacet5_71_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 71) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key113} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_113_mem

theorem atlasFacet5_72_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 72) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key114, key115, key116, key117} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_114_mem
  · exact indexedKey5_115_mem
  · exact indexedKey5_116_mem
  · exact indexedKey5_117_mem

theorem atlasFacet5_73_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 73) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key118} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_118_mem

theorem atlasFacet5_74_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 74) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key119} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_119_mem

theorem atlasFacet5_75_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 75) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key120, key121, key122, key123} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_120_mem
  · exact indexedKey5_121_mem
  · exact indexedKey5_122_mem
  · exact indexedKey5_123_mem

theorem atlasFacet5_76_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 76) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key124, key125, key126, key127} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_124_mem
  · exact indexedKey5_125_mem
  · exact indexedKey5_126_mem
  · exact indexedKey5_127_mem

theorem atlasFacet5_77_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 77) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key128} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_128_mem

theorem atlasFacet5_78_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 78) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key129} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_129_mem

theorem atlasFacet5_79_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 79) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key130} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_130_mem

theorem atlasFacet5_80_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 80) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key131} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_131_mem

theorem atlasFacet5_81_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 81) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key132, key133, key134, key135} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_132_mem
  · exact indexedKey5_133_mem
  · exact indexedKey5_134_mem
  · exact indexedKey5_135_mem

theorem atlasFacet5_82_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 82) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key136} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_136_mem

theorem atlasFacet5_83_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 83) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key137} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_137_mem

theorem atlasFacet5_84_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 84) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key138} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_138_mem

theorem atlasFacet5_85_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 85) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key139} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_139_mem

theorem atlasFacet5_86_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 86) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key140} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_140_mem

theorem atlasFacet5_87_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 87) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key141} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_141_mem

theorem atlasFacet5_88_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 88) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key142, key143, key144, key145} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_142_mem
  · exact indexedKey5_143_mem
  · exact indexedKey5_144_mem
  · exact indexedKey5_145_mem

theorem atlasFacet5_89_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 89) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key146} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_146_mem

theorem atlasFacet5_90_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 90) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key147} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_147_mem

theorem atlasFacet5_91_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 91) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key148} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_148_mem

theorem atlasFacet5_92_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 92) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key149} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_149_mem

theorem atlasFacet5_93_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 93) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key150} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_150_mem

theorem atlasFacet5_94_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 94) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key151} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_151_mem

theorem atlasFacet5_95_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 95) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key152, key153, key154, key155} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_152_mem
  · exact indexedKey5_153_mem
  · exact indexedKey5_154_mem
  · exact indexedKey5_155_mem

theorem atlasReverse5Chunk2 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨64 + i.val, by omega⟩, b.toKeyData 19200 ∈ keys5 := by
  fin_cases i
  · exact atlasFacet5_64_literal
  · exact atlasFacet5_65_literal
  · exact atlasFacet5_66_literal
  · exact atlasFacet5_67_literal
  · exact atlasFacet5_68_literal
  · exact atlasFacet5_69_literal
  · exact atlasFacet5_70_literal
  · exact atlasFacet5_71_literal
  · exact atlasFacet5_72_literal
  · exact atlasFacet5_73_literal
  · exact atlasFacet5_74_literal
  · exact atlasFacet5_75_literal
  · exact atlasFacet5_76_literal
  · exact atlasFacet5_77_literal
  · exact atlasFacet5_78_literal
  · exact atlasFacet5_79_literal
  · exact atlasFacet5_80_literal
  · exact atlasFacet5_81_literal
  · exact atlasFacet5_82_literal
  · exact atlasFacet5_83_literal
  · exact atlasFacet5_84_literal
  · exact atlasFacet5_85_literal
  · exact atlasFacet5_86_literal
  · exact atlasFacet5_87_literal
  · exact atlasFacet5_88_literal
  · exact atlasFacet5_89_literal
  · exact atlasFacet5_90_literal
  · exact atlasFacet5_91_literal
  · exact atlasFacet5_92_literal
  · exact atlasFacet5_93_literal
  · exact atlasFacet5_94_literal
  · exact atlasFacet5_95_literal

#print axioms atlasReverse5Chunk2
end SparseMonotiles.Canonical
