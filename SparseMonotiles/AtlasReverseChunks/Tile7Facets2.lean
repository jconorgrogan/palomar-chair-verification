module

public import SparseMonotiles.AtlasReverseChunks.Tile7Keys2
public import SparseMonotiles.AtlasReverseChunks.Tile7Keys3
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact

open Contact.IndexedData7

theorem atlasFacet7_64_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 64) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key73, key74} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_73_mem
  · exact indexedKey7_74_mem

theorem atlasFacet7_65_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 65) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key75} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_75_mem

theorem atlasFacet7_66_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 66) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key76} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_76_mem

theorem atlasFacet7_67_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 67) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key77} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_77_mem

theorem atlasFacet7_68_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 68) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key78} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_78_mem

theorem atlasFacet7_69_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 69) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key79} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_79_mem

theorem atlasFacet7_70_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 70) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key80} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_80_mem

theorem atlasFacet7_71_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 71) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key81} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_81_mem

theorem atlasFacet7_72_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 72) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key82} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_82_mem

theorem atlasFacet7_73_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 73) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key83} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_83_mem

theorem atlasFacet7_74_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 74) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key84, key85} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_84_mem
  · exact indexedKey7_85_mem

theorem atlasFacet7_75_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 75) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key86} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_86_mem

theorem atlasFacet7_76_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 76) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key87} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_87_mem

theorem atlasFacet7_77_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 77) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key88, key89} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_88_mem
  · exact indexedKey7_89_mem

theorem atlasFacet7_78_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 78) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key90} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_90_mem

theorem atlasFacet7_79_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 79) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key91} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_91_mem

theorem atlasFacet7_80_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 80) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key92} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_92_mem

theorem atlasFacet7_81_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 81) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key93} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_93_mem

theorem atlasFacet7_82_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 82) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key94} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_94_mem

theorem atlasFacet7_83_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 83) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key95} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_95_mem

theorem atlasFacet7_84_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 84) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key96, key97} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_96_mem
  · exact indexedKey7_97_mem

theorem atlasFacet7_85_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 85) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key98} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_98_mem

theorem atlasFacet7_86_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 86) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key99} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_99_mem

theorem atlasFacet7_87_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 87) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key100} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_100_mem

theorem atlasFacet7_88_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 88) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key101} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_101_mem

theorem atlasFacet7_89_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 89) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key102} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_102_mem

theorem atlasFacet7_90_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 90) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key103} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_103_mem

theorem atlasFacet7_91_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 91) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key104} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_104_mem

theorem atlasFacet7_92_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 92) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key105} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_105_mem

theorem atlasFacet7_93_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 93) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key106, key107} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_106_mem
  · exact indexedKey7_107_mem

theorem atlasFacet7_94_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 94) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key108} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_108_mem

theorem atlasFacet7_95_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 95) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key109} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_109_mem

theorem atlasReverse7Chunk2 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨64 + i.val, by omega⟩, b.toKeyData 188160 ∈ keys7 := by
  fin_cases i
  · exact atlasFacet7_64_literal
  · exact atlasFacet7_65_literal
  · exact atlasFacet7_66_literal
  · exact atlasFacet7_67_literal
  · exact atlasFacet7_68_literal
  · exact atlasFacet7_69_literal
  · exact atlasFacet7_70_literal
  · exact atlasFacet7_71_literal
  · exact atlasFacet7_72_literal
  · exact atlasFacet7_73_literal
  · exact atlasFacet7_74_literal
  · exact atlasFacet7_75_literal
  · exact atlasFacet7_76_literal
  · exact atlasFacet7_77_literal
  · exact atlasFacet7_78_literal
  · exact atlasFacet7_79_literal
  · exact atlasFacet7_80_literal
  · exact atlasFacet7_81_literal
  · exact atlasFacet7_82_literal
  · exact atlasFacet7_83_literal
  · exact atlasFacet7_84_literal
  · exact atlasFacet7_85_literal
  · exact atlasFacet7_86_literal
  · exact atlasFacet7_87_literal
  · exact atlasFacet7_88_literal
  · exact atlasFacet7_89_literal
  · exact atlasFacet7_90_literal
  · exact atlasFacet7_91_literal
  · exact atlasFacet7_92_literal
  · exact atlasFacet7_93_literal
  · exact atlasFacet7_94_literal
  · exact atlasFacet7_95_literal

#print axioms atlasReverse7Chunk2
end SparseMonotiles.Canonical
