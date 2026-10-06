module

public import SparseMonotiles.AtlasReverseChunks.Tile5Keys1
public import SparseMonotiles.AtlasReverseChunks.Tile5Keys2
public import SparseMonotiles.AtlasReverseChunks.Tile5Keys3
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
open Contact.IndexedData5

theorem atlasFacet5_32_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 32) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key53} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_53_mem

theorem atlasFacet5_33_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 33) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key54} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_54_mem

theorem atlasFacet5_34_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 34) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key55} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_55_mem

theorem atlasFacet5_35_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 35) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key56} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_56_mem

theorem atlasFacet5_36_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 36) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key57} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_57_mem

theorem atlasFacet5_37_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 37) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key58} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_58_mem

theorem atlasFacet5_38_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 38) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key59, key60, key61, key62} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_59_mem
  · exact indexedKey5_60_mem
  · exact indexedKey5_61_mem
  · exact indexedKey5_62_mem

theorem atlasFacet5_39_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 39) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key63} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_63_mem

theorem atlasFacet5_40_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 40) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key64} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_64_mem

theorem atlasFacet5_41_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 41) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key65, key66, key67, key68} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_65_mem
  · exact indexedKey5_66_mem
  · exact indexedKey5_67_mem
  · exact indexedKey5_68_mem

theorem atlasFacet5_42_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 42) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key69} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_69_mem

theorem atlasFacet5_43_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 43) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key70} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_70_mem

theorem atlasFacet5_44_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 44) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key71} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_71_mem

theorem atlasFacet5_45_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 45) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key72, key73, key74, key75} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_72_mem
  · exact indexedKey5_73_mem
  · exact indexedKey5_74_mem
  · exact indexedKey5_75_mem

theorem atlasFacet5_46_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 46) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key76} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_76_mem

theorem atlasFacet5_47_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 47) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key77} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_77_mem

theorem atlasFacet5_48_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 48) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key78} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_78_mem

theorem atlasFacet5_49_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 49) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key79} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_79_mem

theorem atlasFacet5_50_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 50) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key80} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_80_mem

theorem atlasFacet5_51_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 51) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key81} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_81_mem

theorem atlasFacet5_52_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 52) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key82, key83, key84, key85} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_82_mem
  · exact indexedKey5_83_mem
  · exact indexedKey5_84_mem
  · exact indexedKey5_85_mem

theorem atlasFacet5_53_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 53) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key86} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_86_mem

theorem atlasFacet5_54_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 54) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key87} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_87_mem

theorem atlasFacet5_55_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 55) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key88} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_88_mem

theorem atlasFacet5_56_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 56) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key89, key90, key91, key92} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_89_mem
  · exact indexedKey5_90_mem
  · exact indexedKey5_91_mem
  · exact indexedKey5_92_mem

theorem atlasFacet5_57_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 57) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key93} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_93_mem

theorem atlasFacet5_58_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 58) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key94} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_94_mem

theorem atlasFacet5_59_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 59) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key95} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_95_mem

theorem atlasFacet5_60_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 60) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key96} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_96_mem

theorem atlasFacet5_61_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 61) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key97} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_97_mem

theorem atlasFacet5_62_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 62) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key98} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_98_mem

theorem atlasFacet5_63_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 63) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key99} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_99_mem

theorem atlasReverse5Chunk1 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨32 + i.val, by omega⟩, b.toKeyData 19200 ∈ keys5 := by
  fin_cases i
  · exact atlasFacet5_32_literal
  · exact atlasFacet5_33_literal
  · exact atlasFacet5_34_literal
  · exact atlasFacet5_35_literal
  · exact atlasFacet5_36_literal
  · exact atlasFacet5_37_literal
  · exact atlasFacet5_38_literal
  · exact atlasFacet5_39_literal
  · exact atlasFacet5_40_literal
  · exact atlasFacet5_41_literal
  · exact atlasFacet5_42_literal
  · exact atlasFacet5_43_literal
  · exact atlasFacet5_44_literal
  · exact atlasFacet5_45_literal
  · exact atlasFacet5_46_literal
  · exact atlasFacet5_47_literal
  · exact atlasFacet5_48_literal
  · exact atlasFacet5_49_literal
  · exact atlasFacet5_50_literal
  · exact atlasFacet5_51_literal
  · exact atlasFacet5_52_literal
  · exact atlasFacet5_53_literal
  · exact atlasFacet5_54_literal
  · exact atlasFacet5_55_literal
  · exact atlasFacet5_56_literal
  · exact atlasFacet5_57_literal
  · exact atlasFacet5_58_literal
  · exact atlasFacet5_59_literal
  · exact atlasFacet5_60_literal
  · exact atlasFacet5_61_literal
  · exact atlasFacet5_62_literal
  · exact atlasFacet5_63_literal

#print axioms atlasReverse5Chunk1
end SparseMonotiles.Canonical
