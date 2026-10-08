module

public import SparseMonotiles.AtlasReverseChunks.Tile7Keys1
public import SparseMonotiles.AtlasReverseChunks.Tile7Keys2
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact

open Contact.IndexedData7

theorem atlasFacet7_32_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 32) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key36, key37} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_36_mem
  · exact indexedKey7_37_mem

theorem atlasFacet7_33_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 33) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key38} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_38_mem

theorem atlasFacet7_34_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 34) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key39} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_39_mem

theorem atlasFacet7_35_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 35) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key40} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_40_mem

theorem atlasFacet7_36_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 36) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key41} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_41_mem

theorem atlasFacet7_37_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 37) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key42} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_42_mem

theorem atlasFacet7_38_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 38) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key43} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_43_mem

theorem atlasFacet7_39_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 39) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key44} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_44_mem

theorem atlasFacet7_40_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 40) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key45, key46} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_45_mem
  · exact indexedKey7_46_mem

theorem atlasFacet7_41_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 41) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key47} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_47_mem

theorem atlasFacet7_42_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 42) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key48} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_48_mem

theorem atlasFacet7_43_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 43) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key49, key50} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_49_mem
  · exact indexedKey7_50_mem

theorem atlasFacet7_44_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 44) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key51} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_51_mem

theorem atlasFacet7_45_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 45) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key52} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_52_mem

theorem atlasFacet7_46_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 46) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key53} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_53_mem

theorem atlasFacet7_47_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 47) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key54} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_54_mem

theorem atlasFacet7_48_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 48) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key55} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_55_mem

theorem atlasFacet7_49_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 49) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key56} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_56_mem

theorem atlasFacet7_50_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 50) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key57} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_57_mem

theorem atlasFacet7_51_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 51) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key58} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_58_mem

theorem atlasFacet7_52_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 52) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key59} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_59_mem

theorem atlasFacet7_53_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 53) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key60} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_60_mem

theorem atlasFacet7_54_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 54) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key61, key62} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_61_mem
  · exact indexedKey7_62_mem

theorem atlasFacet7_55_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 55) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key63} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_63_mem

theorem atlasFacet7_56_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 56) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key64} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_64_mem

theorem atlasFacet7_57_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 57) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key65} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_65_mem

theorem atlasFacet7_58_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 58) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key66} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_66_mem

theorem atlasFacet7_59_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 59) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key67, key68} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_67_mem
  · exact indexedKey7_68_mem

theorem atlasFacet7_60_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 60) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key69} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_69_mem

theorem atlasFacet7_61_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 61) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key70} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_70_mem

theorem atlasFacet7_62_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 62) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key71} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_71_mem

theorem atlasFacet7_63_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 63) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key72} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_72_mem

theorem atlasReverse7Chunk1 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨32 + i.val, by omega⟩, b.toKeyData 188160 ∈ keys7 := by
  fin_cases i
  · exact atlasFacet7_32_literal
  · exact atlasFacet7_33_literal
  · exact atlasFacet7_34_literal
  · exact atlasFacet7_35_literal
  · exact atlasFacet7_36_literal
  · exact atlasFacet7_37_literal
  · exact atlasFacet7_38_literal
  · exact atlasFacet7_39_literal
  · exact atlasFacet7_40_literal
  · exact atlasFacet7_41_literal
  · exact atlasFacet7_42_literal
  · exact atlasFacet7_43_literal
  · exact atlasFacet7_44_literal
  · exact atlasFacet7_45_literal
  · exact atlasFacet7_46_literal
  · exact atlasFacet7_47_literal
  · exact atlasFacet7_48_literal
  · exact atlasFacet7_49_literal
  · exact atlasFacet7_50_literal
  · exact atlasFacet7_51_literal
  · exact atlasFacet7_52_literal
  · exact atlasFacet7_53_literal
  · exact atlasFacet7_54_literal
  · exact atlasFacet7_55_literal
  · exact atlasFacet7_56_literal
  · exact atlasFacet7_57_literal
  · exact atlasFacet7_58_literal
  · exact atlasFacet7_59_literal
  · exact atlasFacet7_60_literal
  · exact atlasFacet7_61_literal
  · exact atlasFacet7_62_literal
  · exact atlasFacet7_63_literal

#print axioms atlasReverse7Chunk1
end SparseMonotiles.Canonical
