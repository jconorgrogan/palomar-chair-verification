module

public import SparseMonotiles.AtlasReverseChunks.Tile7Keys0
public import SparseMonotiles.AtlasReverseChunks.Tile7Keys1
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact

open Contact.IndexedData7

theorem atlasFacet7_0_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 0) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key0, key1} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_0_mem
  · exact indexedKey7_1_mem

theorem atlasFacet7_1_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 1) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key2} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_2_mem

theorem atlasFacet7_2_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 2) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key3} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_3_mem

theorem atlasFacet7_3_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 3) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key4} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_4_mem

theorem atlasFacet7_4_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 4) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key5} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_5_mem

theorem atlasFacet7_5_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 5) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key6} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_6_mem

theorem atlasFacet7_6_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 6) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key7} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_7_mem

theorem atlasFacet7_7_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 7) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key8} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_8_mem

theorem atlasFacet7_8_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 8) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key9} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_9_mem

theorem atlasFacet7_9_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 9) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key10} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_10_mem

theorem atlasFacet7_10_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 10) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key11} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_11_mem

theorem atlasFacet7_11_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 11) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key12} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_12_mem

theorem atlasFacet7_12_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 12) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key13} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_13_mem

theorem atlasFacet7_13_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 13) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key14, key15} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_14_mem
  · exact indexedKey7_15_mem

theorem atlasFacet7_14_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 14) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key16} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_16_mem

theorem atlasFacet7_15_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 15) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key17} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_17_mem

theorem atlasFacet7_16_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 16) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key18} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_18_mem

theorem atlasFacet7_17_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 17) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key19} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_19_mem

theorem atlasFacet7_18_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 18) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key20} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_20_mem

theorem atlasFacet7_19_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 19) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key21, key22} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_21_mem
  · exact indexedKey7_22_mem

theorem atlasFacet7_20_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 20) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key23} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_23_mem

theorem atlasFacet7_21_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 21) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key24} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_24_mem

theorem atlasFacet7_22_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 22) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key25} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_25_mem

theorem atlasFacet7_23_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 23) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key26, key27} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_26_mem
  · exact indexedKey7_27_mem

theorem atlasFacet7_24_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 24) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key28} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_28_mem

theorem atlasFacet7_25_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 25) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key29} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_29_mem

theorem atlasFacet7_26_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 26) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key30} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_30_mem

theorem atlasFacet7_27_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 27) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key31} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_31_mem

theorem atlasFacet7_28_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 28) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key32} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_32_mem

theorem atlasFacet7_29_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 29) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key33} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_33_mem

theorem atlasFacet7_30_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 30) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key34} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_34_mem

theorem atlasFacet7_31_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 31) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key35} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_35_mem

theorem atlasReverse7Chunk0 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨0 + i.val, by omega⟩, b.toKeyData 188160 ∈ keys7 := by
  fin_cases i
  · exact atlasFacet7_0_literal
  · exact atlasFacet7_1_literal
  · exact atlasFacet7_2_literal
  · exact atlasFacet7_3_literal
  · exact atlasFacet7_4_literal
  · exact atlasFacet7_5_literal
  · exact atlasFacet7_6_literal
  · exact atlasFacet7_7_literal
  · exact atlasFacet7_8_literal
  · exact atlasFacet7_9_literal
  · exact atlasFacet7_10_literal
  · exact atlasFacet7_11_literal
  · exact atlasFacet7_12_literal
  · exact atlasFacet7_13_literal
  · exact atlasFacet7_14_literal
  · exact atlasFacet7_15_literal
  · exact atlasFacet7_16_literal
  · exact atlasFacet7_17_literal
  · exact atlasFacet7_18_literal
  · exact atlasFacet7_19_literal
  · exact atlasFacet7_20_literal
  · exact atlasFacet7_21_literal
  · exact atlasFacet7_22_literal
  · exact atlasFacet7_23_literal
  · exact atlasFacet7_24_literal
  · exact atlasFacet7_25_literal
  · exact atlasFacet7_26_literal
  · exact atlasFacet7_27_literal
  · exact atlasFacet7_28_literal
  · exact atlasFacet7_29_literal
  · exact atlasFacet7_30_literal
  · exact atlasFacet7_31_literal

#print axioms atlasReverse7Chunk0
end SparseMonotiles.Canonical
