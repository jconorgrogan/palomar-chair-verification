module

public import SparseMonotiles.AtlasReverseChunks.Tile5Keys0
public import SparseMonotiles.AtlasReverseChunks.Tile5Keys1
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
open Contact.IndexedData5

theorem atlasFacet5_0_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 0) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key0, key1, key2, key3} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_0_mem
  · exact indexedKey5_1_mem
  · exact indexedKey5_2_mem
  · exact indexedKey5_3_mem

theorem atlasFacet5_1_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 1) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key4} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_4_mem

theorem atlasFacet5_2_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 2) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key5} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_5_mem

theorem atlasFacet5_3_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 3) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key6} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_6_mem

theorem atlasFacet5_4_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 4) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key7} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_7_mem

theorem atlasFacet5_5_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 5) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key8} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_8_mem

theorem atlasFacet5_6_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 6) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key9} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_9_mem

theorem atlasFacet5_7_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 7) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key10} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_10_mem

theorem atlasFacet5_8_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 8) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key11} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_11_mem

theorem atlasFacet5_9_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 9) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key12, key13, key14, key15} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_12_mem
  · exact indexedKey5_13_mem
  · exact indexedKey5_14_mem
  · exact indexedKey5_15_mem

theorem atlasFacet5_10_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 10) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key16} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_16_mem

theorem atlasFacet5_11_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 11) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key17} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_17_mem

theorem atlasFacet5_12_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 12) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key18} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_18_mem

theorem atlasFacet5_13_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 13) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key19, key20, key21, key22} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_19_mem
  · exact indexedKey5_20_mem
  · exact indexedKey5_21_mem
  · exact indexedKey5_22_mem

theorem atlasFacet5_14_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 14) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key23} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_23_mem

theorem atlasFacet5_15_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 15) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key24} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_24_mem

theorem atlasFacet5_16_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 16) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key25, key26, key27, key28} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_25_mem
  · exact indexedKey5_26_mem
  · exact indexedKey5_27_mem
  · exact indexedKey5_28_mem

theorem atlasFacet5_17_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 17) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key29} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_29_mem

theorem atlasFacet5_18_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 18) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key30} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_30_mem

theorem atlasFacet5_19_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 19) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key31} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_31_mem

theorem atlasFacet5_20_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 20) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key32} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_32_mem

theorem atlasFacet5_21_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 21) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key33} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_33_mem

theorem atlasFacet5_22_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 22) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key34, key35, key36, key37} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_34_mem
  · exact indexedKey5_35_mem
  · exact indexedKey5_36_mem
  · exact indexedKey5_37_mem

theorem atlasFacet5_23_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 23) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key38} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_38_mem

theorem atlasFacet5_24_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 24) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key39} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_39_mem

theorem atlasFacet5_25_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 25) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key40} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_40_mem

theorem atlasFacet5_26_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 26) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key41} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_41_mem

theorem atlasFacet5_27_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 27) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key42} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_42_mem

theorem atlasFacet5_28_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 28) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key43, key44, key45, key46} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_43_mem
  · exact indexedKey5_44_mem
  · exact indexedKey5_45_mem
  · exact indexedKey5_46_mem

theorem atlasFacet5_29_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 29) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key47} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_47_mem

theorem atlasFacet5_30_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 30) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key48, key49, key50, key51} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact indexedKey5_48_mem
  · exact indexedKey5_49_mem
  · exact indexedKey5_50_mem
  · exact indexedKey5_51_mem

theorem atlasFacet5_31_literal (b : BoxKey 5) (hb : b ∈ geometry.profile 31) :
    b.toKeyData 19200 ∈ keys5 := by
  change b ∈ ({key52} : Finset (BoxKey 5)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey5_52_mem

theorem atlasReverse5Chunk0 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨0 + i.val, by omega⟩, b.toKeyData 19200 ∈ keys5 := by
  fin_cases i
  · exact atlasFacet5_0_literal
  · exact atlasFacet5_1_literal
  · exact atlasFacet5_2_literal
  · exact atlasFacet5_3_literal
  · exact atlasFacet5_4_literal
  · exact atlasFacet5_5_literal
  · exact atlasFacet5_6_literal
  · exact atlasFacet5_7_literal
  · exact atlasFacet5_8_literal
  · exact atlasFacet5_9_literal
  · exact atlasFacet5_10_literal
  · exact atlasFacet5_11_literal
  · exact atlasFacet5_12_literal
  · exact atlasFacet5_13_literal
  · exact atlasFacet5_14_literal
  · exact atlasFacet5_15_literal
  · exact atlasFacet5_16_literal
  · exact atlasFacet5_17_literal
  · exact atlasFacet5_18_literal
  · exact atlasFacet5_19_literal
  · exact atlasFacet5_20_literal
  · exact atlasFacet5_21_literal
  · exact atlasFacet5_22_literal
  · exact atlasFacet5_23_literal
  · exact atlasFacet5_24_literal
  · exact atlasFacet5_25_literal
  · exact atlasFacet5_26_literal
  · exact atlasFacet5_27_literal
  · exact atlasFacet5_28_literal
  · exact atlasFacet5_29_literal
  · exact atlasFacet5_30_literal
  · exact atlasFacet5_31_literal

#print axioms atlasReverse5Chunk0
end SparseMonotiles.Canonical
