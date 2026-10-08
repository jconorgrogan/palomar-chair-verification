module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk0
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk1
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk2
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk3
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk4

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey7Chunk0 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData7.geometry.profile ⟨0+j.val,by omega⟩,
      b.toKeyData 188160 ∈ keys7 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData7.key0,by decide,?_⟩
    rw [indexedKeyDecode7_0]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key2,by decide,?_⟩
    rw [indexedKeyDecode7_2]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key3,by decide,?_⟩
    rw [indexedKeyDecode7_3]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key4,by decide,?_⟩
    rw [indexedKeyDecode7_4]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key5,by decide,?_⟩
    rw [indexedKeyDecode7_5]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key6,by decide,?_⟩
    rw [indexedKeyDecode7_6]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key7,by decide,?_⟩
    rw [indexedKeyDecode7_7]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key8,by decide,?_⟩
    rw [indexedKeyDecode7_8]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key9,by decide,?_⟩
    rw [indexedKeyDecode7_9]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key10,by decide,?_⟩
    rw [indexedKeyDecode7_10]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key11,by decide,?_⟩
    rw [indexedKeyDecode7_11]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key12,by decide,?_⟩
    rw [indexedKeyDecode7_12]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key13,by decide,?_⟩
    rw [indexedKeyDecode7_13]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key14,by decide,?_⟩
    rw [indexedKeyDecode7_14]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key16,by decide,?_⟩
    rw [indexedKeyDecode7_16]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key17,by decide,?_⟩
    rw [indexedKeyDecode7_17]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key18,by decide,?_⟩
    rw [indexedKeyDecode7_18]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key19,by decide,?_⟩
    rw [indexedKeyDecode7_19]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key20,by decide,?_⟩
    rw [indexedKeyDecode7_20]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key21,by decide,?_⟩
    rw [indexedKeyDecode7_21]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key23,by decide,?_⟩
    rw [indexedKeyDecode7_23]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key24,by decide,?_⟩
    rw [indexedKeyDecode7_24]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key25,by decide,?_⟩
    rw [indexedKeyDecode7_25]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key26,by decide,?_⟩
    rw [indexedKeyDecode7_26]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key28,by decide,?_⟩
    rw [indexedKeyDecode7_28]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key29,by decide,?_⟩
    rw [indexedKeyDecode7_29]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key30,by decide,?_⟩
    rw [indexedKeyDecode7_30]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key31,by decide,?_⟩
    rw [indexedKeyDecode7_31]
    exact atlasWitness_keys7Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key32,by decide,?_⟩
    rw [indexedKeyDecode7_32]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key33,by decide,?_⟩
    rw [indexedKeyDecode7_33]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key34,by decide,?_⟩
    rw [indexedKeyDecode7_34]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key35,by decide,?_⟩
    rw [indexedKeyDecode7_35]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key36,by decide,?_⟩
    rw [indexedKeyDecode7_36]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key38,by decide,?_⟩
    rw [indexedKeyDecode7_38]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key39,by decide,?_⟩
    rw [indexedKeyDecode7_39]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key40,by decide,?_⟩
    rw [indexedKeyDecode7_40]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key41,by decide,?_⟩
    rw [indexedKeyDecode7_41]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key42,by decide,?_⟩
    rw [indexedKeyDecode7_42]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key43,by decide,?_⟩
    rw [indexedKeyDecode7_43]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key44,by decide,?_⟩
    rw [indexedKeyDecode7_44]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key45,by decide,?_⟩
    rw [indexedKeyDecode7_45]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key47,by decide,?_⟩
    rw [indexedKeyDecode7_47]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key48,by decide,?_⟩
    rw [indexedKeyDecode7_48]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key49,by decide,?_⟩
    rw [indexedKeyDecode7_49]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key51,by decide,?_⟩
    rw [indexedKeyDecode7_51]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key52,by decide,?_⟩
    rw [indexedKeyDecode7_52]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key53,by decide,?_⟩
    rw [indexedKeyDecode7_53]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key54,by decide,?_⟩
    rw [indexedKeyDecode7_54]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key55,by decide,?_⟩
    rw [indexedKeyDecode7_55]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key56,by decide,?_⟩
    rw [indexedKeyDecode7_56]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key57,by decide,?_⟩
    rw [indexedKeyDecode7_57]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key58,by decide,?_⟩
    rw [indexedKeyDecode7_58]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key59,by decide,?_⟩
    rw [indexedKeyDecode7_59]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key60,by decide,?_⟩
    rw [indexedKeyDecode7_60]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key61,by decide,?_⟩
    rw [indexedKeyDecode7_61]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key63,by decide,?_⟩
    rw [indexedKeyDecode7_63]
    exact atlasWitness_keys7Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key64,by decide,?_⟩
    rw [indexedKeyDecode7_64]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key65,by decide,?_⟩
    rw [indexedKeyDecode7_65]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key66,by decide,?_⟩
    rw [indexedKeyDecode7_66]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key67,by decide,?_⟩
    rw [indexedKeyDecode7_67]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key69,by decide,?_⟩
    rw [indexedKeyDecode7_69]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key70,by decide,?_⟩
    rw [indexedKeyDecode7_70]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key71,by decide,?_⟩
    rw [indexedKeyDecode7_71]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key72,by decide,?_⟩
    rw [indexedKeyDecode7_72]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key73,by decide,?_⟩
    rw [indexedKeyDecode7_73]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key75,by decide,?_⟩
    rw [indexedKeyDecode7_75]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key76,by decide,?_⟩
    rw [indexedKeyDecode7_76]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key77,by decide,?_⟩
    rw [indexedKeyDecode7_77]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key78,by decide,?_⟩
    rw [indexedKeyDecode7_78]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key79,by decide,?_⟩
    rw [indexedKeyDecode7_79]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key80,by decide,?_⟩
    rw [indexedKeyDecode7_80]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key81,by decide,?_⟩
    rw [indexedKeyDecode7_81]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key82,by decide,?_⟩
    rw [indexedKeyDecode7_82]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key83,by decide,?_⟩
    rw [indexedKeyDecode7_83]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key84,by decide,?_⟩
    rw [indexedKeyDecode7_84]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key86,by decide,?_⟩
    rw [indexedKeyDecode7_86]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key87,by decide,?_⟩
    rw [indexedKeyDecode7_87]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key88,by decide,?_⟩
    rw [indexedKeyDecode7_88]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key90,by decide,?_⟩
    rw [indexedKeyDecode7_90]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key91,by decide,?_⟩
    rw [indexedKeyDecode7_91]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key92,by decide,?_⟩
    rw [indexedKeyDecode7_92]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key93,by decide,?_⟩
    rw [indexedKeyDecode7_93]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key94,by decide,?_⟩
    rw [indexedKeyDecode7_94]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key95,by decide,?_⟩
    rw [indexedKeyDecode7_95]
    exact atlasWitness_keys7Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key96,by decide,?_⟩
    rw [indexedKeyDecode7_96]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key98,by decide,?_⟩
    rw [indexedKeyDecode7_98]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key99,by decide,?_⟩
    rw [indexedKeyDecode7_99]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key100,by decide,?_⟩
    rw [indexedKeyDecode7_100]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key101,by decide,?_⟩
    rw [indexedKeyDecode7_101]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key102,by decide,?_⟩
    rw [indexedKeyDecode7_102]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key103,by decide,?_⟩
    rw [indexedKeyDecode7_103]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key104,by decide,?_⟩
    rw [indexedKeyDecode7_104]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key105,by decide,?_⟩
    rw [indexedKeyDecode7_105]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key106,by decide,?_⟩
    rw [indexedKeyDecode7_106]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key108,by decide,?_⟩
    rw [indexedKeyDecode7_108]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key109,by decide,?_⟩
    rw [indexedKeyDecode7_109]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key110,by decide,?_⟩
    rw [indexedKeyDecode7_110]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key111,by decide,?_⟩
    rw [indexedKeyDecode7_111]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key112,by decide,?_⟩
    rw [indexedKeyDecode7_112]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key113,by decide,?_⟩
    rw [indexedKeyDecode7_113]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key114,by decide,?_⟩
    rw [indexedKeyDecode7_114]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key115,by decide,?_⟩
    rw [indexedKeyDecode7_115]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key116,by decide,?_⟩
    rw [indexedKeyDecode7_116]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key118,by decide,?_⟩
    rw [indexedKeyDecode7_118]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key119,by decide,?_⟩
    rw [indexedKeyDecode7_119]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key120,by decide,?_⟩
    rw [indexedKeyDecode7_120]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key121,by decide,?_⟩
    rw [indexedKeyDecode7_121]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key123,by decide,?_⟩
    rw [indexedKeyDecode7_123]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key124,by decide,?_⟩
    rw [indexedKeyDecode7_124]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key125,by decide,?_⟩
    rw [indexedKeyDecode7_125]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key126,by decide,?_⟩
    rw [indexedKeyDecode7_126]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key127,by decide,?_⟩
    rw [indexedKeyDecode7_127]
    exact atlasWitness_keys7Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key128,by decide,?_⟩
    rw [indexedKeyDecode7_128]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key129,by decide,?_⟩
    rw [indexedKeyDecode7_129]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key130,by decide,?_⟩
    rw [indexedKeyDecode7_130]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key132,by decide,?_⟩
    rw [indexedKeyDecode7_132]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key133,by decide,?_⟩
    rw [indexedKeyDecode7_133]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key134,by decide,?_⟩
    rw [indexedKeyDecode7_134]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key135,by decide,?_⟩
    rw [indexedKeyDecode7_135]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key136,by decide,?_⟩
    rw [indexedKeyDecode7_136]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key137,by decide,?_⟩
    rw [indexedKeyDecode7_137]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key138,by decide,?_⟩
    rw [indexedKeyDecode7_138]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key139,by decide,?_⟩
    rw [indexedKeyDecode7_139]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key140,by decide,?_⟩
    rw [indexedKeyDecode7_140]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key142,by decide,?_⟩
    rw [indexedKeyDecode7_142]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key143,by decide,?_⟩
    rw [indexedKeyDecode7_143]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key144,by decide,?_⟩
    rw [indexedKeyDecode7_144]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key146,by decide,?_⟩
    rw [indexedKeyDecode7_146]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey7Chunk0
end SparseMonotiles.Canonical
