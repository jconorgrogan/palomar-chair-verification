module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk0
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk1
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk2
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk3
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk4
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk5
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk6

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey5Chunk0 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData5.geometry.profile ⟨0+j.val,by omega⟩,
      b.toKeyData 19200 ∈ keys5 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData5.key0,by decide,?_⟩
    rw [indexedKeyDecode5_0]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key4,by decide,?_⟩
    rw [indexedKeyDecode5_4]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key5,by decide,?_⟩
    rw [indexedKeyDecode5_5]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key6,by decide,?_⟩
    rw [indexedKeyDecode5_6]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key7,by decide,?_⟩
    rw [indexedKeyDecode5_7]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key8,by decide,?_⟩
    rw [indexedKeyDecode5_8]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key9,by decide,?_⟩
    rw [indexedKeyDecode5_9]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key10,by decide,?_⟩
    rw [indexedKeyDecode5_10]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key11,by decide,?_⟩
    rw [indexedKeyDecode5_11]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key12,by decide,?_⟩
    rw [indexedKeyDecode5_12]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key16,by decide,?_⟩
    rw [indexedKeyDecode5_16]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key17,by decide,?_⟩
    rw [indexedKeyDecode5_17]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key18,by decide,?_⟩
    rw [indexedKeyDecode5_18]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key19,by decide,?_⟩
    rw [indexedKeyDecode5_19]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key23,by decide,?_⟩
    rw [indexedKeyDecode5_23]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key24,by decide,?_⟩
    rw [indexedKeyDecode5_24]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key25,by decide,?_⟩
    rw [indexedKeyDecode5_25]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key29,by decide,?_⟩
    rw [indexedKeyDecode5_29]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key30,by decide,?_⟩
    rw [indexedKeyDecode5_30]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key31,by decide,?_⟩
    rw [indexedKeyDecode5_31]
    exact atlasWitness_keys5Chunk0_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key32,by decide,?_⟩
    rw [indexedKeyDecode5_32]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key33,by decide,?_⟩
    rw [indexedKeyDecode5_33]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key34,by decide,?_⟩
    rw [indexedKeyDecode5_34]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key38,by decide,?_⟩
    rw [indexedKeyDecode5_38]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key39,by decide,?_⟩
    rw [indexedKeyDecode5_39]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key40,by decide,?_⟩
    rw [indexedKeyDecode5_40]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key41,by decide,?_⟩
    rw [indexedKeyDecode5_41]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key42,by decide,?_⟩
    rw [indexedKeyDecode5_42]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key43,by decide,?_⟩
    rw [indexedKeyDecode5_43]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key47,by decide,?_⟩
    rw [indexedKeyDecode5_47]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key48,by decide,?_⟩
    rw [indexedKeyDecode5_48]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key52,by decide,?_⟩
    rw [indexedKeyDecode5_52]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key53,by decide,?_⟩
    rw [indexedKeyDecode5_53]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key54,by decide,?_⟩
    rw [indexedKeyDecode5_54]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key55,by decide,?_⟩
    rw [indexedKeyDecode5_55]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key56,by decide,?_⟩
    rw [indexedKeyDecode5_56]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key57,by decide,?_⟩
    rw [indexedKeyDecode5_57]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key58,by decide,?_⟩
    rw [indexedKeyDecode5_58]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key59,by decide,?_⟩
    rw [indexedKeyDecode5_59]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key63,by decide,?_⟩
    rw [indexedKeyDecode5_63]
    exact atlasWitness_keys5Chunk1_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key64,by decide,?_⟩
    rw [indexedKeyDecode5_64]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key65,by decide,?_⟩
    rw [indexedKeyDecode5_65]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key69,by decide,?_⟩
    rw [indexedKeyDecode5_69]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key70,by decide,?_⟩
    rw [indexedKeyDecode5_70]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key71,by decide,?_⟩
    rw [indexedKeyDecode5_71]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key72,by decide,?_⟩
    rw [indexedKeyDecode5_72]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key76,by decide,?_⟩
    rw [indexedKeyDecode5_76]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key77,by decide,?_⟩
    rw [indexedKeyDecode5_77]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key78,by decide,?_⟩
    rw [indexedKeyDecode5_78]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key79,by decide,?_⟩
    rw [indexedKeyDecode5_79]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key80,by decide,?_⟩
    rw [indexedKeyDecode5_80]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key81,by decide,?_⟩
    rw [indexedKeyDecode5_81]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key82,by decide,?_⟩
    rw [indexedKeyDecode5_82]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key86,by decide,?_⟩
    rw [indexedKeyDecode5_86]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key87,by decide,?_⟩
    rw [indexedKeyDecode5_87]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key88,by decide,?_⟩
    rw [indexedKeyDecode5_88]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key89,by decide,?_⟩
    rw [indexedKeyDecode5_89]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key93,by decide,?_⟩
    rw [indexedKeyDecode5_93]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key94,by decide,?_⟩
    rw [indexedKeyDecode5_94]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key95,by decide,?_⟩
    rw [indexedKeyDecode5_95]
    exact atlasWitness_keys5Chunk2_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key96,by decide,?_⟩
    rw [indexedKeyDecode5_96]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key97,by decide,?_⟩
    rw [indexedKeyDecode5_97]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key98,by decide,?_⟩
    rw [indexedKeyDecode5_98]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key99,by decide,?_⟩
    rw [indexedKeyDecode5_99]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key100,by decide,?_⟩
    rw [indexedKeyDecode5_100]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key104,by decide,?_⟩
    rw [indexedKeyDecode5_104]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key105,by decide,?_⟩
    rw [indexedKeyDecode5_105]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key106,by decide,?_⟩
    rw [indexedKeyDecode5_106]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key107,by decide,?_⟩
    rw [indexedKeyDecode5_107]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key108,by decide,?_⟩
    rw [indexedKeyDecode5_108]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key112,by decide,?_⟩
    rw [indexedKeyDecode5_112]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key113,by decide,?_⟩
    rw [indexedKeyDecode5_113]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key114,by decide,?_⟩
    rw [indexedKeyDecode5_114]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key118,by decide,?_⟩
    rw [indexedKeyDecode5_118]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key119,by decide,?_⟩
    rw [indexedKeyDecode5_119]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key120,by decide,?_⟩
    rw [indexedKeyDecode5_120]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key124,by decide,?_⟩
    rw [indexedKeyDecode5_124]
    exact atlasWitness_keys5Chunk3_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key128,by decide,?_⟩
    rw [indexedKeyDecode5_128]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key129,by decide,?_⟩
    rw [indexedKeyDecode5_129]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key130,by decide,?_⟩
    rw [indexedKeyDecode5_130]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key131,by decide,?_⟩
    rw [indexedKeyDecode5_131]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key132,by decide,?_⟩
    rw [indexedKeyDecode5_132]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key136,by decide,?_⟩
    rw [indexedKeyDecode5_136]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key137,by decide,?_⟩
    rw [indexedKeyDecode5_137]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key138,by decide,?_⟩
    rw [indexedKeyDecode5_138]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key139,by decide,?_⟩
    rw [indexedKeyDecode5_139]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key140,by decide,?_⟩
    rw [indexedKeyDecode5_140]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key141,by decide,?_⟩
    rw [indexedKeyDecode5_141]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key142,by decide,?_⟩
    rw [indexedKeyDecode5_142]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key146,by decide,?_⟩
    rw [indexedKeyDecode5_146]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key147,by decide,?_⟩
    rw [indexedKeyDecode5_147]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key148,by decide,?_⟩
    rw [indexedKeyDecode5_148]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key149,by decide,?_⟩
    rw [indexedKeyDecode5_149]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key150,by decide,?_⟩
    rw [indexedKeyDecode5_150]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key151,by decide,?_⟩
    rw [indexedKeyDecode5_151]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key152,by decide,?_⟩
    rw [indexedKeyDecode5_152]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key156,by decide,?_⟩
    rw [indexedKeyDecode5_156]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key157,by decide,?_⟩
    rw [indexedKeyDecode5_157]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key158,by decide,?_⟩
    rw [indexedKeyDecode5_158]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key159,by decide,?_⟩
    rw [indexedKeyDecode5_159]
    exact atlasWitness_keys5Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key160,by decide,?_⟩
    rw [indexedKeyDecode5_160]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key164,by decide,?_⟩
    rw [indexedKeyDecode5_164]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key165,by decide,?_⟩
    rw [indexedKeyDecode5_165]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key169,by decide,?_⟩
    rw [indexedKeyDecode5_169]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key170,by decide,?_⟩
    rw [indexedKeyDecode5_170]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key171,by decide,?_⟩
    rw [indexedKeyDecode5_171]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key172,by decide,?_⟩
    rw [indexedKeyDecode5_172]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key173,by decide,?_⟩
    rw [indexedKeyDecode5_173]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key174,by decide,?_⟩
    rw [indexedKeyDecode5_174]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key178,by decide,?_⟩
    rw [indexedKeyDecode5_178]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key179,by decide,?_⟩
    rw [indexedKeyDecode5_179]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key180,by decide,?_⟩
    rw [indexedKeyDecode5_180]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key184,by decide,?_⟩
    rw [indexedKeyDecode5_184]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key185,by decide,?_⟩
    rw [indexedKeyDecode5_185]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key186,by decide,?_⟩
    rw [indexedKeyDecode5_186]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key187,by decide,?_⟩
    rw [indexedKeyDecode5_187]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key188,by decide,?_⟩
    rw [indexedKeyDecode5_188]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key189,by decide,?_⟩
    rw [indexedKeyDecode5_189]
    exact atlasWitness_keys5Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key193,by decide,?_⟩
    rw [indexedKeyDecode5_193]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key194,by decide,?_⟩
    rw [indexedKeyDecode5_194]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key195,by decide,?_⟩
    rw [indexedKeyDecode5_195]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key196,by decide,?_⟩
    rw [indexedKeyDecode5_196]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key197,by decide,?_⟩
    rw [indexedKeyDecode5_197]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key198,by decide,?_⟩
    rw [indexedKeyDecode5_198]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key199,by decide,?_⟩
    rw [indexedKeyDecode5_199]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key200,by decide,?_⟩
    rw [indexedKeyDecode5_200]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key204,by decide,?_⟩
    rw [indexedKeyDecode5_204]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key205,by decide,?_⟩
    rw [indexedKeyDecode5_205]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey5Chunk0
end SparseMonotiles.Canonical
