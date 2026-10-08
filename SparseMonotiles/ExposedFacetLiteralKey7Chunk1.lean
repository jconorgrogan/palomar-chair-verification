module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk4
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk5
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk6
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk7
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk8
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk9

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey7Chunk1 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData7.geometry.profile ⟨128+j.val,by omega⟩,
      b.toKeyData 188160 ∈ keys7 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData7.key147,by decide,?_⟩
    rw [indexedKeyDecode7_147]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key148,by decide,?_⟩
    rw [indexedKeyDecode7_148]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key149,by decide,?_⟩
    rw [indexedKeyDecode7_149]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key150,by decide,?_⟩
    rw [indexedKeyDecode7_150]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key151,by decide,?_⟩
    rw [indexedKeyDecode7_151]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key152,by decide,?_⟩
    rw [indexedKeyDecode7_152]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key153,by decide,?_⟩
    rw [indexedKeyDecode7_153]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key154,by decide,?_⟩
    rw [indexedKeyDecode7_154]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key156,by decide,?_⟩
    rw [indexedKeyDecode7_156]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key157,by decide,?_⟩
    rw [indexedKeyDecode7_157]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key158,by decide,?_⟩
    rw [indexedKeyDecode7_158]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key159,by decide,?_⟩
    rw [indexedKeyDecode7_159]
    exact atlasWitness_keys7Chunk4_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key160,by decide,?_⟩
    rw [indexedKeyDecode7_160]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key161,by decide,?_⟩
    rw [indexedKeyDecode7_161]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key162,by decide,?_⟩
    rw [indexedKeyDecode7_162]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key163,by decide,?_⟩
    rw [indexedKeyDecode7_163]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key165,by decide,?_⟩
    rw [indexedKeyDecode7_165]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key166,by decide,?_⟩
    rw [indexedKeyDecode7_166]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key167,by decide,?_⟩
    rw [indexedKeyDecode7_167]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key168,by decide,?_⟩
    rw [indexedKeyDecode7_168]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key169,by decide,?_⟩
    rw [indexedKeyDecode7_169]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key170,by decide,?_⟩
    rw [indexedKeyDecode7_170]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key171,by decide,?_⟩
    rw [indexedKeyDecode7_171]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key172,by decide,?_⟩
    rw [indexedKeyDecode7_172]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key174,by decide,?_⟩
    rw [indexedKeyDecode7_174]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key175,by decide,?_⟩
    rw [indexedKeyDecode7_175]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key176,by decide,?_⟩
    rw [indexedKeyDecode7_176]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key177,by decide,?_⟩
    rw [indexedKeyDecode7_177]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key178,by decide,?_⟩
    rw [indexedKeyDecode7_178]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key179,by decide,?_⟩
    rw [indexedKeyDecode7_179]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key180,by decide,?_⟩
    rw [indexedKeyDecode7_180]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key181,by decide,?_⟩
    rw [indexedKeyDecode7_181]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key182,by decide,?_⟩
    rw [indexedKeyDecode7_182]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key184,by decide,?_⟩
    rw [indexedKeyDecode7_184]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key185,by decide,?_⟩
    rw [indexedKeyDecode7_185]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key186,by decide,?_⟩
    rw [indexedKeyDecode7_186]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key187,by decide,?_⟩
    rw [indexedKeyDecode7_187]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key188,by decide,?_⟩
    rw [indexedKeyDecode7_188]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key189,by decide,?_⟩
    rw [indexedKeyDecode7_189]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key190,by decide,?_⟩
    rw [indexedKeyDecode7_190]
    exact atlasWitness_keys7Chunk5_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key192,by decide,?_⟩
    rw [indexedKeyDecode7_192]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key193,by decide,?_⟩
    rw [indexedKeyDecode7_193]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key194,by decide,?_⟩
    rw [indexedKeyDecode7_194]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key195,by decide,?_⟩
    rw [indexedKeyDecode7_195]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key196,by decide,?_⟩
    rw [indexedKeyDecode7_196]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key197,by decide,?_⟩
    rw [indexedKeyDecode7_197]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key198,by decide,?_⟩
    rw [indexedKeyDecode7_198]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key200,by decide,?_⟩
    rw [indexedKeyDecode7_200]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key201,by decide,?_⟩
    rw [indexedKeyDecode7_201]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key202,by decide,?_⟩
    rw [indexedKeyDecode7_202]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key203,by decide,?_⟩
    rw [indexedKeyDecode7_203]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key204,by decide,?_⟩
    rw [indexedKeyDecode7_204]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key205,by decide,?_⟩
    rw [indexedKeyDecode7_205]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key206,by decide,?_⟩
    rw [indexedKeyDecode7_206]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key208,by decide,?_⟩
    rw [indexedKeyDecode7_208]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key209,by decide,?_⟩
    rw [indexedKeyDecode7_209]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key211,by decide,?_⟩
    rw [indexedKeyDecode7_211]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key212,by decide,?_⟩
    rw [indexedKeyDecode7_212]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key213,by decide,?_⟩
    rw [indexedKeyDecode7_213]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key214,by decide,?_⟩
    rw [indexedKeyDecode7_214]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key215,by decide,?_⟩
    rw [indexedKeyDecode7_215]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key216,by decide,?_⟩
    rw [indexedKeyDecode7_216]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key217,by decide,?_⟩
    rw [indexedKeyDecode7_217]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key218,by decide,?_⟩
    rw [indexedKeyDecode7_218]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key219,by decide,?_⟩
    rw [indexedKeyDecode7_219]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key220,by decide,?_⟩
    rw [indexedKeyDecode7_220]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key222,by decide,?_⟩
    rw [indexedKeyDecode7_222]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key223,by decide,?_⟩
    rw [indexedKeyDecode7_223]
    exact atlasWitness_keys7Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key224,by decide,?_⟩
    rw [indexedKeyDecode7_224]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key225,by decide,?_⟩
    rw [indexedKeyDecode7_225]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key226,by decide,?_⟩
    rw [indexedKeyDecode7_226]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key227,by decide,?_⟩
    rw [indexedKeyDecode7_227]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key229,by decide,?_⟩
    rw [indexedKeyDecode7_229]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key230,by decide,?_⟩
    rw [indexedKeyDecode7_230]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key231,by decide,?_⟩
    rw [indexedKeyDecode7_231]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key232,by decide,?_⟩
    rw [indexedKeyDecode7_232]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key233,by decide,?_⟩
    rw [indexedKeyDecode7_233]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key234,by decide,?_⟩
    rw [indexedKeyDecode7_234]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key236,by decide,?_⟩
    rw [indexedKeyDecode7_236]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key237,by decide,?_⟩
    rw [indexedKeyDecode7_237]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key238,by decide,?_⟩
    rw [indexedKeyDecode7_238]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key239,by decide,?_⟩
    rw [indexedKeyDecode7_239]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key240,by decide,?_⟩
    rw [indexedKeyDecode7_240]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key242,by decide,?_⟩
    rw [indexedKeyDecode7_242]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key243,by decide,?_⟩
    rw [indexedKeyDecode7_243]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key244,by decide,?_⟩
    rw [indexedKeyDecode7_244]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key245,by decide,?_⟩
    rw [indexedKeyDecode7_245]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key246,by decide,?_⟩
    rw [indexedKeyDecode7_246]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key247,by decide,?_⟩
    rw [indexedKeyDecode7_247]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key248,by decide,?_⟩
    rw [indexedKeyDecode7_248]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key249,by decide,?_⟩
    rw [indexedKeyDecode7_249]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key250,by decide,?_⟩
    rw [indexedKeyDecode7_250]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key251,by decide,?_⟩
    rw [indexedKeyDecode7_251]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key252,by decide,?_⟩
    rw [indexedKeyDecode7_252]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key254,by decide,?_⟩
    rw [indexedKeyDecode7_254]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key255,by decide,?_⟩
    rw [indexedKeyDecode7_255]
    exact atlasWitness_keys7Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key256,by decide,?_⟩
    rw [indexedKeyDecode7_256]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key257,by decide,?_⟩
    rw [indexedKeyDecode7_257]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key259,by decide,?_⟩
    rw [indexedKeyDecode7_259]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key260,by decide,?_⟩
    rw [indexedKeyDecode7_260]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key261,by decide,?_⟩
    rw [indexedKeyDecode7_261]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key262,by decide,?_⟩
    rw [indexedKeyDecode7_262]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key263,by decide,?_⟩
    rw [indexedKeyDecode7_263]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key264,by decide,?_⟩
    rw [indexedKeyDecode7_264]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key266,by decide,?_⟩
    rw [indexedKeyDecode7_266]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key267,by decide,?_⟩
    rw [indexedKeyDecode7_267]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key268,by decide,?_⟩
    rw [indexedKeyDecode7_268]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key269,by decide,?_⟩
    rw [indexedKeyDecode7_269]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key270,by decide,?_⟩
    rw [indexedKeyDecode7_270]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key271,by decide,?_⟩
    rw [indexedKeyDecode7_271]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key272,by decide,?_⟩
    rw [indexedKeyDecode7_272]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key273,by decide,?_⟩
    rw [indexedKeyDecode7_273]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key274,by decide,?_⟩
    rw [indexedKeyDecode7_274]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key275,by decide,?_⟩
    rw [indexedKeyDecode7_275]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key277,by decide,?_⟩
    rw [indexedKeyDecode7_277]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key278,by decide,?_⟩
    rw [indexedKeyDecode7_278]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key279,by decide,?_⟩
    rw [indexedKeyDecode7_279]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key280,by decide,?_⟩
    rw [indexedKeyDecode7_280]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key281,by decide,?_⟩
    rw [indexedKeyDecode7_281]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key282,by decide,?_⟩
    rw [indexedKeyDecode7_282]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key283,by decide,?_⟩
    rw [indexedKeyDecode7_283]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key284,by decide,?_⟩
    rw [indexedKeyDecode7_284]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key286,by decide,?_⟩
    rw [indexedKeyDecode7_286]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key287,by decide,?_⟩
    rw [indexedKeyDecode7_287]
    exact atlasWitness_keys7Chunk8_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key288,by decide,?_⟩
    rw [indexedKeyDecode7_288]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key289,by decide,?_⟩
    rw [indexedKeyDecode7_289]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key290,by decide,?_⟩
    rw [indexedKeyDecode7_290]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key291,by decide,?_⟩
    rw [indexedKeyDecode7_291]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey7Chunk1
end SparseMonotiles.Canonical
