module

public import SparseMonotiles.AtlasReverseChunks.Tile7Keys8
public import SparseMonotiles.AtlasReverseChunks.Tile7Keys9
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact

open Contact.IndexedData7

theorem atlasFacet7_224_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 224) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key256} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_256_mem

theorem atlasFacet7_225_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 225) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key257, key258} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_257_mem
  · exact indexedKey7_258_mem

theorem atlasFacet7_226_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 226) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key259} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_259_mem

theorem atlasFacet7_227_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 227) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key260} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_260_mem

theorem atlasFacet7_228_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 228) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key261} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_261_mem

theorem atlasFacet7_229_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 229) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key262} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_262_mem

theorem atlasFacet7_230_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 230) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key263} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_263_mem

theorem atlasFacet7_231_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 231) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key264, key265} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_264_mem
  · exact indexedKey7_265_mem

theorem atlasFacet7_232_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 232) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key266} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_266_mem

theorem atlasFacet7_233_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 233) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key267} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_267_mem

theorem atlasFacet7_234_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 234) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key268} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_268_mem

theorem atlasFacet7_235_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 235) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key269} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_269_mem

theorem atlasFacet7_236_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 236) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key270} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_270_mem

theorem atlasFacet7_237_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 237) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key271} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_271_mem

theorem atlasFacet7_238_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 238) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key272} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_272_mem

theorem atlasFacet7_239_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 239) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key273} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_273_mem

theorem atlasFacet7_240_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 240) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key274} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_274_mem

theorem atlasFacet7_241_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 241) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key275, key276} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_275_mem
  · exact indexedKey7_276_mem

theorem atlasFacet7_242_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 242) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key277} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_277_mem

theorem atlasFacet7_243_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 243) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key278} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_278_mem

theorem atlasFacet7_244_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 244) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key279} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_279_mem

theorem atlasFacet7_245_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 245) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key280} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_280_mem

theorem atlasFacet7_246_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 246) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key281} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_281_mem

theorem atlasFacet7_247_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 247) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key282} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_282_mem

theorem atlasFacet7_248_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 248) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key283} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_283_mem

theorem atlasFacet7_249_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 249) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key284, key285} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_284_mem
  · exact indexedKey7_285_mem

theorem atlasFacet7_250_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 250) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key286} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_286_mem

theorem atlasFacet7_251_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 251) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key287} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_287_mem

theorem atlasFacet7_252_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 252) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key288} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_288_mem

theorem atlasFacet7_253_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 253) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key289} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_289_mem

theorem atlasFacet7_254_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 254) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key290} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_290_mem

theorem atlasFacet7_255_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 255) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key291} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_291_mem

theorem atlasReverse7Chunk7 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨224 + i.val, by omega⟩, b.toKeyData 188160 ∈ keys7 := by
  fin_cases i
  · exact atlasFacet7_224_literal
  · exact atlasFacet7_225_literal
  · exact atlasFacet7_226_literal
  · exact atlasFacet7_227_literal
  · exact atlasFacet7_228_literal
  · exact atlasFacet7_229_literal
  · exact atlasFacet7_230_literal
  · exact atlasFacet7_231_literal
  · exact atlasFacet7_232_literal
  · exact atlasFacet7_233_literal
  · exact atlasFacet7_234_literal
  · exact atlasFacet7_235_literal
  · exact atlasFacet7_236_literal
  · exact atlasFacet7_237_literal
  · exact atlasFacet7_238_literal
  · exact atlasFacet7_239_literal
  · exact atlasFacet7_240_literal
  · exact atlasFacet7_241_literal
  · exact atlasFacet7_242_literal
  · exact atlasFacet7_243_literal
  · exact atlasFacet7_244_literal
  · exact atlasFacet7_245_literal
  · exact atlasFacet7_246_literal
  · exact atlasFacet7_247_literal
  · exact atlasFacet7_248_literal
  · exact atlasFacet7_249_literal
  · exact atlasFacet7_250_literal
  · exact atlasFacet7_251_literal
  · exact atlasFacet7_252_literal
  · exact atlasFacet7_253_literal
  · exact atlasFacet7_254_literal
  · exact atlasFacet7_255_literal

#print axioms atlasReverse7Chunk7
end SparseMonotiles.Canonical
