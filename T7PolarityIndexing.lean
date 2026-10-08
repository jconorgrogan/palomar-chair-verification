module
public import T7PolarityIndexBlock0
public import T7PolarityIndexBlock1
public import T7PolarityIndexBlock2
public import T7PolarityIndexBlock3
@[expose] public section
namespace SparseMonotiles.T7PolarityIndexing
open Contact CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem allCover (i : Fin 1024) : checkCover i = true := by
  by_cases h0 : i.val < 256
  · have h := allPairsB_sound coverBlock0 0 (⟨i.val - 0, by omega⟩ : Fin 256)
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 1024) = i := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using h
  by_cases h1 : i.val < 512
  · have h := allPairsB_sound coverBlock1 0 (⟨i.val - 256, by omega⟩ : Fin 256)
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 1024) = i := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using h
  by_cases h2 : i.val < 768
  · have h := allPairsB_sound coverBlock2 0 (⟨i.val - 512, by omega⟩ : Fin 256)
    have he : (⟨512 + (i.val - 512), by omega⟩ : Fin 1024) = i := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using h
  by_cases h3 : i.val < 1024
  · have h := allPairsB_sound coverBlock3 0 (⟨i.val - 768, by omega⟩ : Fin 256)
    have he : (⟨768 + (i.val - 768), by omega⟩ : Fin 1024) = i := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using h
  omega
theorem bumpIndex_covers {a : Fin 1024}
    (ha : (T7KeyIndexing.generatorIndexingT7.key a).bump = true) :
    bumpIndex (rank a) = a := by
  have h := allCover a
  simpa [checkCover, ha] using h

theorem dentIndex_covers {a : Fin 1024}
    (ha : (T7KeyIndexing.generatorIndexingT7.key a).bump = false) :
    dentIndex (rank a) = a := by
  have h := allCover a
  simpa [checkCover, ha] using h

/-- All 512 by 512 listed pairs suffice for the complete physical contact
classifier. The index coverage, including both coefficient classes, is checked. -/
theorem contact_mem_M7_of_512_pair_classifications
    (hpairs : ∀ (a b : Fin 512) (p : Pose 7),
      T7KeyIndexing.generatorIndexingT7.pair (bumpIndex a) (dentIndex b) = some p →
      IndexedData7.geometry.LegalContact p → p ∈ M7)
    {p : Pose 7} (legal : IndexedData7.geometry.LegalContact p) : p ∈ M7 := by
  apply T7_contact_mem_M7_of_bump_dent_pair_classifications ?_ legal
  intro a b q ha hb generated hq
  apply hpairs (rank a) (rank b) q
  · simpa only [bumpIndex_covers ha, dentIndex_covers hb] using generated
  · exact hq

#print axioms allCover
#print axioms bumpIndex_covers
#print axioms dentIndex_covers
#print axioms contact_mem_M7_of_512_pair_classifications
end SparseMonotiles.T7PolarityIndexing
