module
public import T7KeyIndexingChunk00
public import T7KeyIndexingChunk01
public import T7KeyIndexingChunk02
public import T7KeyIndexingChunk03
public import T7KeyIndexingChunk04
public import T7KeyIndexingChunk05
public import T7KeyIndexingChunk06
public import T7KeyIndexingChunk07
public import T7KeyIndexingChunk08
public import T7KeyIndexingChunk09
public import T7KeyIndexingChunk10
public import T7KeyIndexingChunk11
public import T7KeyIndexingChunk12
public import T7KeyIndexingChunk13
public import T7KeyIndexingChunk14
public import T7KeyIndexingChunk15
public import T7KeyIndexingChunk16
public import T7KeyIndexingChunk17
public import T7KeyIndexingChunk18
public import T7KeyIndexingChunk19
public import T7KeyIndexingChunk20
public import T7KeyIndexingChunk21
public import T7KeyIndexingChunk22
public import T7KeyIndexingChunk23
public import T7KeyIndexingChunk24
public import T7KeyIndexingChunk25
public import T7KeyIndexingChunk26
public import T7KeyIndexingChunk27
@[expose] public section
namespace SparseMonotiles.Contact.T7KeyIndexing
open IndexedData7 RootZeroPilot7
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] IndexBinding

/-- All 896 static facet profile bindings, assembled from 28 kernel-checked
blocks of 32. No ordered-pair certificates are checked in this theorem. -/
theorem all_indexBinding (i : Fin 896) : IndexBinding i := by
  by_cases h0 : i.val < 32
  · have h := indexBindingChunk00 ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := indexBindingChunk01 ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := indexBindingChunk02 ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := indexBindingChunk03 ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h4 : i.val < 160
  · have h := indexBindingChunk04 ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h5 : i.val < 192
  · have h := indexBindingChunk05 ⟨i.val - 160, by omega⟩
    have he : (⟨160 + (i.val - 160), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h6 : i.val < 224
  · have h := indexBindingChunk06 ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h7 : i.val < 256
  · have h := indexBindingChunk07 ⟨i.val - 224, by omega⟩
    have he : (⟨224 + (i.val - 224), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h8 : i.val < 288
  · have h := indexBindingChunk08 ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h9 : i.val < 320
  · have h := indexBindingChunk09 ⟨i.val - 288, by omega⟩
    have he : (⟨288 + (i.val - 288), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h10 : i.val < 352
  · have h := indexBindingChunk10 ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h11 : i.val < 384
  · have h := indexBindingChunk11 ⟨i.val - 352, by omega⟩
    have he : (⟨352 + (i.val - 352), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h12 : i.val < 416
  · have h := indexBindingChunk12 ⟨i.val - 384, by omega⟩
    have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h13 : i.val < 448
  · have h := indexBindingChunk13 ⟨i.val - 416, by omega⟩
    have he : (⟨416 + (i.val - 416), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h14 : i.val < 480
  · have h := indexBindingChunk14 ⟨i.val - 448, by omega⟩
    have he : (⟨448 + (i.val - 448), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h15 : i.val < 512
  · have h := indexBindingChunk15 ⟨i.val - 480, by omega⟩
    have he : (⟨480 + (i.val - 480), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h16 : i.val < 544
  · have h := indexBindingChunk16 ⟨i.val - 512, by omega⟩
    have he : (⟨512 + (i.val - 512), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h17 : i.val < 576
  · have h := indexBindingChunk17 ⟨i.val - 544, by omega⟩
    have he : (⟨544 + (i.val - 544), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h18 : i.val < 608
  · have h := indexBindingChunk18 ⟨i.val - 576, by omega⟩
    have he : (⟨576 + (i.val - 576), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h19 : i.val < 640
  · have h := indexBindingChunk19 ⟨i.val - 608, by omega⟩
    have he : (⟨608 + (i.val - 608), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h20 : i.val < 672
  · have h := indexBindingChunk20 ⟨i.val - 640, by omega⟩
    have he : (⟨640 + (i.val - 640), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h21 : i.val < 704
  · have h := indexBindingChunk21 ⟨i.val - 672, by omega⟩
    have he : (⟨672 + (i.val - 672), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h22 : i.val < 736
  · have h := indexBindingChunk22 ⟨i.val - 704, by omega⟩
    have he : (⟨704 + (i.val - 704), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h23 : i.val < 768
  · have h := indexBindingChunk23 ⟨i.val - 736, by omega⟩
    have he : (⟨736 + (i.val - 736), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h24 : i.val < 800
  · have h := indexBindingChunk24 ⟨i.val - 768, by omega⟩
    have he : (⟨768 + (i.val - 768), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h25 : i.val < 832
  · have h := indexBindingChunk25 ⟨i.val - 800, by omega⟩
    have he : (⟨800 + (i.val - 800), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h26 : i.val < 864
  · have h := indexBindingChunk26 ⟨i.val - 832, by omega⟩
    have he : (⟨832 + (i.val - 832), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h27 : i.val < 896
  · have h := indexBindingChunk27 ⟨i.val - 864, by omega⟩
    have he : (⟨864 + (i.val - 864), by omega⟩ : Fin 896) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  omega

theorem all_profile_eq (i : Fin 896) :
    ((profileList i).map sourceKey).toFinset = geometry.profile i :=
  by
    have h := all_indexBinding i
    unfold IndexBinding at h
    exact h.1

theorem all_owner_checked (i : Fin 896) :
    (profileList i).all (fun a => decide (sourceOwner a = i)) = true :=
  by
    have h := all_indexBinding i
    unfold IndexBinding at h
    exact h.2

/-- Reusable exact indexing of the original T7 896-facet geometry by all
1,024 dictionary keys. Its fields are the existing PilotBase functions. -/
noncomputable def generatorIndexingT7 : KeyIndexing IndexedData7.geometry 1024 :=
  KeyIndexing.ofLists sourceOwner sourceKey profileList all_profile_eq all_owner_checked


#print axioms all_indexBinding
#print axioms all_profile_eq
#print axioms all_owner_checked
#print axioms generatorIndexingT7
end SparseMonotiles.Contact.T7KeyIndexing
