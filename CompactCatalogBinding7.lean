module
public import CatalogRows0
public import CatalogRows1
public import CatalogRows2
public import CatalogRows3
public import CatalogRows4
public import CatalogRows5
public import CatalogRows6
public import CatalogRows7
public import CatalogRows8
public import CatalogRows9
public import CatalogRows10
public import CatalogRows11
public import CatalogRows12
@[expose] public section
namespace SparseMonotiles.CompactCatalogBinding7
open Contact CarrierHierarchy CompactPoseAdapter
set_option maxRecDepth 100000

theorem all_rows_same (i : Fin 408) : RowSame i := by
  by_cases h0 : i.val < 32
  · have h := rows0_checked ⟨i.val - 0, by omega⟩
    have he : (⟨i.val - 0, by omega⟩ : Fin 408) = i := by apply Fin.ext; rfl
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := rows1_checked ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := rows2_checked ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := rows3_checked ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h4 : i.val < 160
  · have h := rows4_checked ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h5 : i.val < 192
  · have h := rows5_checked ⟨i.val - 160, by omega⟩
    have he : (⟨160 + (i.val - 160), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h6 : i.val < 224
  · have h := rows6_checked ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h7 : i.val < 256
  · have h := rows7_checked ⟨i.val - 224, by omega⟩
    have he : (⟨224 + (i.val - 224), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h8 : i.val < 288
  · have h := rows8_checked ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h9 : i.val < 320
  · have h := rows9_checked ⟨i.val - 288, by omega⟩
    have he : (⟨288 + (i.val - 288), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h10 : i.val < 352
  · have h := rows10_checked ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  by_cases h11 : i.val < 384
  · have h := rows11_checked ⟨i.val - 352, by omega⟩
    have he : (⟨352 + (i.val - 352), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
    exact he ▸ h
  have h := rows12_checked ⟨i.val - 384, by omega⟩
  have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 408) = i := by apply Fin.ext; dsimp; omega
  exact he ▸ h

/-- Exact ordered equality of full signed poses, beyond count or external hash agreement. -/
theorem mapped_supplied_eq_literal :
    Catalog7.supplied.map toRP = CompactT7Preparation.literalCatalog := by
  apply List.ext_getElem
  · simp only [List.length_map, Catalog7.supplied_count, CompactT7Preparation.literalCatalog_length]
  · intro n hn hm
    have hi : n < 408 := by simpa only [List.length_map, Catalog7.supplied_count] using hn
    have h := RegisteredPrime.Pose.Same.eq (all_rows_same ⟨n, hi⟩)
    rw [List.getElem_map]
    simpa only [nativeRow, literalRow, List.get_eq_getElem] using h

/-- The actual compact registered catalog maps to the independently checked literal list. -/
theorem M7_to_literal {p : Contact.Pose 7} (hp : p ∈ M7) :
    toRP p ∈ CompactT7Preparation.literalCatalog := by
  rw [← mapped_supplied_eq_literal]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem M7_to_arithmeticAtlas {p : Contact.Pose 7} (hp : p ∈ M7) :
    RegisteredPrime.ArithmeticAtlasContact CompactT7Preparation.P7 (toRP p) :=
  CompactT7Preparation.literalCatalog_arithmeticAtlas _ (M7_to_literal hp)

/-- Concrete compact-library registered zero periods. No finite coarse-certificate
package, abstract atlas inclusion, or world transport remains as a premise. -/
theorem registered_compact7_period_zero (W : RegisteredWorld 7)
    (legal : W.Legal M7) (v : Contact.Cell 7) (period : W.IsPeriod v) : v = 0 := by
  have hatlas : RegisteredPrime.ArithmeticAtlasLegal CompactT7Preparation.P7
      (toRegisteredWorld W) :=
    toRegisteredWorld_atlas_legal W M7 CompactT7Preparation.P7 rfl
      (fun p hp => M7_to_arithmeticAtlas hp) legal
  have hperiod := (toRegisteredWorld_period_iff W v).mpr period
  exact RegisteredPrime.AtlasPeriods.arithmetic_atlas_translation_aperiodic
    CompactT7Preparation.P7 (toRegisteredWorld W) hatlas v hperiod

#print axioms mapped_supplied_eq_literal
#print axioms M7_to_arithmeticAtlas
#print axioms registered_compact7_period_zero
end SparseMonotiles.CompactCatalogBinding7
