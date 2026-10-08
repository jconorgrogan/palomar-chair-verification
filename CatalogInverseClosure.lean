module
public import CatalogInverseRows0
public import CatalogInverseRows1
public import CatalogInverseRows2
public import CatalogInverseRows3
public import CatalogInverseRows4
public import CatalogInverseRows5
public import CatalogInverseRows6
public import CatalogInverseRows7
public import CatalogInverseRows8
public import CatalogInverseRows9
public import CatalogInverseRows10
public import CatalogInverseRows11
public import CatalogInverseRows12
@[expose] public section
namespace SparseMonotiles.ContactInverseReuse
open Contact CarrierHierarchy
set_option maxRecDepth 100000

theorem catalogInverse_all_rows (i : Fin 408) : CatalogInverseRow i := by
  by_cases h0 : i.val < 32
  · have h := inverse_rows_0 ⟨i.val - 0, by omega⟩
    have he : (⟨0 + (i.val - 0), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h1 : i.val < 64
  · have h := inverse_rows_1 ⟨i.val - 32, by omega⟩
    have he : (⟨32 + (i.val - 32), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h2 : i.val < 96
  · have h := inverse_rows_2 ⟨i.val - 64, by omega⟩
    have he : (⟨64 + (i.val - 64), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h3 : i.val < 128
  · have h := inverse_rows_3 ⟨i.val - 96, by omega⟩
    have he : (⟨96 + (i.val - 96), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h4 : i.val < 160
  · have h := inverse_rows_4 ⟨i.val - 128, by omega⟩
    have he : (⟨128 + (i.val - 128), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h5 : i.val < 192
  · have h := inverse_rows_5 ⟨i.val - 160, by omega⟩
    have he : (⟨160 + (i.val - 160), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h6 : i.val < 224
  · have h := inverse_rows_6 ⟨i.val - 192, by omega⟩
    have he : (⟨192 + (i.val - 192), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h7 : i.val < 256
  · have h := inverse_rows_7 ⟨i.val - 224, by omega⟩
    have he : (⟨224 + (i.val - 224), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h8 : i.val < 288
  · have h := inverse_rows_8 ⟨i.val - 256, by omega⟩
    have he : (⟨256 + (i.val - 256), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h9 : i.val < 320
  · have h := inverse_rows_9 ⟨i.val - 288, by omega⟩
    have he : (⟨288 + (i.val - 288), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h10 : i.val < 352
  · have h := inverse_rows_10 ⟨i.val - 320, by omega⟩
    have he : (⟨320 + (i.val - 320), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  by_cases h11 : i.val < 384
  · have h := inverse_rows_11 ⟨i.val - 352, by omega⟩
    have he : (⟨352 + (i.val - 352), by omega⟩ : Fin 408) = i := by
      apply Fin.ext
      dsimp
      omega
    exact he ▸ h
  have h := inverse_rows_12 ⟨i.val - 384, by omega⟩
  have he : (⟨384 + (i.val - 384), by omega⟩ : Fin 408) = i := by
    apply Fin.ext
    dsimp
    omega
  exact he ▸ h

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only

/-- Full pose equality reconstructed from the kernel-checked coordinate witnesses. -/
theorem inversePose_catalogRow (i : Fin 408) :
    inversePose (catalogRow i) = catalogRow (inverseIndex i) := by
  apply pose_ext
  · apply Equiv.ext
    intro j
    exact (catalogInverse_all_rows i j).1
  · funext j
    exact (catalogInverse_all_rows i j).2.1
  · funext j
    exact (catalogInverse_all_rows i j).2.2

/-- The original compact 408-pose catalog itself is inverse-closed. -/
theorem M7_inversePose_closed (p : Pose 7) (hp : p ∈ M7) : inversePose p ∈ M7 := by
  change p ∈ Catalog7.supplied at hp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  let k : Fin 408 := ⟨i.val, by simpa only [Catalog7.supplied_count] using i.isLt⟩
  have hk : catalogRow k = p := by simpa only [catalogRow, k] using hi
  rw [← hk, inversePose_catalogRow]
  change Catalog7.supplied.get _ ∈ Catalog7.supplied
  exact List.get_mem _ _

theorem M7_inversePose_iff (p : Pose 7) : p ∈ M7 ↔ inversePose p ∈ M7 := by
  constructor
  · exact M7_inversePose_closed p
  · intro h
    simpa only [inversePose_inversePose] using M7_inversePose_closed (inversePose p) h

/-- Certified exact inversion reuses a representative's original-M7 classification. -/
theorem classify_M7_of_eq_inversePose {n : ℕ} {g : IndexedGeometry 7 n}
    {p q : Pose 7} (he : p = inversePose q)
    (hq : g.LegalContact q → q ∈ M7) : g.LegalContact p → p ∈ M7 :=
  classify_of_eq_inversePose M7_inversePose_closed he hq

#print axioms catalogInverse_all_rows
#print axioms inversePose_catalogRow
#print axioms M7_inversePose_closed
#print axioms M7_inversePose_iff
#print axioms classify_M7_of_eq_inversePose
end SparseMonotiles.ContactInverseReuse
