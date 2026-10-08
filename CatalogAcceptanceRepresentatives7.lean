module
public import CatalogInverseClosure
public import SparseMonotiles.ContactCertificateDataIndexed7Base
@[expose] public section
namespace SparseMonotiles.ContactInverseReuse
open Contact CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Proposed inverse indices are checked as an actual involution, separately
from the full-pose inverse equalities already proved for the catalog. -/
theorem inverseIndex_involutive : Function.Involutive inverseIndex := by
  change ∀ i : Fin 408, inverseIndex (inverseIndex i) = i
  decide +kernel

def acceptanceRepresentatives : Finset (Fin 408) :=
  Finset.univ.filter (fun i => i.val ≤ (inverseIndex i).val)

theorem acceptanceRepresentatives_count : acceptanceRepresentatives.card = 208 := by
  decide +kernel

theorem inverseFixedIndex_count :
    (Finset.univ.filter (fun i : Fin 408 => inverseIndex i = i)).card = 8 := by
  decide +kernel

/-- Every original M7 pose is a representative or its exact inverse.
No acceptance, contact classification or tiling premise is used. -/
theorem M7_has_acceptance_representative (p : Pose 7) (hp : p ∈ M7) :
    ∃ i ∈ acceptanceRepresentatives,
      p = catalogRow i ∨ p = inversePose (catalogRow i) := by
  change p ∈ Catalog7.supplied at hp
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
  let k : Fin 408 := ⟨j.val, by simpa only [Catalog7.supplied_count] using j.isLt⟩
  have hk : catalogRow k = p := by simpa only [catalogRow, k] using hj
  by_cases hle : k.val ≤ (inverseIndex k).val
  · exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩, Or.inl hk.symm⟩
  · refine ⟨inverseIndex k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Or.inr ?_⟩
    · rw [inverseIndex_involutive k]
      omega
    · calc
        p = catalogRow k := hk.symm
        _ = inversePose (inversePose (catalogRow k)) := (inversePose_inversePose _).symm
        _ = inversePose (catalogRow (inverseIndex k)) :=
          congrArg inversePose (inversePose_catalogRow k)

/-- For any indexed geometry, acceptance of the 208 chosen catalog rows
implies acceptance of the entire M7 language by proved inversion transport. -/
theorem M7_legal_of_acceptance_representatives {n : ℕ} (g : IndexedGeometry 7 n)
    (hlegal : ∀ i ∈ acceptanceRepresentatives, g.LegalContact (catalogRow i)) :
    ∀ p ∈ M7, g.LegalContact p := by
  intro p hp
  obtain ⟨i, hi, he⟩ := M7_has_acceptance_representative p hp
  have h := hlegal i hi
  rcases he with he | he
  · simpa only [he] using h
  · simpa only [he] using legalContact_inversePose h

#print axioms inverseIndex_involutive
#print axioms acceptanceRepresentatives_count
#print axioms inverseFixedIndex_count
#print axioms M7_has_acceptance_representative
#print axioms M7_legal_of_acceptance_representatives
end SparseMonotiles.ContactInverseReuse
