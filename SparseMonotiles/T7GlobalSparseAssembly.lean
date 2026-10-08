module
public import SparseMonotiles.ForwardSparseAssembly
public import SparseMonotiles.T7Existence205
public import SparseMonotiles.T7SparseForwardBase
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7GlobalSparseAssembly
open Contact ContactInverseReuse Existence.Catalog7World T7SparseForwardBlock
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem registry_covers {p : Pose 7} (hp : p ∈ M7) :
    ∃ i : Fin 408, registry i = p := by
  change p ∈ Catalog7.supplied at hp
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
  let i : Fin 408 := ⟨j.val, by simpa only [Catalog7.supplied_count] using j.isLt⟩
  exact ⟨i, by simpa only [registry, i] using hj⟩

abbrev SparseRows := List (Fin 128 × Fin 408)

def childFields (i : Fin 128) : CoarseFields := exactFields (sourceChild i)
def crossFields (k : Fin 408) (i : Fin 128) : CoarseFields :=
  (registryFields k).dilate.compose (childFields i)

def SiblingChecks (rows : Fin 128 → SparseRows) : Prop :=
  ∀ a, sparseMemberChecks 7 registryFields (childFields a) childFields (rows a) = true

def CrossChecks (rows : Fin 408 → Fin 128 → SparseRows) : Prop :=
  ∀ k a, sparseMemberChecks 7 registryFields (childFields a) (crossFields k) (rows k a) = true

/-- Semantic completeness is separate from the inexpensive retained-row
membership checks. This is the only place omitted roles must be justified. -/
structure CompleteSparseCoverage
    (siblingRows : Fin 128 → SparseRows)
    (crossRows : Fin 408 → Fin 128 → SparseRows) : Prop where
  sibling : ∀ a b, sourceChild a ≠ sourceChild b → CellContact (sourceChild a) (sourceChild b) →
    ∃ j, (b,j) ∈ siblingRows a
  cross : ∀ k a b,
    CellContact (sourceChild a) (compose (dilatePose (registry k)) (sourceChild b)) →
    ∃ j, (b,j) ∈ crossRows k a

/-- Exact original-table forward rules, without a legal-world or tiling
assumption, from sparse coverage and only retained full-pose checks. -/
theorem forwardRules_of_complete_sparse_rows
    (siblingRows : Fin 128 → SparseRows)
    (crossRows : Fin 408 → Fin 128 → SparseRows)
    (coverage : CompleteSparseCoverage siblingRows crossRows)
    (siblings : SiblingChecks siblingRows) (crosses : CrossChecks crossRows) :
    ForwardRules children7 M7 :=
  forwardRules_of_sparse_member_rows children7 M7 sourceChild registry registry
    (fun _ h => children7_covered h) (fun _ h => registry_covers h) registry_mem
    childFields registryFields registryFields
    (fun _ => exactFields_represents _) registryFields_represents registryFields_represents
    siblingRows crossRows coverage.sibling coverage.cross siblings crosses

/-- A proved source-role generator need only be checked against the first
projection of each sparse witness list, not against all128 source roles. -/
theorem coverage_of_complete_generators
    (siblingRows : Fin 128 → SparseRows)
    (crossRows : Fin 408 → Fin 128 → SparseRows)
    (siblingRoles : Fin 128 → List (Fin 128))
    (crossRoles : Fin 408 → Fin 128 → List (Fin 128))
    (sibling_complete : ∀ a b, sourceChild a ≠ sourceChild b →
      CellContact (sourceChild a) (sourceChild b) → b ∈ siblingRoles a)
    (cross_complete : ∀ k a b,
      CellContact (sourceChild a) (compose (dilatePose (registry k)) (sourceChild b)) →
      b ∈ crossRoles k a)
    (sibling_binding : ∀ a, siblingRoles a = (siblingRows a).map Prod.fst)
    (cross_binding : ∀ k a, crossRoles k a = (crossRows k a).map Prod.fst) :
    CompleteSparseCoverage siblingRows crossRows := by
  constructor
  · intro a b hne hc
    have h := sibling_complete a b hne hc
    rw [sibling_binding a] at h
    obtain ⟨⟨i,j⟩, hrow, he⟩ := List.mem_map.mp h
    exact ⟨j, by simpa only [Prod.fst] using he ▸ hrow⟩
  · intro k a b hc
    have h := cross_complete k a b hc
    rw [cross_binding k a] at h
    obtain ⟨⟨i,j⟩, hrow, he⟩ := List.mem_map.mp h
    exact ⟨j, by simpa only [Prod.fst] using he ▸ hrow⟩

/-- Full original compact-body existence follows when all sparse witnesses
are certified and the remaining205 inverse representatives are legal. -/
theorem hasTiling_of_complete_sparse_rows_and_remaining205
    (siblingRows : Fin 128 → SparseRows)
    (crossRows : Fin 408 → Fin 128 → SparseRows)
    (coverage : CompleteSparseCoverage siblingRows crossRows)
    (siblings : SiblingChecks siblingRows) (crosses : CrossChecks crossRows)
    (hrest : ∀ i ∈ Existence.ProfileBridge7.remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i)) : HasTiling T7 :=
  hasTiling_of_forward_and_remaining205
    (forwardRules_of_complete_sparse_rows siblingRows crossRows coverage siblings crosses) hrest

#print axioms registry_covers
#print axioms forwardRules_of_complete_sparse_rows
#print axioms coverage_of_complete_generators
#print axioms hasTiling_of_complete_sparse_rows_and_remaining205
end SparseMonotiles.CarrierHierarchy.T7GlobalSparseAssembly
