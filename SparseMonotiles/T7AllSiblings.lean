module
public import SparseMonotiles.T7SiblingChunk0
public import SparseMonotiles.T7SiblingChunk1
public import SparseMonotiles.T7SiblingChunk2
public import SparseMonotiles.T7SiblingChunk3
public import SparseMonotiles.T7SiblingChunk4
public import SparseMonotiles.T7SiblingChunk5
public import SparseMonotiles.T7SiblingChunk6
public import SparseMonotiles.T7SiblingChunk7
public import SparseMonotiles.T7SiblingChunk8
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AllSiblings
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows T7SiblingData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All128 roots. Each retained row is checked in exactly one finite chunk. -/
theorem siblings_checked : SiblingChecks (siblingRows siblingMate) := by
  intro a
  by_cases h0 : a.val < 16
  · exact T7SiblingChunk0.checked a (by omega) h0
  by_cases h1 : a.val < 32
  · exact T7SiblingChunk1.checked a (by omega) h1
  by_cases h2 : a.val < 48
  · exact T7SiblingChunk2.checked a (by omega) h2
  by_cases h3 : a.val < 64
  · exact T7SiblingChunk3.checked a (by omega) h3
  by_cases h4 : a.val < 80
  · exact T7SiblingChunk4.checked a (by omega) h4
  by_cases h5 : a.val < 96
  · exact T7SiblingChunk5.checked a (by omega) h5
  by_cases h6 : a.val < 112
  · exact T7SiblingChunk6.checked a (by omega) h6
  by_cases h7 : a.val < 127
  · exact T7SiblingChunk7.checked a (by omega) h7
  exact T7SiblingChunk8.checked a (by omega) a.isLt

/-- The actual sibling field, stated for distinct child poses in the original table. -/
theorem sibling_rule : ∀ a ∈ children7, ∀ b ∈ children7,
    a ≠ b → CellContact a b → normalize a b ∈ M7 := by
  intro a ha b hb hne hc
  obtain ⟨i, rfl⟩ := children7_covered ha
  obtain ⟨j, rfl⟩ := children7_covered hb
  obtain ⟨n, hn⟩ := codeBinding_member (siblingRows_binding siblingMate i)
    (cellContact_sibling_generated i j hne hc)
  have he := sparseMemberChecks_sound registry registryFields registryFields_represents
    (exactFields_represents _) (fun _ => exactFields_represents _)
    (siblings_checked i) hn
  rw [he]
  exact registry_mem n

/-- Sibling data is discharged; only cross-parent finite checks are needed here. -/
theorem forwardRules_of_cross_checks
    (crossMate : Fin 408 → Fin 128 → Fin 128 → Fin 408)
    (crosses : CrossChecks (crossRows crossMate)) : ForwardRules children7 M7 :=
  forwardRules_of_generated_member_checks siblingMate crossMate siblings_checked crosses

#print axioms siblings_checked
#print axioms sibling_rule
#print axioms forwardRules_of_cross_checks
end SparseMonotiles.CarrierHierarchy.T7AllSiblings
