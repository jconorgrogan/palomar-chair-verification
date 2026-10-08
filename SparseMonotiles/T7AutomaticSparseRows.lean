module
public import SparseMonotiles.T7GeneratedForwardAssembly
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7AutomaticSparseRows
open Contact ContactInverseReuse Existence.Catalog7World
open T7SparseForwardBlock T7GlobalSparseAssembly T7SparseGenerator T7GeneratedForwardAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem generatedCodes_lt (root parent : Pose 7) {n : ℕ}
    (hn : n ∈ generatedCodes root parent) : n < 128 := by
  unfold generatedCodes at hn
  rcases List.mem_append.mp hn with ho | hc
  · have h := of_decide_eq_true (List.mem_filter.mp ho).2
    omega
  · split at hc
    · simp only [List.mem_singleton] at hc
      omega
    · cases hc

/-- Attaching a proposed catalog index cannot discard or insert a role.
The role bound is a proved property of the generator, not a data premise. -/
def witnessedRows (codes : List ℕ) (bound : ∀ n ∈ codes, n < 128)
    (mate : Fin 128 → Fin 408) : SparseRows :=
  codes.attach.map (fun n =>
    let role : Fin 128 := ⟨n.val, bound n.val n.property⟩
    (role, mate role))

theorem witnessedRows_binding (codes : List ℕ) (bound : ∀ n ∈ codes, n < 128)
    (mate : Fin 128 → Fin 408) : CodeBinding codes (witnessedRows codes bound mate) := by
  unfold CodeBinding witnessedRows
  simp only [List.map_map, Function.comp_def]
  simp

def crossRows (mate : Fin 408 → Fin 128 → Fin 128 → Fin 408)
    (k : Fin 408) (a : Fin 128) : SparseRows :=
  witnessedRows (generatedCodes (sourceChild a) (registry k))
    (fun _ h => generatedCodes_lt _ _ h) (mate k a)

def siblingRows (mate : Fin 128 → Fin 128 → Fin 408) (a : Fin 128) : SparseRows :=
  witnessedRows (siblingGeneratedCodes a)
    (fun _ h => generatedCodes_lt _ _ (List.mem_filter.mp h).1) (mate a)

theorem crossRows_binding (mate : Fin 408 → Fin 128 → Fin 128 → Fin 408)
    (k : Fin 408) (a : Fin 128) :
    CodeBinding (generatedCodes (sourceChild a) (registry k)) (crossRows mate k a) :=
  witnessedRows_binding _ _ _

theorem siblingRows_binding (mate : Fin 128 → Fin 128 → Fin 408) (a : Fin 128) :
    CodeBinding (siblingGeneratedCodes a) (siblingRows mate a) :=
  witnessedRows_binding _ _ _

/-- Uniform completeness removes all per-block projection comparisons.
Only proposed full-pose membership checks over generated roles remain.
This is a sufficient certificate, not a claim that every safe role contacts. -/
theorem forwardRules_of_generated_member_checks
    (siblingMate : Fin 128 → Fin 128 → Fin 408)
    (crossMate : Fin 408 → Fin 128 → Fin 128 → Fin 408)
    (siblings : SiblingChecks (siblingRows siblingMate))
    (crosses : CrossChecks (crossRows crossMate)) : ForwardRules children7 M7 :=
  forwardRules_of_generated_bindings_and_members (siblingRows siblingMate) (crossRows crossMate)
    (siblingRows_binding siblingMate) (crossRows_binding crossMate) siblings crosses

theorem hasTiling_of_generated_member_checks_and_remaining205
    (siblingMate : Fin 128 → Fin 128 → Fin 408)
    (crossMate : Fin 408 → Fin 128 → Fin 128 → Fin 408)
    (siblings : SiblingChecks (siblingRows siblingMate))
    (crosses : CrossChecks (crossRows crossMate))
    (hrest : ∀ i ∈ Existence.ProfileBridge7.remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i)) : HasTiling T7 :=
  hasTiling_of_forward_and_remaining205
    (forwardRules_of_generated_member_checks siblingMate crossMate siblings crosses) hrest

#print axioms generatedCodes_lt
#print axioms witnessedRows_binding
#print axioms forwardRules_of_generated_member_checks
#print axioms hasTiling_of_generated_member_checks_and_remaining205
end SparseMonotiles.CarrierHierarchy.T7AutomaticSparseRows
