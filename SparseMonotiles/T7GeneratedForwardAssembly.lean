module
public import SparseMonotiles.T7SparseMemberThreeBlocks
public import SparseMonotiles.T7SparseGeneratorThreeBlocks
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7GeneratedForwardAssembly
open Contact ContactInverseReuse Existence.Catalog7World
open T7SparseForwardBlock T7GlobalSparseAssembly T7SparseMemberThreeBlocks T7SparseGenerator
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Equality of finite projections is sufficient. No list-order or
duplicate-free assumption is needed in the complete certificate interface. -/
def CodeBinding (codes : List ℕ) (rows : SparseRows) : Prop :=
  codes.toFinset = (rows.map (fun pair => pair.1.val)).toFinset

theorem codeBinding_member {codes : List ℕ} {rows : SparseRows}
    (binding : CodeBinding codes rows) {n : Fin 128} (hn : n.val ∈ codes) :
    ∃ j, (n,j) ∈ rows := by
  have hm : n.val ∈ (rows.map (fun pair => pair.1.val)).toFinset := by
    rw [← binding]
    exact List.mem_toFinset.mpr hn
  obtain ⟨⟨i,j⟩, hij, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  have heq : i = n := Fin.ext he
  exact ⟨j, heq ▸ hij⟩

def siblingGeneratedCodes (a : Fin 128) : List ℕ :=
  (generatedCodes (sourceChild a) (rootPose 7)).filter (fun n => decide (n ≠ a.val))

theorem cellContact_sibling_generated (a b : Fin 128)
    (hne : sourceChild a ≠ sourceChild b) (hc : CellContact (sourceChild a) (sourceChild b)) :
    b.val ∈ siblingGeneratedCodes a := by
  have hc' : CellContact (sourceChild a)
      (compose (dilatePose (rootPose 7)) (sourceChild b)) := by
    simpa only [dilatePose_root, compose_root_left] using hc
  have hg := cellContact_sourceChild_generated (sourceChild a) (rootPose 7) b hc'
  apply List.mem_filter.mpr
  refine ⟨hg, ?_⟩
  simp only [decide_eq_true_eq]
  intro hval
  have hba : b = a := Fin.ext hval
  exact hne (congrArg sourceChild hba.symm)

/-- The generator has already proved omitted-role completeness uniformly.
Only equality to each sparse row projection remains a finite certificate. -/
theorem completeCoverage_of_generated_bindings
    (siblingRows : Fin 128 → SparseRows) (crossRows : Fin 408 → Fin 128 → SparseRows)
    (sibling_binding : ∀ a, CodeBinding (siblingGeneratedCodes a) (siblingRows a))
    (cross_binding : ∀ k a, CodeBinding
      (generatedCodes (sourceChild a) (registry k)) (crossRows k a)) :
    CompleteSparseCoverage siblingRows crossRows := by
  constructor
  · intro a b hne hc
    exact codeBinding_member (sibling_binding a) (cellContact_sibling_generated a b hne hc)
  · intro k a b hc
    exact codeBinding_member (cross_binding k a)
      (cellContact_sourceChild_generated (sourceChild a) (registry k) b hc)

/-- Full exact ForwardRules now reduce to finite generated-list bindings
and full-pose checks only for the retained witness rows. -/
theorem forwardRules_of_generated_bindings_and_members
    (siblingRows : Fin 128 → SparseRows) (crossRows : Fin 408 → Fin 128 → SparseRows)
    (sibling_binding : ∀ a, CodeBinding (siblingGeneratedCodes a) (siblingRows a))
    (cross_binding : ∀ k a, CodeBinding
      (generatedCodes (sourceChild a) (registry k)) (crossRows k a))
    (siblings : SiblingChecks siblingRows) (crosses : CrossChecks crossRows) :
    ForwardRules children7 M7 :=
  forwardRules_of_complete_sparse_rows siblingRows crossRows
    (completeCoverage_of_generated_bindings siblingRows crossRows sibling_binding cross_binding)
    siblings crosses

theorem hasTiling_of_generated_bindings_members_and_remaining205
    (siblingRows : Fin 128 → SparseRows) (crossRows : Fin 408 → Fin 128 → SparseRows)
    (sibling_binding : ∀ a, CodeBinding (siblingGeneratedCodes a) (siblingRows a))
    (cross_binding : ∀ k a, CodeBinding
      (generatedCodes (sourceChild a) (registry k)) (crossRows k a))
    (siblings : SiblingChecks siblingRows) (crosses : CrossChecks crossRows)
    (hrest : ∀ i ∈ Existence.ProfileBridge7.remainingAfterThree,
      IndexedData7.geometry.LegalContact (catalogRow i)) : HasTiling T7 :=
  hasTiling_of_forward_and_remaining205
    (forwardRules_of_generated_bindings_and_members siblingRows crossRows
      sibling_binding cross_binding siblings crosses) hrest

theorem generated_cross_block {k : Fin 408} {a : Fin 128} {rows : SparseRows}
    (binding : CodeBinding (generatedCodes (sourceChild a) (registry k)) rows)
    (checked : sparseMemberChecks 7 registryFields (childFields a) (crossFields k) rows = true) :
    ∀ b ∈ children7,
      CellContact (sourceChild a) (compose (dilatePose (registry k)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry k)) b) ∈ M7 := by
  intro b hb hc
  obtain ⟨n, rfl⟩ := children7_covered hb
  obtain ⟨j, hj⟩ := codeBinding_member binding
    (cellContact_sourceChild_generated (sourceChild a) (registry k) n hc)
  rw [sparse_row_exact checked hj]
  exact registry_mem j

theorem zero_binding : CodeBinding (generatedCodes (sourceChild 0) (registry 0)) zeroRows := by
  rw [CodeBinding, zero_generated_exact]
  decide +kernel

theorem one_binding : CodeBinding (generatedCodes (sourceChild 63) (registry 0)) oneRows := by
  rw [CodeBinding, one_generated_exact]
  decide +kernel

theorem eight_binding : CodeBinding (generatedCodes (sourceChild 11) (registry 2)) eightRows := by
  rw [CodeBinding, eight_generated_exact]
  decide +kernel

/-- Three complete blocks via the sparse generator and retained rows only;
this proof never checks all128 source roles inside an individual block. -/
theorem three_generated_blocks (k : Fin 408) (a : Fin 128)
    (h : (k = 0 ∧ a = 0) ∨ (k = 0 ∧ a = 63) ∨ (k = 2 ∧ a = 11)) :
    ∀ b ∈ children7,
      CellContact (sourceChild a) (compose (dilatePose (registry k)) b) →
      normalize (sourceChild a) (compose (dilatePose (registry k)) b) ∈ M7 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact generated_cross_block zero_binding zero_checked
  · exact generated_cross_block one_binding one_checked
  · exact generated_cross_block eight_binding eight_checked

#print axioms cellContact_sibling_generated
#print axioms completeCoverage_of_generated_bindings
#print axioms forwardRules_of_generated_bindings_and_members
#print axioms hasTiling_of_generated_bindings_members_and_remaining205
#print axioms three_generated_blocks
end SparseMonotiles.CarrierHierarchy.T7GeneratedForwardAssembly
