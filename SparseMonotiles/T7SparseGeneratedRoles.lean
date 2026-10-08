module
public import SparseMonotiles.SparseGeneratedRoles
public import SparseMonotiles.T7SparseForwardBase
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7SparseGenerator
open Contact Existence.Catalog7World T7SparseForwardBlock

/-- Actual original source-role codes, excluding outer 127 and checking the
central 127 separately. No `Fin 128` enumeration occurs in this generator. -/
def generatedCodes (root parent : Pose 7) : List ℕ :=
  ((generatedOuterBits root parent).map bitCode).filter (fun n => decide (n < 127)) ++
    if centralBudgetB root parent then [127] else []

/-- Every original contacting source role is produced by the sparse generator. -/
theorem cellContact_sourceChild_generated (root parent : Pose 7) (n : Fin 128)
    (hc : CellContact root (compose (dilatePose parent) (sourceChild n))) :
    n.val ∈ generatedCodes root parent := by
  by_cases hn : n.val = 127
  · have hcentral : sourceChild n = centralPose 7 := by simp [sourceChild, hn]
    rw [hcentral] at hc
    simp [generatedCodes, hn, cellContact_refinedCentral_budget root parent hc]
  · rw [sourceChild_outer n hn] at hc
    have ha := cellContact_refinedOuter_generated root parent (maskBits n.val)
      (Catalog7.childPerm (maskBits n.val)) hc
    apply List.mem_append_left
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using (show n.val < 127 by omega)⟩
    exact List.mem_map.mpr ⟨maskBits n.val, ha, code_maskBits n⟩

/-- A generated-role-only block proof covers the complete original child table. -/
theorem generated_block_assemble (root parent : Pose 7)
    (hretained : ∀ n : Fin 128, n.val ∈ generatedCodes root parent →
      CellContact root (compose (dilatePose parent) (sourceChild n)) →
      normalize root (compose (dilatePose parent) (sourceChild n)) ∈ M7) :
    ∀ b ∈ children7, CellContact root (compose (dilatePose parent) b) →
      normalize root (compose (dilatePose parent) b) ∈ M7 := by
  intro b hb hc
  obtain ⟨n, rfl⟩ := children7_covered hb
  exact hretained n (cellContact_sourceChild_generated root parent n hc) hc

#print axioms cellContact_sourceChild_generated
#print axioms generated_block_assemble
end SparseMonotiles.CarrierHierarchy.T7SparseGenerator
