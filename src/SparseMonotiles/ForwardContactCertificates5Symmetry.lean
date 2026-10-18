module

public import SparseMonotiles.ForwardContactCertificates5Base
public import SparseMonotiles.CoarseContactCertificates5SymmetryTransport
public import SparseMonotiles.CarrierHierarchyForwardAssembly

@[expose] public section

namespace SparseMonotiles.CarrierHierarchy.ForwardContactCertificates5
open Contact CoarseContactCertificates5 CoarseContactCertificates5Symmetry

/-- Every original ordered child pair is transported to its checked representative.
The same coordinate conjugation transports the complete parent registry. -/
theorem forwardRules_of_representatives
    (siblings : ∀ a, SiblingImplication a)
    (crosses : ∀ a k, CrossImplication a k) : ForwardRules C L := by
  constructor
  · intro a ha b hb hne hc
    obtain ⟨i, rfl⟩ := child_indexed ha
    obtain ⟨j, rfl⟩ := child_indexed hb
    let s := (pairReduction i j).1
    let rep := (pairReduction i j).2
    have hpair := pair_reduction i j
    have hai : conjugatePose (symmetry s) (child i) = child (representativePair rep).1 :=
      (child_action s i).trans (congrArg child hpair.1)
    have hbj : conjugatePose (symmetry s) (child j) = child (representativePair rep).2 :=
      (child_action s j).trans (congrArg child hpair.2)
    have hne' : child (representativePair rep).1 ≠ child (representativePair rep).2 := by
      intro he
      rw [← hai, ← hbj] at he
      have hh := congrArg (conjugatePose (symmetry s).symm) he
      simp only [conjugatePose_symm_cancel] at hh
      exact hne hh
    have hc' := hc.conjugate (symmetry s)
    rw [hai, hbj] at hc'
    have hmem := siblings rep hne' hc'
    apply (language_iff s _).mp
    rw [conjugatePose_normalize, hai, hbj]
    exact hmem
  · intro k hk a ha b hb hc
    obtain ⟨i, rfl⟩ := child_indexed ha
    obtain ⟨j, rfl⟩ := child_indexed hb
    let s := (pairReduction i j).1
    let rep := (pairReduction i j).2
    have hpair := pair_reduction i j
    have hai : conjugatePose (symmetry s) (child i) = child (representativePair rep).1 :=
      (child_action s i).trans (congrArg child hpair.1)
    have hbj : conjugatePose (symmetry s) (child j) = child (representativePair rep).2 :=
      (child_action s j).trans (congrArg child hpair.2)
    obtain ⟨l, hl⟩ := registry_complete (registry_closed s k hk)
    change registry l = conjugatePose (symmetry s) k at hl
    have hright : conjugatePose (symmetry s) (compose (dilatePose k) (child j)) =
        compose (dilatePose (registry l)) (child (representativePair rep).2) := by
      rw [conjugatePose_compose, ← dilatePose_conjugate, ← hl, hbj]
    have hc' := hc.conjugate (symmetry s)
    rw [hai, hright] at hc'
    have hmem := crosses rep l hc'
    apply (language_iff s _).mp
    rw [conjugatePose_normalize, hai, hright]
    exact hmem

#print axioms forwardRules_of_representatives
end SparseMonotiles.CarrierHierarchy.ForwardContactCertificates5
