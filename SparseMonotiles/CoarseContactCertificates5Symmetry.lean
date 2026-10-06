module

public import Mathlib.Tactic.FinCases
public import SparseMonotiles.CoarseContactCertificates5SymmetryCheck0
public import SparseMonotiles.CoarseContactCertificates5SymmetryCheck1
public import SparseMonotiles.CoarseContactCertificates5SymmetryCheck2
public import SparseMonotiles.CoarseContactCertificates5SymmetryCheck3

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
open Contact CoarseContactCertificates5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem child_action (s : Fin 4) (i : Fin 32) : conjugate s (child i) = child (childAction s i) := by
  fin_cases s
  · exact child_action0 i
  · exact child_action1 i
  · exact child_action2 i
  · exact child_action3 i
theorem registry_action (s : Fin 4) (i : Fin 284) : conjugate s (registry i) = registry (registryAction s i) := by
  fin_cases s
  · exact registry_action0 i
  · exact registry_action1 i
  · exact registry_action2 i
  · exact registry_action3 i
theorem child_indexed {q : Pose 5} (h : q ∈ C) : ∃ i, child i = q := by
  change q ∈ childList at h
  obtain ⟨i, _, he⟩ := List.mem_map.mp h
  exact ⟨i, he⟩
theorem child_closed (s : Fin 4) : ∀ q ∈ C, conjugate s q ∈ C := by
  intro q hq
  obtain ⟨i, rfl⟩ := child_indexed hq
  rw [child_action]
  change child (childAction s i) ∈ childList
  exact List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
theorem registry_closed (s : Fin 4) : ∀ q ∈ L, conjugate s q ∈ L := by
  intro q hq
  obtain ⟨i, rfl⟩ := registry_complete hq
  rw [registry_action]
  exact registry_mem _
theorem pair_reduction_checked : coarseAllB (fun a => coarseAllB (fun b =>
    decide (childAction (pairReduction a b).1 a = (representativePair (pairReduction a b).2).1) &&
    decide (childAction (pairReduction a b).1 b = (representativePair (pairReduction a b).2).2))) = true := by decide +kernel
theorem pair_reduction (a b : Fin 32) :
    childAction (pairReduction a b).1 a = (representativePair (pairReduction a b).2).1 ∧
    childAction (pairReduction a b).1 b = (representativePair (pairReduction a b).2).2 := by
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using
    coarseAllB_sound (coarseAllB_sound pair_reduction_checked a) b
#print axioms child_closed
#print axioms registry_closed
#print axioms pair_reduction
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
