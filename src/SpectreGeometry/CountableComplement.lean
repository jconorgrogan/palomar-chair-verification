module

/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section


/-! Exact proof adaptation of the two countable-complement results from
Mathlib/Analysis/Normed/Module/Connected.lean, using only its required cached
imports rather than the unrelated contractibility closure. Source SHA256:
74d7e723415f4f3e0d5a577a8b881c60d5c4d3267dba1310121c134820bed135.
No cached theorem or custom axiom is substituted for a proof. -/
namespace SpectreGeometry
open Set Metric
open scoped Convex ENNReal
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem countable_compl_pathConnected
    (h : 1 < Module.rank ℝ E) {s : Set E} (hs : s.Countable) :
    IsPathConnected sᶜ := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `a ∈ sᶜ`. We have to show that any
  -- `b ∈ sᶜ` can be joined to `a`.
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := (hs.dense_compl ℝ).nonempty
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  /- Assume `b ≠ a`. Write `a = c - x` and `b = c + x` for some nonzero `x`. Choose `y` which
  is linearly independent from `x`. Then the segments joining `a = c - x` to `c + ty` are pairwise
  disjoint for varying `t` (except for the endpoint `a`) so only countably many of them can
  intersect `s`. In the same way, there are countably many `t`s for which the segment
  from `b = c + x` to `c + ty` intersects `s`. Choosing `t` outside of these countable exceptions,
  one gets a path in the complement of `s` from `a` to `z = c + ty` and then to `b`.
  -/
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [c, x]
    module
  have Ib : c + x = b := by
    simp only [c, x]
    module
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  obtain ⟨t, ht⟩ : Set.Nonempty ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty}
      ∪ {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty})ᶜ := ((A.union B).dense_compl ℝ).nonempty
  let z := c + t • y
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty]
    at ht
  have JA : JoinedIn sᶜ a z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert! ht.2
    exact Ia.symm
  have JB : JoinedIn sᶜ b z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    convert! ht.1
    exact Ib.symm
  exact JA.trans JB.symm

/-- In a real vector space of dimension `> 1`, the complement of any countable set is
connected. -/
theorem countable_compl_connected (h : 1 < Module.rank ℝ E) {s : Set E}
    (hs : s.Countable) : IsConnected sᶜ :=
  (countable_compl_pathConnected h hs).isConnected

end SpectreGeometry
