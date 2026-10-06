module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Sequences
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Common

@[expose] public section

/-! # Compact congruent solids cannot be properly nested
This avoids an extra volume or base-plane premise once actual solid inclusion
has been derived from the closed side faces.
-/
namespace SparseMonotiles
open Set Filter
open scoped Topology

theorem compact_isometry_image_eq_of_subset {E : Type*} [MetricSpace E]
    {K : Set E} (hK : IsCompact K) (e : E ≃ᵢ E) (hsub : e '' K ⊆ K) : e '' K=K := by
  classical
  apply Subset.antisymm hsub
  intro x hx
  by_contra hxnot
  have hopen := (hK.image e.continuous).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen x hxnot
  let u : ℕ → E := fun n => (e : E → E)^[n] x
  have hu (n : ℕ) : u n ∈ K := by
    induction n with
    | zero => exact hx
    | succ n ih =>
        change (e : E → E)^[n+1] x ∈ K
        rw [Function.iterate_succ_apply']
        exact hsub ⟨u n,ih,rfl⟩
  have hiso (n : ℕ) : Isometry ((e : E → E)^[n]) := by
    induction n with
    | zero => exact isometry_id
    | succ n ih =>
        rw [Function.iterate_succ']
        exact e.isometry.comp ih
  have hgap {n m : ℕ} (hnm : n < m) : ε ≤ dist (u n) (u m) := by
    have hmn : m=n+(m-n) := by omega
    have hmpos : 0 < m-n := by omega
    have hmem : u (m-n) ∈ e '' K := by
      obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
      rw [hr]
      refine ⟨u r,hu r,?_⟩
      exact (Function.iterate_succ_apply' (e : E → E) r x).symm
    have hdist : dist (u n) (u m)=dist x (u (m-n)) := by
      change dist ((e : E → E)^[n] x) ((e : E → E)^[m] x)=_
      conv_lhs =>
        arg 2
        rw [hmn,Function.iterate_add_apply]
      exact (hiso n).dist_eq _ _
    rw [hdist]
    by_contra hlt
    have hballmem : u (m-n) ∈ Metric.ball x ε := by
      rw [Metric.mem_ball,dist_comm]
      exact lt_of_not_ge hlt
    exact hball hballmem hmem
  obtain ⟨z,hz,φ,hφ,hlim⟩ := hK.tendsto_subseq hu
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq ε hε
  have hnear := hN N (le_refl N) (N+1) (by omega)
  have hfar := hgap (hφ (Nat.lt_succ_self N))
  exact not_lt_of_ge hfar hnear

/-- Two images of one compact model are equal as soon as one contains the other. -/
theorem compact_congruent_images_eq_of_subset {E : Type*} [MetricSpace E]
    {K : Set E} (hK : IsCompact K) (e f : E ≃ᵢ E)
    (hsub : e '' K ⊆ f '' K) : e '' K=f '' K := by
  let t : E ≃ᵢ E := e.trans f.symm
  have ht : t '' K ⊆ K := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hsub ⟨x,hx,rfl⟩
    change f.symm (e x) ∈ K
    rw [← he,f.symm_apply_apply]
    exact hy
  have heq := compact_isometry_image_eq_of_subset hK t ht
  apply Subset.antisymm hsub
  rintro _ ⟨x,hx,rfl⟩
  rw [← heq] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  refine ⟨y,hy,?_⟩
  change e y=f (f.symm (e y))
  exact (f.apply_symm_apply _).symm

#print axioms compact_isometry_image_eq_of_subset
#print axioms compact_congruent_images_eq_of_subset
end SparseMonotiles
