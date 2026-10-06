module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable

@[expose] public section

/-!
# Affine exceptional-set avoidance

The geometric input is independent of the tile model.  We work in a finite-dimensional
real normed vector space, so the result applies in an intrinsic Euclidean chart of a facet.
The dimension hypothesis is stated without truncated subtraction: each forbidden affine
subspace has direction dimension plus two at most the dimension of the ambient space.
-/

namespace SparseMonotiles

open Set AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A proper affine subspace has dense complement. -/
theorem affineSubspace_dense_compl (L : AffineSubspace ℝ E) (hL : L ≠ ⊤) :
    Dense (L : Set E)ᶜ := by
  rw [← interior_eq_empty_iff_dense_compl]
  apply Set.not_nonempty_iff_eq_empty.mp
  intro h
  apply hL
  apply top_unique
  calc
    (⊤ : AffineSubspace ℝ E) = affineSpan ℝ (interior (L : Set E)) :=
      (isOpen_interior.affineSpan_eq_top h).symm
    _ ≤ L := affineSpan_le.mpr interior_subset

/-- Even a countable union of proper affine subspaces has dense complement. -/
theorem affineSubspaces_dense_avoid [FiniteDimensional ℝ E] {ι : Type*} [Countable ι]
    (L : ι → AffineSubspace ℝ E) (hL : ∀ i, L i ≠ ⊤) :
    Dense {x : E | ∀ i, x ∉ L i} := by
  have hd : Dense (⋂ i, (L i : Set E)ᶜ) :=
    dense_iInter_of_isOpen (fun i => (L i).closed_of_finiteDimensional.isOpen_compl)
      (fun i => affineSubspace_dense_compl (L i) (hL i))
  convert hd using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, SetLike.mem_coe]

/-- Adjoining one point to an affine subspace of codimension at least two
still gives a proper affine subspace. -/
theorem affineSpan_insert_ne_top (L : AffineSubspace ℝ E) (p : E)
    (hL : Module.finrank ℝ L.direction + 2 ≤ Module.finrank ℝ E) :
    affineSpan ℝ (insert p (L : Set E)) ≠ ⊤ := by
  intro h
  have hdim := finrank_vectorSpan_insert_le L p
  rw [← direction_affineSpan, h, direction_top, finrank_top] at hdim
  omega

/-- If an endpoint is outside an affine subspace and the other endpoint avoids its
span with the first endpoint, then the whole closed segment avoids that subspace. -/
theorem segment_avoids_affineSubspace (L : AffineSubspace ℝ E) {p w : E}
    (hp : p ∉ L) (hw : w ∉ affineSpan ℝ (insert p (L : Set E))) :
    segment ℝ p w ⊆ (L : Set E)ᶜ := by
  rw [segment_eq_image_lineMap]
  rintro x ⟨t, ht, rfl⟩ hx
  by_cases ht0 : t = 0
  · exact hp (by simpa [ht0] using hx)
  apply hw
  have hp' : p ∈ affineSpan ℝ (insert p (L : Set E)) :=
    subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hx' : AffineMap.lineMap p w t ∈ affineSpan ℝ (insert p (L : Set E)) :=
    subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ hx)
  have hw' := AffineMap.lineMap_mem t⁻¹ hp' hx'
  simpa [AffineMap.lineMap_lineMap_right, ht0] using hw'

/-- Under a codimension-two bound, every forbidden affine subspace is proper. -/
theorem affineSubspace_ne_top_of_codim_two (L : AffineSubspace ℝ E)
    (hL : Module.finrank ℝ L.direction + 2 ≤ Module.finrank ℝ E) : L ≠ ⊤ := by
  intro h
  rw [h, direction_top, finrank_top] at hL
  omega

/-- The complement of the exceptional affine subspaces is dense inside every open set.
The closure is the same as the closure of the original open set. -/
theorem closure_diff_affineSubspaces [FiniteDimensional ℝ E] {ι : Type*} [Countable ι]
    {O : Set E} (hO : IsOpen O) (L : ι → AffineSubspace ℝ E)
    (hL : ∀ i, L i ≠ ⊤) :
    closure (O \ ⋃ i, (L i : Set E)) = closure O := by
  apply le_antisymm
  · exact closure_mono Set.diff_subset
  · apply closure_minimal _ isClosed_closure
    have hset : O \ ⋃ i, (L i : Set E) = O ∩ {x : E | ∀ i, x ∉ L i} := by
      ext x
      simp only [Set.mem_diff, Set.mem_iUnion, not_exists, Set.mem_inter_iff,
        Set.mem_setOf_eq, SetLike.mem_coe]
    rw [hset]
    exact (affineSubspaces_dense_avoid L hL).open_subset_closure_inter hO

/-- Any two surviving points can be joined through a single intermediate point, with
both closed segments contained in the surviving part of the open convex set. -/
theorem affineAvoidance_exists_intermediate [FiniteDimensional ℝ E] {ι : Type*} [Countable ι]
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O)
    (L : ι → AffineSubspace ℝ E)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 2 ≤ Module.finrank ℝ E)
    {p q : E} (hp : p ∈ O \ ⋃ i, (L i : Set E))
    (hq : q ∈ O \ ⋃ i, (L i : Set E)) :
    ∃ w ∈ O, segment ℝ p w ⊆ O \ ⋃ i, (L i : Set E) ∧
      segment ℝ q w ⊆ O \ ⋃ i, (L i : Set E) := by
  let H : Bool × ι → AffineSubspace ℝ E := fun j =>
    affineSpan ℝ (insert (if j.1 then p else q) (L j.2 : Set E))
  have hd : Dense {w : E | ∀ j, w ∉ H j} :=
    affineSubspaces_dense_avoid H (fun j => affineSpan_insert_ne_top _ _ (hL j.2))
  obtain ⟨w, hwO, hw⟩ := hd.inter_open_nonempty O hO ⟨p, hp.1⟩
  refine ⟨w, hwO, ?_, ?_⟩
  · intro x hx
    refine ⟨hconv.segment_subset hp.1 hwO hx, ?_⟩
    simp only [Set.mem_diff, Set.mem_iUnion, not_exists, SetLike.mem_coe] at hp ⊢
    intro i
    exact segment_avoids_affineSubspace (L i) (hp.2 i)
      (by simpa [H] using hw (true, i)) hx
  · intro x hx
    refine ⟨hconv.segment_subset hq.1 hwO hx, ?_⟩
    simp only [Set.mem_diff, Set.mem_iUnion, not_exists, SetLike.mem_coe] at hq ⊢
    intro i
    exact segment_avoids_affineSubspace (L i) (hq.2 i)
      (by simpa [H] using hw (false, i)) hx

/-- Removing countably many affine subspaces of codimension at least two from a nonempty
open convex subset of a finite-dimensional real normed space leaves a path-connected set.
In particular this covers the finite exceptional families in the registration proof. -/
theorem isPathConnected_diff_affineSubspaces [FiniteDimensional ℝ E] {ι : Type*} [Countable ι]
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O) (hne : O.Nonempty)
    (L : ι → AffineSubspace ℝ E)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 2 ≤ Module.finrank ℝ E) :
    IsPathConnected (O \ ⋃ i, (L i : Set E)) := by
  have hd := affineSubspaces_dense_avoid L
    (fun i => affineSubspace_ne_top_of_codim_two (L i) (hL i))
  have hne' : (O \ ⋃ i, (L i : Set E)).Nonempty := by
    obtain ⟨x, hxO, hx⟩ := hd.inter_open_nonempty O hO hne
    refine ⟨x, hxO, ?_⟩
    change ∀ i, x ∉ L i at hx
    simpa only [Set.mem_iUnion, not_exists, SetLike.mem_coe] using hx
  rw [isPathConnected_iff]
  refine ⟨hne', ?_⟩
  intro p hp q hq
  obtain ⟨w, _, hpw, hqw⟩ := affineAvoidance_exists_intermediate hO hconv L hL hp hq
  exact (JoinedIn.of_segment_subset hpw).trans (JoinedIn.of_segment_subset hqw).symm

/-- Connectedness form of the exceptional-set avoidance theorem. -/
theorem isConnected_diff_affineSubspaces [FiniteDimensional ℝ E] {ι : Type*} [Countable ι]
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O) (hne : O.Nonempty)
    (L : ι → AffineSubspace ℝ E)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 2 ≤ Module.finrank ℝ E) :
    IsConnected (O \ ⋃ i, (L i : Set E)) :=
  (isPathConnected_diff_affineSubspaces hO hconv hne L hL).isConnected

/-- The combined generic-point lemma: deleting a countable (hence also finite) family
of codimension-at-least-two affine subspaces preserves path connectedness and relative
density in a nonempty open convex set. -/
theorem affineAvoidance_pathConnected_dense [FiniteDimensional ℝ E] {ι : Type*} [Countable ι]
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O) (hne : O.Nonempty)
    (L : ι → AffineSubspace ℝ E)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 2 ≤ Module.finrank ℝ E) :
    IsPathConnected (O \ ⋃ i, (L i : Set E)) ∧
      closure (O \ ⋃ i, (L i : Set E)) = closure O :=
  ⟨isPathConnected_diff_affineSubspaces hO hconv hne L hL,
    closure_diff_affineSubspaces hO L
      (fun i => affineSubspace_ne_top_of_codim_two (L i) (hL i))⟩

#print axioms affineSubspace_dense_compl
#print axioms affineSubspaces_dense_avoid
#print axioms affineSpan_insert_ne_top
#print axioms segment_avoids_affineSubspace
#print axioms closure_diff_affineSubspaces
#print axioms affineAvoidance_exists_intermediate
#print axioms isPathConnected_diff_affineSubspaces
#print axioms isConnected_diff_affineSubspaces
#print axioms affineAvoidance_pathConnected_dense

end SparseMonotiles
