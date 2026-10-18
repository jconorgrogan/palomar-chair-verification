module

public import ProductClosure.RetainedBall
public import ProductClosure.IsometryTransport
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.LocallyFinite

@[expose] public section

/-!
# Local finiteness of actual congruent native-chair packings

The index type and ambient isometric placements are arbitrary. Pairwise
interior-disjointness, the proved retained ball, and compactness of the
actual body imply finite compact incidence and local finiteness. No
local-finiteness or diameter certificate is assumed.
-/

namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {C : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell C)]

/-- Every isometric copy retains the same literal open ball. -/
theorem placedBody_retained_ball {J : ℕ} [NeZero m]
    (a : Coefficients C J) (f : Space m ≃ᵢ Space m) :
    Metric.ball (f (referencePoint C)) (1 / 4) ⊆ interior (placedBody a f) := by
  rw [← f.image_ball]
  exact (Set.image_mono (referencePoint_ball_subset_interior_body a)).trans
    (f.toHomeomorph.isOpenMap.image_interior_subset (body a))

/-- Disjoint placed interiors force uniformly separated retained-ball centers. -/
theorem placedBody_centers_separated {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j)))) :
    Pairwise fun i j => (1 / 4 : ℝ) ≤ dist (f i (referencePoint C)) (f j (referencePoint C)) := by
  intro i j hij
  by_contra! hdist
  have hi : f i (referencePoint C) ∈ interior (placedBody a (f i)) :=
    placedBody_retained_ball a (f i) (Metric.mem_ball_self (by norm_num))
  have hj : f i (referencePoint C) ∈ interior (placedBody a (f j)) :=
    placedBody_retained_ball a (f j) hdist
  exact Set.disjoint_left.mp (hdisjoint hij) hi hj

/-- Only finitely many retained-ball centers lie in any compact set. -/
theorem finite_placedBody_centers_mem_compact {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (K : Set (Space m)) (hK : IsCompact K) :
    {i | f i (referencePoint C) ∈ K}.Finite := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := discreteTopology_bot ι
  have hf := Metric.isClosedEmbedding_of_pairwise_le_dist
    (by norm_num : (0 : ℝ) < 1 / 4) (placedBody_centers_separated a f hdisjoint)
  exact (hf.isCompact_preimage hK).finite_of_discrete

/-- Any compact set meets only finitely many actual bodies in an arbitrary
interior-disjoint isometric packing. The body-radius bound is derived from
`body_isCompact`; it is not an extra geometric assumption. -/
theorem finite_placedBody_inter_compact {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (K : Set (Space m)) (hK : IsCompact K) :
    {i | (placedBody a (f i) ∩ K).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := (body_isCompact a).isBounded.subset_closedBall (referencePoint C)
  obtain ⟨S, hS⟩ := hK.isBounded.subset_closedBall (0 : Space m)
  have hfinite := finite_placedBody_centers_mem_compact a f hdisjoint
    (Metric.closedBall (0 : Space m) (R + S)) (isCompact_closedBall _ _)
  apply hfinite.subset
  intro i hi
  obtain ⟨x, hxbody, hxK⟩ := hi
  obtain ⟨z, hz, rfl⟩ := hxbody
  change dist (f i (referencePoint C)) 0 ≤ R + S
  calc
    dist (f i (referencePoint C)) 0 ≤
        dist (f i (referencePoint C)) (f i z) + dist (f i z) 0 := dist_triangle _ _ _
    _ = dist (referencePoint C) z + dist (f i z) 0 := by rw [(f i).dist_eq]
    _ ≤ R + S := add_le_add (by simpa only [Metric.mem_closedBall, dist_comm] using hR hz)
      (hS hxK)

/-- Arbitrary interior-disjoint isometric placements of the literal native
body form a genuinely locally finite family. -/
theorem placedBody_locallyFinite {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j)))) :
    LocallyFinite (fun i => placedBody a (f i)) := by
  intro x
  exact ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x (by norm_num),
    finite_placedBody_inter_compact a f hdisjoint _ (isCompact_closedBall x 1)⟩

/-- In particular every fixed copy has only finitely many touching neighbors,
including lower-dimensional contacts. -/
theorem finite_placedBody_neighbors {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j)))) (i : ι) :
    {j | (placedBody a (f j) ∩ placedBody a (f i)).Nonempty}.Finite :=
  finite_placedBody_inter_compact a f hdisjoint _
    ((body_isCompact a).image (f i).continuous)

end
end ProductClosure.NativeCompiler
