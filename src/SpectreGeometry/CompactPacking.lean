module

public import SpectreGeometry.EuclideanCarrier
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.LocallyFinite

@[expose] public section


/-! Local finiteness for arbitrary isometric packings of any compact
Euclidean body with nonempty interior. This generalizes the already checked
retained-ball argument without assuming an aperiodic tile or a tiling. -/
namespace SpectreGeometry.CompactPacking
noncomputable section
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem placed_ball {d : ℕ} (T : Set (Space d)) (c : Space d) (r : ℝ)
    (hball : Metric.ball c r ⊆ interior T) (f : Space d ≃ᵢ Space d) :
    Metric.ball (f c) r ⊆ interior (f '' T) := by
  rw [←f.image_ball]
  exact (Set.image_mono hball).trans (f.toHomeomorph.isOpenMap.image_interior_subset T)

theorem centers_separated {d : ℕ} {ι : Type*} (T : Set (Space d)) (c : Space d) (r : ℝ)
    (hr : 0 < r) (hball : Metric.ball c r ⊆ interior T)
    (f : ι → Space d ≃ᵢ Space d)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (f i '' T)) (interior (f j '' T))) :
    Pairwise fun i j => r ≤ dist (f i c) (f j c) := by
  intro i j hij
  by_contra! hdist
  have hi : f i c ∈ interior (f i '' T) := placed_ball T c r hball (f i) (Metric.mem_ball_self hr)
  have hj : f i c ∈ interior (f j '' T) := placed_ball T c r hball (f j) hdist
  exact Set.disjoint_left.mp (hdisjoint hij) hi hj

theorem finite_centers_in_compact {d : ℕ} {ι : Type*} (T : Set (Space d))
    (c : Space d) (r : ℝ) (hr : 0 < r) (hball : Metric.ball c r ⊆ interior T)
    (f : ι → Space d ≃ᵢ Space d)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (f i '' T)) (interior (f j '' T)))
    (K : Set (Space d)) (hK : IsCompact K) : {i | f i c ∈ K}.Finite := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := discreteTopology_bot ι
  have hf := Metric.isClosedEmbedding_of_pairwise_le_dist hr (centers_separated T c r hr hball f hdisjoint)
  exact (hf.isCompact_preimage hK).finite_of_discrete

theorem finite_inter_compact {d : ℕ} {ι : Type*} (T : Set (Space d))
    (hT : IsCompact T) (hI : (interior T).Nonempty)
    (f : ι → Space d ≃ᵢ Space d)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (f i '' T)) (interior (f j '' T)))
    (K : Set (Space d)) (hK : IsCompact K) : {i | ((f i '' T) ∩ K).Nonempty}.Finite := by
  obtain ⟨c,hc⟩ := hI
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  obtain ⟨R,hR⟩ := hT.isBounded.subset_closedBall c
  obtain ⟨S,hS⟩ := hK.isBounded.subset_closedBall (0 : Space d)
  have hf := finite_centers_in_compact T c r hr hball f hdisjoint
    (Metric.closedBall (0 : Space d) (R+S)) (isCompact_closedBall _ _)
  apply hf.subset
  intro i hi
  obtain ⟨x,⟨z,hz,rfl⟩,hxK⟩ := hi
  change dist (f i c) 0 ≤ R+S
  calc
    dist (f i c) 0 ≤ dist (f i c) (f i z) + dist (f i z) 0 := dist_triangle _ _ _
    _ = dist c z + dist (f i z) 0 := by rw [(f i).dist_eq]
    _ ≤ R+S := add_le_add (by simpa only [Metric.mem_closedBall,dist_comm] using hR hz) (hS hxK)

theorem locallyFinite {d : ℕ} {ι : Type*} (T : Set (Space d))
    (hT : IsCompact T) (hI : (interior T).Nonempty)
    (f : ι → Space d ≃ᵢ Space d)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (f i '' T)) (interior (f j '' T))) :
    LocallyFinite (fun i => f i '' T) := by
  intro x
  exact ⟨Metric.closedBall x 1,Metric.closedBall_mem_nhds x (by norm_num),
    finite_inter_compact T hT hI f hdisjoint _ (isCompact_closedBall x 1)⟩

theorem polygon_packing_locallyFinite {ι : Type*}
    (f : ι → Space 2 ≃ᵢ Space 2)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody))) :
    LocallyFinite (fun i => f i '' euclideanBody) :=
  locallyFinite euclideanBody euclideanBody_compact euclideanBody_interior_nonempty f hdisjoint

end
end SpectreGeometry.CompactPacking
