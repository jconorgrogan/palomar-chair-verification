module

public import Mathlib.Analysis.Normed.Module.Connected
public import SpectreGeometry.DenseConnectedCompleteness
public import SpectreGeometry.EuclideanCarrier

@[expose] public section


/-! The official countable-complement theorem specializes the dense-connected
completeness lemma to the actual Euclidean plane. -/
namespace SpectreGeometry
open Set

theorem closed_plane_eq_univ_of_countable_frontier
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : IsClosed S)
    (hne : (interior S).Nonempty) (hfrontier : (frontier S).Countable) : S = univ := by
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank]
    simp
  exact closed_eq_univ_of_dense_preconnected_avoid_frontier S (frontier S)ᶜ hS hne
    (hfrontier.dense_compl ℝ) (hfrontier.isConnected_compl_of_one_lt_rank hdim).isPreconnected
    disjoint_compl_left

end SpectreGeometry
