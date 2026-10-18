module

public import PrimeFacetClosure.StarHolonomy
public import PhysicalRegistration.NativeGraphCoefficients

@[expose] public section

/-!
# From literal native graph coefficients to odd star-gauged transport

The graph here is the actual finite graph of native free-orbit sites, using
complete tangent-axis, reversed-normal, and site-center transport. Its
coefficients and orientation character are the geometric definitions from
`NativeGraphCoefficients`, rather than abstract supplied component labels.

The only extra input is `StarGauge`'s local geometric generator-edge
classification. This file does not assert that that classification has yet
been established for the concrete prime chair language. The conclusions
identify the product along an actual graph walk. Identifying it with an
independently recovered candidate placement additionally requires the
complete-frame uniqueness/transport bridge.
-/
namespace PhysicalRegistration.NativeChair
noncomputable section
open RegisteredPrime
open RegisteredPrime.PrimeFacetClosure
open RegisteredPrime.PrimeFacetClosure.StarHolonomy

/-- On the literal full-site contact graph, opposite compiler coefficients
force an odd finite graph walk, not merely unspecified connectedness. -/
theorem opposite_coefficients_odd_walk
    {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m}
    (ha : (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u) :
    ∃ w : (contactGraph A hA).Walk u v, w.length % 2 = 1 := by
  have hh := (graphCoefficients_opposite_iff (contactGraph A hA) u v).mp ha
  obtain ⟨w⟩ := hh.1
  exact ⟨w, StarGauge.odd_length_of_opposite orientation
    (fun h => contactGraph_edge_orientation A hA h) w (orientation_nonzero u) hh.2⟩

/-- Every path joining native sites with opposite graph coefficients is odd;
there is no ambiguity from a choice of connecting path. -/
theorem opposite_coefficients_every_walk_odd
    {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m}
    (ha : (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u)
    (w : (contactGraph A hA).Walk u v) : w.length % 2 = 1 := by
  have hh := (graphCoefficients_opposite_iff (contactGraph A hA) u v).mp ha
  exact StarGauge.odd_length_of_opposite orientation
    (fun h => contactGraph_edge_orientation A hA h) w (orientation_nonzero u) hh.2

/-- Literal native component coefficients, the proved orientation character,
and local edge classification give the exact odd full-frame path transport.
No graph-closure or path-product conclusion is assumed. -/
theorem opposite_coefficients_star_transport
    {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {F : RegisteredFrame (m + 1)} (S : StarGauge (contactGraph A hA) F)
    {u v : Site m}
    (ha : (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u)
    (ht : S.outer u = S.outer v) :
    ∃ w : (contactGraph A hA).Walk u v, w.length % 2 = 1 ∧
      S.label v = F.perm (S.label u) ∧
      S.transport w = ((S.gauge u).comp (bridge F (S.label u))).comp (S.gauge v).inv := by
  have hh := (graphCoefficients_opposite_iff (contactGraph A hA) u v).mp ha
  exact S.reachable_opposite_same_type orientation
    (fun h => contactGraph_edge_orientation A hA h) hh.1 (orientation_nonzero u) hh.2 ht

/-- Inner/outer pairing instead has identity star-gauged transport. The odd
length is accounted for by the unmatched hole-star edge. -/
theorem opposite_coefficients_different_type_transport
    {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {F : RegisteredFrame (m + 1)} (S : StarGauge (contactGraph A hA) F)
    {u v : Site m}
    (ha : (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u)
    (ht : S.outer u ≠ S.outer v) :
    ∃ w : (contactGraph A hA).Walk u v, w.length % 2 = 1 ∧
      S.label v = S.label u ∧
      S.transport w = (S.gauge u).comp (S.gauge v).inv := by
  obtain ⟨w, hw⟩ := opposite_coefficients_odd_walk A hA ha
  have hh := S.odd_different_type w ht hw
  refine ⟨w, hw, hh.1, ?_⟩
  simpa only [frame_comp_one] using ungauge _ _ _ _ hh.2

#print axioms opposite_coefficients_odd_walk
#print axioms opposite_coefficients_every_walk_odd
#print axioms opposite_coefficients_star_transport
#print axioms opposite_coefficients_different_type_transport
end
end PhysicalRegistration.NativeChair
