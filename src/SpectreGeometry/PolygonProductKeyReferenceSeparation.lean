module

public import SpectreGeometry.PolygonProductKeyReferenceRigidity

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open SparseMonotiles
noncomputable section

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem integer_fingerprints_separate_labels : ∀ (i j : Fin 2)
    (a b : Option (Fin 3 → Bool)),
    integerDistanceFingerprint (vertices i) a = integerDistanceFingerprint (vertices j) b → i = j := by
  decide +kernel

theorem fingerprint_transport_between {X : Type*} [MetricSpace X]
    (s t : Finset X) (g : X ≃ᵢ X) (hg : g '' (s : Set X) = t) (x : X) :
    squaredDistanceFingerprint t (g x) = squaredDistanceFingerprint s x := by
  classical
  have hmaps : ∀ y ∈ s, g y ∈ t := by
    intro y hy
    have : g y ∈ g '' (s : Set X) := ⟨y, hy, rfl⟩
    rwa [hg] at this
  have hsurj : (s : Set X).SurjOn g (t : Set X) := by
    intro y hy
    have : y ∈ g '' (s : Set X) := by rwa [hg]
    exact this
  symm
  unfold squaredDistanceFingerprint
  exact Finset.sum_nbij g hmaps g.injective.injOn hsurj
    (fun y _ => by rw [g.dist_eq])

theorem reference_label_of_isometric_image (i j : Fin 2) (g : Point 4 ≃ᵢ Point 4)
    (hg : g '' referenceSolid i = referenceSolid j) : i = j := by
  classical
  let s := scaledIntegerVertexFinset (vertices i) referenceDenominator
  let t := scaledIntegerVertexFinset (vertices j) referenceDenominator
  have hext : g '' (s : Set (Point 4)) = t := by
    change g '' (scaledIntegerVertexFinset (vertices i) referenceDenominator : Set (Point 4)) =
      (scaledIntegerVertexFinset (vertices j) referenceDenominator : Set (Point 4))
    rw [←reference_extremePoints i, ←reference_extremePoints j,
      isometryEquiv_image_extremePoints, hg]
  let a := scaledIntegerVertex (vertices i) referenceDenominator none
  have ha : a ∈ s := by simp [a, s, scaledIntegerVertexFinset]
  have hga : g a ∈ t := by
    change g a ∈ (t : Set (Point 4))
    rw [←hext]
    exact ⟨a, ha, rfl⟩
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hga
  have heq := fingerprint_transport_between s t g hext a
  rw [←hb] at heq
  have hd : referenceDenominator ≠ 0 := by norm_num [referenceDenominator]
  have hvi := integerVertex_injective_of_fingerprint (vertices i) (fingerprints_injective i)
  have hvj := integerVertex_injective_of_fingerprint (vertices j) (fingerprints_injective j)
  change squaredDistanceFingerprint (scaledIntegerVertexFinset (vertices j) referenceDenominator)
    (scaledIntegerVertex (vertices j) referenceDenominator b) =
    squaredDistanceFingerprint (scaledIntegerVertexFinset (vertices i) referenceDenominator)
    (scaledIntegerVertex (vertices i) referenceDenominator none) at heq
  rw [scaledIntegerVertex_fingerprint _ hd hvj,
    scaledIntegerVertex_fingerprint _ hd hvi] at heq
  have hden : (referenceDenominator : ℝ)^2 ≠ 0 := by norm_num [referenceDenominator]
  have hInt : integerDistanceFingerprint (vertices j) b =
      integerDistanceFingerprint (vertices i) none := by
    exact_mod_cast (div_left_inj' hden).mp heq
  exact (integer_fingerprints_separate_labels j i b none hInt).symm

end
end SpectreGeometry.ProductKeyReference
