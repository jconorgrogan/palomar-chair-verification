module

public import SpectreGeometry.ReverseLocalStarInclusion

@[expose] public section


/-! Transfer actual local-star neighborhoods into placed cluster carriers. -/
namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseExistence ReverseFinitePL

/-- A nonzero dilation followed by translation carries an origin neighborhood
into an ambient neighborhood of its translated center. The superset can be a
single carrier or a finite union of incident carriers. -/
theorem translated_scaled_origin_interior
    (center : RealPoint) (scale : ℝ) (hscale : scale ≠ 0)
    {s t : Set RealPoint} (hzero : (0 : RealPoint) ∈ interior s)
    (hsub : (fun q : RealPoint => center + scale • q) '' s ⊆ t) :
    center ∈ interior t := by
  let H : RealPoint ≃ₜ RealPoint :=
    (scalarHomeomorph scale hscale).trans (axialMotionHomeomorph 0 center)
  have hH0 : H 0 = center := by
    change center + scale • (0 : RealPoint) = center
    simp
  have hsub' : H '' s ⊆ t := by
    change (fun q : RealPoint => center + scale • q) '' s ⊆ t
    exact hsub
  have hi : H 0 ∈ H '' interior s := ⟨0,hzero,rfl⟩
  rw [H.image_interior] at hi
  have hout := interior_mono hsub' hi
  simpa only [hH0] using hout

/-- The actual incident-star origin neighborhood gives a genuine ambient
neighborhood of the placed target vertex in its closed cluster carrier. -/
theorem localStar_origin_interior_placedClusterCarrier
    (k : Fin 9) (r : Fin 6) (v : Nat) (anchor : RealPoint)
    (hids : ∀ i ∈ incidentIds k v, i < (meshTriangles k).length)
    (hzero : (0 : RealPoint) ∈ interior (starBody (localStar (k,r) v))) :
    anchor + gridRotation r ((1/6 : ℝ) • integerPoint (targetVertex k v)) ∈
      interior (placedClusterCarrier r anchor (SpectreClusters.ReverseExistence.clusterOfMark k)) := by
  exact translated_scaled_origin_interior _ (1/6) (by norm_num) hzero
    (localStar_image_subset_placedClusterCarrier k r v anchor hids)

end
end SpectreGeometry.ReverseLocalStarOccurrences
