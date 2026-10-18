module

public import LiteralPlanar.IsometryCoefficients

@[expose] public section


/-! Euclidean-space contact rigidity for the actual closed quintic graph arc.
It has no body-frontier or global-tiling premise. -/
namespace LiteralPlanar.Quintic
noncomputable section
open SpectreGeometry

def standardArc (ε : ℝ) : Set EPlane :=
  (fun t : ℝ => euclideanCoordinates (t,height ε t)) '' Set.Icc (-1/2 : ℝ) (1/2)

theorem standardArc_parameter_injective (ε : ℝ) :
    Function.Injective (fun t : ℝ => euclideanCoordinates (t,height ε t)) := by
  intro s t h
  exact congrArg Prod.fst (euclideanCoordinates.injective h)

theorem contact_parameter_mem_coincidence (ε : ℝ) (f : EPlane ≃ᵢ EPlane)
    (t : ℝ) (h : f (euclideanCoordinates (t,height ε t)) ∈ standardArc ε) :
    t ∈ coincidenceParameters ε (isometryCoefficients f) := by
  obtain ⟨u,hu,he⟩ := h
  have hc := isometry_coefficients_apply f (t,height ε t)
  rw [←he,Homeomorph.symm_apply_apply] at hc
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  simp only [Prod.fst,Prod.snd] at hx hy
  change height ε _ = _
  rw [←hx]
  exact hy

theorem improper_standardArc_contact_finite (ε : ℝ) (hε : ε ≠ 0)
    (f : EPlane ≃ᵢ EPlane)
    (hf : RealPoint.det (frameFirst f) (frameSecond f) = -1) :
    (f '' standardArc ε ∩ standardArc ε).Finite := by
  have hp := improper_coincidence_finite ε hε (isometryCoefficients f)
    ((isometry_coefficients_determinant f).trans hf)
  apply (hp.image (fun t : ℝ => f (euclideanCoordinates (t,height ε t)))).subset
  rintro x ⟨⟨y,⟨t,ht,rfl⟩,rfl⟩,hx⟩
  exact ⟨t,contact_parameter_mem_coincidence ε f t hx,rfl⟩

/-- Infinite contact of the two actual arc sets forces exact identity or
central reversal of the entire canonical polynomial graph. -/
theorem infinite_standardArc_contact_rigidity (ε : ℝ) (hε : ε ≠ 0)
    (f : EPlane ≃ᵢ EPlane) (h : (f '' standardArc ε ∩ standardArc ε).Infinite) :
    IsGraphSymmetry (isometryCoefficients f) := by
  apply infinite_coincidence_rigidity ε hε
  by_contra hf
  have hp : (coincidenceParameters ε (isometryCoefficients f)).Finite := by
    exact not_not.mp hf
  apply h
  apply (hp.image (fun t : ℝ => f (euclideanCoordinates (t,height ε t)))).subset
  rintro x ⟨⟨y,⟨t,ht,rfl⟩,rfl⟩,hx⟩
  exact ⟨t,contact_parameter_mem_coincidence ε f t hx,rfl⟩

theorem graph_symmetry_arc_image (ε : ℝ) (f : EPlane ≃ᵢ EPlane)
    (hf : IsGraphSymmetry (isometryCoefficients f)) :
    f '' standardArc ε = standardArc ε := by
  have happ (t : ℝ) := isometry_coefficients_apply f (t,height ε t)
  rcases hf with ⟨hb,hc,hu,hv,⟨ha,hd⟩ | ⟨ha,hd⟩⟩
  · have hid (t : ℝ) : f (euclideanCoordinates (t,height ε t)) =
        euclideanCoordinates (t,height ε t) := by
      apply euclideanCoordinates.symm.injective
      simpa only [ha,hb,hc,hd,hu,hv,zero_mul,one_mul,add_zero,zero_add,
        Homeomorph.symm_apply_apply] using happ t
    apply Set.Subset.antisymm
    · rintro x ⟨y,⟨t,ht,rfl⟩,rfl⟩
      rw [hid]
      exact ⟨t,ht,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      exact ⟨euclideanCoordinates (t,height ε t),⟨t,ht,rfl⟩,hid t⟩
  · have hneg (t : ℝ) : f (euclideanCoordinates (t,height ε t)) =
        euclideanCoordinates (-t,height ε (-t)) := by
      apply euclideanCoordinates.symm.injective
      simpa only [ha,hb,hc,hd,hu,hv,zero_mul,neg_one_mul,add_zero,zero_add,
        height_neg,Homeomorph.symm_apply_apply] using happ t
    apply Set.Subset.antisymm
    · rintro x ⟨y,⟨t,ht,rfl⟩,rfl⟩
      rw [hneg]
      exact ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      refine ⟨euclideanCoordinates (-t,height ε (-t)),
        ⟨-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,rfl⟩,?_⟩
      simpa only [neg_neg] using hneg (-t)

end
end LiteralPlanar.Quintic
