module

public import PrimeFacetClosure.RealizedFacetClosure

@[expose] public section

/-! Original generated-language worlds satisfy the complete native physical
profiles. The actual matched sites supply carrier face contact. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
open RegisteredPrime RegisteredPrime.PrimeFacetClosure

 theorem adjacent_facet_inside_outside {m : ℕ} (f : Facet m) :
    Adjacent (cellIndex (facetInsideCell f)) (facetOutsideIndex f) := by
  refine ⟨normalIndex f, ?_, ?_⟩
  · cases h : facetPositive f <;> simp [facetOutsideIndex,latticeStep,h]
  · intro i hi
    simp [facetOutsideIndex,latticeStep,hi]

/-- Matched full native sites of nonoverlapping carriers give an actual
registered face contact, not merely a combinatorial matching assertion. -/
 theorem SiteTransport.faceContact {m : ℕ} {q : Pose (m+1)} {u v : Site m}
    (ht : SiteTransport (poseIsometry q) u v)
    (hd : RegisteredPrime.Disjoint (identityPose (m+1)) q) :
    FaceContact (identityPose (m+1)) q := by
  refine ⟨hd, cellIndex (facetInsideCell u.1), facetOutsideIndex u.1, ?_, ?_,
    adjacent_facet_inside_outside u.1⟩
  · exact ⟨_,cellIndex_unitChairCell _,identity_cell _⟩
  · exact ⟨_,cellIndex_unitChairCell _,ht.registered_cell⟩

 theorem registeredWorld_disjoint {p : ℕ} (W : RegisteredWorld p) {q r : Pose p}
    (hq : W.tiles q) (hr : W.tiles r) (hne : q ≠ r) : RegisteredPrime.Disjoint q r := by
  intro c hc
  exact hne (W.nonoverlap q r hq hr c hc.1 hc.2).eq

 theorem relative_disjoint {p : ℕ} (q r : Pose p) (hd : RegisteredPrime.Disjoint q r) :
    RegisteredPrime.Disjoint (identityPose p) (q.relative r) := by
  intro c hc
  apply hd (q.cell c)
  have h₁ := (occupies_comp_cell q (identityPose p) c).mpr hc.1
  have h₂ := (occupies_comp_cell q (q.relative r) c).mpr hc.2
  simpa only [Pose.comp_identity,Pose.comp_relative] using And.intro h₁ h₂

/-- Every actual site mating between distinct tiles in an original E-legal
world satisfies the constructed compiler's complete physical profile. -/
 theorem generatedWorld_fullProfileMating {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (W : RegisteredWorld (m+1)) (hl : W.Legal (minusParameters (m+1) hp hmod))
    {q r : Pose (m+1)} (hq : W.tiles q) (hr : W.tiles r) (hne : q ≠ r) :
    FullProfileMating (GeneratedCompiler.coefficients hp hmod) (poseIsometry (q.relative r)) := by
  intro u v ht
  have hc := ht.faceContact (relative_disjoint q r (registeredWorld_disjoint W hq hr hne))
  have hcr := q.face_contact (identityPose (m+1)) (q.relative r) hc
  rw [Pose.comp_identity,Pose.comp_relative] at hcr
  exact GeneratedCompiler.coefficients_satisfy_E hp hmod (hl q r hq hr hcr) ht

#print axioms SiteTransport.faceContact
#print axioms generatedWorld_fullProfileMating
end
end PhysicalRegistration.NativeChair
