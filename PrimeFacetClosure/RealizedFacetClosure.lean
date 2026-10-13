module

public import PrimeFacetClosure.GeneratedStarHolonomy
public import PrimeFacetClosure.NativeAtlasBridge
public import PrimeFacetClosure.NativeGeneratedGauge
public import PrimeFacetClosure.NativeContactFacet
public import PhysicalRegistration.PhysicalProfileLaw

@[expose] public section

/-! The finite literal native compiler and the original generated contact
language coincide. The final facet-closure theorem below tests every actual
native site and feeds the resulting arithmetic atlas to the existing hierarchy. -/
namespace PhysicalRegistration.NativeChair.GeneratedCompiler
noncomputable section
open RegisteredPrime RegisteredPrime.PrimeFacetClosure

/-- A generated contact has an exposed facet, hence a full native-site pair.
The selected finite presentation therefore contains every generated pose. -/
theorem generated_mem (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    {q : Pose (m+1)} (hq : GeneratedContact (minusParameters (m+1) hp hmod) q) :
    poseIsometry q ∈ generators hp hmod := by
  obtain ⟨u,v,ht⟩ := faceContact_exists_siteTransport q
    (generated_root_face_contact (minusParameters (m+1) hp hmod) q hq)
  exact generated_transport_mem hp hmod hq ht

/-- Exact finite realization of E, not an enlarged generator language. -/
theorem mem_generators_iff (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (q : Pose (m+1)) : poseIsometry q ∈ generators hp hmod ↔
      GeneratedContact (minusParameters (m+1) hp hmod) q := by
  constructor
  · intro h
    obtain ⟨r,hr,he⟩ := generators_all_generated hp hmod h
    have hqr := poseIsometry_injective he
    exact hqr ▸ hr
  · exact generated_mem hp hmod

/-- Catalogue-free facet closure into the closed arithmetic atlas. The only
candidate hypotheses are genuine carrier face contact and every literal
native profile equation for the completely specified original-E compiler. -/
theorem fullProfile_arithmetic_atlas (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (q : Pose (m+1)) (hc : FaceContact (identityPose (m+1)) q)
    (hprofile : FullProfileMating (coefficients hp hmod) (poseIsometry q)) :
    ArithmeticAtlasContact (minusParameters (m+1) hp hmod) q := by
  let P := minusParameters (m+1) hp hmod
  obtain ⟨⟨f,U⟩,⟨g,V⟩,ht⟩ := faceContact_exists_siteTransport q hc
  cases f with
  | inl Aj =>
    obtain ⟨A,j⟩ := Aj
    cases g with
    | inl Bk =>
      obtain ⟨B,k⟩ := Bk
      exact native_outer_arithmetic_atlas hp hmod q (reflectionFrame P)
        (reflectionFrame_affine P) (negIndex_zero P)
        (fun C D l n X Y hxy => candidate_outer_outer_frame hp hmod q C D l n X Y hxy
          (hprofile _ _ hxy)) A B j k U V ht
    | inr k =>
      exact native_incoming_arithmetic_atlas hp hmod q A j k U V ht
        (candidate_outer_inner_frame hp hmod q A j k U V ht (hprofile _ _ ht))
  | inr j =>
    cases g with
    | inl Bk =>
      obtain ⟨B,k⟩ := Bk
      exact native_outgoing_arithmetic_atlas hp hmod q B j k U V ht
        (candidate_inner_outer_frame hp hmod q B j k U V ht (hprofile _ _ ht))
    | inr k =>
      exact False.elim ((native_inner_bridge_not_disjoint hp hmod q (reflectionFrame P)
        j k U V ht (candidate_inner_inner_frame hp hmod q j k U V ht (hprofile _ _ ht))) hc.1)

/-- Every registered world obeying the literal physical profiles of the
constructed compiler satisfies the existing closed arithmetic atlas law.
No hierarchy, parent assignment, graph closure, or E membership is supplied. -/
theorem fullProfile_world_arithmetic_atlas (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (W : RegisteredWorld (m+1))
    (hprofile : ∀ r s, W.tiles r → W.tiles s →
      FullProfileMating (coefficients hp hmod) (poseIsometry (r.relative s))) :
    ArithmeticAtlasLegal (minusParameters (m+1) hp hmod) W := by
  intro r s hr hs hc
  have h := r.inv.face_contact r s hc
  rw [Pose.inv_comp] at h
  change FaceContact (identityPose (m+1)) (r.relative s) at h
  exact fullProfile_arithmetic_atlas hp hmod (r.relative s) h (hprofile r s hr hs)

#print axioms mem_generators_iff
#print axioms fullProfile_arithmetic_atlas
#print axioms fullProfile_world_arithmetic_atlas

end
end PhysicalRegistration.NativeChair.GeneratedCompiler
