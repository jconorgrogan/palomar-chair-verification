module

public import PrimeFacetClosure.Parameters
public import PrimeFacetClosure.HoleAtlasBridge
public import PrimeFacetClosure.RegisteredStarTransport
public import PhysicalRegistration.PoseRealization
public import PhysicalRegistration.RegisteredPoseProperness
public import PhysicalRegistration.NativeComponentOrder

@[expose] public section

/-!
# A genuinely finite compiler for the actual generated contact language

A native full site has only finitely many possible partners. The complete
native frame and center determine an isometry uniquely. Thus it suffices to
choose one *actual generated contact* for every eligible ordered site pair.
The finite image below retains every original generated site equation, without
assuming or enumerating a finite catalog of generated contacts.

Properness is proved from actual generated-frame properness and the exact
historical/Euclidean determinant bridge.
No graph-closure, path-holonomy, or candidate-classification premise is used.
-/
namespace PhysicalRegistration.NativeChair.GeneratedCompiler
noncomputable section
open RegisteredPrime
open RegisteredPrime.PrimeFacetClosure
open RegisteredPrime.PrimeFacetClosure.StarHolonomy
open NativeWalkTransport

variable {m : ℕ}

/-- Eligibility is witnessed by an actual original `GeneratedContact` pose,
with its genuine Euclidean realization transporting the complete native site. -/
def Eligible (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (uv : Site m × Site m) : Prop :=
  ∃ q : Pose (m+1), GeneratedContact (minusParameters (m+1) hp hmod) q ∧
    SiteTransport (poseIsometry q) uv.1 uv.2

abbrev EligiblePair (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :=
  {uv : Site m × Site m // Eligible hp hmod uv}

/-- No new isometry is introduced by selection: this is an actual generated
pose supplied by the pair's eligibility proof. -/
def selectedPose (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (uv : EligiblePair hp hmod) : Pose (m+1) := uv.property.choose

theorem selectedPose_generated (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (uv : EligiblePair hp hmod) :
    GeneratedContact (minusParameters (m+1) hp hmod) (selectedPose hp hmod uv) :=
  uv.property.choose_spec.1

theorem selectedPose_transport (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (uv : EligiblePair hp hmod) :
    SiteTransport (poseIsometry (selectedPose hp hmod uv)) uv.val.1 uv.val.2 :=
  uv.property.choose_spec.2

/-- The finite real generator language, indexed by eligible full native-site
pairs. Finiteness comes from native site finiteness, not a supplied E catalog. -/
def generators (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :
    Finset (Space m ≃ᵢ Space m) := by
  classical
  exact Finset.univ.image (fun uv : EligiblePair hp hmod => poseIsometry (selectedPose hp hmod uv))

/-- Every selected finite generator belongs to the original generated language. -/
theorem generators_all_generated (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {e : Space m ≃ᵢ Space m} (he : e ∈ generators hp hmod) :
    ∃ q : Pose (m+1), GeneratedContact (minusParameters (m+1) hp hmod) q ∧
      e = poseIsometry q := by
  classical
  obtain ⟨uv, _, rfl⟩ := Finset.mem_image.mp he
  exact ⟨selectedPose hp hmod uv, selectedPose_generated hp hmod uv, rfl⟩

/-- Complete site-frame uniqueness makes the selected witness equal to every
actual generated witness for this same ordered site pair. -/
theorem selectedPose_eq (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (uv : EligiblePair hp hmod) (q : Pose (m+1))
    (ht : SiteTransport (poseIsometry q) uv.val.1 uv.val.2) :
    selectedPose hp hmod uv = q := by
  apply poseIsometry_injective
  exact siteTransport_unique (selectedPose_transport hp hmod uv) ht

/-- Every original generated contact which pairs these actual native sites
is literally in the finite generator set, as a complete affine isometry. -/
theorem generated_transport_mem (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {q : Pose (m+1)} (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    {u v : Site m} (ht : SiteTransport (poseIsometry q) u v) :
    poseIsometry q ∈ generators hp hmod := by
  classical
  let uv : EligiblePair hp hmod := ⟨(u,v), q, hq, ht⟩
  apply Finset.mem_image.mpr
  refine ⟨uv, Finset.mem_univ _, ?_⟩
  rw [selectedPose_eq hp hmod uv q ht]

/-- Isolated properness interface. It asks only for the existing generated
poses' determinant, and has no component-closure or classification content. -/
theorem generators_proper_of (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (hproper : ∀ q : Pose (m+1), GeneratedContact (minusParameters (m+1) hp hmod) q →
      IsProperPlacement (poseIsometry q)) :
    ∀ e ∈ generators hp hmod, IsProperPlacement e := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := generators_all_generated hp hmod he
  exact hproper q hq


/-- The actual finite generators are proper Euclidean placements. This is a
proved determinant fact, not a remaining compiler assumption. -/
theorem generators_proper (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :
    ∀ e ∈ generators hp hmod, IsProperPlacement e := by
  apply generators_proper_of hp hmod
  intro q hq
  exact (poseIsometry_isProper_iff q).mpr
    (generated_frame_proper (minusParameters (m+1) hp hmod) q hq)

/-- The fully specified finite native compiler graph for the original
completed dense-family generated language. -/
def graph (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) : SimpleGraph (Site m) :=
  contactGraph (generators hp hmod) (generators_proper hp hmod)

theorem nativeDimension_ge_two (hmod : (m+1) % 4 = 3) : 2 ≤ m := by omega

/-- The literal lexicographically ordered native coefficient assignment. -/
def coefficients (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :=
  compiledCoefficients (nativeDimension_ge_two hmod) (generators hp hmod) (generators_proper hp hmod)

/-- Every original generating site equation is an actual edge of the finite
compiler graph. Neither endpoints nor tangent frames are quotiented. -/
theorem generated_transport_edge (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (hA : ∀ e ∈ generators hp hmod, IsProperPlacement e)
    {q : Pose (m+1)} (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    {u v : Site m} (ht : SiteTransport (poseIsometry q) u v) :
    (contactGraph (generators hp hmod) hA).Adj u v :=
  ⟨poseIsometry q, generated_transport_mem hp hmod hq ht, Or.inl ht⟩

/-- The finite compiler satisfies every full original E site equation. -/
theorem coefficients_satisfy_generated_transport
    [LinearOrder (Site m)] (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (hA : ∀ e ∈ generators hp hmod, IsProperPlacement e)
    {q : Pose (m+1)} (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    {u v : Site m} (ht : SiteTransport (poseIsometry q) u v) :
    (graphCoefficients (contactGraph (generators hp hmod) hA)).value v =
      -(graphCoefficients (contactGraph (generators hp hmod) hA)).value u :=
  contactGraph_coefficients_satisfy_all_edges _ hA
    (generated_transport_edge hp hmod hA hq ht)

private theorem realized_inverse (q : Pose (m+1)) :
    poseIsometry q.inv = (poseIsometry q).symm := by
  apply IsometryEquiv.ext
  intro x
  apply (poseIsometry q).injective
  have hh := congrArg (fun e : Space m ≃ᵢ Space m => e x) (poseIsometry_comp q q.inv)
  rw [Pose.comp_inv, poseIsometry_identity] at hh
  rw [IsometryEquiv.apply_symm_apply]
  exact hh.symm

/-- Every directed edge placement remains a genuine generated pose, including
edges traversed in reverse. Membership is obtained from actual generator
membership and inverse closure, not an assumed catalog. -/
theorem edgePlacement_generated (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (hA : ∀ e ∈ generators hp hmod, IsProperPlacement e)
    {u v : Site m} (h : (contactGraph (generators hp hmod) hA).Adj u v) :
    ∃ q : Pose (m+1), GeneratedContact (minusParameters (m+1) hp hmod) q ∧
      edgePlacement (generators hp hmod) hA h = poseIsometry q := by
  obtain ⟨g, hg, hdir⟩ := edgePlacement_generator_or_inverse (generators hp hmod) hA h
  obtain ⟨q, hq, rfl⟩ := generators_all_generated hp hmod hg
  rcases hdir with hf | hr
  · exact ⟨q, hq, hf⟩
  · exact ⟨q.inv, generated_contact_inverse (minusParameters (m+1) hp hmod) q hq, hr.trans (realized_inverse q).symm⟩


/-- The canonical registered edge pose transports the literal sites in its
actual Euclidean realization, ready for local geometric classification. -/
theorem edgePose_transport (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (hA : ∀ e ∈ generators hp hmod, IsProperPlacement e)
    {u v : Site m} (h : (contactGraph (generators hp hmod) hA).Adj u v) :
    SiteTransport (poseIsometry (edgePose (generators hp hmod) hA h)) u v := by
  rw [← (edgePose_realizes (generators hp hmod) hA h).eq_poseIsometry]
  exact edgePlacement_spec (generators hp hmod) hA h

/-- Canonical edgePose is exactly that actual generated pose. This is the
input needed to apply concrete generated-contact gauge classification. -/
theorem edgePose_generated (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (hA : ∀ e ∈ generators hp hmod, IsProperPlacement e)
    {u v : Site m} (h : (contactGraph (generators hp hmod) hA).Adj u v) :
    GeneratedContact (minusParameters (m+1) hp hmod)
      (edgePose (generators hp hmod) hA h) := by
  obtain ⟨q, hq, he⟩ := edgePlacement_generated hp hmod hA h
  have hr := edgePose_realizes (generators hp hmod) hA h
  rw [he] at hr
  have hpq := registeredPoseRealizes_unique hr (poseIsometry_realizes q)
  rwa [hpq]

/-- The contact graph is exactly the original generated site relation, even
though its finite presentation did not require an E-finiteness theorem. -/
theorem contactGraph_adj_iff_generated (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (hA : ∀ e ∈ generators hp hmod, IsProperPlacement e) (u v : Site m) :
    (contactGraph (generators hp hmod) hA).Adj u v ↔
      ∃ q : Pose (m+1), GeneratedContact (minusParameters (m+1) hp hmod) q ∧
        SiteTransport (poseIsometry q) u v := by
  constructor
  · intro h
    refine ⟨edgePose (generators hp hmod) hA h, edgePose_generated hp hmod hA h, ?_⟩
    have he := (edgePose_realizes (generators hp hmod) hA h).eq_poseIsometry
    rw [← he]
    exact edgePlacement_spec (generators hp hmod) hA h
  · rintro ⟨q, hq, ht⟩
    exact generated_transport_edge hp hmod hA hq ht


/-- Original E equations hold for the actual geometrically ordered compiler,
with its component count computed from the constructed finite graph. -/
theorem coefficients_satisfy_E (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {q : Pose (m+1)} (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    {u v : Site m} (ht : SiteTransport (poseIsometry q) u v) :
    (coefficients hp hmod).value v = -(coefficients hp hmod).value u := by
  exact compiledCoefficients_edge_neg (nativeDimension_ge_two hmod)
    (generators hp hmod) (generators_proper hp hmod)
    (generated_transport_edge hp hmod (generators_proper hp hmod) hq ht)

/-- Exact presentation of the original E relation, with no properness or
finiteness parameter left over. -/
theorem graph_adj_iff_generated (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (u v : Site m) : (graph hp hmod).Adj u v ↔
      ∃ q : Pose (m+1), GeneratedContact (minusParameters (m+1) hp hmod) q ∧
        SiteTransport (poseIsometry q) u v :=
  contactGraph_adj_iff_generated hp hmod (generators_proper hp hmod) u v

#print axioms generators_all_generated
#print axioms generators_proper
#print axioms coefficients_satisfy_E
#print axioms graph_adj_iff_generated
#print axioms generated_transport_mem
#print axioms coefficients_satisfy_generated_transport
#print axioms edgePose_generated
#print axioms contactGraph_adj_iff_generated
end
end PhysicalRegistration.NativeChair.GeneratedCompiler
