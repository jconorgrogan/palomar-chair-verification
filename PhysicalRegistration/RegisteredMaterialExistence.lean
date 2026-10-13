module

public import PhysicalRegistration.RegisteredTubeOwners
public import PhysicalRegistration.RegisteredTubeMatching
public import PhysicalRegistration.RegisteredTubeOpposition
public import PhysicalRegistration.PhysicalTilingUnmarked
public import RegisteredPrime.WorldExistence

@[expose] public section

/-! Actual existence of the literal compiled physical body. Registered cell
coverage, exposed-facet ownership, full-orbit matching, coefficient opposition,
and local material partitions discharge every finite-tube gluing hypothesis. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- Distinct registered-world tubes either miss or have exact full native
site transport. Opposite normals follow from integer-cell nonoverlap. -/
theorem registered_world_tubes_disjoint_or_matched {m J : ℕ} (hm : 2 ≤ m)
    (W : RegisteredPrime.RegisteredWorld (m+1))
    (q r : RegisteredPrime.Pose (m+1)) (hq : W.tiles q) (hr : W.tiles r)
    (hne : q ≠ r) (u v : Site m) :
    Disjoint (poseIsometry q '' closedTube J u) (poseIsometry r '' closedTube J v) ∨
      SiteTransport (relativePlacement (poseIsometry q) (poseIsometry r)) u v := by
  have hd := relative_disjoint q r (registeredWorld_disjoint W hq hr hne)
  rcases registered_tubes_disjoint_or_matched (J := J) hm (q.relative r) u v
    (fun hx => registered_closedTube_intersection_opposed hm (q.relative r) u v hx hd)
      with ht | ht
  · left
    have ht' := (Set.disjoint_image_iff (poseIsometry q).injective).mpr ht
    rwa [poseIsometry_relative, placed_relative_image] at ht'
  · right
    rwa [poseIsometry_relative] at ht

namespace GeneratedCompiler
open RegisteredPrime RegisteredPrime.PrimeFacetClosure

/-- Every actual E-legal registered world becomes a genuine physical tiling
by the explicitly generated coefficients. No body tiling or material-gluing
certificate is an input. -/
theorem registered_world_physicalTiling {m : ℕ} [NeZero m]
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (W : RegisteredWorld (m+1)) (hl : W.Legal (minusParameters (m+1) hp hmod)) :
    PhysicalTiling (coefficients hp hmod)
      (fun q : {q // W.tiles q} => poseIsometry q.val) := by
  apply physicalTiling_of_matched_tubes (nativeDimension_ge_two hmod)
  · intro x
    obtain ⟨q, hq, hx⟩ := registered_carriers_cover W x
    exact ⟨⟨q, hq⟩, hx⟩
  · intro q r hne
    exact registered_carrier_interiors_disjoint W q.property r.property
      (fun he => hne (Subtype.ext he))
  · intro q u
    obtain ⟨r, hr, hne, v, ht⟩ := registered_world_site_mate W q.val q.property u
    refine ⟨⟨r, hr⟩, v, ht, ?_⟩
    apply generatedWorld_fullProfileMating hp hmod W hl q.property hr hne.symm
    rwa [poseIsometry_relative]
  · intro q r hne u
    exact registered_world_tube_isolation W q.val r.val q.property r.property
      (fun he => hne (Subtype.ext he)) u
  · intro q r hne u v
    have hqr : q.val ≠ r.val := fun he => hne (Subtype.ext he)
    rcases registered_world_tubes_disjoint_or_matched (nativeDimension_ge_two hmod)
      W q.val r.val q.property r.property hqr u v with hd | ht
    · exact Or.inl hd
    · refine Or.inr ⟨ht, ?_⟩
      apply generatedWorld_fullProfileMating hp hmod W hl q.property r.property hqr
      rwa [poseIsometry_relative]

/-- The historical nested-supertiling construction gives a nonvacuous
unmarked tiling of the very same literal compiled body used for aperiodicity. -/
theorem body_hasTiling {m : ℕ} [NeZero m]
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) :
    SparseMonotiles.HasTiling (body (coefficients hp hmod)) := by
  obtain ⟨W, hl⟩ := registered_E_world_exists (minusParameters (m+1) hp hmod)
  exact (registered_world_physicalTiling hp hmod W hl).hasTiling

#print axioms registered_world_physicalTiling
#print axioms body_hasTiling
end GeneratedCompiler
#print axioms registered_world_tubes_disjoint_or_matched
end
end PhysicalRegistration.NativeChair
