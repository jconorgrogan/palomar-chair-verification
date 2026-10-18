module

public import ProductClosure.RegisteredTubeOwners
public import ProductClosure.RegisteredTubeMatching
public import ProductClosure.RegisteredTubeOpposition
public import ProductClosure.ProductWorldRealization
public import ProductClosure.PhysicalTilingUnmarked

@[expose] public section

/-! Literal keyed-body existence from complete registered finite-cell worlds.
Tube ownership and all geometric mating are proved from finite occupancy. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}

/-- Real intersections of registered tubes force complete native frame matches. -/
theorem registered_world_tubes_disjoint_or_matched {J : ℕ} (hm : 2 ≤ m)
    (W : World.CompleteTiling (World.placedCells S))
    (q r : RegisteredPrime.Pose (m+1)) (hq : q ∈ W.tiles) (hr : r ∈ W.tiles)
    (hne : q ≠ r) (u v : Site S) :
    Disjoint (poseIsometry q '' closedTube J u) (poseIsometry r '' closedTube J v) ∨
      SiteTransport (relativePlacement (poseIsometry q) (poseIsometry r)) u v := by
  have hroot : RegisteredPrime.identityPose (m + 1) ∈ (W.reframe q).tiles := by
    change q.comp (RegisteredPrime.identityPose (m + 1)) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_identity] using hq
  have hs : q.relative r ∈ (W.reframe q).tiles := by
    change q.comp (q.relative r) ∈ W.tiles
    simpa only [RegisteredPrime.Pose.comp_relative] using hr
  have hne' : RegisteredPrime.identityPose (m + 1) ≠ q.relative r := by
    intro he
    have he' := congrArg (q.comp ·) he
    apply hne
    simpa only [RegisteredPrime.Pose.comp_identity, RegisteredPrime.Pose.comp_relative] using he'
  have hd : Disjoint (S : Set (LatticeIndex m)) (World.placedCells S (q.relative r)) := by
    simpa only [placedCells_identity] using (W.reframe q).disjoint _ hroot _ hs hne'
  rcases registered_tubes_disjoint_or_matched (J := J) hm (q.relative r) u v
    (fun hx => registered_closedTube_intersection_opposed hm (q.relative r) u v hx hd)
      with ht | ht
  · left
    have ht' := (Set.disjoint_image_iff (poseIsometry q).injective).mpr ht
    rwa [poseIsometry_relative, placed_relative_image] at ht'
  · right
    rwa [poseIsometry_relative] at ht

/-- A complete cell world with its actual full profile equations tiles by the
literal compiled body. No keyed-body tiling, tube ownership, geometric mating,
or material partition certificate is an assumption. -/
theorem registered_world_physicalTiling {J : ℕ} [NeZero m]
    (hm : 2 ≤ m) (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S))
    (hprofile : ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r →
      FullProfileMating a (relativePlacement (poseIsometry q) (poseIsometry r))) :
    PhysicalTiling a (fun q : W.tiles => poseIsometry q.val) := by
  apply physicalTiling_of_matched_tubes hm
  · intro x
    obtain ⟨q, hq, hx⟩ := W.realize.cover x
    exact ⟨⟨q, hq⟩, hx⟩
  · intro q r hne
    exact W.realize.disjoint q.val q.property r.val r.property
      (fun he => hne (Subtype.ext he))
  · intro q u
    obtain ⟨r, hr, hne, v, ht⟩ := registered_world_site_mate W q.val q.property u
    exact ⟨⟨r, hr⟩, v, ht, hprofile q.val q.property r hr hne.symm u v ht⟩
  · intro q r hne u
    exact registered_world_tube_isolation W q.val r.val q.property r.property
      (fun he => hne (Subtype.ext he)) u
  · intro q r hne u v
    have hqr : q.val ≠ r.val := fun he => hne (Subtype.ext he)
    rcases registered_world_tubes_disjoint_or_matched hm W q.val r.val
      q.property r.property hqr u v with hd | ht
    · exact Or.inl hd
    · exact Or.inr ⟨ht, hprofile q.val q.property r.val r.property hqr u v ht⟩

/-- The same proved construction yields the unmarked physical existence target. -/
theorem registered_world_body_hasTiling {J : ℕ} [NeZero m]
    [Nonempty (Polycube.Cell S)] (hm : 2 ≤ m) (a : Coefficients S J)
    (W : World.CompleteTiling (World.placedCells S))
    (hprofile : ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r →
      FullProfileMating a (relativePlacement (poseIsometry q) (poseIsometry r))) :
    SparseMonotiles.HasTiling (body a) :=
  (registered_world_physicalTiling hm a W hprofile).hasTiling

#print axioms registered_world_tubes_disjoint_or_matched
#print axioms registered_world_physicalTiling
#print axioms registered_world_body_hasTiling
end
end ProductClosure.NativeCompiler
