module
public import RegisteredPrime.ArithmeticAtlas
public import closure_analysis.CoarseGeometryCases
public import closure_analysis.CoarseWalls
public import closure_analysis.CoarseIncoming
@[expose] public section
namespace RegisteredPrime

/-- Uniform pairwise coarsening closure of the explicit enlarged atlas.
Both directional fine tests range over all actual face contacts. There is no
E=atlas identification, contact table, full-world oracle, or closure premise. -/
theorem arithmetic_atlas_coarse_closed (P : Parameters) (e : Pose P.p)
    (hc : FaceContact (identityPose P.p) e)
    (hf : ChildArithmeticAtlas P (identityPose P.p) (doubleAnchor e))
    (hr : ChildArithmeticAtlas P (doubleAnchor e) (identityPose P.p)) :
    ArithmeticAtlasContact P e := by
  have hrecf := ChildArithmeticAtlas.recognition P _ _ hf
  have hrecr := ChildArithmeticAtlas.recognition P _ _ hr
  have hpar := coarse_parity_of_child_recognition P e hc hrecf
  have hd : DoubledFaceContact (identityPose P.p) (doubleAnchor e) := by
    simpa only [doubleAnchor_identity] using face_contact_doubled (identityPose P.p) e hc
  have haff := child_arithmetic_atlas_parent_affine P (identityPose P.p) (doubleAnchor e) hd hf
  rw [(relative_identity_same (doubleAnchor e)).eq] at haff
  have hzero : ∀ a b : Role P.p,
      FaceContact (arithmeticChild P a) (refine P e b) →
      (∀ i, ((arithmeticChild P a).relative (refine P e b)).anchor i = 0) →
      ((arithmeticChild P a).relative (refine P e b)).ZeroOrigin P := by
    intro a b hface hz
    have hfine : ArithmeticAtlasContact P ((arithmeticChild P a).relative (refine P e b)) := by
      have h := hf a b (by simpa only [Pose.identity_comp, refine, doubleAnchor] using hface)
      simpa only [Pose.identity_comp, refine, doubleAnchor] using h
    exact hfine.zero_origin hz
  refine ⟨⟨hpar, ?_, ?_, ?_⟩, haff, ?_⟩
  · intro he
    obtain ⟨j, side, hb⟩ := even_coarse_contact_canonical_box P e hc hrecf he
    exact (coarse_wall_preservation P e j side hb haff hzero).1
  · intro A hA hin
    have he := coarse_incoming_pose_of_child_recognition P e A hA hin hc.1 hrecr
    rw [he]
    exact Pose.Same.refl _
  · intro ho
    have hh : Occupies e (hole (identityPose P.p)) := by
      simpa only [hole, identity_cell] using ho
    have hb := hole_owner_box_position (P.prime.three_le P.odd) (identityPose P.p) e
      ⟨false, fun _ => rfl⟩ hpar hc.1 hh
    have hone : boxLower e = (fun _ => 1) := by
      funext i
      simpa [boxLower, identityPose, bit] using hb i
    exact coarse_outgoing_seed_of_child_recognition P e hone ho hc.1 hrecf
  · intro hz
    have he : ∀ i, e.anchor i % 2 = 0 := fun i => by rw [hz i]; rfl
    obtain ⟨j, side, hb⟩ := even_coarse_contact_canonical_box P e hc hrecf he
    exact (coarse_wall_preservation P e j side hb haff hzero).2 hz

end RegisteredPrime
