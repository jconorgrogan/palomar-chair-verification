module
public import RegisteredPrime.CoarseGeometry
@[expose] public section
namespace RegisteredPrime

/-- Four explicit local contact conditions sufficient for first-parent
recognition. This predicate contains no hierarchy, coarsening, or recognition
conclusion as a field. -/
structure RecognitionContact (P : Parameters) (e : Pose P.p) : Prop where
  parity : e.UniformParity
  walls : (∀ i, e.anchor i % 2 = 0) → WallGeometry e
  incoming : ∀ A (hA : Proper A), IncomingSupport e A → e.Same (incomingPose P A hA)
  outgoing : Occupies e (fun _ => 1) → OutgoingSeed P e

/-- The actual generated E language satisfies every recognition clause. -/
theorem generated_recognition_contact (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) : RecognitionContact P e :=
  ⟨generated_contact_constant_parity P e he, generated_wall_property P e he,
    incoming_frame_property P e he, generated_outgoing_seed P e he⟩

namespace WeakRecognition

/-- Universal legality over actual face contacts, with no catalog or hierarchy. -/
def Legal (P : Parameters) (W : RegisteredWorld P.p) : Prop :=
  ∀ q r, W.tiles q → W.tiles r → FaceContact q r → RecognitionContact P (q.relative r)

theorem legal_of_E (P : Parameters) (W : RegisteredWorld P.p) (hl : W.Legal P) :
    Legal P W := fun q r hq hr hc => generated_recognition_contact P _ (hl q r hq hr hc)

theorem reframe_legal (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (g : Pose P.p) : Legal P (W.reframe g) := by
  intro q r hq hr hc
  have h := hl (g.comp q) (g.comp r) hq hr (g.face_contact q r hc)
  rw [Pose.relative_left_cancel] at h
  exact h

theorem recognition_of_root_neighbor (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (hroot : W.tiles (identityPose P.p)) (q : Pose P.p)
    (hq : W.tiles q) (hc : FaceContact (identityPose P.p) q) : RecognitionContact P q := by
  have h := hl _ _ hroot hq hc
  rwa [(relative_identity_same q).eq] at h

/-- The actual exterior-cell owners supply the geometric local patch. -/
def normalizedLocalPatch (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (hroot : W.tiles (identityPose P.p)) : LocalPatch P.p where
  tiles := fun q => W.tiles q ∧ FaceContact (identityPose P.p) q
  parity := fun q hq => (recognition_of_root_neighbor P W hl hroot q hq.1 hq.2).parity
  walls := fun q hq => (recognition_of_root_neighbor P W hl hroot q hq.1 hq.2).walls
  covers := by
    intro A hA j
    obtain ⟨q, hq, hx⟩ := W.covers (exterior A j)
    exact ⟨q, ⟨hq, exterior_owner_face_contact W hroot A hA j q hq hx⟩, hx⟩
  root_disjoint := by
    intro q hq A hA hx
    exact hq.2.1 _ ⟨root_owns_role A hA, hx⟩
  nonoverlap := fun q r hq hr c hqc hrc => W.nonoverlap q r hq.1 hr.1 c hqc hrc

def worldLocalPatch (P : Parameters) (W : RegisteredWorld P.p) (hl : Legal P W)
    (g : Pose P.p) (hg : W.tiles g) : LocalPatch P.p :=
  normalizedLocalPatch P (W.reframe g) (reframe_legal P W hl g) (W.reframe_root g hg)

/-- Incoming support completion is geometric; the explicit incoming clause
upgrades it to complete prescribed full poses. -/
theorem all_incoming_completeStar (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (g : Pose P.p) (hg : W.tiles g)
    (hall : ∀ A, Proper A → (worldLocalPatch P W hl g hg).incoming A) :
    CompleteStar P W g := by
  intro A hA
  obtain ⟨e, he, hs⟩ := hall A hA
  have hrec := recognition_of_root_neighbor P (W.reframe g) (reframe_legal P W hl g)
    (W.reframe_root g hg) e he.1 he.2
  have hf := hrec.incoming A hA hs
  have hm := he.1
  change W.tiles (g.comp e) at hm
  rwa [hf.eq] at hm

theorem completeStar_of_incoming (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (g : Pose P.p) (hg : W.tiles g)
    {A : Mask P.p} (hA : Proper A) (hnA : NonemptyMask A)
    (hin : (worldLocalPatch P W hl g hg).incoming A) : CompleteStar P W g :=
  all_incoming_completeStar P W hl g hg
    ((worldLocalPatch P W hl g hg).complete_of_nonempty_incoming
      (P.prime.three_le P.odd) hA hnA hin)

theorem completeStar_all_incoming (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (g : Pose P.p) (hg : W.tiles g) (hs : CompleteStar P W g) :
    ∀ A, Proper A → (worldLocalPatch P W hl g hg).incoming A := by
  intro A hA
  exact ⟨incomingPose P A hA, ⟨hs A hA, incoming_root_contact P A hA⟩,
    incoming_support P A hA⟩

theorem local_incoming_of_pose (P : Parameters) (W : RegisteredWorld P.p) (hl : Legal P W)
    (g : Pose P.p) (hg : W.tiles g) (A : Mask P.p) (hA : Proper A)
    (htile : W.tiles (g.comp (incomingPose P A hA))) :
    (worldLocalPatch P W hl g hg).incoming A :=
  ⟨incomingPose P A hA, ⟨htile, incoming_root_contact P A hA⟩, incoming_support P A hA⟩

theorem local_incomplete (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (g : Pose P.p) (hg : W.tiles g) (hn : ¬ CompleteStar P W g) :
    ¬ ∀ A, Proper A → (worldLocalPatch P W hl g hg).incoming A :=
  fun h => hn (all_incoming_completeStar P W hl g hg h)

/-- The actual owner of a tile's missing cell has a prescribed outgoing pose.
Only the fourth explicit recognition clause is used here. -/
theorem owner_seed (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (q : Pose P.p) (hq : W.tiles q) : OutgoingSeed P (q.relative (W.owner q)) := by
  have he := hl q (W.owner q) hq (W.owner_mem q)
    (W.owner_contact (P.prime.three_le P.odd) q hq)
  apply he.outgoing
  have h : Occupies (q.comp (q.relative (W.owner q))) (hole q) := by
    rw [Pose.comp_relative]
    exact W.owner_occupies q
  rw [occupies_comp_iff] at h
  have hh : q.inv.cell (hole q) = (fun _ => (1 : Int)) := q.inv_cell_cell _
  rwa [hh] at h

theorem owner_star_of_nonempty_role (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (q : Pose P.p) (hq : W.tiles q) (A : Mask P.p) (hA : Proper A)
    (hnA : NonemptyMask A) (hs : q.relative (W.owner q) = outgoingSeed P A hA) :
    CompleteStar P W (W.owner q) := by
  apply completeStar_of_incoming P W hl (W.owner q) (W.owner_mem q)
    (scalarRole_proper P A hA) (scalarRole_nonempty P A hnA)
  apply local_incoming_of_pose P W hl (W.owner q) (W.owner_mem q)
    (scalarRole P A) (scalarRole_proper P A hA)
  rw [owner_incoming_pose P W q A hA hs]
  exact hq

end WeakRecognition
end RegisteredPrime
