module
public import RegisteredPrime.LocalRecognition
@[expose] public section
namespace RegisteredPrime
theorem Pose.Same.symm {p : Nat} {q r : Pose p} (h : q.Same r) : r.Same q :=
  ⟨fun i => (h.1 i).symm, fun i => (h.2.1 i).symm, fun i => (h.2.2 i).symm⟩
theorem Pose.Same.trans {p : Nat} {q r s : Pose p} (h : q.Same r) (k : r.Same s) :
    q.Same s :=
  ⟨fun i => (h.1 i).trans (k.1 i), fun i => (h.2.1 i).trans (k.2.1 i),
    fun i => (h.2.2 i).trans (k.2.2 i)⟩
theorem Pose.Same.cell {p : Nat} {q r : Pose p} (h : q.Same r) (x : Cell p) :
    q.cell x = r.cell x := by
  funext i
  simp only [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign]
  rw [h.1 i, h.2.1 i, h.2.2 i]
theorem Pose.Same.occupies {p : Nat} {q r : Pose p} (h : q.Same r) (x : Cell p)
    (hq : Occupies q x) : Occupies r x := by
  obtain ⟨b, hb, he⟩ := hq
  exact ⟨b, hb, (h.cell b).symm.trans he⟩
theorem relative_identity_same {p : Nat} (q : Pose p) :
    ((identityPose p).relative q).Same q := by
  constructor
  · intro i
    rfl
  constructor
  · intro i
    simp [Pose.relative, Pose.inv, Pose.comp, identityPose, RegisteredFrame.inv,
      RegisteredFrame.comp]
  · intro i
    simp [Pose.relative, Pose.inv, Pose.comp, identityPose, RegisteredFrame.inv,
      RegisteredFrame.linear, RegisteredFrame.sign]
@[simp] theorem identity_cell {p : Nat} (x : Cell p) : (identityPose p).cell x = x := by
  funext i
  simp [Pose.cell, identityPose, RegisteredFrame.linear, RegisteredFrame.sign, bit]
@[simp] theorem identity_occupies {p : Nat} (x : Cell p) :
    Occupies (identityPose p) x ↔ UnitChairCell x := by
  constructor
  · rintro ⟨b, hb, he⟩
    rw [identity_cell] at he
    exact he ▸ hb
  · intro h
    exact ⟨x, h, identity_cell x⟩
theorem root_owns_role {p : Nat} (A : Mask p) (hA : Proper A) :
    Occupies (identityPose p) (fun i => bit (A i)) := by
  apply (identity_occupies _).mpr
  constructor
  · intro i
    cases h : A i <;> simp [bit, h]
  · obtain ⟨i, hi⟩ := hA
    exact ⟨i, by simp [bit, hi]⟩
theorem root_not_exterior {p : Nat} (A : Mask p) (j : Fin p) :
    ¬ Occupies (identityPose p) (exterior A j) := by
  intro h
  have hj := ((identity_occupies _).mp h).1 j
  cases ha : A j <;> simp [exterior, bit, ha] at hj
theorem role_adjacent_exterior {p : Nat} (A : Mask p) (j : Fin p) :
    Adjacent (fun i => bit (A i)) (exterior A j) := by
  refine ⟨j, ?_, fun i hi => by simp [exterior, hi]⟩
  cases ha : A j <;> simp [exterior, bit, ha]
theorem exterior_owner_face_contact {p : Nat} (W : RegisteredWorld p)
    (hroot : W.tiles (identityPose p)) (A : Mask p) (hA : Proper A) (j : Fin p)
    (q : Pose p) (hq : W.tiles q) (hx : Occupies q (exterior A j)) :
    FaceContact (identityPose p) q := by
  constructor
  · intro c ⟨hrc, hqc⟩
    have he := W.nonoverlap _ _ hroot hq c hrc hqc
    exact root_not_exterior A j (he.symm.occupies _ hx)
  · exact ⟨fun i => bit (A i), exterior A j, root_owns_role A hA, hx,
      role_adjacent_exterior A j⟩
def GeneratedWallProperty (P : Parameters) : Prop :=
  ∀ q, GeneratedContact P q → (∀ i, q.anchor i % 2 = 0) → WallGeometry q
theorem generated_of_root_neighbor (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p)) (q : Pose P.p)
    (hq : W.tiles q) (hc : FaceContact (identityPose P.p) q) : GeneratedContact P q := by
  obtain ⟨n, a, b, ha, hb, hab, he⟩ := hl _ _ hroot hq hc
  exact ⟨n, a, b, ha, hb, hab, he.trans (relative_identity_same q)⟩
def normalizedLocalPatch (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p))
    (hwalls : GeneratedWallProperty P) : LocalPatch P.p where
  tiles := fun q => W.tiles q ∧ FaceContact (identityPose P.p) q
  parity := fun q hq => generated_contact_constant_parity P q
    (generated_of_root_neighbor P W hl hroot q hq.1 hq.2)
  walls := fun q hq he => hwalls q
    (generated_of_root_neighbor P W hl hroot q hq.1 hq.2) he
  covers := by
    intro A hA j
    obtain ⟨q, hq, hx⟩ := W.covers (exterior A j)
    exact ⟨q, ⟨hq, exterior_owner_face_contact W hroot A hA j q hq hx⟩, hx⟩
  root_disjoint := by
    intro q hq A hA hx
    exact hq.2.1 _ ⟨root_owns_role A hA, hx⟩
  nonoverlap := fun q r hq hr c hqc hrc => W.nonoverlap q r hq.1 hr.1 c hqc hrc
theorem registered_support_fan (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p))
    (hwalls : GeneratedWallProperty P) {A : Mask P.p} (hA : Proper A)
    (hnA : NonemptyMask A) (hin : (normalizedLocalPatch P W hl hroot hwalls).incoming A) :
    ∀ B, Proper B → (normalizedLocalPatch P W hl hroot hwalls).incoming B :=
  (normalizedLocalPatch P W hl hroot hwalls).complete_of_nonempty_incoming
    (P.prime.three_le P.odd) hA hnA hin
end RegisteredPrime
