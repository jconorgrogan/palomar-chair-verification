module
public import RegisteredPrime.WorldNormalization
@[expose] public section
namespace RegisteredPrime

theorem generated_outgoing_seed (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) (hown : Occupies e (fun _ => 1)) : OutgoingSeed P e := by
  obtain ⟨n, q, r, hq, hr, _, hs⟩ := he
  have ho : Occupies (q.relative r) (fun _ => 1) := by rwa [hs.eq]
  have hactual : Occupies r (hole q) := by
    have h : Occupies (q.comp (q.relative r)) (hole q) := by
      rw [occupies_comp_iff]
      have hh : q.inv.cell (hole q) = (fun _ => (1 : Int)) := q.inv_cell_cell _
      rwa [hh]
    rwa [Pose.comp_relative] at h
  rw [← hs.eq]
  exact finite_hole_owner_is_seed P n q r hq hr hactual

noncomputable def RegisteredWorld.owner {p : Nat} (W : RegisteredWorld p) (q : Pose p) : Pose p :=
  Classical.choose (W.covers (hole q))

theorem RegisteredWorld.owner_mem {p : Nat} (W : RegisteredWorld p) (q : Pose p) :
    W.tiles (W.owner q) := (Classical.choose_spec (W.covers (hole q))).1

theorem RegisteredWorld.owner_occupies {p : Nat} (W : RegisteredWorld p) (q : Pose p) :
    Occupies (W.owner q) (hole q) := (Classical.choose_spec (W.covers (hole q))).2

theorem RegisteredWorld.owner_disjoint {p : Nat} (W : RegisteredWorld p) (q : Pose p)
    (hq : W.tiles q) : Disjoint q (W.owner q) := by
  intro c ⟨hqc, hoc⟩
  have he := W.nonoverlap q (W.owner q) hq (W.owner_mem q) c hqc hoc
  exact not_occupies_hole q (he.symm.occupies _ (W.owner_occupies q))

theorem RegisteredWorld.owner_contact {p : Nat} (W : RegisteredWorld p) (hp : 3 ≤ p)
    (q : Pose p) (hq : W.tiles q) : FaceContact q (W.owner q) :=
  hole_owner_face_contact hp q (W.owner q) (W.owner_disjoint q hq) (W.owner_occupies q)

theorem RegisteredWorld.owner_seed (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (q : Pose P.p) (hq : W.tiles q) : OutgoingSeed P (q.relative (W.owner q)) := by
  have he := hl q (W.owner q) hq (W.owner_mem q)
    (W.owner_contact (P.prime.three_le P.odd) q hq)
  apply generated_outgoing_seed P _ he
  have h : Occupies (q.comp (q.relative (W.owner q))) (hole q) := by
    rw [Pose.comp_relative]
    exact W.owner_occupies q
  rw [occupies_comp_iff] at h
  have hh : q.inv.cell (hole q) = (fun _ => (1 : Int)) := q.inv_cell_cell _
  rwa [hh] at h

theorem incoming_root_contact (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    FaceContact (identityPose P.p) (incomingPose P A hA) := by
  obtain ⟨n, q, r, hq, hr, hc, he⟩ := incoming_generated P A hA
  have h := q.inv.face_contact q r hc
  rw [Pose.inv_comp] at h
  change FaceContact (identityPose P.p) (q.relative r) at h
  rwa [he.eq] at h

theorem local_incoming_of_pose (P : Parameters) (W : RegisteredWorld P.p) (hl : W.Legal P)
    (g : Pose P.p) (hg : W.tiles g) (A : Mask P.p) (hA : Proper A)
    (htile : W.tiles (g.comp (incomingPose P A hA))) :
    (worldLocalPatch P W hl g hg).incoming A :=
  ⟨incomingPose P A hA, ⟨htile, incoming_root_contact P A hA⟩, incoming_support P A hA⟩

theorem all_incoming_completeStar (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (g : Pose P.p) (hg : W.tiles g)
    (hall : ∀ A, Proper A → (worldLocalPatch P W hl g hg).incoming A) : CompleteStar P W g := by
  intro A hA
  obtain ⟨e, he, hs⟩ := hall A hA
  have hgen := generated_of_root_neighbor P (W.reframe g) (W.reframe_legal P hl g)
    (W.reframe_root g hg) e he.1 he.2
  have hf := incoming_frame_property P e hgen A hA hs
  have hm := he.1
  change W.tiles (g.comp e) at hm
  rwa [hf.eq] at hm

theorem local_incomplete (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (g : Pose P.p) (hg : W.tiles g) (hn : ¬ CompleteStar P W g) :
    ¬ ∀ A, Proper A → (worldLocalPatch P W hl g hg).incoming A :=
  fun h => hn (all_incoming_completeStar P W hl g hg h)

theorem owner_incoming_pose (P : Parameters) (W : RegisteredWorld P.p)
    (q : Pose P.p) (A : Mask P.p) (hA : Proper A)
    (hs : q.relative (W.owner q) = outgoingSeed P A hA) :
    (W.owner q).comp (incomingPose P (scalarRole P A) (scalarRole_proper P A hA)) = q := by
  have hr := congrArg Pose.inv hs
  rw [Pose.relative_reverse, seed_inverse_incoming] at hr
  rw [← hr, Pose.comp_relative]

theorem owner_star_of_nonempty_role (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (q : Pose P.p) (hq : W.tiles q) (A : Mask P.p) (hA : Proper A)
    (hnA : NonemptyMask A) (hs : q.relative (W.owner q) = outgoingSeed P A hA) :
    CompleteStar P W (W.owner q) := by
  apply completeStar_of_incoming P W hl (W.owner q) (W.owner_mem q)
    (scalarRole_proper P A hA) (scalarRole_nonempty P A hnA)
  apply local_incoming_of_pose P W hl (W.owner q) (W.owner_mem q)
    (scalarRole P A) (scalarRole_proper P A hA)
  rw [owner_incoming_pose P W q A hA hs]
  exact hq

end RegisteredPrime
