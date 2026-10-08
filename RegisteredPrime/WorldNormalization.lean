module
public import RegisteredPrime.IncomingExhaustiveness
@[expose] public section
namespace RegisteredPrime

theorem Pose.comp_left_cancel {p : Nat} (g q r : Pose p) (h : g.comp q = g.comp r) : q = r := by
  have he := congrArg (fun t => g.inv.comp t) h
  simp only [← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp] at he
  exact he

theorem occupies_comp_cell {p : Nat} (g q : Pose p) (c : Cell p) :
    Occupies (g.comp q) (g.cell c) ↔ Occupies q c := by
  rw [occupies_comp_iff, Pose.inv_cell_cell]

theorem Pose.adjacent_cells {p : Nat} (g : Pose p) (a b : Cell p)
    (h : Adjacent a b) : Adjacent (g.cell a) (g.cell b) := by
  obtain ⟨j, hj, ht⟩ := h
  refine ⟨g.frame.inverse j, ?_, ?_⟩
  · simp only [Pose.cell, RegisteredFrame.linear, g.frame.right_inverse]
    by_cases hn : g.frame.negative (g.frame.inverse j) = true <;>
      simp [RegisteredFrame.sign, hn] <;> omega
  · intro i hi
    have hp : g.frame.perm i ≠ j := by
      intro he
      apply hi
      have hh := congrArg g.frame.inverse he
      rw [g.frame.left_inverse] at hh
      exact hh
    simp only [Pose.cell, RegisteredFrame.linear]
    rw [ht _ hp]

theorem Pose.face_contact {p : Nat} (g q r : Pose p) (h : FaceContact q r) :
    FaceContact (g.comp q) (g.comp r) := by
  obtain ⟨hd, a, b, hqa, hrb, hab⟩ := h
  constructor
  · intro c ⟨hqc, hrc⟩
    exact hd (g.inv.cell c) ⟨(occupies_comp_iff g q c).mp hqc,
      (occupies_comp_iff g r c).mp hrc⟩
  · exact ⟨g.cell a, g.cell b, (occupies_comp_cell g q a).mpr hqa,
      (occupies_comp_cell g r b).mpr hrb, g.adjacent_cells a b hab⟩

/-- Pull an actual world back through a common full signed pose. -/
def RegisteredWorld.reframe {p : Nat} (W : RegisteredWorld p) (g : Pose p) : RegisteredWorld p where
  tiles := fun q => W.tiles (g.comp q)
  covers := by
    intro c
    obtain ⟨q, hq, hc⟩ := W.covers (g.cell c)
    refine ⟨g.relative q, ?_, ?_⟩
    · rwa [Pose.comp_relative]
    · have hgc : Occupies (g.comp (g.relative q)) (g.cell c) := by
        rw [Pose.comp_relative]
        exact hc
      exact (occupies_comp_cell g (g.relative q) c).mp hgc
  nonoverlap := by
    intro q r hq hr c hqc hrc
    have he := W.nonoverlap (g.comp q) (g.comp r) hq hr (g.cell c)
      ((occupies_comp_cell g q c).mpr hqc) ((occupies_comp_cell g r c).mpr hrc)
    have hqr := Pose.comp_left_cancel g q r he.eq
    subst r
    exact Pose.Same.refl _

theorem RegisteredWorld.reframe_legal (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (g : Pose P.p) : (W.reframe g).Legal P := by
  intro q r hq hr hc
  have h := hl (g.comp q) (g.comp r) hq hr (g.face_contact q r hc)
  rw [Pose.relative_left_cancel] at h
  exact h

theorem RegisteredWorld.reframe_root {p : Nat} (W : RegisteredWorld p) (g : Pose p)
    (hg : W.tiles g) : (W.reframe g).tiles (identityPose p) := by
  change W.tiles (g.comp (identityPose p))
  rwa [Pose.comp_identity]

/-- Normalize any actual tile to the identity without changing actual E legality. -/
def worldLocalPatch (P : Parameters) (W : RegisteredWorld P.p) (hl : W.Legal P)
    (g : Pose P.p) (hg : W.tiles g) : LocalPatch P.p :=
  normalizedLocalPatch P (W.reframe g) (W.reframe_legal P hl g) (W.reframe_root g hg)
    (generated_wall_property P)

/-- Canonical full star centred at an actual tile. Completeness is a concrete
membership assertion, not a structure field or recognition assumption. -/
def CompleteStar (P : Parameters) (W : RegisteredWorld P.p) (g : Pose P.p) : Prop :=
  ∀ A (hA : Proper A), W.tiles (g.comp (incomingPose P A hA))

theorem completeStar_of_incoming (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (g : Pose P.p) (hg : W.tiles g)
    {A : Mask P.p} (hA : Proper A) (hnA : NonemptyMask A)
    (hin : (worldLocalPatch P W hl g hg).incoming A) : CompleteStar P W g := by
  intro B hB
  obtain ⟨q, hq, hsame⟩ := registered_marked_fan P (W.reframe g)
    (W.reframe_legal P hl g) (W.reframe_root g hg) hA hnA hin B hB
  change W.tiles (g.comp q) at hq
  rw [hsame.eq] at hq
  exact hq

/-- An actual complete star supplies every geometric incoming support. -/
theorem completeStar_all_incoming (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (g : Pose P.p) (hg : W.tiles g) (hs : CompleteStar P W g) :
    ∀ A, Proper A → (worldLocalPatch P W hl g hg).incoming A := by
  intro A hA
  refine ⟨incomingPose P A hA, ?_, incoming_support P A hA⟩
  constructor
  · exact hs A hA
  · have hseed := incoming_generated P A hA
    obtain ⟨n, q, r, hq, hr, hc, he⟩ := hseed
    have hc' := q.inv.face_contact q r hc
    have hid : q.inv.comp q = identityPose P.p := q.inv_comp
    rw [hid] at hc'
    change FaceContact (identityPose P.p) (q.relative r) at hc'
    rwa [he.eq] at hc'

end RegisteredPrime
