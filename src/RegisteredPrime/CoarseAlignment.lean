module
public import RegisteredPrime.CoarseGeometry
@[expose] public section
namespace RegisteredPrime

theorem doubled_occupies_comp_iff {p : Nat} (g t : Pose p) (c : Cell p) :
    DoubledOccupies (g.comp t) c ↔ DoubledOccupies t (g.inv.cell c) := by
  unfold DoubledOccupies
  rw [Pose.inv_compose, Pose.comp_cell]

theorem doubled_occupies_comp_cell {p : Nat} (g t : Pose p) (c : Cell p) :
    DoubledOccupies (g.comp t) (g.cell c) ↔ DoubledOccupies t c := by
  rw [doubled_occupies_comp_iff, Pose.inv_cell_cell]

theorem Pose.doubled_face_contact {p : Nat} (g t u : Pose p)
    (h : DoubledFaceContact t u) : DoubledFaceContact (g.comp t) (g.comp u) := by
  obtain ⟨hd, a, b, hta, hub, hab⟩ := h
  constructor
  · intro c ⟨htc, huc⟩
    exact hd (g.inv.cell c) ⟨(doubled_occupies_comp_iff g t c).mp htc,
      (doubled_occupies_comp_iff g u c).mp huc⟩
  · exact ⟨g.cell a, g.cell b, (doubled_occupies_comp_cell g t a).mpr hta,
      (doubled_occupies_comp_cell g u b).mpr hub, g.adjacent_cells a b hab⟩

/-- An odd change of grid origin moves each even-grid cell boundary into the
interior of a cell of the shifted grid, in either orientation. -/
theorem odd_offset_floor {s x y : Int} (hs : s % 2 = 1)
    (hxy : x = y + 1 ∨ y = x + 1) :
    x / 2 = y / 2 ∨
      ((x - s) / 2 = (y - s) / 2 ∧ (s - 1 - x) / 2 = (s - 1 - y) / 2) := by
  by_cases h : x / 2 = y / 2
  · exact Or.inl h
  · right
    constructor <;> omega

/-- Along a common face, if one dyadic grid changes coarse cell, a grid with
odd relative origin cannot change coarse cell on that face. -/
theorem adjacent_floor_alternative {p : Nat} (e : Pose p) (a b : Cell p)
    (hab : Adjacent a b) (ho : ∀ i, e.anchor i % 2 = 1) :
    floorCell a = floorCell b ∨ floorCell (e.inv.cell a) = floorCell (e.inv.cell b) := by
  obtain ⟨j, hj, ht⟩ := hab
  rcases odd_offset_floor (ho j) hj with he | ⟨hp, hn⟩
  · left
    funext i
    by_cases hij : i = j
    · subst i
      exact he
    · exact congrArg (fun z : Int => z / 2) (ht i hij)
  · right
    funext k
    let i := e.frame.inverse k
    have hik : e.frame.perm i = k := e.frame.right_inverse k
    change e.inv.cell a k / 2 = e.inv.cell b k / 2
    rw [← hik, inverse_at, inverse_at]
    by_cases hij : i = j
    · rw [hij]
      cases hneg : e.frame.negative j
      · exact hp
      · exact hn
    · rw [ht i hij]

/-- Disjoint doubled chairs cannot touch across a face when their relative
anchor is odd in every coordinate. This is exact carrier geometry, independent
of arithmetic-frame restrictions. -/
theorem odd_offset_doubled_contact_false {p : Nat} (e : Pose p)
    (hc : DoubledFaceContact (identityPose p) e) (ho : ∀ i, e.anchor i % 2 = 1) : False := by
  obtain ⟨hd, a, b, ha, hb, hab⟩ := hc
  have ha' : DoubledChairCell a := by
    simpa only [DoubledOccupies, identity_inverse_cell] using ha
  rcases adjacent_floor_alternative e a b hab ho with he | he
  · have hu := (doubled_iff_unit_floor a).mp ha'
    rw [he] at hu
    have hd' := (doubled_iff_unit_floor b).mpr hu
    have hroot : DoubledOccupies (identityPose p) b := by
      simpa only [DoubledOccupies, identity_inverse_cell] using hd'
    exact hd b ⟨hroot, hb⟩
  · have hu := (doubled_iff_unit_floor (e.inv.cell b)).mp hb
    rw [← he] at hu
    exact hd a ⟨ha, (doubled_iff_unit_floor (e.inv.cell a)).mpr hu⟩

/-- Exact generated child legality and geometric disjointness force adjacent
parent anchors to agree modulo two, without assuming coarse E-legality. -/
theorem child_legal_parent_even (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) (hl : ChildLegal P t u) :
    ∀ i, (t.relative u).anchor i % 2 = 0 := by
  obtain ⟨b, hb⟩ := child_legal_parent_constant_parity P t u hc hl
  cases b with
  | false => exact hb
  | true =>
    have hn := t.inv.doubled_face_contact t u hc
    rw [Pose.inv_comp] at hn
    change DoubledFaceContact (identityPose P.p) (t.relative u) at hn
    exact False.elim (odd_offset_doubled_contact_false _ hn hb)

/-- The scale-aligned child-legal coarse-contact predicate. It is kept separate
from GeneratedContact: identifying these languages is a further theorem. -/
def CoarseContact (P : Parameters) (e : Pose P.p) : Prop :=
  DoubledFaceContact (identityPose P.p) (doubleAnchor e) ∧
  ChildLegal P (identityPose P.p) (doubleAnchor e)

def halfAnchor {p : Nat} (q : Pose p) : Pose p where
  frame := q.frame
  anchor := fun i => q.anchor i / 2

theorem double_halfAnchor {p : Nat} (q : Pose p) (he : ∀ i, q.anchor i % 2 = 0) :
    doubleAnchor (halfAnchor q) = q := by
  apply Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, fun i => ?_⟩
  have hi := he i
  change 2 * (q.anchor i / 2) = q.anchor i
  omega

/-- Common rigid re-registration preserves the exact child-contact predicate. -/
theorem ChildLegal.reframe (P : Parameters) (g t u : Pose P.p)
    (hl : ChildLegal P t u) : ChildLegal P (g.comp t) (g.comp u) := by
  intro a b hc
  have hc' : FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) := by
    have h := g.inv.face_contact _ _ hc
    simpa only [← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp] using h
  rw [Pose.comp_assoc, Pose.comp_assoc, Pose.relative_left_cancel]
  exact hl a b hc'

/-- A recognized actual parent contact has a scale-aligned representative in
CL(E), defined by every genuine cross-child contact rather than a catalog. -/
theorem CompleteParent.coarse_contact (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) (hc : DoubledFaceContact t u) :
    CoarseContact P (halfAnchor (t.relative u)) := by
  have hchild := CompleteParent.child_legal P W hl t u ht hu
  have he := child_legal_parent_even P t u hc hchild
  unfold CoarseContact
  rw [double_halfAnchor _ he]
  constructor
  · have h := t.inv.doubled_face_contact t u hc
    rwa [Pose.inv_comp] at h
  · have h := ChildLegal.reframe P t.inv t u hchild
    rwa [Pose.inv_comp] at h

end RegisteredPrime
