module
public import RegisteredPrime.CoarseCellWalls
@[expose] public section
namespace RegisteredPrime

/-- A directly tested condition on actual occupied coarse-cell face edges. -/
def RootCellWallTest {p : Nat} (e : Pose p) : Prop :=
  ∀ x y : Cell p, Occupies (identityPose p) x → Occupies e y →
    ∀ j : Fin p, (x j = y j + 1 ∨ y j = x j + 1) →
      (∀ i, i ≠ j → x i = y i) →
      WallMaskAt (fun i => xor (cellDigit (identityPose p) x i) (cellDigit e y i)) j

/-- Equal coarse box digits measure the box displacement by y-x. -/
theorem root_digits_xor_false {p : Nat} (e : Pose p) (x y : Cell p)
    (hx : Occupies (identityPose p) x) (hy : Occupies e y) (i : Fin p)
    (hxor : xor (cellDigit (identityPose p) x i) (cellDigit e y i) = false) :
    boxLower e i = y i - x i := by
  have hxb := cellDigit_bit (identityPose p) x hx i
  have hyb := cellDigit_bit e y hy i
  change bit (cellDigit (identityPose p) x i) = x i - 0 at hxb
  simp only [Int.sub_zero] at hxb
  cases ha : cellDigit (identityPose p) x i <;> cases hb : cellDigit e y i <;>
    simp [ha, hb, bit] at hxor hxb hyb <;> omega

/-- Unequal coarse box digits measure the box displacement by x+y-1. -/
theorem root_digits_xor_true {p : Nat} (e : Pose p) (x y : Cell p)
    (hx : Occupies (identityPose p) x) (hy : Occupies e y) (i : Fin p)
    (hxor : xor (cellDigit (identityPose p) x i) (cellDigit e y i) = true) :
    boxLower e i = y i + x i - 1 := by
  have hxb := cellDigit_bit (identityPose p) x hx i
  have hyb := cellDigit_bit e y hy i
  change bit (cellDigit (identityPose p) x i) = x i - 0 at hxb
  simp only [Int.sub_zero] at hxb
  cases ha : cellDigit (identityPose p) x i <;> cases hb : cellDigit e y i <;>
    simp [ha, hb, bit] at hxor hxb hyb <;> omega

/-- A single actual coarse contact and its wall-mask test suffice: its boxes
are canonically adjacent, or their intersection consists of one unit cell.
This excludes all transverse shifts and all two-cell overlaps uniformly. -/
theorem root_contact_box_cases {p : Nat} (hp : 3 ≤ p) (e : Pose p)
    (hc : FaceContact (identityPose p) e) (htest : RootCellWallTest e) :
    (∃ j side, boxLower e = wallBox j side) ∨
      (∀ i, boxLower e i = 1 ∨ boxLower e i = -1) := by
  obtain ⟨hd, x, y, hx, hy, j, hj, htrans⟩ := hc
  obtain ⟨color, hm⟩ := htest x y hx hy j hj htrans
  have hxb := ((identity_occupies x).mp hx).1
  cases color with
  | false =>
    have hzero : ∀ i, i ≠ j → boxLower e i = 0 := by
      intro i hij
      have hmask : xor (cellDigit (identityPose p) x i) (cellDigit e y i) = false := by
        simpa [hij] using hm i
      have hi := root_digits_xor_false e x y hx hy i hmask
      have ht := htrans i hij
      omega
    have haxis : boxLower e j = -2 ∨ boxLower e j = 0 ∨ boxLower e j = 2 := by
      have hmask : xor (cellDigit (identityPose p) x j) (cellDigit e y j) = true := by
        simpa using hm j
      have hi := root_digits_xor_true e x y hx hy j hmask
      have hb := hxb j
      omega
    rcases haxis with hneg | hsame | hpos
    · left
      refine ⟨j, false, ?_⟩
      funext i
      by_cases hij : i = j
      · subst i
        simp [wallBox, hneg]
      · simp [wallBox, hij, hzero i hij]
    · have hbox : boxLower (identityPose p) = boxLower e := by
        funext i
        by_cases hij : i = j
        · subst i
          change (0 : Int) = boxLower e j
          exact hsame.symm
        · change (0 : Int) = boxLower e i
          exact (hzero i hij).symm
      let k : Fin p := ⟨0, by omega⟩
      let l : Fin p := ⟨1, by omega⟩
      have hkl : k ≠ l := by intro he; have := congrArg Fin.val he; simp [k, l] at this
      obtain ⟨c, hroot, he⟩ := same_box_overlap (identityPose p) e k l hkl hbox
      exact False.elim (hd c ⟨hroot, he⟩)
    · left
      refine ⟨j, true, ?_⟩
      funext i
      by_cases hij : i = j
      · subst i
        simp [wallBox, hpos]
      · simp [wallBox, hij, hzero i hij]
  | true =>
    right
    intro i
    by_cases hij : i = j
    · subst i
      have hmask : xor (cellDigit (identityPose p) x j) (cellDigit e y j) = false := by
        simpa using hm j
      have hi := root_digits_xor_false e x y hx hy j hmask
      omega
    · have hmask : xor (cellDigit (identityPose p) x i) (cellDigit e y i) = true := by
        simpa [hij] using hm i
      have hi := root_digits_xor_true e x y hx hy i hmask
      have ht := htrans i hij
      have hb := hxb i
      omega

/-- If a contacting chair box begins at ones, the actual neighboring chair
owns the root hole. In particular the case where both omit their common
cell cannot be a face contact. -/
theorem positive_diagonal_contact_owns_root_hole {p : Nat} (e : Pose p)
    (hb : boxLower e = (fun _ => 1)) (hc : FaceContact (identityPose p) e) :
    Occupies e (fun _ => 1) := by
  obtain ⟨_, x, y, hx, hy, j, hj, ht⟩ := hc
  have hxu := (identity_occupies x).mp hx
  have hyb := ((occupies_box_iff e y).mp hy).1
  obtain ⟨k, hk⟩ := hxu.2
  have hkj : k = j := by
    apply Classical.byContradiction
    intro hne
    have he := ht k hne
    have hyk := hyb k
    rw [congrFun hb k] at hyk
    omega
  subst k
  have hyone : y = fun _ => 1 := by
    funext i
    have hyi := hyb i
    rw [congrFun hb i] at hyi
    by_cases hij : i = j
    · subst i
      omega
    · have hxi := hxu.1 i
      have he := ht i hij
      omega
  rwa [hyone] at hy

/-- With one-cell box intersection, disjointness and actual face contact
force one of the two directed hole-support geometries. -/
theorem one_cell_contact_hole_cases {p : Nat} (e : Pose p)
    (hc : FaceContact (identityPose p) e)
    (hb : ∀ i, boxLower e i = 1 ∨ boxLower e i = -1) :
    (boxLower e = (fun _ => 1) ∧ Occupies e (fun _ => 1)) ∨
      ∃ A, ∃ _hA : Proper A, IncomingSupport e A := by
  classical
  let A : Mask p := fun i => decide (boxLower e i = 1)
  let c : Cell p := fun i => bit (A i)
  have hdelta : ∀ i, boxLower e i = 2 * bit (A i) - 1 := by
    intro i
    rcases hb i with hi | hi <;> simp [A, bit, hi]
  have hcbox : ∀ i, c i = boxLower e i ∨ c i = boxLower e i + 1 := by
    intro i
    rw [hdelta i]
    cases ha : A i <;> simp [c, bit, ha]
  by_cases hcone : c = (fun _ => 1)
  · left
    have hbone : boxLower e = (fun _ => 1) := by
      funext i
      have hi := congrFun hcone i
      change bit (A i) = 1 at hi
      rw [hdelta i, hi]
      rfl
    exact ⟨hbone, positive_diagonal_contact_owns_root_hole e hbone hc⟩
  · right
    have hA : Proper A := by
      apply Classical.byContradiction
      intro hnA
      apply hcone
      funext i
      cases hi : A i
      · exact False.elim (hnA ⟨i, hi⟩)
      · simp [c, bit, hi]
    have hhole : c = hole e := by
      apply Classical.byContradiction
      intro hne
      have he : Occupies e c := (occupies_box_iff e c).mpr ⟨hcbox, hne⟩
      exact hc.1 c ⟨root_owns_role A hA, he⟩
    refine ⟨A, hA, funext hdelta, ?_⟩
    exact hhole.symm

/-- Complete noncanonical coarse-geometry exclusion from actual cell-wall
tests, with no contact census, hierarchy, or full-world extension premise. -/
theorem coarse_geometry_cases_of_cell_wall_test {p : Nat} (hp : 3 ≤ p) (e : Pose p)
    (hc : FaceContact (identityPose p) e) (htest : RootCellWallTest e) :
    (∃ j side, boxLower e = wallBox j side) ∨
      (boxLower e = (fun _ => 1) ∧ Occupies e (fun _ => 1)) ∨
      ∃ A, ∃ _hA : Proper A, IncomingSupport e A := by
  rcases root_contact_box_cases hp e hc htest with hw | hh
  · exact Or.inl hw
  · exact Or.inr (one_cell_contact_hole_cases e hc hh)

/-- The required cell-wall tests come from explicit recognition of actual
fine contacts. One direction of fine legality already suffices for geometry. -/
theorem coarse_geometry_cases_of_child_recognition (P : Parameters) (e : Pose P.p)
    (hc : FaceContact (identityPose P.p) e)
    (hl : WeakRecognition.ChildRecognition P (identityPose P.p) (doubleAnchor e)) :
    (∃ j side, boxLower e = wallBox j side) ∨
      (boxLower e = (fun _ => 1) ∧ Occupies e (fun _ => 1)) ∨
      ∃ A, ∃ _hA : Proper A, IncomingSupport e A := by
  apply coarse_geometry_cases_of_cell_wall_test (P.prime.three_le P.odd) e hc
  intro x y hx hy j hj ht
  have hchild : WeakRecognition.ChildRecognition P (doubleAnchor (identityPose P.p))
      (doubleAnchor e) := by simpa only [doubleAnchor_identity] using hl
  exact child_recognition_coarse_cell_wall_test P (identityPose P.p) e hchild
    x y hx hy j hj ht


/-- Constant box-lower parity is the same registered parity invariant. -/
theorem uniform_parity_of_box_lower {p : Nat} (e : Pose p) (color : Bool)
    (h : ∀ i, boxLower e i % 2 = bit color) : e.UniformParity := by
  refine ⟨color, fun i => ?_⟩
  have hi := h i
  simp only [boxLower] at hi
  omega

/-- Geometry alone supplies the coarse registered parity clause. -/
theorem coarse_parity_of_child_recognition (P : Parameters) (e : Pose P.p)
    (hc : FaceContact (identityPose P.p) e)
    (hl : WeakRecognition.ChildRecognition P (identityPose P.p) (doubleAnchor e)) :
    e.UniformParity := by
  rcases coarse_geometry_cases_of_child_recognition P e hc hl with
    ⟨j, side, hb⟩ | ⟨hb, _⟩ | ⟨A, hA, hin⟩
  · apply uniform_parity_of_box_lower e false
    intro i
    rw [congrFun hb i]
    cases side <;> by_cases hij : i = j <;> simp [wallBox, bit, hij]
  · apply uniform_parity_of_box_lower e true
    intro i
    rw [congrFun hb i]
    rfl
  · apply uniform_parity_of_box_lower e true
    intro i
    rw [congrFun hin.1 i]
    cases A i <;> simp [bit]


/-- The even coarse contacts are precisely in the canonical-box branch. -/
theorem even_coarse_contact_canonical_box (P : Parameters) (e : Pose P.p)
    (hc : FaceContact (identityPose P.p) e)
    (hl : WeakRecognition.ChildRecognition P (identityPose P.p) (doubleAnchor e))
    (he : ∀ i, e.anchor i % 2 = 0) : ∃ j side, boxLower e = wallBox j side := by
  have hbpar := uniform_parity_box e false he
  let i : Fin P.p := ⟨0, by have := P.prime.two_le; omega⟩
  rcases coarse_geometry_cases_of_child_recognition P e hc hl with
    hw | ⟨hb, _⟩ | ⟨A, _, hin⟩
  · exact hw
  · have hi := hbpar i
    rw [congrFun hb i] at hi
    simp [bit] at hi
  · have hi := hbpar i
    rw [congrFun hin.1 i] at hi
    cases ha : A i <;> simp [bit, ha] at hi

end RegisteredPrime
