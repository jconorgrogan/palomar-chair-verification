module
public import RegisteredPrime.FiniteSupertiles
@[expose] public section
namespace RegisteredPrime
theorem not_occupies_hole {p : Nat} (q : Pose p) : ¬ Occupies q (hole q) := by
  intro h
  have hu := (occupies_inverse_iff q (hole q)).mp h
  have he : q.inv.cell (hole q) = (fun _ => (1 : Int)) := q.inv_cell_cell _
  rw [he] at hu
  obtain ⟨i, hi⟩ := hu.2
  change (1 : Int) = 0 at hi
  omega
theorem central_owns_outer_hole (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    Occupies (arithmeticChild P .central) (hole (arithmeticChild P (.outer A hA))) := by
  have he : hole (arithmeticChild P (.outer A hA)) = fun i => 1 + bit (A i) :=
    outer_cell_hole P A hA
  rw [he]
  exact (central_image_iff P _).mpr (central_fills_outer_hole A hA)
theorem refined_central_owns_outer_hole (P : Parameters) (q : Pose P.p)
    (A : Mask P.p) (hA : Proper A) :
    Occupies (refine P q .central) (hole (refine P q (.outer A hA))) := by
  change Occupies ((doubleAnchor q).comp (arithmeticChild P .central))
    (((doubleAnchor q).comp (arithmeticChild P (.outer A hA))).cell (fun _ => 1))
  rw [Pose.comp_cell, occupies_comp_iff, Pose.inv_cell_cell]
  exact central_owns_outer_hole P A hA
theorem outer_leaf_owner_is_centre (P : Parameters) (n : Nat)
    (root parent owner : Pose P.p) (A : Mask P.p) (hA : Proper A)
    (hp : Descendant P n root parent) (ho : Descendant P (n + 1) root owner)
    (hown : Occupies owner (hole (refine P parent (.outer A hA)))) :
    (refine P parent .central).Same owner := by
  have hc : Descendant P (n + 1) root (refine P parent .central) :=
    (descendant_succ_iff P n root _).mpr ⟨parent, .central, hp, Pose.Same.refl _⟩
  exact finite_supertile_unique_owner P (n + 1) root _ owner hc ho _
    (refined_central_owns_outer_hole P parent A hA) hown
theorem central_hole_floor (P : Parameters) (q : Pose P.p) :
    floorCell (hole (refine P q .central)) = hole q := by
  funext i
  simp only [floorCell, hole_from_box, refine_central_lower, refine_central_negative]
  cases hn : q.frame.negative i <;> simp [bit, hn] <;> omega
theorem central_leaf_owner_parent (P : Parameters) (q r : Pose P.p) (a : Role P.p)
    (hown : Occupies (refine P r a) (hole (refine P q .central))) : Occupies r (hole q) := by
  have h := refine_occupies_parent P r a _ hown
  rw [central_hole_floor] at h
  exact h
theorem descendant_hole_owner_disjoint (P : Parameters) (n : Nat) (root q r : Pose P.p)
    (hq : Descendant P n root q) (hr : Descendant P n root r)
    (hown : Occupies r (hole q)) : Disjoint q r := by
  intro c ⟨hqc, hrc⟩
  have hs := finite_supertile_unique_owner P n root q r hq hr c hqc hrc
  exact not_occupies_hole q (hs.symm.occupies _ hown)
theorem hole_owner_face_contact {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (hd : Disjoint q r) (hown : Occupies r (hole q)) : FaceContact q r := by
  classical
  let j : Fin p := ⟨0, by omega⟩
  let c : Cell p := fun i => if i = j then boxLower q i + bit (q.frame.negative i) else hole q i
  have hc : Occupies q c := by
    apply (occupies_box_iff q c).mpr
    constructor
    · intro i
      by_cases hi : i = j
      · subst i
        cases hn : q.frame.negative j <;> simp [c, bit, hn]
      · rw [show c i = hole q i by simp [c, hi], hole_from_box]
        cases hn : q.frame.negative i <;> simp [bit, hn]
    · intro he
      have hj := congrFun he j
      rw [hole_from_box] at hj
      cases hn : q.frame.negative j <;> simp [c, bit, hn] at hj <;> omega
  refine ⟨hd, c, hole q, hc, hown, j, ?_, ?_⟩
  · rw [show c j = boxLower q j + bit (q.frame.negative j) by simp [c], hole_from_box]
    cases hn : q.frame.negative j <;> simp [bit, hn] <;> omega
  · intro i hi
    simp [c, hi]
theorem descendant_hole_contact_generated (P : Parameters) (n : Nat) (root q r : Pose P.p)
    (hroot : root = identityPose P.p)
    (hq : Descendant P n root q) (hr : Descendant P n root r)
    (hown : Occupies r (hole q)) : GeneratedContact P (q.relative r) := by
  subst root
  exact ⟨n, q, r, hq, hr,
    hole_owner_face_contact (P.prime.three_le P.odd) q r
      (descendant_hole_owner_disjoint P n _ q r hq hr hown) hown,
    Pose.Same.refl _⟩
end RegisteredPrime
