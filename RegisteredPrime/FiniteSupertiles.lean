module
public import RegisteredPrime.HoleCarryArithmetic
@[expose] public section
namespace RegisteredPrime
theorem RegisteredFrame.ext_data {p : Nat} (F G : RegisteredFrame p)
    (hp : F.perm = G.perm) (hn : F.negative = G.negative) : F = G := by
  have hi : F.inverse = G.inverse := by
    funext i
    calc
      F.inverse i = F.inverse (G.perm (G.inverse i)) := by rw [G.right_inverse]
      _ = F.inverse (F.perm (G.inverse i)) := by rw [hp]
      _ = G.inverse i := F.left_inverse _
  cases F
  cases G
  cases hp
  cases hn
  cases hi
  rfl
theorem Pose.Same.eq {p : Nat} {q r : Pose p} (h : q.Same r) : q = r := by
  have hf := RegisteredFrame.ext_data q.frame r.frame (funext h.1) (funext h.2.1)
  have ha := funext h.2.2
  cases q
  cases r
  cases hf
  cases ha
  rfl
theorem Pose.Same.refl {p : Nat} (q : Pose p) : q.Same q :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
theorem Pose.cell_injective {p : Nat} (q : Pose p) (a b : Cell p)
    (h : q.cell a = q.cell b) : a = b := by
  have he := congrArg q.inv.cell h
  simpa using he
theorem occupies_comp_iff {p : Nat} (q r : Pose p) (c : Cell p) :
    Occupies (q.comp r) c ↔ Occupies r (q.inv.cell c) := by
  constructor
  · rintro ⟨b, hb, he⟩
    rw [Pose.comp_cell] at he
    have hx := congrArg q.inv.cell he
    refine ⟨b, hb, ?_⟩
    simpa using hx
  · rintro ⟨b, hb, he⟩
    refine ⟨b, hb, ?_⟩
    rw [Pose.comp_cell, he, q.cell_inv_cell]
def floorCell {p : Nat} (c : Cell p) : Cell p := fun i => c i / 2
def doubleAnchor {p : Nat} (q : Pose p) : Pose p where
  frame := q.frame
  anchor := fun i => 2 * q.anchor i
theorem doubled_iff_unit_floor {p : Nat} (c : Cell p) :
    DoubledChairCell c ↔ UnitChairCell (floorCell c) := by
  constructor
  · rintro ⟨h, j, hj⟩
    refine ⟨fun i => ?_, j, ?_⟩
    · have hi := h i
      simp only [floorCell]
      omega
    · have hi := h j
      simp only [floorCell]
      omega
  · rintro ⟨h, j, hj⟩
    refine ⟨fun i => ?_, j, ?_⟩
    · have hi := h i
      simp only [floorCell] at hi
      omega
    · simp only [floorCell] at hj
      omega
theorem doubleAnchor_cell_floor {p : Nat} (q : Pose p) (c : Cell p) :
    floorCell ((doubleAnchor q).cell c) = q.cell (floorCell c) := by
  funext i
  simp only [floorCell, doubleAnchor, Pose.cell, RegisteredFrame.linear,
    RegisteredFrame.sign, bit]
  by_cases hn : q.frame.negative i = true <;> simp [hn] <;> omega
theorem refine_occupies_parent (P : Parameters) (q : Pose P.p) (a : Role P.p)
    (c : Cell P.p) (hc : Occupies (refine P q a) c) : Occupies q (floorCell c) := by
  change Occupies ((doubleAnchor q).comp (arithmeticChild P a)) c at hc
  have hchild := (occupies_comp_iff (doubleAnchor q) (arithmeticChild P a) c).mp hc
  have hd : DoubledChairCell ((doubleAnchor q).inv.cell c) :=
    (exact_child_cover P _).mpr ⟨a, hchild⟩
  have hu := (doubled_iff_unit_floor _).mp hd
  refine ⟨floorCell ((doubleAnchor q).inv.cell c), hu, ?_⟩
  rw [← doubleAnchor_cell_floor, Pose.cell_inv_cell]
theorem parent_occupies_refinement (P : Parameters) (q : Pose P.p) (c : Cell P.p)
    (hq : Occupies q (floorCell c)) : ∃ a, Occupies (refine P q a) c := by
  let x := (doubleAnchor q).inv.cell c
  have he : q.cell (floorCell x) = floorCell c := by
    rw [← doubleAnchor_cell_floor, Pose.cell_inv_cell]
  have hinv : q.inv.cell (floorCell c) = floorCell x := by
    rw [← he, Pose.inv_cell_cell]
  have hu : UnitChairCell (floorCell x) := by
    rw [← hinv]
    exact (occupies_inverse_iff q (floorCell c)).mp hq
  have hd := (doubled_iff_unit_floor x).mpr hu
  obtain ⟨a, ha⟩ := (exact_child_cover P x).mp hd
  refine ⟨a, ?_⟩
  change Occupies ((doubleAnchor q).comp (arithmeticChild P a)) c
  exact (occupies_comp_iff (doubleAnchor q) (arithmeticChild P a) c).mpr ha
theorem refine_occupied_role_unique (P : Parameters) (q : Pose P.p)
    (a b : Role P.p) (c : Cell P.p)
    (ha : Occupies (refine P q a) c) (hb : Occupies (refine P q b) c) : a = b := by
  change Occupies ((doubleAnchor q).comp (arithmeticChild P a)) c at ha
  change Occupies ((doubleAnchor q).comp (arithmeticChild P b)) c at hb
  exact exact_child_unique P ((doubleAnchor q).inv.cell c) a b
    ((occupies_comp_iff _ _ _).mp ha) ((occupies_comp_iff _ _ _).mp hb)
theorem descendant_succ_iff (P : Parameters) (n : Nat) (root t : Pose P.p) :
    Descendant P (n + 1) root t ↔
      ∃ parent a, Descendant P n root parent ∧ (refine P parent a).Same t := by
  induction n generalizing root with
  | zero =>
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨root, a, Pose.Same.refl _, ha⟩
    · rintro ⟨parent, a, hp, ht⟩
      have he : root = parent := Pose.Same.eq hp
      subst parent
      exact ⟨a, ht⟩
  | succ n ih =>
    constructor
    · rintro ⟨b, ht⟩
      obtain ⟨parent, a, hp, hlast⟩ := (ih (refine P root b)).mp ht
      exact ⟨parent, a, ⟨b, hp⟩, hlast⟩
    · rintro ⟨parent, a, ⟨b, hp⟩, hlast⟩
      exact ⟨b, (ih (refine P root b)).mpr ⟨parent, a, hp, hlast⟩⟩
theorem finite_supertile_unique_owner (P : Parameters) (n : Nat) (root q r : Pose P.p)
    (hq : Descendant P n root q) (hr : Descendant P n root r) (c : Cell P.p)
    (hqc : Occupies q c) (hrc : Occupies r c) : q.Same r := by
  induction n generalizing q r c with
  | zero => exact Pose.Same.trans (Pose.Same.symm hq) hr
  | succ n ih =>
    obtain ⟨parent, a, hp, hpa⟩ := (descendant_succ_iff P n root q).mp hq
    obtain ⟨other, b, ho, hob⟩ := (descendant_succ_iff P n root r).mp hr
    have hac := hpa.symm.occupies c hqc
    have hbc := hob.symm.occupies c hrc
    have he := ih parent other hp ho (floorCell c)
      (refine_occupies_parent P parent a c hac) (refine_occupies_parent P other b c hbc)
    have heq := he.eq
    subst other
    have hab := refine_occupied_role_unique P parent a b c hac hbc
    subst b
    exact hpa.symm.trans hob
end RegisteredPrime
