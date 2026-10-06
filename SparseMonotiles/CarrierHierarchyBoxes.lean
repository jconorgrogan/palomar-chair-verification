module

public import SparseMonotiles.CarrierHierarchyCatalog

@[expose] public section

/-!
Exact occupied-cell and exterior-owner geometry behind the local fan premises.
There is no Euclidean registration assumption hidden here: these statements
concern already registered `Contact.Pose` values and explicitly stated parity.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

@[simp] theorem hole_coordinate {d : ℕ} (p : Pose d) (i : Fin d) :
    hole p i = p.shift i + 1 - if p.negative i then 3 else 0 := by
  cases h : p.negative i <;> simp [hole, Pose.cell, Pose.sign, h] <;> omega

private theorem inverse_at {d : ℕ} (p : Pose d) (x : Cell d) (i : Fin d) :
    p.inverseCell x (p.perm i) =
      if p.negative i then p.shift i - 1 - x i else x i - p.shift i := by
  simp only [Pose.inverseCell, Equiv.symm_apply_apply, Pose.sign]
  cases h : p.negative i <;> simp [h] <;> omega

/-- Every registered chair is exactly its side-two integer box minus one cell. -/
theorem occupies_box_iff {d : ℕ} (p : Pose d) (x : Cell d) :
    Occupies p x ↔
      (∀ i, x i = boxLower p i ∨ x i = boxLower p i + 1) ∧ x ≠ hole p := by
  constructor
  · rintro ⟨h, j, hj⟩
    constructor
    · intro i
      have hi := h (p.perm i)
      rw [inverse_at] at hi
      cases hn : p.negative i <;> simp [boxLower, hn] at hi ⊢ <;> omega
    · intro he
      obtain ⟨i, rfl⟩ := p.perm.surjective j
      rw [inverse_at] at hj
      have hi := congrFun he i
      rw [hole_coordinate] at hi
      cases hn : p.negative i <;> simp [hn] at hi hj <;> omega
  · rintro ⟨h, hn⟩
    constructor
    · intro j
      obtain ⟨i, rfl⟩ := p.perm.surjective j
      rw [inverse_at]
      have hi := h i
      cases hn : p.negative i <;> simp [boxLower, hn] at hi ⊢ <;> omega
    · have hn' : ∃ i, x i ≠ hole p i := by
        by_contra hh
        apply hn
        funext i
        by_contra hi
        exact hh ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hn'
      refine ⟨p.perm i, ?_⟩
      rw [inverse_at]
      have hb := h i
      rw [hole_coordinate] at hi
      cases hn : p.negative i <;> simp [boxLower, hn] at hi hb ⊢ <;> omega

/-- Exterior cell adjacent to occupied root role a on coordinate j. -/
def exterior {d : ℕ} (a : Bits d) (j : Fin d) : Cell d :=
  fun i => bit a i + if i = j then 2 * bit a j - 1 else 0

/-- Same-grid owner of an exterior cell must occupy the corresponding wall box. -/
theorem even_exterior_box {d : ℕ} (p : Pose d) (a : Bits d) (j : Fin d)
    (hp : Occupies p (exterior a j)) (he : ∀ i, boxLower p i % 2 = 0) :
    boxLower p = fun i => if i = j then 2 * (2 * bit a j - 1) else 0 := by
  funext i
  have hb := ((occupies_box_iff p _).mp hp).1 i
  have hi := he i
  by_cases hij : i = j
  · subst i
    cases ha : a j <;> simp [exterior, bit, ha] at hb ⊢ <;> omega
  · cases ha : a i <;> simp [exterior, bit, ha, hij] at hb ⊢ <;> omega

/-- Opposite-grid owner of an exterior cell must occupy the canonical incoming
box. This is the exhaustive two-box argument, not a finite search cutoff. -/
theorem odd_exterior_box {d : ℕ} (p : Pose d) (a : Bits d) (j : Fin d)
    (hp : Occupies p (exterior a j)) (ho : ∀ i, boxLower p i % 2 = 1) :
    boxLower p = fun i => 2 * bit a i - 1 := by
  funext i
  have hb := ((occupies_box_iff p _).mp hp).1 i
  have hi := ho i
  by_cases hij : i = j
  · subst i
    cases ha : a j <;> simp [exterior, bit, ha] at hb ⊢ <;> omega
  · cases ha : a i <;> simp [exterior, bit, ha, hij] at hb ⊢ <;> omega

/-- If the root owns role a, an opposite-grid exterior owner must omit exactly a.
The nonoverlap premise is a single concrete cell, not parent recognizability. -/
theorem odd_exterior_hole {d : ℕ} (p : Pose d) (a : Bits d) (j : Fin d)
    (hp : Occupies p (exterior a j)) (ho : ∀ i, boxLower p i % 2 = 1)
    (hn : ¬ Occupies p (fun i => bit a i)) :
    hole p = fun i => bit a i := by
  have hb := odd_exterior_box p a j hp ho
  by_contra hne
  apply hn
  apply (occupies_box_iff p _).mpr
  constructor
  · intro i
    rw [congrFun hb i]
    cases ha : a i <;> simp [bit, ha]
  · exact fun h => hne h.symm

/-- The canonical incoming pose has the exact opposite-grid box. -/
theorem incoming_boxLower {d : ℕ} (a : Bits d) (σ : Equiv.Perm (Fin d)) :
    boxLower (incomingPose a σ) = fun i => 2 * bit a i - 1 := by
  funext i
  cases h : a i <;> simp [boxLower, incomingPose, bit, h]

/-- Its missing cell is the occupied root role itself. -/
theorem incoming_hole {d : ℕ} (a : Bits d) (σ : Equiv.Perm (Fin d)) :
    hole (incomingPose a σ) = fun i => bit a i := by
  funext i
  rw [hole_coordinate]
  cases h : a i <;> simp [incomingPose, bit, h]

theorem incoming_owns_exterior {d : ℕ} (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (j : Fin d) :
    Occupies (incomingPose a σ) (exterior a j) := by
  rw [occupies_box_iff, incoming_boxLower, incoming_hole]
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      cases h : a j <;> simp [exterior, bit, h]
    · cases h : a i <;> simp [exterior, bit, h, hij]
  · intro h
    have hj := congrFun h j
    cases h : a j <;> simp [exterior, bit, h] at hj

theorem gauge_hole_eq {d : ℕ} {r : Equiv.Perm (Fin d)}
    {p q : Pose d} (h : GaugeRel r p q) : hole p = hole q := by
  rcases h with rfl | rfl
  · rfl
  · funext i
    simp [hole_coordinate, rightGauge]

/-- A right unsigned gauge leaves carrier occupancy unchanged. This is not a
claim about the body's full symmetry group. -/
theorem rightGauge_occupies {d : ℕ} (r : Equiv.Perm (Fin d))
    (p : Pose d) (x : Cell d) : Occupies (rightGauge r p) x ↔ Occupies p x := by
  rw [occupies_box_iff, occupies_box_iff]
  have hh : hole (rightGauge r p) = hole p := by
    funext i
    simp [hole_coordinate, rightGauge]
  rw [hh]
  rfl

theorem gauge_occupies_iff {d : ℕ} {r : Equiv.Perm (Fin d)}
    {p q : Pose d} (h : GaugeRel r p q) (x : Cell d) :
    Occupies p x ↔ Occupies q x := by
  rcases h with rfl | rfl
  · rfl
  · exact (rightGauge_occupies r p x).symm

/-- The incoming role is recovered from its actual box and missing cell, so
there cannot be competing role labels for a physical incoming predecessor. -/
theorem role_of_box_and_hole {d : ℕ} {p : Pose d} {a : Bits d}
    (hb : boxLower p = fun i => 2 * bit a i - 1)
    (hh : hole p = fun i => bit a i) : p.negative = a := by
  funext i
  have hb' := congrFun hb i
  have hh' := congrFun hh i
  rw [hole_coordinate] at hh'
  cases hp : p.negative i <;> cases ha : a i <;>
    simp [boxLower, bit, hp, ha] at hb' hh' ⊢ <;> omega

#print axioms occupies_box_iff
#print axioms even_exterior_box
#print axioms odd_exterior_hole
end SparseMonotiles.CarrierHierarchy
