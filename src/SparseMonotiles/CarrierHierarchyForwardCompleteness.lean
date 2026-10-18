module

public import SparseMonotiles.CarrierHierarchyForwardChecker

@[expose] public section

/-! Completeness of the bounded separation/contact test. A nonempty
intersection of two chair boxes can contain at most their two omitted cells
when the actual chairs are disjoint. Three corner cells rule out every other
case. This justifies using the arithmetic checker as an exact contact decision. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem raised_ne_base {d : ℕ} (j : Fin d) (c : Cell d) : raisedCell j c ≠ c := by
  intro h
  have hi := congrFun h j
  simp [raisedCell, unitAxis] at hi

private theorem raised_ne_raised {d : ℕ} {j k : Fin d} (hjk : j ≠ k) (c : Cell d) :
    raisedCell j c ≠ raisedCell k c := by
  intro h
  have hi := congrFun h j
  simp [raisedCell, unitAxis, hjk] at hi

theorem cellSeparated_complete {d : ℕ} (p q : Pose d)
    (hno : ∀ c, ¬ (Occupies p c ∧ Occupies q c)) : CellSeparated p q := by
  classical
  by_cases hgap : ∃ i, boxLower p i + 1 < boxLower q i ∨ boxLower q i + 1 < boxLower p i
  · exact Or.inl (Or.inl hgap)
  have hwidth : ∀ i, intersectionLower p q i ≤ intersectionUpper p q i ∧
      intersectionUpper p q i ≤ intersectionLower p q i + 1 := by
    intro i
    have hn : ¬ (boxLower p i + 1 < boxLower q i ∨ boxLower q i + 1 < boxLower p i) :=
      fun h => hgap ⟨i, h⟩
    constructor
    · simp only [intersectionLower, intersectionUpper, max_le_iff, le_min_iff]
      omega
    · have hu := min_le_left (boxLower p i + 1) (boxLower q i + 1)
      have hl := le_max_left (boxLower p i) (boxLower q i)
      change min _ _ ≤ max _ _ + 1
      omega
  have at_hole : ∀ c : Cell d,
      (∀ i, intersectionLower p q i ≤ c i ∧ c i ≤ intersectionUpper p q i) →
      c = hole p ∨ c = hole q := by
    intro c hc
    by_cases hp : c = hole p
    · exact Or.inl hp
    right
    by_contra hq
    apply hno c
    constructor
    · apply (occupies_box_iff p c).mpr
      refine ⟨?_, hp⟩
      intro i
      have hlo := (max_le_iff.mp (hc i).1).1
      have hhi := (le_min_iff.mp (hc i).2).1
      omega
    · apply (occupies_box_iff q c).mpr
      refine ⟨?_, hq⟩
      intro i
      have hlo := (max_le_iff.mp (hc i).1).2
      have hhi := (le_min_iff.mp (hc i).2).2
      omega
  have hbase := at_hole (intersectionLower p q) (fun i => ⟨le_rfl, (hwidth i).1⟩)
  by_cases hfixed : ∀ i, intersectionUpper p q i = intersectionLower p q i
  · left
    rcases hbase with hp | hq
    · exact Or.inr (Or.inl (fun i => ⟨(hfixed i).symm, congrFun hp i⟩))
    · exact Or.inr (Or.inr (fun i => ⟨(hfixed i).symm, congrFun hq i⟩))
  have hj : ∃ j, intersectionUpper p q j = intersectionLower p q j + 1 := by
    push_neg at hfixed
    obtain ⟨j, hj⟩ := hfixed
    exact ⟨j, by have hw := hwidth j; omega⟩
  obtain ⟨j, hj⟩ := hj
  have raised_inside : ∀ k, intersectionUpper p q k = intersectionLower p q k + 1 →
      ∀ i, intersectionLower p q i ≤ raisedCell k (intersectionLower p q) i ∧
        raisedCell k (intersectionLower p q) i ≤ intersectionUpper p q i := by
    intro k hk i
    by_cases hi : i = k
    · subst i
      simp only [raisedCell, unitAxis, if_pos rfl]
      omega
    · simpa only [raisedCell, unitAxis, if_neg hi, add_zero] using
        And.intro (le_refl (intersectionLower p q i)) (hwidth i).1
  have hu := at_hole _ (raised_inside j hj)
  have hh : (hole p = intersectionLower p q ∧ hole q = raisedCell j (intersectionLower p q)) ∨
      (hole q = intersectionLower p q ∧ hole p = raisedCell j (intersectionLower p q)) := by
    rcases hbase with hp | hq <;> rcases hu with hup | huq
    · exact False.elim (raised_ne_base j _ (hup.trans hp.symm))
    · exact Or.inl ⟨hp.symm, huq.symm⟩
    · exact Or.inr ⟨hq.symm, hup.symm⟩
    · exact False.elim (raised_ne_base j _ (huq.trans hq.symm))
  right
  refine ⟨j, ?_, hj, hh⟩
  intro k hkj
  by_contra hne
  have hk : intersectionUpper p q k = intersectionLower p q k + 1 := by
    have hw := hwidth k
    omega
  have hv := at_hole _ (raised_inside k hk)
  rcases hh with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · rcases hv with hv | hv
    · exact raised_ne_base k _ (hv.trans hp)
    · exact raised_ne_raised hkj _ (hv.trans hq)
  · rcases hv with hv | hv
    · exact raised_ne_raised hkj _ (hv.trans hp)
    · exact raised_ne_base k _ (hv.trans hq)

theorem noContactCertificate_complete {d : ℕ} (p q : Pose d) (hn : ¬ CellContact p q) :
    NoContactCertificate p q := by
  intro j
  constructor
  · apply cellSeparated_complete
    rintro c ⟨hc, hq⟩
    apply hn
    refine ⟨c, (fun i => c i - (-unitAxis j i)), hc,
      (occupies_forwardShift_iff _ q c).mp hq, j, Or.inl ?_, ?_⟩
    · simp [unitAxis]
    · intro i hij
      simp [unitAxis, hij]
  · apply cellSeparated_complete
    rintro c ⟨hc, hq⟩
    apply hn
    refine ⟨c, (fun i => c i - unitAxis j i), hc,
      (occupies_forwardShift_iff _ q c).mp hq, j, Or.inr ?_, ?_⟩
    · simp [unitAxis]
    · intro i hij
      simp [unitAxis, hij]

theorem noContactCertificate_iff {d : ℕ} (p q : Pose d) :
    NoContactCertificate p q ↔ ¬ CellContact p q :=
  ⟨noContactCertificate_sound, noContactCertificate_complete p q⟩

instance decidableCellContact {d : ℕ} (p q : Pose d) : Decidable (CellContact p q) :=
  decidable_of_iff (¬ NoContactCertificate p q) (by rw [noContactCertificate_iff, not_not])

/-- A realizable two-hole intersection omitted by the earlier singleton test. -/
def twoHoleExample : Pose 3 := ⟨Equiv.refl _, fun _ => true, ![2, 3, 3]⟩

theorem two_hole_case_realized : TwoHoleSeparate (rootPose 3) twoHoleExample ∧
    ¬ Separate (rootPose 3) twoHoleExample := by decide

#print axioms cellSeparated_complete
#print axioms noContactCertificate_iff
#print axioms decidableCellContact
#print axioms two_hole_case_realized
end SparseMonotiles.CarrierHierarchy
