module

public import SparseMonotiles.CarrierHierarchyWitnessChecker
public import SparseMonotiles.CarrierHierarchyCharts

@[expose] public section

/-! A bounded, sound no-contact checker for finite forward substitution rows.
The two-hole case covers a box intersection consisting of two cells, each
omitted by one chair. No unbounded cell search is trusted or assumed. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Integer anchor translation, kept local to the lightweight finite checker. -/
def forwardShift {d : ℕ} (v : Cell d) (p : Pose d) : Pose d where
  perm := p.perm
  negative := p.negative
  shift := fun i => p.shift i + v i

def intersectionLower {d : ℕ} (p q : Pose d) : Cell d :=
  fun i => max (boxLower p i) (boxLower q i)

def intersectionUpper {d : ℕ} (p q : Pose d) : Cell d :=
  fun i => min (boxLower p i + 1) (boxLower q i + 1)

def raisedCell {d : ℕ} (j : Fin d) (c : Cell d) : Cell d := fun i => c i + unitAxis j i

def TwoHoleSeparate {d : ℕ} (p q : Pose d) : Prop := ∃ j : Fin d,
  (∀ i, i ≠ j → intersectionUpper p q i = intersectionLower p q i) ∧
  intersectionUpper p q j = intersectionLower p q j + 1 ∧
  ((hole p = intersectionLower p q ∧ hole q = raisedCell j (intersectionLower p q)) ∨
   (hole q = intersectionLower p q ∧ hole p = raisedCell j (intersectionLower p q)))

instance {d : ℕ} (p q : Pose d) : Decidable (TwoHoleSeparate p q) :=
  inferInstanceAs (Decidable (∃ _, _ ∧ _ ∧ (_ ∨ _)))

theorem twoHoleSeparate_sound {d : ℕ} {p q : Pose d} (h : TwoHoleSeparate p q)
    (c : Cell d) : ¬ (Occupies p c ∧ Occupies q c) := by
  rintro ⟨hpc, hqc⟩
  obtain ⟨j, hfixed, hwidth, hholes⟩ := h
  have hp := (occupies_box_iff p c).mp hpc
  have hq := (occupies_box_iff q c).mp hqc
  have hbounds : ∀ i, intersectionLower p q i ≤ c i ∧ c i ≤ intersectionUpper p q i := by
    intro i
    have hpi := hp.1 i
    have hqi := hq.1 i
    exact ⟨max_le (by omega) (by omega), le_min (by omega) (by omega)⟩
  have hj : c j = intersectionLower p q j ∨ c j = intersectionLower p q j + 1 := by
    have hb := hbounds j
    omega
  have hc : c = intersectionLower p q ∨ c = raisedCell j (intersectionLower p q) := by
    rcases hj with hj | hj
    · left
      funext i
      by_cases hi : i = j
      · subst i
        exact hj
      · have hb := hbounds i
        have hf := hfixed i hi
        omega
    · right
      funext i
      by_cases hi : i = j
      · subst i
        simpa [raisedCell, unitAxis] using hj
      · have hb := hbounds i
        have hf := hfixed i hi
        simp only [raisedCell, unitAxis, if_neg hi, add_zero]
        omega
  rcases hholes with ⟨hp0, hq1⟩ | ⟨hq0, hp1⟩
  · rcases hc with hc | hc
    · exact hp.2 (hc.trans hp0.symm)
    · exact hq.2 (hc.trans hq1.symm)
  · rcases hc with hc | hc
    · exact hq.2 (hc.trans hq0.symm)
    · exact hp.2 (hc.trans hp1.symm)

def CellSeparated {d : ℕ} (p q : Pose d) : Prop := Separate p q ∨ TwoHoleSeparate p q

instance {d : ℕ} (p q : Pose d) : Decidable (CellSeparated p q) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem cellSeparated_sound {d : ℕ} {p q : Pose d} (h : CellSeparated p q)
    (c : Cell d) : ¬ (Occupies p c ∧ Occupies q c) := by
  rcases h with h | h
  · exact separate_sound h c
  · exact twoHoleSeparate_sound h c

theorem occupies_forwardShift_iff {d : ℕ} (v : Cell d) (p : Pose d) (c : Cell d) :
    Occupies (forwardShift v p) c ↔ Occupies p (fun i => c i - v i) := by
  have he : (forwardShift v p).inverseCell c = p.inverseCell (fun i => c i - v i) := by
    funext i
    cases h : p.negative (p.perm.symm i) <;>
      simp [Pose.inverseCell, forwardShift, Pose.sign, h] <;> ring
  simp only [Occupies, he]

def NoContactCertificate {d : ℕ} (p q : Pose d) : Prop := ∀ j : Fin d,
  CellSeparated p (forwardShift (fun i => -unitAxis j i) q) ∧
  CellSeparated p (forwardShift (unitAxis j) q)

instance {d : ℕ} (p q : Pose d) : Decidable (NoContactCertificate p q) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

theorem noContactCertificate_sound {d : ℕ} {p q : Pose d} (h : NoContactCertificate p q) :
    ¬ CellContact p q := by
  rintro ⟨c, e, hc, he, j, hj, hother⟩
  rcases hj with hj | hj
  · apply cellSeparated_sound (h j).1 c
    refine ⟨hc, (occupies_forwardShift_iff (fun i => -unitAxis j i) q c).mpr ?_⟩
    have heq : (fun i => c i - (-unitAxis j i)) = e := by
      funext i
      by_cases hi : i = j
      · subst i
        simpa [unitAxis] using hj.symm
      · simp only [unitAxis, if_neg hi, neg_zero, sub_zero, hother i hi]
    rw [heq]
    exact he
  · apply cellSeparated_sound (h j).2 c
    refine ⟨hc, (occupies_forwardShift_iff (unitAxis j) q c).mpr ?_⟩
    have heq : (fun i => c i - unitAxis j i) = e := by
      funext i
      by_cases hi : i = j
      · subst i
        simpa [unitAxis] using hj.symm
      · simp only [unitAxis, if_neg hi, sub_zero, hother i hi]
    rw [heq]
    exact he

inductive ForwardPairWitness (κ : Type) where
  | member (index : κ)
  | apart

def ForwardPairWitness.Valid {d : ℕ} {κ : Type} (registry : κ → Pose d)
    (p q : Pose d) : ForwardPairWitness κ → Prop
  | .member i => normalize p q = registry i
  | .apart => NoContactCertificate p q

instance {d : ℕ} {κ : Type} (registry : κ → Pose d) (p q : Pose d) (w : ForwardPairWitness κ) :
    Decidable (w.Valid registry p q) := by
  cases w <;> unfold ForwardPairWitness.Valid <;> infer_instance

/-- Every finite pair row certifies the complete contact implication, including
pairs absent from an exported list, via actual carrier geometry. -/
theorem ForwardPairWitness.sound {d : ℕ} {κ : Type} (registry : κ → Pose d)
    (L : Set (Pose d)) (hRegistry : ∀ i, registry i ∈ L) {p q : Pose d}
    {w : ForwardPairWitness κ} (hw : w.Valid registry p q) (hcontact : CellContact p q) :
    normalize p q ∈ L := by
  cases w with
  | member i =>
      change normalize p q = registry i at hw
      rw [hw]
      exact hRegistry i
  | apart => exact False.elim (noContactCertificate_sound hw hcontact)

#print axioms twoHoleSeparate_sound
#print axioms noContactCertificate_sound
#print axioms ForwardPairWitness.sound
end SparseMonotiles.CarrierHierarchy
