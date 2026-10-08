module

public import SparseMonotiles.CarrierHierarchyH0

@[expose] public section

/-!
A small sound finite checker for positive local-world models. Disjointness uses
an explicit separating coordinate or a singleton box intersection at a missing
cell. It never infers consistency merely from the absence of failed tests.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def Separate {d : ℕ} (p q : Pose d) : Prop :=
  (∃ i, boxLower p i + 1 < boxLower q i ∨ boxLower q i + 1 < boxLower p i) ∨
  (∀ i, max (boxLower p i) (boxLower q i) =
      min (boxLower p i + 1) (boxLower q i + 1) ∧
      max (boxLower p i) (boxLower q i) = hole p i) ∨
  (∀ i, max (boxLower p i) (boxLower q i) =
      min (boxLower p i + 1) (boxLower q i + 1) ∧
      max (boxLower p i) (boxLower q i) = hole q i)

instance {d : ℕ} (p q : Pose d) : Decidable (Separate p q) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

private theorem occupied_bounds {d : ℕ} {p : Pose d} {c : Cell d}
    (h : Occupies p c) (i : Fin d) : boxLower p i ≤ c i ∧ c i ≤ boxLower p i + 1 := by
  have hi := ((occupies_box_iff p c).mp h).1 i
  omega

theorem separate_sound {d : ℕ} {p q : Pose d} (h : Separate p q)
    (c : Cell d) : ¬ (Occupies p c ∧ Occupies q c) := by
  rintro ⟨hp, hq⟩
  rcases h with ⟨i, hi⟩ | h | h
  · have hpi := occupied_bounds hp i
    have hqi := occupied_bounds hq i
    omega
  · apply ((occupies_box_iff p c).mp hp).2
    funext i
    have hpi := occupied_bounds hp i
    have hqi := occupied_bounds hq i
    have hl : max (boxLower p i) (boxLower q i) ≤ c i := max_le hpi.1 hqi.1
    have hu : c i ≤ min (boxLower p i + 1) (boxLower q i + 1) := le_min hpi.2 hqi.2
    have hi := h i
    omega
  · apply ((occupies_box_iff q c).mp hq).2
    funext i
    have hpi := occupied_bounds hp i
    have hqi := occupied_bounds hq i
    have hl : max (boxLower p i) (boxLower q i) ≤ c i := max_le hpi.1 hqi.1
    have hu : c i ≤ min (boxLower p i + 1) (boxLower q i + 1) := le_min hpi.2 hqi.2
    have hi := h i
    omega

def pairCheck {d : ℕ} (ps : List (Pose d)) : Bool :=
  ps.all fun p => ps.all fun q => decide (p = q ∨ Separate p q)

theorem pairCheck_sound {d : ℕ} {ps : List (Pose d)} (h : pairCheck ps = true) :
    ∀ p ∈ ps, ∀ q ∈ ps, ∀ c, Occupies p c → Occupies q c → p = q := by
  simp only [pairCheck, List.all_eq_true, decide_eq_true_eq] at h
  intro p hp q hq c hpc hqc
  rcases h p hp q hq with he | hs
  · exact he
  · exact False.elim (separate_sound hs c ⟨hpc, hqc⟩)

def crossCheck {d : ℕ} (r : Equiv.Perm (Fin d)) (ps qs : List (Pose d)) : Bool :=
  ps.all fun p => qs.all fun q => decide (GaugeRel r p (shiftOne q) ∨ Separate p (shiftOne q))

theorem crossCheck_sound {d : ℕ} {r : Equiv.Perm (Fin d)}
    {ps qs : List (Pose d)} (h : crossCheck r ps qs = true) :
    ∀ p ∈ ps, ∀ q ∈ qs, ∀ c,
      Occupies p c → Occupies (shiftOne q) c → GaugeRel r p (shiftOne q) := by
  simp only [crossCheck, List.all_eq_true, decide_eq_true_eq] at h
  intro p hp q hq c hpc hqc
  rcases h p hp q hq with he | hs
  · exact he
  · exact False.elim (separate_sound hs c ⟨hpc, hqc⟩)

instance {d : ℕ} (p : Pose d) (c : Cell d) : Decidable (Occupies p c) :=
  inferInstanceAs (Decidable (IsChairCell _))

def coverageCheck {d : ℕ} (ps : List (Pose d)) : Prop :=
  ∀ a : Bits d, Proper a → ∀ j : Fin d,
    ps.any (fun p => decide (Occupies p (exterior a j))) = true

instance {d : ℕ} (ps : List (Pose d)) : Decidable (coverageCheck ps) :=
  inferInstanceAs (Decidable (∀ a : Bits d, _))

def rootCheck {d : ℕ} (ps : List (Pose d)) : Bool :=
  ps.all fun p => decide (∀ a : Bits d, Proper a → ¬ Occupies p (fun i => bit a i))

/-- Every field of the concrete local-world interface is reconstructed from
finite checked arithmetic, including its unbounded-cell nonoverlap assertion. -/
def checkedLocalPatch {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) (ps : List (Pose d))
    (hc : ps.all (checkLocalCatalog σ r) = true)
    (hcover : coverageCheck ps) (hroot : rootCheck ps = true)
    (hpairs : pairCheck ps = true) : LocalPatch d σ r where
  tiles := {p | p ∈ ps}
  catalog := localCatalog_of_checked hc
  covers := by
    intro a ha j
    have h := hcover a ha j
    simpa only [Set.mem_setOf_eq, List.any_eq_true, decide_eq_true_eq] using h
  root_disjoint := by
    simpa only [Set.mem_setOf_eq, rootCheck, List.all_eq_true, decide_eq_true_eq] using hroot
  disjoint := pairCheck_sound hpairs

#print axioms separate_sound
#print axioms checkedLocalPatch
end SparseMonotiles.CarrierHierarchy
