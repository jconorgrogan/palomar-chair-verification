module

public import SparseMonotiles.ContactIndexedChecker

@[expose] public section

namespace SparseMonotiles.Contact

def binaryCell {d : ℕ} (bits : Fin d → Bool) : Cell d :=
  fun i => if bits i then 1 else 0

theorem binaryCell_injective {d : ℕ} : Function.Injective (binaryCell (d := d)) := by
  intro a b h
  funext i
  have hi := congrFun h i
  cases ha : a i <;> cases hb : b i <;> simp_all [binaryCell]

def chairCells (d : ℕ) : Finset (Cell d) :=
  ((Finset.univ : Finset (Fin d → Bool)).filter (fun b => ∃ i, b i = false)).map
    ⟨binaryCell, binaryCell_injective⟩

def IsChairCell {d : ℕ} (c : Cell d) : Prop :=
  (∀ i, c i = 0 ∨ c i = 1) ∧ ∃ i, c i = 0

instance {d : ℕ} (c : Cell d) : Decidable (IsChairCell c) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem mem_chairCells {d : ℕ} (c : Cell d) : c ∈ chairCells d ↔ IsChairCell c := by
  simp only [chairCells, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨bits, ⟨i, hi⟩, rfl⟩
    constructor
    · intro j
      cases h : bits j <;> simp [binaryCell, h]
    · exact ⟨i, by simp [binaryCell, hi]⟩
  · rintro ⟨hc, ⟨i, hi⟩⟩
    let bits : Fin d → Bool := fun j => decide (c j = 1)
    refine ⟨bits, ⟨i, ?_⟩, ?_⟩
    · simp [bits, hi]
    · funext j
      rcases hc j with h | h <;> simp [binaryCell, bits, h]

/-- Inverse lower-corner action, including the negative-row correction. -/
def Pose.inverseCell {d : ℕ} (p : Pose d) (c : Cell d) : Cell d :=
  fun j => let i := p.perm.symm j
    p.sign i * (c i - p.shift i + if p.negative i then 1 else 0)

theorem Pose.inverseCell_cell {d : ℕ} (p : Pose d) (c : Cell d) :
    p.inverseCell (p.cell c) = c := by
  funext j
  simp only [Pose.inverseCell, Pose.cell, Equiv.apply_symm_apply]
  cases h : p.negative (p.perm.symm j) <;> simp [Pose.sign, h] <;> ring

theorem Pose.cell_inverseCell {d : ℕ} (p : Pose d) (c : Cell d) :
    p.cell (p.inverseCell c) = c := by
  funext i
  simp only [Pose.cell, Pose.inverseCell, Equiv.symm_apply_apply]
  cases h : p.negative i <;> simp [Pose.sign, h] <;> ring

theorem mem_image_cell {d : ℕ} (p : Pose d) (cells : Finset (Cell d)) (c : Cell d) :
    c ∈ cells.image p.cell ↔ p.inverseCell c ∈ cells := by
  constructor
  · rintro h
    rcases Finset.mem_image.mp h with ⟨b, hb, rfl⟩
    simpa [p.inverseCell_cell] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨p.inverseCell c, h, p.cell_inverseCell c⟩

theorem chair_disjoint_iff {d : ℕ} (p : Pose d) :
    Disjoint (chairCells d) ((chairCells d).image p.cell) ↔
      ∀ c ∈ chairCells d, ¬ IsChairCell (p.inverseCell c) := by
  constructor
  · intro h c hc hn
    exact Finset.disjoint_left.mp h hc ((mem_image_cell p _ c).mpr ((mem_chairCells _).mpr hn))
  · intro h
    apply Finset.disjoint_left.mpr
    intro c hc hm
    exact h c hc ((mem_chairCells _).mp ((mem_image_cell p _ c).mp hm))

def IndexedGeometry.FastAcceptanceAt {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d)
    (i : Fin n) : Option (Fin n) → Prop
  | none => ¬ IsChairCell (p.inverseCell (g.facet i).neighbor)
  | some j => Shared p (g.facet i) (g.facet j) ∧
      g.profile i = (g.profile j).image (p.boxKey g.denominator)

instance {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d) (i : Fin n) :
    (m : Option (Fin n)) → Decidable (g.FastAcceptanceAt p i m)
  | none => inferInstanceAs (Decidable (¬ _))
  | some _ => inferInstanceAs (Decidable (_ ∧ _))

structure MateCertificate (n : ℕ) where
  root : Fin n
  source : Fin n
  mates : Fin n → Option (Fin n)

/-- Exact O(d)-coordinate chair occupancy replaces a search through 2^d cells.
A supplied positive witness avoids an existential search over all facet pairs. -/
def IndexedGeometry.FastAcceptanceValid {d n : ℕ} (g : IndexedGeometry d n)
    (p : Pose d) (cert : MateCertificate n) : Prop :=
  (∀ c ∈ chairCells d, ¬ IsChairCell (p.inverseCell c)) ∧
  cert.mates cert.root = some cert.source ∧
  ∀ i, g.FastAcceptanceAt p i (cert.mates i)

instance {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d)
    (cert : MateCertificate n) : Decidable (g.FastAcceptanceValid p cert) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem IndexedGeometry.fastAcceptance_valid {d n : ℕ} {g : IndexedGeometry d n}
    (cells_eq : g.cells = chairCells d) {p : Pose d} {cert : MateCertificate n}
    (h : g.FastAcceptanceValid p cert) : g.AcceptanceValid p cert.mates := by
  refine ⟨?_, ⟨cert.root, cert.source, h.2.1⟩, ?_⟩
  · simpa [cells_eq] using (chair_disjoint_iff p).mpr h.1
  · intro i
    have hi := h.2.2 i
    cases hm : cert.mates i with
    | none =>
        change (g.facet i).neighbor ∉ g.cells.image p.cell
        rw [cells_eq, mem_image_cell, mem_chairCells]
        simpa [IndexedGeometry.FastAcceptanceAt, hm] using hi
    | some j =>
        simpa [IndexedGeometry.AcceptanceAt, IndexedGeometry.FastAcceptanceAt, hm] using hi

def IndexedRejection.FastValid {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d) :
    IndexedRejection d n → Prop
  | .overlap c => IsChairCell c ∧ IsChairCell (p.inverseCell c)
  | .unmatchedRoot i j k => (IndexedRejection.unmatchedRoot i j k).Valid g p
  | .unmatchedSource i j k => (IndexedRejection.unmatchedSource i j k).Valid g p

instance {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d) :
    (r : IndexedRejection d n) → Decidable (r.FastValid g p)
  | .overlap _ => inferInstanceAs (Decidable (_ ∧ _))
  | .unmatchedRoot i j k => inferInstanceAs (Decidable (IndexedRejection.Valid g p (.unmatchedRoot i j k)))
  | .unmatchedSource i j k => inferInstanceAs (Decidable (IndexedRejection.Valid g p (.unmatchedSource i j k)))

theorem IndexedRejection.fastValid_valid {d n : ℕ} {g : IndexedGeometry d n}
    (cells_eq : g.cells = chairCells d) {p : Pose d} {r : IndexedRejection d n}
    (h : r.FastValid g p) : r.Valid g p := by
  cases r with
  | overlap c =>
      change c ∈ g.cells ∧ c ∈ g.cells.image p.cell
      rw [cells_eq, mem_image_cell, mem_chairCells, mem_chairCells]
      exact h
  | unmatchedRoot _ _ _ => exact h
  | unmatchedSource _ _ _ => exact h

/-- A checked left-inverse tag establishes unique facet IDs in a linear scan. -/
theorem IndexedGeometry.facet_injective_of_tag {d n : ℕ} (g : IndexedGeometry d n)
    (tag : Facet d → ℕ) (lookup : ℕ → ℕ)
    (checked : ∀ i, lookup (tag (g.facet i)) = i.val) : Function.Injective g.facet := by
  intro i j h
  apply Fin.ext
  calc
    i.val = lookup (tag (g.facet i)) := (checked i).symm
    _ = lookup (tag (g.facet j)) := congrArg (fun f => lookup (tag f)) h
    _ = j.val := checked j

/-- A convenient concrete tag; only the checked left-inverse property is needed. -/
def Facet.binaryTag {d : ℕ} (f : Facet d) : ℕ :=
  2 * (d * (∑ i : Fin d, (f.cell i).toNat * 2 ^ i.val) + f.axis.val) +
    if f.positive then 1 else 0

inductive IndexedVerdict (d n : ℕ) where
  | accepted (certificate : MateCertificate n)
  | rejected (reason : IndexedRejection d n)

structure IndexedRow (d n : ℕ) where
  pose : Pose d
  verdict : IndexedVerdict d n

def IndexedRow.Check {d n : ℕ} (g : IndexedGeometry d n) : IndexedRow d n → Prop
  | ⟨p, .accepted mates⟩ => g.FastAcceptanceValid p mates
  | ⟨p, .rejected reason⟩ => reason.FastValid g p

instance {d n : ℕ} (g : IndexedGeometry d n) : (r : IndexedRow d n) → Decidable (r.Check g)
  | ⟨_, .accepted _⟩ => inferInstanceAs (Decidable (IndexedGeometry.FastAcceptanceValid _ _ _))
  | ⟨_, .rejected _⟩ => inferInstanceAs (Decidable (IndexedRejection.FastValid _ _ _))

def IndexedRow.accepted {d n : ℕ} : IndexedRow d n → Bool
  | ⟨_, .accepted _⟩ => true
  | ⟨_, .rejected _⟩ => false

def indexedValidate {d n : ℕ} (g : IndexedGeometry d n) (rows : List (IndexedRow d n)) : Bool :=
  rows.all (fun r => decide (r.Check g))

def indexedAcceptedPoses {d n : ℕ} (rows : List (IndexedRow d n)) : List (Pose d) :=
  (rows.filter IndexedRow.accepted).map IndexedRow.pose

@[simp] theorem indexedValidate_eq_true {d n : ℕ} (g : IndexedGeometry d n)
    (rows : List (IndexedRow d n)) : indexedValidate g rows = true ↔ ∀ r ∈ rows, r.Check g := by
  simp [indexedValidate]

theorem IndexedRow.check_iff_legal {d n : ℕ} {g : IndexedGeometry d n}
    (cells_eq : g.cells = chairCells d) (owned : ∀ j, (g.facet j).cell ∈ g.cells)
    (unique : Function.Injective g.facet) {r : IndexedRow d n} (h : r.Check g) :
    g.LegalContact r.pose ↔ r.accepted = true := by
  cases r with
  | mk p verdict =>
      cases verdict with
      | accepted mates =>
          have hp := IndexedGeometry.acceptance_sound owned unique
            (IndexedGeometry.fastAcceptance_valid cells_eq h)
          simpa [IndexedRow.accepted] using hp
      | rejected reason =>
          have hp := IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq h)
          simp [IndexedRow.accepted, hp]

/-- A complete checked finite table is exact on its stated candidate set. -/
theorem indexed_candidate_language_exact {d n : ℕ} {g : IndexedGeometry d n}
    (cells_eq : g.cells = chairCells d) (owned : ∀ j, (g.facet j).cell ∈ g.cells)
    (unique : Function.Injective g.facet) {rows : List (IndexedRow d n)}
    (h : indexedValidate g rows = true) :
    ∀ p, (p ∈ rows.map IndexedRow.pose ∧ g.LegalContact p) ↔ p ∈ indexedAcceptedPoses rows := by
  intro p
  constructor
  · rintro ⟨hm, hp⟩
    rcases List.mem_map.mp hm with ⟨row, hr, he⟩
    refine List.mem_map.mpr ⟨row, List.mem_filter.mpr ⟨hr, ?_⟩, he⟩
    apply (IndexedRow.check_iff_legal cells_eq owned unique
      ((indexedValidate_eq_true g rows).mp h row hr)).mp
    simpa [he] using hp
  · intro hp
    rcases List.mem_map.mp hp with ⟨row, hr, rfl⟩
    rcases List.mem_filter.mp hr with ⟨hr, ha⟩
    refine ⟨List.mem_map.mpr ⟨row, hr, rfl⟩, ?_⟩
    exact (IndexedRow.check_iff_legal cells_eq owned unique
      ((indexedValidate_eq_true g rows).mp h row hr)).mpr ha

/-- Compact literal encoding for certificate data. No completeness of this bounded
translation representation is asserted by this definition. -/
def Pose.ofCodes {d : ℕ} (perm : Equiv.Perm (Fin d))
    (negativeCode translationCode : ℕ) : Pose d where
  perm := perm
  negative := fun i => decide ((negativeCode / 2 ^ i.val) % 2 = 1)
  shift := fun i => (((translationCode / 7 ^ i.val) % 7 : ℕ) : ℤ) - 2

@[simp] theorem indexedValidate_append {d n : ℕ} (g : IndexedGeometry d n)
    (a b : List (IndexedRow d n)) :
    indexedValidate g (a ++ b) = (indexedValidate g a && indexedValidate g b) := by
  simp [indexedValidate, List.all_append]

#print axioms mem_chairCells
#print axioms Pose.inverseCell_cell
#print axioms IndexedGeometry.fastAcceptance_valid
#print axioms IndexedRejection.fastValid_valid
#print axioms indexed_candidate_language_exact
end SparseMonotiles.Contact
