module

public import SparseMonotiles.ContactChecker

@[expose] public section

namespace SparseMonotiles.Contact

/-- One normal-coordinate test and one apex comparison can refute a whole
pyramid-vertex match, without enumerating all base vertices. -/
def BoxKey.ApexDiscriminates {d : ℕ} (axis : Fin d) (root source : BoxKey d) : Prop :=
  root.bump ≠ source.bump ∨
  (source.radius axis = 0 ∧ root.apex axis ≠ source.centre axis ∧ root.apex ≠ source.apex)

instance {d : ℕ} (axis : Fin d) (root source : BoxKey d) :
    Decidable (BoxKey.ApexDiscriminates axis root source) :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _ ∧ _))

/-- A non-base root apex must coincide with the source apex in any literal match. -/
theorem BoxKey.apexDiscriminates_sound {d : ℕ} {axis : Fin d} {root source : BoxKey d}
    (h : BoxKey.ApexDiscriminates axis root source) : root.literal ≠ source.literal := by
  intro he
  rcases h with hb | ⟨hr, hc, ha⟩
  · exact hb (congrArg VertexKey.bump he)
  · have hv : root.apex ∈ source.literal.vertices := by
      rw [← he]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hv with haeq | hbase
    · exact ha haeq
    · rcases Finset.mem_image.mp hbase with ⟨bits, _, hbits⟩
      have hi := congrFun hbits axis
      simp [BoxKey.corner, hr] at hi
      exact hc hi.symm


theorem Pose.scaledPoint_injective {d : ℕ} (p : Pose d) (den : ℤ) :
    Function.Injective (p.scaledPoint den) := by
  intro x y h
  funext j
  have hi := congrFun h (p.perm.symm j)
  simp only [Pose.scaledPoint, Equiv.apply_symm_apply] at hi
  cases hn : p.negative (p.perm.symm j) <;> simp [Pose.sign, hn] at hi <;> omega

theorem Pose.cell_injective {d : ℕ} (p : Pose d) : Function.Injective p.cell := by
  intro x y h
  funext j
  have hi := congrFun h (p.perm.symm j)
  simp only [Pose.cell, Equiv.apply_symm_apply] at hi
  cases hn : p.negative (p.perm.symm j) <;> simp [Pose.sign, hn] at hi <;> omega

theorem Facet.ext {d : ℕ} {a b : Facet d} (hc : a.cell = b.cell)
    (ha : a.axis = b.axis) (hp : a.positive = b.positive) : a = b := by
  cases a
  cases b
  simp_all

theorem Facet.normal_eq_iff {d : ℕ} (a b : Facet d) :
    a.normal = b.normal ↔ a.positive = b.positive := by
  cases ha : a.positive <;> cases hb : b.positive <;> simp [Facet.normal, ha, hb]

/-- A fixed registered pose and root facet have at most one opposed source facet. -/
theorem shared_source_unique {d : ℕ} {p : Pose d} {a b c : Facet d}
    (hb : Shared p a b) (hc : Shared p a c) : b = c := by
  have hcentre : b.centre2 = c.centre2 :=
    p.scaledPoint_injective 2 (hb.1.symm.trans hc.1)
  have haxis : b.axis = c.axis := hb.2.1.symm.trans hc.2.1
  have hnormal : b.normal = c.normal := by
    have h := hb.2.2.trans hc.2.2.symm
    cases hn : p.negative a.axis <;> simp [Pose.sign, hn] at h <;> omega
  have hpositive := (Facet.normal_eq_iff b c).mp hnormal
  apply Facet.ext _ haxis hpositive
  funext i
  have hi := congrFun hcentre i
  simp only [Facet.centre2] at hi
  rw [haxis, hnormal] at hi
  omega

/-- The unit cell across an oriented carrier facet. -/
def Facet.neighbor {d : ℕ} (a : Facet d) : Cell d :=
  fun i => a.cell i + if i = a.axis then a.normal else 0

/-- Shared opposed facets put the source cell exactly in the neighboring cell.
The negative-row lower-corner correction is retained explicitly throughout. -/
theorem shared_cell_neighbor {d : ℕ} {p : Pose d} {a b : Facet d}
    (h : Shared p a b) : p.cell b.cell = a.neighbor := by
  funext i
  have hc := congrFun h.1 i
  have hn := h.2.2
  have haxis : p.perm i = b.axis ↔ i = a.axis := by
    rw [← h.2.1]
    exact p.perm.injective.eq_iff
  simp only [Facet.centre2, Pose.scaledPoint] at hc
  by_cases hi : i = a.axis
  · subst i
    have hb : p.perm a.axis = b.axis := h.2.1
    simp only [if_pos rfl, if_pos hb] at hc
    simp only [Pose.cell, Facet.neighbor, if_pos rfl]
    cases hneg : p.negative a.axis <;>
      simp [Pose.sign, hneg] at hc hn ⊢ <;> omega
  · have hb : p.perm i ≠ b.axis := mt haxis.mp hi
    simp only [if_neg hi, if_neg hb, add_zero] at hc
    simp only [Pose.cell, Facet.neighbor, if_neg hi, add_zero]
    cases hneg : p.negative i <;> simp [Pose.sign, hneg] at hc ⊢ <;> omega

/-- Array/vector-friendly geometry; facet and profile lookup use bounded indices. -/
structure IndexedGeometry (d n : ℕ) where
  denominator : ℤ
  cells : Finset (Cell d)
  facet : Fin n → Facet d
  profile : Fin n → Finset (BoxKey d)

/-- Literal-vertex semantics of the indexed data. -/
def IndexedGeometry.LegalContact {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d) : Prop :=
  Disjoint g.cells (g.cells.image p.cell) ∧
  (∃ i j, Shared p (g.facet i) (g.facet j)) ∧
  ∀ i j, Shared p (g.facet i) (g.facet j) →
    (g.profile i).image BoxKey.literal =
      ((g.profile j).image BoxKey.literal).image (p.key g.denominator)

def IndexedGeometry.AcceptanceAt {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d)
    (i : Fin n) : Option (Fin n) → Prop
  | none => (g.facet i).neighbor ∉ g.cells.image p.cell
  | some j => Shared p (g.facet i) (g.facet j) ∧
      g.profile i = (g.profile j).image (p.boxKey g.denominator)

instance {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d) (i : Fin n) :
    (m : Option (Fin n)) → Decidable (g.AcceptanceAt p i m)
  | none => inferInstanceAs (Decidable (_ ∉ _))
  | some j => inferInstanceAs (Decidable (_ ∧ _))

/-- A linear scan of root facets: a source index, or a missing neighboring cell. -/
def IndexedGeometry.AcceptanceValid {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d)
    (mates : Fin n → Option (Fin n)) : Prop :=
  Disjoint g.cells (g.cells.image p.cell) ∧
  (∃ i j, mates i = some j) ∧
  ∀ i, g.AcceptanceAt p i (mates i)

instance {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d)
    (mates : Fin n → Option (Fin n)) : Decidable (g.AcceptanceValid p mates) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The linear certificate checks every possible shared facet, by uniqueness.
No candidate-generating or physical-registration assumption appears here. -/
theorem IndexedGeometry.acceptance_sound {d n : ℕ} {g : IndexedGeometry d n}
    (owned : ∀ j, (g.facet j).cell ∈ g.cells) (unique : Function.Injective g.facet)
    {p : Pose d} {mates : Fin n → Option (Fin n)} (h : g.AcceptanceValid p mates) :
    g.LegalContact p := by
  rcases h with ⟨hd, he, hm⟩
  refine ⟨hd, ?_, ?_⟩
  · rcases he with ⟨i, j, hij⟩
    have hs : Shared p (g.facet i) (g.facet j) ∧
        g.profile i = (g.profile j).image (p.boxKey g.denominator) := by
      simpa [IndexedGeometry.AcceptanceAt, hij] using hm i
    exact ⟨i, j, hs.1⟩
  · intro i j hs
    cases heq : mates i with
    | none =>
        have hn : (g.facet i).neighbor ∉ g.cells.image p.cell := by simpa [IndexedGeometry.AcceptanceAt, heq] using hm i
        exact (hn (Finset.mem_image.mpr ⟨(g.facet j).cell, owned j,
          shared_cell_neighbor hs⟩)).elim
    | some k =>
        have hk : Shared p (g.facet i) (g.facet k) ∧
            g.profile i = (g.profile k).image (p.boxKey g.denominator) := by
          simpa [IndexedGeometry.AcceptanceAt, heq] using hm i
        have hjk : j = k := unique (shared_source_unique hs hk.1)
        subst j
        rw [hk.2]
        simp only [Finset.image_image]
        apply Finset.image_congr
        intro key _
        exact p.boxKey_literal g.denominator key


inductive IndexedRejection (d n : ℕ) where
  | overlap (cell : Cell d)
  | unmatchedRoot (root source : Fin n) (key : BoxKey d)
  | unmatchedSource (root source : Fin n) (key : BoxKey d)

def IndexedRejection.Valid {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d) :
    IndexedRejection d n → Prop
  | .overlap c => c ∈ g.cells ∧ c ∈ g.cells.image p.cell
  | .unmatchedRoot i j k => Shared p (g.facet i) (g.facet j) ∧ k ∈ g.profile i ∧
      ∀ l ∈ g.profile j,
        BoxKey.ApexDiscriminates (g.facet i).axis k (p.boxKey g.denominator l)
  | .unmatchedSource i j k => Shared p (g.facet i) (g.facet j) ∧ k ∈ g.profile j ∧
      ∀ l ∈ g.profile i,
        BoxKey.ApexDiscriminates (g.facet i).axis (p.boxKey g.denominator k) l

instance {d n : ℕ} (g : IndexedGeometry d n) (p : Pose d) :
    (r : IndexedRejection d n) → Decidable (r.Valid g p)
  | .overlap c => inferInstanceAs (Decidable (_ ∧ _))
  | .unmatchedRoot i j k => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .unmatchedSource i j k => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Constant-size apex/plane witnesses refute the complete literal profile law. -/
theorem IndexedRejection.sound {d n : ℕ} {g : IndexedGeometry d n} {p : Pose d}
    {r : IndexedRejection d n} (h : r.Valid g p) : ¬ g.LegalContact p := by
  intro legal
  rcases legal with ⟨hd, _, hm⟩
  cases r with
  | overlap c => exact Finset.disjoint_left.mp hd h.1 h.2
  | unmatchedRoot i j k =>
      rcases h with ⟨hs, hk, hw⟩
      have hroot : k.literal ∈ (g.profile i).image BoxKey.literal :=
        Finset.mem_image.mpr ⟨k, hk, rfl⟩
      rw [hm i j hs] at hroot
      rcases Finset.mem_image.mp hroot with ⟨lit, hlit, he⟩
      rcases Finset.mem_image.mp hlit with ⟨l, hl, rfl⟩
      apply BoxKey.apexDiscriminates_sound (hw l hl)
      rw [p.boxKey_literal]
      exact he.symm
  | unmatchedSource i j k =>
      rcases h with ⟨hs, hk, hw⟩
      have hsource : p.key g.denominator k.literal ∈
          ((g.profile j).image BoxKey.literal).image (p.key g.denominator) :=
        Finset.mem_image.mpr ⟨k.literal, Finset.mem_image.mpr ⟨k, hk, rfl⟩, rfl⟩
      rw [← hm i j hs] at hsource
      rcases Finset.mem_image.mp hsource with ⟨l, hl, he⟩
      apply BoxKey.apexDiscriminates_sound (hw l hl)
      rw [p.boxKey_literal]
      exact he.symm

#print axioms BoxKey.apexDiscriminates_sound
#print axioms IndexedRejection.sound
#print axioms shared_cell_neighbor
#print axioms shared_source_unique
#print axioms IndexedGeometry.acceptance_sound
end SparseMonotiles.Contact
