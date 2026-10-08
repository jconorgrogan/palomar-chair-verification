module

public import SparseMonotiles.PyramidGeometry

@[expose] public section

/-!
# Incidence with the supporting planes of a nondegenerate box pyramid

The index `none` denotes the base plane and `some (i, b)` denotes a side
plane, with `false` selecting the lower endpoint of the base interval.
The redundant height bound `t ≤ h` in the H-representation is deliberately
not included. Thus there are `2*k + 1` indexed facet planes, not `2*k + 2`.

Strictly positive height and strictly positive coordinate widths are explicit
hypotheses. No tiling, registration, or unproved geometric premise is used.
-/
namespace SparseMonotiles

/-- The base and the two side planes for each tangential coordinate. -/
abbrev PyramidFacetIndex (k : ℕ) := Option (Fin k × Bool)

@[simp] theorem card_pyramidFacetIndex (k : ℕ) :
    Fintype.card (PyramidFacetIndex k) = 2 * k + 1 := by
  simp [PyramidFacetIndex, Nat.mul_comm]

/-- The corresponding index of the canonical finite H-representation. -/
def pyramidFacetHalfspaceIndex {k : ℕ} :
    PyramidFacetIndex k → PyramidHalfspaceIndex k
  | none => .inl false
  | some s => .inr s

/-- The base plane or a side plane, given by its exact affine equation. -/
def pyramidFacetPlane {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ) :
    PyramidFacetIndex k → Set (PyramidPoint k)
  | none => {p | p.2 = 0}
  | some (i, false) => {p | (h - p.2) * lo i + p.2 * o i = h * p.1 i}
  | some (i, true) => {p | (h - p.2) * hi i + p.2 * o i = h * p.1 i}

/-- These planes are exactly equality in the indicated canonical halfspace. -/
theorem mem_pyramidFacetPlane_iff {k : ℕ} (lo hi o : Fin k → ℝ) (h : ℝ)
    (j : PyramidFacetIndex k) (p : PyramidPoint k) :
    p ∈ pyramidFacetPlane lo hi o h j ↔
      pyramidHalfspaceNormal lo hi o h (pyramidFacetHalfspaceIndex j) p =
        pyramidHalfspaceBound lo hi h (pyramidFacetHalfspaceIndex j) := by
  cases j with
  | none =>
      change p.2 = 0 ↔ -p.2 = 0
      simp
  | some s =>
      rcases s with ⟨i, b⟩
      cases b
      · change (h - p.2) * lo i + p.2 * o i = h * p.1 i ↔
          (o i - lo i) * p.2 - h * p.1 i = -h * lo i
        constructor <;> intro hp <;> nlinarith
      · change (h - p.2) * hi i + p.2 * o i = h * p.1 i ↔
          h * p.1 i + (hi i - o i) * p.2 = h * hi i
        constructor <;> intro hp <;> nlinarith

/-- Restriction of a side plane to the base hyperplane. -/
theorem mem_pyramidSidePlane_at_base_iff {k : ℕ} (lo hi o : Fin k → ℝ)
    {h : ℝ} (hh : 0 < h) (x : Fin k → ℝ) (i : Fin k) (b : Bool) :
    (x, 0) ∈ pyramidFacetPlane lo hi o h (some (i, b)) ↔
      x i = if b then hi i else lo i := by
  cases b <;> simp only [pyramidFacetPlane, Set.mem_setOf_eq, sub_zero,
    zero_mul, add_zero, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> intro hx <;> nlinarith

/-- The apex is on every side plane. -/
theorem apex_mem_pyramidSidePlane {k : ℕ} (lo hi o : Fin k → ℝ)
    (h : ℝ) (i : Fin k) (b : Bool) :
    (o, h) ∈ pyramidFacetPlane lo hi o h (some (i, b)) := by
  cases b <;> simp [pyramidFacetPlane]

/-- Positive height and positive widths make all listed planes distinct. -/
theorem pyramidFacetPlane_injective {k : ℕ} (lo hi o : Fin k → ℝ)
    {h : ℝ} (hh : 0 < h) (hwidth : ∀ i, lo i < hi i) :
    Function.Injective (pyramidFacetPlane lo hi o h) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some s =>
          have hs := apex_mem_pyramidSidePlane lo hi o h s.1 s.2
          rw [← hab] at hs
          exact False.elim ((ne_of_gt hh) hs)
  | some s =>
      cases b with
      | none =>
          have hs := apex_mem_pyramidSidePlane lo hi o h s.1 s.2
          rw [hab] at hs
          exact False.elim ((ne_of_gt hh) hs)
      | some t =>
          rcases s with ⟨i, u⟩
          rcases t with ⟨j, v⟩
          have hbase (x : Fin k → ℝ) :
              (x i = if u then hi i else lo i) ↔
              (x j = if v then hi j else lo j) := by
            rw [← mem_pyramidSidePlane_at_base_iff lo hi o hh x i u,
              ← mem_pyramidSidePlane_at_base_iff lo hi o hh x j v, hab]
          cases u <;> cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] at hbase
          · have hij : i = j := by
              by_contra hneq
              have hx := (hbase (Function.update lo i (hi i))).mpr
                (by simp [hneq, Ne.symm hneq])
              simp only [Function.update_self] at hx
              exact (ne_of_lt (hwidth i)) hx.symm
            subst j
            rfl
          · exact False.elim ((ne_of_lt (hwidth j)) ((hbase lo).mp rfl))
          · exact False.elim ((ne_of_lt (hwidth i)) ((hbase lo).mpr rfl))
          · have hij : i = j := by
              by_contra hneq
              have hx := (hbase (Function.update hi i (lo i))).mpr
                (by simp [hneq, Ne.symm hneq])
              simp only [Function.update_self] at hx
              exact (ne_of_lt (hwidth i)) hx
            subst j
            rfl

/-- The finite set of the listed planes incident to a point. -/
noncomputable def pyramidActiveFacets {k : ℕ} (lo hi o : Fin k → ℝ)
    (h : ℝ) (p : PyramidPoint k) : Finset (PyramidFacetIndex k) := by
  classical
  exact Finset.univ.filter (fun j => p ∈ pyramidFacetPlane lo hi o h j)

@[simp] theorem mem_pyramidActiveFacets {k : ℕ} (lo hi o : Fin k → ℝ)
    (h : ℝ) (p : PyramidPoint k) (j : PyramidFacetIndex k) :
    j ∈ pyramidActiveFacets lo hi o h p ↔ p ∈ pyramidFacetPlane lo hi o h j := by
  classical
  simp [pyramidActiveFacets]

/-- Below apex height, opposite side planes for one coordinate are disjoint. -/
theorem not_mem_both_pyramidSidePlanes_below_apex {k : ℕ}
    (lo hi o : Fin k → ℝ) {h : ℝ} {p : PyramidPoint k} (i : Fin k)
    (hwidth : lo i < hi i) (hph : p.2 < h) :
    ¬ (p ∈ pyramidFacetPlane lo hi o h (some (i, false)) ∧
       p ∈ pyramidFacetPlane lo hi o h (some (i, true))) := by
  rintro ⟨hlo, hhi⟩
  change (h - p.2) * lo i + p.2 * o i = h * p.1 i at hlo
  change (h - p.2) * hi i + p.2 * o i = h * p.1 i at hhi
  have hgap := mul_pos (sub_pos.mpr hph) (sub_pos.mpr hwidth)
  nlinarith

/-- Forget which side of a coordinate was selected, retaining the base index. -/
def pyramidFacetCoordinate {k : ℕ} : PyramidFacetIndex k → Option (Fin k)
  | none => none
  | some (i, _) => some i

/-- An incident facet below the apex is determined by its coordinate or base. -/
theorem pyramidFacetCoordinate_injOn_active_below_apex {k : ℕ}
    (lo hi o : Fin k → ℝ) {h : ℝ} {p : PyramidPoint k}
    (hwidth : ∀ i, lo i < hi i) (hph : p.2 < h) :
    Set.InjOn pyramidFacetCoordinate
      (↑(pyramidActiveFacets lo hi o h p) : Set (PyramidFacetIndex k)) := by
  intro a ha b hb hab
  have ha' := (mem_pyramidActiveFacets lo hi o h p a).mp ha
  have hb' := (mem_pyramidActiveFacets lo hi o h p b).mp hb
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b =>
          rcases b with ⟨i, u⟩
          cases hab
  | some a =>
      cases b with
      | none =>
          rcases a with ⟨i, u⟩
          cases hab
      | some b =>
          rcases a with ⟨i, u⟩
          rcases b with ⟨j, v⟩
          have hij : i = j := by simpa [pyramidFacetCoordinate] using hab
          subst j
          cases u <;> cases v
          · rfl
          · exact False.elim
              (not_mem_both_pyramidSidePlanes_below_apex lo hi o i (hwidth i) hph
                ⟨ha', hb'⟩)
          · exact False.elim
              (not_mem_both_pyramidSidePlanes_below_apex lo hi o i (hwidth i) hph
                ⟨hb', ha'⟩)
          · rfl

/-- At most one plane per coordinate, plus the base, can meet below the apex. -/
theorem card_pyramidActiveFacets_le_of_height_lt {k : ℕ}
    (lo hi o : Fin k → ℝ) {h : ℝ} {p : PyramidPoint k}
    (hwidth : ∀ i, lo i < hi i) (hph : p.2 < h) :
    (pyramidActiveFacets lo hi o h p).card ≤ k + 1 := by
  classical
  have hcard : (pyramidActiveFacets lo hi o h p).card ≤
      (Finset.univ : Finset (Option (Fin k))).card :=
    Finset.card_le_card_of_injOn pyramidFacetCoordinate (fun _ _ => Finset.mem_univ _)
      (pyramidFacetCoordinate_injOn_active_below_apex lo hi o hwidth hph)
  simpa using hcard

/-- A non-apex point of the pyramid lies on at most `k + 1` of its facet planes. -/
theorem card_pyramidActiveFacets_le_of_ne_apex {k : ℕ}
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h)
    (hwidth : ∀ i, lo i < hi i) {p : PyramidPoint k}
    (hp : p ∈ pyramidSolid lo hi o h) (hne : p ≠ (o, h)) :
    (pyramidActiveFacets lo hi o h p).card ≤ k + 1 := by
  rw [pyramidSolid_eq_halfspaces lo hi o hh] at hp
  have hph : p.2 < h := lt_of_le_of_ne hp.2.1 (fun heq =>
    hne (eq_apex_of_mem_pyramidHalfspaces_of_height_eq lo hi o hh hp heq))
  exact card_pyramidActiveFacets_le_of_height_lt lo hi o hwidth hph

/-- Incidence with more than `k + 1` listed planes recognizes the apex. -/
theorem eq_apex_of_many_pyramidActiveFacets {k : ℕ}
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h)
    (hwidth : ∀ i, lo i < hi i) {p : PyramidPoint k}
    (hp : p ∈ pyramidSolid lo hi o h)
    (hcard : k + 1 < (pyramidActiveFacets lo hi o h p).card) : p = (o, h) := by
  by_contra hne
  exact (not_lt_of_ge (card_pyramidActiveFacets_le_of_ne_apex lo hi o hh hwidth hp hne))
    hcard

/-- For tangential dimension at least two, `2*k` incident planes force the apex. -/
theorem eq_apex_of_two_mul_le_card_pyramidActiveFacets {k : ℕ} (hk : 2 ≤ k)
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h)
    (hwidth : ∀ i, lo i < hi i) {p : PyramidPoint k}
    (hp : p ∈ pyramidSolid lo hi o h)
    (hcard : 2 * k ≤ (pyramidActiveFacets lo hi o h p).card) : p = (o, h) := by
  apply eq_apex_of_many_pyramidActiveFacets lo hi o hh hwidth hp
  omega

/-- A finite selection of at least `2*k` distinct incident planes suffices. -/
theorem eq_apex_of_incident_pyramidFacets {k : ℕ} (hk : 2 ≤ k)
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h)
    (hwidth : ∀ i, lo i < hi i) {p : PyramidPoint k}
    (hp : p ∈ pyramidSolid lo hi o h) (s : Finset (PyramidFacetIndex k))
    (hcard : 2 * k ≤ s.card)
    (hs : ∀ j ∈ s, p ∈ pyramidFacetPlane lo hi o h j) : p = (o, h) := by
  apply eq_apex_of_two_mul_le_card_pyramidActiveFacets hk lo hi o hh hwidth hp
  exact hcard.trans (Finset.card_le_card (fun j hj =>
    (mem_pyramidActiveFacets lo hi o h p j).mpr (hs j hj)))

/-- The same conclusion for an injectively indexed family of `2*k` planes. -/
theorem eq_apex_of_injective_incident_pyramidFacets {k : ℕ} (hk : 2 ≤ k)
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h)
    (hwidth : ∀ i, lo i < hi i) {p : PyramidPoint k}
    (hp : p ∈ pyramidSolid lo hi o h) (f : Fin (2 * k) → PyramidFacetIndex k)
    (hf : Function.Injective f) (hfp : ∀ i, p ∈ pyramidFacetPlane lo hi o h (f i)) :
    p = (o, h) := by
  classical
  apply eq_apex_of_incident_pyramidFacets hk lo hi o hh hwidth hp
    (Finset.univ.image f)
  · simp [Finset.card_image_of_injective _ hf]
  · intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
    exact hfp i

/-- The recognition criterion can be stated directly with distinct plane sets. -/
theorem eq_apex_of_distinct_incident_pyramidFacetPlanes {k : ℕ} (hk : 2 ≤ k)
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h)
    (hwidth : ∀ i, lo i < hi i) {p : PyramidPoint k}
    (hp : p ∈ pyramidSolid lo hi o h) (s : Finset (Set (PyramidPoint k)))
    (hcard : 2 * k ≤ s.card)
    (hs : ∀ H ∈ s, (∃ j, H = pyramidFacetPlane lo hi o h j) ∧ p ∈ H) :
    p = (o, h) := by
  classical
  apply eq_apex_of_two_mul_le_card_pyramidActiveFacets hk lo hi o hh hwidth hp
  have hsubset : s ⊆ (pyramidActiveFacets lo hi o h p).image
      (pyramidFacetPlane lo hi o h) := by
    intro H hH
    rcases hs H hH with ⟨⟨j, rfl⟩, hpH⟩
    exact Finset.mem_image.mpr ⟨j, (mem_pyramidActiveFacets lo hi o h p j).mpr hpH, rfl⟩
  exact hcard.trans ((Finset.card_le_card hsubset).trans Finset.card_image_le)

/-- Exactly the `2*k` side planes, and not the base, meet at the apex. -/
theorem card_pyramidActiveFacets_apex {k : ℕ} (lo hi o : Fin k → ℝ)
    {h : ℝ} (hh : 0 < h) :
    (pyramidActiveFacets lo hi o h (o, h)).card = 2 * k := by
  classical
  have hset : pyramidActiveFacets lo hi o h (o, h) =
      Finset.univ.erase (none : PyramidFacetIndex k) := by
    ext j
    rw [mem_pyramidActiveFacets, Finset.mem_erase]
    simp only [Finset.mem_univ, and_true]
    cases j with
    | none =>
        constructor
        · intro hp
          exact False.elim ((ne_of_gt hh) hp)
        · intro hn
          exact (hn rfl).elim
    | some s =>
        rcases s with ⟨i, b⟩
        cases b <;> simp [pyramidFacetPlane, Set.mem_setOf_eq]
  rw [hset]
  simp [PyramidFacetIndex, Nat.mul_comm]

/-- In dimension `k ≥ 2`, maximal side incidence characterizes the apex. -/
theorem card_pyramidActiveFacets_eq_two_mul_iff {k : ℕ} (hk : 2 ≤ k)
    (lo hi o : Fin k → ℝ) {h : ℝ} (hh : 0 < h)
    (hwidth : ∀ i, lo i < hi i) {p : PyramidPoint k}
    (hp : p ∈ pyramidSolid lo hi o h) :
    (pyramidActiveFacets lo hi o h p).card = 2 * k ↔ p = (o, h) := by
  constructor
  · intro hcard
    exact eq_apex_of_two_mul_le_card_pyramidActiveFacets hk lo hi o hh hwidth hp
      (le_of_eq hcard.symm)
  · rintro rfl
    exact card_pyramidActiveFacets_apex lo hi o hh

#print axioms pyramidFacetPlane_injective
#print axioms card_pyramidActiveFacets_le_of_ne_apex
#print axioms eq_apex_of_incident_pyramidFacets
#print axioms eq_apex_of_injective_incident_pyramidFacets
#print axioms eq_apex_of_distinct_incident_pyramidFacetPlanes
#print axioms card_pyramidActiveFacets_eq_two_mul_iff

end SparseMonotiles
