module

public import SparseMonotiles.CarrierHierarchyQuotient
public import SparseMonotiles.CarrierHierarchyH0

@[expose] public section

/-!
Construct actual normalized local charts from one global registered cell tiling.
The full-cell tiling and exact relative contact-law premise are explicit. No
independently postulated local worlds or same-index corona transport is used.
Binding this registered world to arbitrary Euclidean physical tilings remains
the separate registration/carrier-ownership obligation.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

def inversePose {d : ℕ} (p : Pose d) : Pose d where
  perm := p.perm.symm
  negative := fun i => p.negative (p.perm.symm i)
  shift := fun i => -p.sign (p.perm.symm i) * p.shift (p.perm.symm i)

theorem compose_root_left {d : ℕ} (p : Pose d) : compose (rootPose d) p = p := by
  apply pose_ext
  · ext i
    rfl
  · funext i
    simp [compose, rootPose]
  · funext i
    simp [compose, rootPose, Pose.sign]

theorem compose_inversePose {d : ℕ} (p : Pose d) : compose p (inversePose p) = rootPose d := by
  apply pose_ext
  · ext i
    simp [compose, inversePose, rootPose]
  · funext i
    simp [compose, inversePose, rootPose]
  · funext i
    simp only [compose, inversePose, rootPose, Equiv.symm_apply_apply, Pose.sign]
    rcases Bool.eq_false_or_eq_true (p.negative i) with h | h <;> simp [h]

theorem inversePose_compose {d : ℕ} (p : Pose d) : compose (inversePose p) p = rootPose d := by
  apply pose_ext
  · ext i
    simp [compose, inversePose, rootPose]
  · funext i
    simp [compose, inversePose, rootPose]
  · funext i
    simp [compose, inversePose, rootPose, Pose.sign]

def normalize {d : ℕ} (p q : Pose d) : Pose d := compose (inversePose p) q

@[simp] theorem normalize_self {d : ℕ} (p : Pose d) : normalize p p = rootPose d :=
  inversePose_compose p

@[simp] theorem compose_normalize {d : ℕ} (p q : Pose d) : compose p (normalize p q) = q := by
  rw [normalize, ← compose_assoc, compose_inversePose, compose_root_left]

theorem normalize_cocycle {d : ℕ} (p q s : Pose d) :
    compose (normalize p q) (normalize q s) = normalize p s := by
  simp only [normalize]
  rw [compose_assoc, ← compose_assoc q, compose_inversePose, compose_root_left]

/-- Occupancy in a normalized chart is exactly occupancy in the original world. -/
theorem normalize_occupies {d : ℕ} (p q : Pose d) (c : Cell d) :
    Occupies (normalize p q) c ↔ Occupies q (p.cell c) := by
  have h := occupies_compose_cell p (normalize p q) c
  rw [compose_normalize] at h
  exact h.symm

theorem root_occupies_cell {d : ℕ} (p : Pose d) (c : Cell d) :
    Occupies p (p.cell c) ↔ IsChairCell c := by
  simp only [Occupies, Pose.inverseCell_cell]

/-- Discrete unit-face adjacency, with no arbitrary bounded search box. -/
def AdjacentCells {d : ℕ} (c b : Cell d) : Prop := ∃ i,
  (b i = c i + 1 ∨ b i = c i - 1) ∧ ∀ j, j ≠ i → b j = c j

theorem AdjacentCells.symm {d : ℕ} {c b : Cell d} (h : AdjacentCells c b) :
    AdjacentCells b c := by
  obtain ⟨i, hi, hj⟩ := h
  exact ⟨i, by omega, fun j hji => (hj j hji).symm⟩

theorem adjacent_cell_image {d : ℕ} (p : Pose d) {c b : Cell d}
    (h : AdjacentCells c b) : AdjacentCells (p.cell c) (p.cell b) := by
  obtain ⟨i, hi, hj⟩ := h
  refine ⟨p.perm.symm i, ?_, ?_⟩
  · simp only [Pose.cell, Equiv.apply_symm_apply]
    rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm i)) with hn | hn <;>
      simp [Pose.sign, hn] <;> omega
  · intro j hji
    have hpi : p.perm j ≠ i := by
      intro he
      apply hji
      simpa only [Equiv.symm_apply_apply] using congrArg p.perm.symm he
    simp [Pose.cell, hj _ hpi]

def CellContact {d : ℕ} (p q : Pose d) : Prop :=
  ∃ c b, Occupies p c ∧ Occupies q b ∧ AdjacentCells c b

theorem CellContact.symm {d : ℕ} {p q : Pose d} (h : CellContact p q) : CellContact q p := by
  obtain ⟨c, b, hc, hb, ha⟩ := h
  exact ⟨b, c, hb, hc, ha.symm⟩

theorem bit_isChairCell {d : ℕ} {a : Bits d} (ha : Proper a) : IsChairCell (bit a) := by
  constructor
  · intro i
    cases h : a i <;> simp [bit, h]
  · obtain ⟨i, hi⟩ := ha
    exact ⟨i, by simp [bit, hi]⟩

theorem exterior_adjacent {d : ℕ} (a : Bits d) (j : Fin d) :
    AdjacentCells (bit a) (exterior a j) := by
  refine ⟨j, ?_, ?_⟩
  · cases h : a j <;> simp [exterior, bit, h]
  · intro i hij
    simp [exterior, hij]

theorem exterior_not_chair {d : ℕ} (a : Bits d) (j : Fin d) : ¬ IsChairCell (exterior a j) := by
  intro h
  have hj := h.1 j
  cases ha : a j <;> simp [exterior, bit, ha] at hj

/-- A global registered tiling by actual occupied integer cells, with one
chosen frame per physical tile. Arbitrary frame gauges need not be synchronized. -/
structure RegisteredWorld (d : ℕ) where
  tiles : Set (Pose d)
  covers : ∀ c, ∃ p ∈ tiles, Occupies p c
  disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
    Occupies p c → Occupies q c → p = q

/-- Exact contact law remains an explicit premise, separate from the world. -/
def RegisteredWorld.Legal {d : ℕ} (W : RegisteredWorld d) (L : Set (Pose d)) : Prop :=
  ∀ p ∈ W.tiles, ∀ q ∈ W.tiles, p ≠ q → CellContact p q → normalize p q ∈ L

def RegisteredWorld.chartTiles {d : ℕ} (W : RegisteredWorld d) (p : Pose d) : Set (Pose d) :=
  {s | ∃ q ∈ W.tiles, q ≠ p ∧ CellContact p q ∧ normalize p q = s}

/-- All local-world fields are derived from the same global tiling and its law. -/
def RegisteredWorld.chart {d : ℕ} (W : RegisteredWorld d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)} {L : Set (Pose d)}
    (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (p : Pose d) (hp : p ∈ W.tiles) : LocalPatch d σ r where
  tiles := W.chartTiles p
  catalog := by
    rintro s ⟨q, hq, hne, hface, rfl⟩
    exact hL _ (hl p hp q hq hne.symm hface)
  covers := by
    intro a ha j
    obtain ⟨q, hq, hqx⟩ := W.covers (p.cell (exterior a j))
    have hne : q ≠ p := by
      intro he
      subst q
      exact exterior_not_chair a j ((root_occupies_cell p _).mp hqx)
    have hface : CellContact p q :=
      ⟨p.cell (bit a), p.cell (exterior a j), (root_occupies_cell p _).mpr (bit_isChairCell ha),
        hqx, adjacent_cell_image p (exterior_adjacent a j)⟩
    exact ⟨normalize p q, ⟨q, hq, hne, hface, rfl⟩, (normalize_occupies p q _).mpr hqx⟩
  root_disjoint := by
    rintro s ⟨q, hq, hne, _, rfl⟩ a ha hs
    have hqOwn := (normalize_occupies p q _).mp hs
    have hpOwn := (root_occupies_cell p (bit a)).mpr (bit_isChairCell ha)
    exact hne (W.disjoint q hq p hp _ hqOwn hpOwn)
  disjoint := by
    rintro s ⟨q, hq, _, _, rfl⟩ t ⟨u, hu, _, _, rfl⟩ c hqc huc
    have he := W.disjoint q hq u hu (p.cell c)
      ((normalize_occupies p q c).mp hqc) ((normalize_occupies p u c).mp huc)
    exact congrArg (normalize p) he

/-- Cross-chart compatibility follows from global ownership, without any claim
that all rows of either root-excluding chart occur in the other. -/
theorem RegisteredWorld.cross_charts {d : ℕ} (W : RegisteredWorld d)
    (p q : Pose d) {r : Equiv.Perm (Fin d)} :
    ∀ s ∈ W.chartTiles p, ∀ t ∈ W.chartTiles q, ∀ c,
      Occupies s c → Occupies (compose (normalize p q) t) c →
      GaugeRel r s (compose (normalize p q) t) := by
  rintro s ⟨u, hu, _, _, rfl⟩ t ⟨v, hv, _, _, rfl⟩ c huc hvc
  rw [normalize_cocycle] at hvc ⊢
  have he := W.disjoint u hu v hv (p.cell c)
    ((normalize_occupies p u c).mp huc) ((normalize_occupies p v c).mp hvc)
  subst v
  exact Or.inl rfl

private theorem central_compose {d : ℕ} (p : Pose d) :
    compose (centralPose d) p = shiftOne p := by
  apply pose_ext
  · ext i
    rfl
  · funext i
    simp [compose, centralPose, shiftOne]
  · funext i
    simp [compose, centralPose, shiftOne, Pose.sign, add_comm]

theorem RegisteredWorld.h0_cross_charts {d : ℕ} (W : RegisteredWorld d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)} {L : Set (Pose d)}
    (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (p q : Pose d) (hp : p ∈ W.tiles) (hq : q ∈ W.tiles)
    (hH0 : normalize p q = centralPose d) :
    H0CrossCompatible (W.chart hL hl p hp) (W.chart hL hl q hq) := by
  have h := W.cross_charts p q (r := r)
  simpa only [H0CrossCompatible, RegisteredWorld.chart, hH0, central_compose] using h

#print axioms RegisteredWorld.chart
#print axioms RegisteredWorld.cross_charts
#print axioms RegisteredWorld.h0_cross_charts
end SparseMonotiles.CarrierHierarchy
