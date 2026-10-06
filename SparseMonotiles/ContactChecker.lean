module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
A finite checker for registered, full-unit-facet contacts. This module does not
assert registration of arbitrary isometries, completeness of a candidate list,
or equality of literal vertex profiles with physical boundary functions.
Those are separate mathematical obligations, never inferred from a list check.
All executable checks below use ordinary `decide`, not a native evaluation axiom.
-/
namespace SparseMonotiles.Contact

abbrev Cell (d : ℕ) := Fin d → ℤ
abbrev ScaledPoint (d : ℕ) := Fin d → ℤ

/-- Output-row convention: y i = sign i * x (perm i) + shift i. -/
structure Pose (d : ℕ) where
  perm : Equiv.Perm (Fin d)
  negative : Fin d → Bool
  shift : Cell d

instance {d : ℕ} : DecidableEq (Pose d) := fun a b =>
  decidable_of_iff (a.perm = b.perm ∧ a.negative = b.negative ∧ a.shift = b.shift)
    (by cases a; cases b; simp only [Pose.mk.injEq])

def Pose.sign {d : ℕ} (p : Pose d) (i : Fin d) : ℤ :=
  if p.negative i then -1 else 1

/-- The correction by -1 for a negative row is essential for lower corners. -/
def Pose.cell {d : ℕ} (p : Pose d) (c : Cell d) : Cell d :=
  fun i => p.sign i * c (p.perm i) + p.shift i - if p.negative i then 1 else 0

def Pose.scaledPoint {d : ℕ} (p : Pose d) (den : ℤ)
    (x : ScaledPoint d) : ScaledPoint d :=
  fun i => p.sign i * x (p.perm i) + den * p.shift i

/-- Literal vertices and bump/dent coefficient; no symbolic component labels. -/
structure VertexKey (d : ℕ) where
  vertices : Finset (ScaledPoint d)
  bump : Bool

instance {d : ℕ} : DecidableEq (VertexKey d) := fun a b =>
  decidable_of_iff (a.vertices = b.vertices ∧ a.bump = b.bump)
    (by cases a; cases b; simp only [VertexKey.mk.injEq])

/-- The coefficient reverses when the two outward normals are opposed. -/
def Pose.key {d : ℕ} (p : Pose d) (den : ℤ) (k : VertexKey d) : VertexKey d :=
  ⟨k.vertices.image (p.scaledPoint den), !k.bump⟩

structure Facet (d : ℕ) where
  cell : Cell d
  axis : Fin d
  positive : Bool

instance {d : ℕ} : DecidableEq (Facet d) := fun a b =>
  decidable_of_iff (a.cell = b.cell ∧ a.axis = b.axis ∧ a.positive = b.positive)
    (by cases a; cases b; simp only [Facet.mk.injEq])

def Facet.normal {d : ℕ} (f : Facet d) : ℤ :=
  if f.positive then 1 else -1

def Facet.centre2 {d : ℕ} (f : Facet d) : Cell d :=
  fun i => 2 * f.cell i + 1 + if i = f.axis then f.normal else 0

/-- Exact equality of facet squares and opposition of their outward normals. -/
def Shared {d : ℕ} (p : Pose d) (a b : Facet d) : Prop :=
  a.centre2 = p.scaledPoint 2 b.centre2 ∧
  p.perm a.axis = b.axis ∧ p.sign a.axis * b.normal = -a.normal

instance {d : ℕ} (p : Pose d) (a b : Facet d) : Decidable (Shared p a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The finite dictionary is an explicit input, not silently trusted geometry. -/
structure Geometry (d : ℕ) where
  denominator : ℤ
  cells : Finset (Cell d)
  facets : Finset (Facet d)
  profile : Facet d → Finset (VertexKey d)

def movedCells {d : ℕ} (g : Geometry d) (p : Pose d) : Finset (Cell d) :=
  g.cells.image p.cell

def movedProfile {d : ℕ} (g : Geometry d) (p : Pose d)
    (b : Facet d) : Finset (VertexKey d) :=
  (g.profile b).image (p.key g.denominator)

/-- Precisely the finite predicate decided here, not arbitrary physical contact. -/
def LegalContact {d : ℕ} (g : Geometry d) (p : Pose d) : Prop :=
  Disjoint g.cells (movedCells g p) ∧
  (∃ a ∈ g.facets, ∃ b ∈ g.facets, Shared p a b) ∧
  ∀ a ∈ g.facets, ∀ b ∈ g.facets,
    Shared p a b → g.profile a = movedProfile g p b

instance {d : ℕ} (g : Geometry d) (p : Pose d) : Decidable (LegalContact g p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def accept {d : ℕ} (g : Geometry d) (p : Pose d) : Bool := decide (LegalContact g p)

@[simp] theorem accept_eq_true {d : ℕ} (g : Geometry d) (p : Pose d) :
    accept g p = true ↔ LegalContact g p := by simp [accept]

inductive Rejection (d : ℕ) where
  | overlap (common : Cell d)
  | unmatchedRoot (root source : Facet d) (key : VertexKey d)
  | unmatchedSource (root source : Facet d) (key : VertexKey d)
  deriving DecidableEq

def Rejection.Valid {d : ℕ} (g : Geometry d) (p : Pose d) : Rejection d → Prop
  | .overlap c => c ∈ g.cells ∧ c ∈ movedCells g p
  | .unmatchedRoot a b k => a ∈ g.facets ∧ b ∈ g.facets ∧ Shared p a b ∧
      k ∈ g.profile a ∧ k ∉ movedProfile g p b
  | .unmatchedSource a b k => a ∈ g.facets ∧ b ∈ g.facets ∧ Shared p a b ∧
      k ∈ g.profile b ∧ p.key g.denominator k ∉ g.profile a

instance {d : ℕ} (g : Geometry d) (p : Pose d) (r : Rejection d) :
    Decidable (r.Valid g p) := by cases r <;> unfold Rejection.Valid <;> infer_instance

def reject {d : ℕ} (g : Geometry d) (p : Pose d) (r : Rejection d) : Bool :=
  decide (r.Valid g p)

@[simp] theorem reject_eq_true {d : ℕ} (g : Geometry d) (p : Pose d)
    (r : Rejection d) : reject g p r = true ↔ r.Valid g p := by simp [reject]

/-- A checked rejection really refutes the entire finite contact predicate. -/
theorem rejection_sound {d : ℕ} {g : Geometry d} {p : Pose d} {r : Rejection d}
    (hr : r.Valid g p) : ¬ LegalContact g p := by
  intro h
  rcases h with ⟨hd, _, hm⟩
  cases r with
  | overlap c => exact Finset.disjoint_left.mp hd hr.1 hr.2
  | unmatchedRoot a b k =>
      rcases hr with ⟨ha, hb, hs, hk, hn⟩
      exact hn ((hm a ha b hb hs) ▸ hk)
  | unmatchedSource a b k =>
      rcases hr with ⟨ha, hb, hs, hk, hn⟩
      apply hn
      rw [hm a ha b hb hs]
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

/-- An accepted row carries a full direct check, not an asserted survivor flag. -/
structure Row (d : ℕ) where
  pose : Pose d
  rejection : Option (Rejection d)

instance {d : ℕ} : DecidableEq (Row d) := fun a b =>
  decidable_of_iff (a.pose = b.pose ∧ a.rejection = b.rejection)
    (by cases a; cases b; simp only [Row.mk.injEq])

def Row.Valid {d : ℕ} (g : Geometry d) (row : Row d) : Prop :=
  match row.rejection with
  | none => LegalContact g row.pose
  | some r => r.Valid g row.pose

instance {d : ℕ} (g : Geometry d) : (row : Row d) → Decidable (row.Valid g)
  | ⟨p, none⟩ => inferInstanceAs (Decidable (LegalContact g p))
  | ⟨p, some r⟩ => inferInstanceAs (Decidable (r.Valid g p))

def Row.accepted {d : ℕ} (row : Row d) : Bool := row.rejection.isNone

def validate {d : ℕ} (g : Geometry d) (rows : List (Row d)) : Bool :=
  rows.all (fun row => decide (row.Valid g))

def acceptedPoses {d : ℕ} (rows : List (Row d)) : List (Pose d) :=
  (rows.filter Row.accepted).map Row.pose

@[simp] theorem validate_eq_true {d : ℕ} (g : Geometry d) (rows : List (Row d)) :
    validate g rows = true ↔ ∀ row ∈ rows, row.Valid g := by
  simp [validate]

theorem Row.valid_iff_contact {d : ℕ} {g : Geometry d} {row : Row d}
    (h : row.Valid g) : LegalContact g row.pose ↔ row.accepted = true := by
  cases he : row.rejection with
  | none => simp_all [Row.Valid, Row.accepted]
  | some r =>
      have hr : r.Valid g row.pose := by simpa [Row.Valid, he] using h
      simp [Row.accepted, he, rejection_sound hr]

/-- All checked survivors are contacts, regardless of candidate completeness. -/
theorem acceptedPoses_sound {d : ℕ} {g : Geometry d} {rows : List (Row d)}
    (hv : validate g rows = true) {p : Pose d} (hp : p ∈ acceptedPoses rows) :
    LegalContact g p := by
  rcases List.mem_map.mp hp with ⟨row, hr, rfl⟩
  rcases List.mem_filter.mp hr with ⟨hr, ha⟩
  exact (Row.valid_iff_contact ((validate_eq_true g rows).mp hv row hr)).mpr ha

/-- Exact language on the explicitly supplied candidates, with no global
completeness claim. This is the unconditional conclusion of a finite replay. -/
theorem candidate_contact_language_exact {d : ℕ} {g : Geometry d}
    {rows : List (Row d)} (hv : validate g rows = true) :
    ∀ p, (p ∈ rows.map Row.pose ∧ LegalContact g p) ↔ p ∈ acceptedPoses rows := by
  intro p
  constructor
  · rintro ⟨hm, hp⟩
    rcases List.mem_map.mp hm with ⟨row, hr, he⟩
    apply List.mem_map.mpr
    refine ⟨row, List.mem_filter.mpr ⟨hr, ?_⟩, he⟩
    apply (Row.valid_iff_contact ((validate_eq_true g rows).mp hv row hr)).mp
    simpa [he] using hp
  · intro hp
    refine ⟨?_, acceptedPoses_sound hv hp⟩
    rcases List.mem_map.mp hp with ⟨row, hr, he⟩
    exact List.mem_map.mpr ⟨row, (List.mem_filter.mp hr).1, he⟩

/-- Exhaustiveness is a separate, explicitly required mathematical hypothesis. -/
theorem contact_language_exact_of_complete {d : ℕ} {g : Geometry d}
    {rows : List (Row d)} (hv : validate g rows = true)
    (complete : ∀ p, LegalContact g p → ∃ row ∈ rows, row.pose = p) :
    ∀ p, LegalContact g p ↔ p ∈ acceptedPoses rows := by
  intro p
  constructor
  · intro hp
    rcases complete p hp with ⟨row, hr, he⟩
    apply List.mem_map.mpr
    refine ⟨row, List.mem_filter.mpr ⟨hr, ?_⟩, he⟩
    apply (Row.valid_iff_contact ((validate_eq_true g rows).mp hv row hr)).mp
    simpa [he] using hp
  · exact acceptedPoses_sound hv

/-- Concatenated certificate chunks can be proved separately in the kernel. -/
@[simp] theorem validate_append {d : ℕ} (g : Geometry d) (a b : List (Row d)) :
    validate g (a ++ b) = (validate g a && validate g b) := by
  simp [validate, List.all_append]

/-- Relabel every coordinate by q, including both input and output pose axes. -/
def Pose.relabel {d : ℕ} (q : Equiv.Perm (Fin d)) (p : Pose d) : Pose d where
  perm := (q.trans p.perm).trans q.symm
  negative := fun i => p.negative (q i)
  shift := fun i => p.shift (q i)

/-- Coordinate form of an open Euclidean unit cube. -/
def OpenCell {d : ℕ} (c : Cell d) (x : Fin d → ℝ) : Prop :=
  ∀ i, (c i : ℝ) < x i ∧ x i < (c i : ℝ) + 1

noncomputable def midpoint {d : ℕ} (c : Cell d) : Fin d → ℝ := fun i => (c i : ℝ) + 1 / 2

def Pose.realPoint {d : ℕ} (p : Pose d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (p.sign i : ℝ) * x (p.perm i) + (p.shift i : ℝ)

/-- The relabeling used by the T3 calibration is genuine affine conjugacy. -/
theorem Pose.relabel_realPoint {d : ℕ} (q : Equiv.Perm (Fin d)) (p : Pose d)
    (x : Fin d → ℝ) :
    (p.relabel q).realPoint (fun i => x (q i)) = fun i => p.realPoint x (q i) := by
  funext i
  rcases Bool.eq_false_or_eq_true (p.negative (q i)) with hn | hn <;>
    simp [Pose.realPoint, Pose.relabel, Pose.sign, Equiv.trans_apply, hn]

theorem midpoint_mem_openCell {d : ℕ} (c : Cell d) : OpenCell c (midpoint c) := by
  intro i
  simp only [midpoint]
  constructor <;> linarith

/-- Negative rows act on unit-cell midpoints with exactly the lower-corner rule. -/
theorem Pose.midpoint_cell {d : ℕ} (p : Pose d) (c : Cell d) :
    p.realPoint (midpoint c) = midpoint (p.cell c) := by
  funext i
  simp only [Pose.realPoint, midpoint, Pose.cell, Pose.sign]
  split <;> simp <;> ring

/-- A cell-overlap certificate exhibits a point in both open carrier cubes.
This makes no claim that the carrier cubes equal the deformed physical tile. -/
theorem overlap_geometric_witness {d : ℕ} {g : Geometry d} {p : Pose d}
    {c : Cell d} (h : (Rejection.overlap c).Valid g p) :
    ∃ a ∈ g.cells, ∃ b ∈ g.cells, ∃ x y : Fin d → ℝ,
      OpenCell a x ∧ OpenCell b y ∧ p.realPoint y = x := by
  rcases h with ⟨hc, hm⟩
  rcases Finset.mem_image.mp hm with ⟨b, hb, he⟩
  refine ⟨c, hc, b, hb, midpoint c, midpoint b,
    midpoint_mem_openCell c, midpoint_mem_openCell b, ?_⟩
  rw [p.midpoint_cell, he]

/-- Literal scaled integer vertices represent exact rational vertices. -/
def rationalVertex {d : ℕ} (den : ℤ) (v : ScaledPoint d) : Fin d → ℚ :=
  fun i => (v i : ℚ) / (den : ℚ)

theorem rationalVertex_injective {d : ℕ} {den : ℤ} (hd : den ≠ 0) :
    Function.Injective (rationalVertex (d := d) den) := by
  intro v w he
  funext i
  have hi := congrFun he i
  have hden : (den : ℚ) ≠ 0 := by exact_mod_cast hd
  have hc : (v i : ℚ) = (w i : ℚ) := (div_left_inj' hden).mp hi
  exact_mod_cast hc

structure RationalVertexKey (d : ℕ) where
  vertices : Finset (Fin d → ℚ)
  bump : Bool

instance {d : ℕ} : DecidableEq (RationalVertexKey d) := fun a b =>
  decidable_of_iff (a.vertices = b.vertices ∧ a.bump = b.bump)
    (by cases a; cases b; simp only [RationalVertexKey.mk.injEq])

def rationalKey {d : ℕ} (den : ℤ) (k : VertexKey d) : RationalVertexKey d :=
  ⟨k.vertices.image (rationalVertex den), k.bump⟩

theorem rationalKey_injective {d : ℕ} {den : ℤ} (hd : den ≠ 0) :
    Function.Injective (rationalKey (d := d) den) := by
  intro k l he
  have hv : k.vertices = l.vertices := Finset.image_injective
    (rationalVertex_injective hd) (congrArg RationalVertexKey.vertices he)
  have hb : k.bump = l.bump := congrArg RationalVertexKey.bump he
  cases k
  cases l
  simp_all

/-- Mismatch of finite vertex profiles persists after exact rational decoding. -/
theorem rational_profiles_ne {d : ℕ} {den : ℤ} (hd : den ≠ 0)
    {s t : Finset (VertexKey d)} (hne : s ≠ t) :
    s.image (rationalKey den) ≠ t.image (rationalKey den) := by
  intro he
  exact hne (Finset.image_injective (rationalKey_injective hd) he)

/-- Rational affine action associated to the registered integer pose. -/
def Pose.rationalPoint {d : ℕ} (p : Pose d) (x : Fin d → ℚ) : Fin d → ℚ :=
  fun i => (p.sign i : ℚ) * x (p.perm i) + (p.shift i : ℚ)

/-- Exact denominator clearing commutes with geometric affine transport. -/
theorem rationalVertex_transformed {d : ℕ} (p : Pose d) {den : ℤ}
    (hd : den ≠ 0) (v : ScaledPoint d) :
    rationalVertex den (p.scaledPoint den v) =
      p.rationalPoint (rationalVertex den v) := by
  funext i
  have hden : (den : ℚ) ≠ 0 := by exact_mod_cast hd
  simp only [rationalVertex, Pose.scaledPoint, Pose.rationalPoint, Int.cast_add,
    Int.cast_mul]
  field_simp
  <;> ring

/-- The literal key transport has exactly the intended rational vertex action. -/
theorem rationalKey_transformed {d : ℕ} (p : Pose d) {den : ℤ}
    (hd : den ≠ 0) (k : VertexKey d) :
    rationalKey den (p.key den k) =
      ⟨(rationalKey den k).vertices.image p.rationalPoint, !k.bump⟩ := by
  change RationalVertexKey.mk _ (!k.bump) = RationalVertexKey.mk _ (!k.bump)
  congr 1
  simp only [rationalKey, Pose.key, Finset.image_image]
  apply Finset.image_congr
  intro v _
  exact rationalVertex_transformed p hd v

/-- A private apex-foot evaluates exactly one normalized pyramid contribution.
For the sparse shapes, geometric separation must supply `private` and `unit`;
this theorem does not assume or assert that those hypotheses have been proved. -/
def profileValue {α X : Type*} (labels : Finset α) (amplitude : α → ℚ)
    (shape : α → X → ℚ) (x : X) : ℚ :=
  ∑ a ∈ labels, amplitude a * shape a x

theorem profileValue_at_private_witness {α X : Type*} [DecidableEq α]
    (labels : Finset α) (amplitude : α → ℚ) (shape : α → X → ℚ)
    {a : α} (ha : a ∈ labels) {x : X} (unit : shape a x = 1)
    (privateSupport : ∀ b ∈ labels, b ≠ a → shape b x = 0) :
    profileValue labels amplitude shape x = amplitude a := by
  unfold profileValue
  rw [Finset.sum_eq_single a]
  · rw [unit, mul_one]
  · intro b hb hba
    rw [privateSupport b hb hba, mul_zero]
  · intro h
    exact (h ha).elim

/-- An unmatched coefficient gives a concrete rational height discrepancy when
all other allowed key supports miss its private apex-foot witness. -/
theorem profile_ne_of_private_witness {α X : Type*} [DecidableEq α]
    (labels : Finset α) (root source : α → ℚ) (shape : α → X → ℚ)
    {a : α} (ha : a ∈ labels) {x : X} (unit : shape a x = 1)
    (privateSupport : ∀ b ∈ labels, b ≠ a → shape b x = 0)
    (mismatch : root a ≠ source a) :
    profileValue labels root shape x ≠ profileValue labels source shape x := by
  simpa only [profileValue_at_private_witness labels root shape ha unit privateSupport,
    profileValue_at_private_witness labels source shape ha unit privateSupport] using mismatch

/-- Compact integer signature of a rectangular pyramid, before vertex expansion. -/
structure BoxKey (d : ℕ) where
  centre : ScaledPoint d
  radius : ScaledPoint d
  apex : ScaledPoint d
  bump : Bool

instance {d : ℕ} : DecidableEq (BoxKey d) := fun a b =>
  decidable_of_iff
    (a.centre = b.centre ∧ a.radius = b.radius ∧ a.apex = b.apex ∧ a.bump = b.bump)
    (by cases a; cases b; simp only [BoxKey.mk.injEq])

def BoxKey.corner {d : ℕ} (k : BoxKey d) (bits : Fin d → Bool) : ScaledPoint d :=
  fun i => k.centre i + if bits i then k.radius i else -k.radius i

def BoxKey.literal {d : ℕ} (k : BoxKey d) : VertexKey d :=
  ⟨insert k.apex (Finset.univ.image k.corner), k.bump⟩

def Pose.boxKey {d : ℕ} (p : Pose d) (den : ℤ) (k : BoxKey d) : BoxKey d :=
  ⟨p.scaledPoint den k.centre, fun i => k.radius (p.perm i),
    p.scaledPoint den k.apex, !k.bump⟩

def Pose.cornerBits {d : ℕ} (p : Pose d) (bits : Fin d → Bool) : Fin d → Bool :=
  fun i => if p.negative i then !(bits (p.perm i)) else bits (p.perm i)

theorem Pose.cornerBits_surjective {d : ℕ} (p : Pose d) :
    Function.Surjective p.cornerBits := by
  intro bits
  refine ⟨fun j => if p.negative (p.perm.symm j) then
    !(bits (p.perm.symm j)) else bits (p.perm.symm j), ?_⟩
  funext i
  simp only [Pose.cornerBits, Equiv.symm_apply_apply]
  cases p.negative i <;> simp

theorem Pose.corner_transformed {d : ℕ} (p : Pose d) (den : ℤ)
    (k : BoxKey d) (bits : Fin d → Bool) :
    p.scaledPoint den (k.corner bits) =
      (p.boxKey den k).corner (p.cornerBits bits) := by
  funext i
  simp only [Pose.scaledPoint, Pose.boxKey, BoxKey.corner, Pose.cornerBits, Pose.sign]
  rcases Bool.eq_false_or_eq_true (p.negative i) with hn | hn <;>
    rcases Bool.eq_false_or_eq_true (bits (p.perm i)) with hb | hb <;>
    simp [hn, hb] <;> ring

/-- One symbolic proof replaces repeated enumeration of all 2^(d-1) corners. -/
theorem Pose.boxKey_literal {d : ℕ} (p : Pose d) (den : ℤ) (k : BoxKey d) :
    (p.boxKey den k).literal = p.key den k.literal := by
  change VertexKey.mk _ (!k.bump) = VertexKey.mk _ (!k.bump)
  congr 1
  simp only [BoxKey.literal, Pose.boxKey, Pose.key, Finset.image_insert,
    Finset.image_image]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨bits, rfl⟩
    obtain ⟨original, ho⟩ := p.cornerBits_surjective bits
    refine ⟨original, ?_⟩
    rw [p.corner_transformed, ho]
    rfl
  · rintro ⟨bits, rfl⟩
    exact ⟨p.cornerBits bits, (p.corner_transformed den k bits).symm⟩

structure BoxGeometry (d : ℕ) where
  denominator : ℤ
  cells : Finset (Cell d)
  facets : Finset (Facet d)
  profile : Facet d → Finset (BoxKey d)

def BoxGeometry.literal {d : ℕ} (g : BoxGeometry d) : Geometry d where
  denominator := g.denominator
  cells := g.cells
  facets := g.facets
  profile := fun f => (g.profile f).image BoxKey.literal

def BoxGeometry.LegalContact {d : ℕ} (g : BoxGeometry d) (p : Pose d) : Prop :=
  Disjoint g.cells (g.cells.image p.cell) ∧
  (∃ a ∈ g.facets, ∃ b ∈ g.facets, Shared p a b) ∧
  ∀ a ∈ g.facets, ∀ b ∈ g.facets, Shared p a b →
    g.profile a = (g.profile b).image (p.boxKey g.denominator)

instance {d : ℕ} (g : BoxGeometry d) (p : Pose d) :
    Decidable (g.LegalContact p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Exact integer signature acceptance entails literal-vertex acceptance. -/
theorem BoxGeometry.legal_sound {d : ℕ} {g : BoxGeometry d} {p : Pose d}
    (h : g.LegalContact p) : SparseMonotiles.Contact.LegalContact g.literal p := by
  rcases h with ⟨hc, hs, hk⟩
  refine ⟨hc, hs, ?_⟩
  intro a ha b hb hab
  change (g.profile a).image BoxKey.literal = _
  rw [hk a ha b hb hab]
  simp only [movedProfile, BoxGeometry.literal, Finset.image_image]
  apply Finset.image_congr
  intro k _
  exact p.boxKey_literal g.denominator k

/-- Use a separately proved sufficient acceptance test; rejections remain exact. -/
def verifyWith {d : ℕ} (g : Geometry d) (fast : Pose d → Bool) (row : Row d) : Bool :=
  match row.rejection with
  | none => fast row.pose
  | some r => reject g row.pose r

def validateWith {d : ℕ} (g : Geometry d) (fast : Pose d → Bool)
    (rows : List (Row d)) : Bool := rows.all (verifyWith g fast)

theorem validateWith_sound {d : ℕ} {g : Geometry d} {fast : Pose d → Bool}
    (sound : ∀ p, fast p = true → LegalContact g p) {rows : List (Row d)}
    (h : validateWith g fast rows = true) : validate g rows = true := by
  apply (validate_eq_true g rows).mpr
  intro row hr
  have hv := List.all_eq_true.mp h row hr
  cases he : row.rejection with
  | none =>
      have hp : LegalContact g row.pose := sound row.pose (by simpa [verifyWith, he] using hv)
      simpa [Row.Valid, he] using hp
  | some r =>
      have hp := (reject_eq_true g row.pose r).mp (by simpa [verifyWith, he] using hv)
      simpa [Row.Valid, he] using hp

#print axioms candidate_contact_language_exact
#print axioms Pose.relabel_realPoint
#print axioms rejection_sound
#print axioms contact_language_exact_of_complete
#print axioms overlap_geometric_witness
#print axioms rational_profiles_ne
#print axioms rationalKey_transformed
#print axioms profile_ne_of_private_witness
#print axioms Pose.boxKey_literal
#print axioms BoxGeometry.legal_sound
#print axioms validateWith_sound

end SparseMonotiles.Contact
