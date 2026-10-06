module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Migration pilot only: three supporting statements copied from the actual
4.19 development. This is not the full monotile claim or a submission. -/

namespace SparseMonotiles

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure KeyData (d : ℕ) where
  centre : Fin d → ℚ
  radius : Fin d → ℚ
  apex : Fin d → ℚ
  bump : Bool

noncomputable def rationalPoint {d : ℕ} (q : Fin d → ℚ) : Point d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (q i : ℝ))

def keyBase {d : ℕ} (k : KeyData d) : Set (Point d) :=
  {x | ∀ i, |x i - (k.centre i : ℝ)| ≤ (k.radius i : ℝ)}

def keySolid {d : ℕ} (k : KeyData d) : Set (Point d) :=
  convexHull ℝ (insert (rationalPoint k.apex) (keyBase k))

/-- The closed union of all binary unit cubes except the all-one cube. -/
def carrier (d : ℕ) : Set (Point d) :=
  {x | ∃ c : Fin d → Bool,
    (∃ i, c i = false) ∧
    ∀ i, (if c i then (1 : ℝ) else 0) ≤ x i ∧
      x i ≤ (if c i then (1 : ℝ) else 0) + 1}

def keyUnion {d : ℕ} (ks : List (KeyData d)) (b : Bool) : Set (Point d) :=
  {x | ∃ k ∈ ks, k.bump = b ∧ x ∈ keySolid k}

/-- Closure restores the boundary of each removed closed dent pyramid. -/
def body {d : ℕ} (ks : List (KeyData d)) : Set (Point d) :=
  closure ((carrier d ∪ keyUnion ks true) \ keyUnion ks false)

/-- A tiling is a set of physical tiles, not a set of chosen frames. -/
def IsTiling {d : ℕ} (T : Set (Point d)) (tiles : Set (Set (Point d))) : Prop :=
  (∀ A ∈ tiles, ∃ g : Point d ≃ᵢ Point d, A = g '' T) ∧
  (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
  (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))

def translate {d : ℕ} (v : Point d) (A : Set (Point d)) : Set (Point d) :=
  (fun x => x + v) '' A

/-- Translation must preserve the physical tile collection, not just its union. -/
def IsPeriod {d : ℕ} (tiles : Set (Set (Point d))) (v : Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ translate v A ∈ tiles

def HasTiling {d : ℕ} (T : Set (Point d)) : Prop :=
  ∃ tiles, IsTiling T tiles

def IsAperiodic {d : ℕ} (T : Set (Point d)) : Prop :=
  ∀ tiles, IsTiling T tiles → ∀ v, IsPeriod tiles v → v = 0

def IsAperiodicMonotile {d : ℕ} (T : Set (Point d)) : Prop :=
  IsCompact T ∧ HasTiling T ∧ IsAperiodic T

theorem body_isClosed {d : ℕ} (ks : List (KeyData d)) : IsClosed (body ks) := by
  sorry

end SparseMonotiles

namespace SparseMonotiles

def widths5 : Fin 4 → ℚ := ![1/80, 1/64, 3/160, 7/320]
def offsets5 : Fin 4 → ℚ := ![1/240, 1/256, 3/800, 7/1920]
def widths7 : Fin 6 → ℚ := ![1/112, 1/96, 1/84, 3/224, 5/336, 11/672]
def offsets7 : Fin 6 → ℚ := ![1/336, 1/384, 1/420, 1/448, 5/2352, 11/5376]

theorem key5_offsets_inside (i : Fin 4) :
    0 < offsets5 i ∧ offsets5 i < widths5 i := by
  fin_cases i <;> norm_num [offsets5, widths5]

theorem key7_offsets_inside (i : Fin 6) :
    0 < offsets7 i ∧ offsets7 i < widths7 i := by
  fin_cases i <;> norm_num [offsets7, widths7]

theorem key5_inside_collar (i : Fin 4) :
    ((i.val + 1 : ℕ) : ℚ) / 20 + widths5 i < 1/4 := by
  sorry

end SparseMonotiles

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
  sorry

end SparseMonotiles.Contact

namespace SparseMonotiles.Contact

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


end SparseMonotiles.Contact

namespace SparseMonotiles.Contact.Calibration3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def perm0 : Equiv.Perm (Fin 3) :=
  ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩
def perm1 : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def perm2 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
def perm3 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def perm4 : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
def perm5 : Equiv.Perm (Fin 3) :=
  ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩
def key0 : VertexKey 3 :=
  ⟨{![-8, 777, 472], ![0, 732, 456], ![0, 732, 504], ![0, 804, 456], ![0, 804, 504]}, true⟩
def key1 : VertexKey 3 :=
  ⟨{![732, 0, 456], ![732, 0, 504], ![777, 8, 472], ![804, 0, 456], ![804, 0, 504]}, false⟩
def key2 : VertexKey 3 :=
  ⟨{![456, 348, 0], ![456, 420, 0], ![472, 375, -8], ![504, 348, 0], ![504, 420, 0]}, true⟩
def key3 : VertexKey 3 :=
  ⟨{![348, 456, 0], ![348, 504, 0], ![375, 472, 8], ![420, 456, 0], ![420, 504, 0]}, false⟩
def key4 : VertexKey 3 :=
  ⟨{![0, 732, 1800], ![0, 732, 1848], ![0, 804, 1800], ![0, 804, 1848], ![8, 777, 1832]}, false⟩
def key5 : VertexKey 3 :=
  ⟨{![732, 0, 1800], ![732, 0, 1848], ![777, -8, 1832], ![804, 0, 1800], ![804, 0, 1848]}, true⟩
def key6 : VertexKey 3 :=
  ⟨{![456, 348, 2304], ![456, 420, 2304], ![472, 375, 2296], ![504, 348, 2304], ![504, 420, 2304]}, false⟩
def key7 : VertexKey 3 :=
  ⟨{![348, 456, 2304], ![348, 504, 2304], ![375, 472, 2312], ![420, 456, 2304], ![420, 504, 2304]}, true⟩
def key8 : VertexKey 3 :=
  ⟨{![-8, 1832, 777], ![0, 1800, 732], ![0, 1800, 804], ![0, 1848, 732], ![0, 1848, 804]}, true⟩
def key9 : VertexKey 3 :=
  ⟨{![456, 2304, 348], ![456, 2304, 420], ![472, 2312, 375], ![504, 2304, 348], ![504, 2304, 420]}, true⟩
def key10 : VertexKey 3 :=
  ⟨{![348, 2304, 456], ![348, 2304, 504], ![375, 2296, 472], ![420, 2304, 456], ![420, 2304, 504]}, false⟩
def key11 : VertexKey 3 :=
  ⟨{![732, 1800, 0], ![732, 1848, 0], ![777, 1832, 8], ![804, 1800, 0], ![804, 1848, 0]}, false⟩
def key12 : VertexKey 3 :=
  ⟨{![-8, 1832, 1929], ![0, 1800, 1884], ![0, 1800, 1956], ![0, 1848, 1884], ![0, 1848, 1956]}, true⟩
def key13 : VertexKey 3 :=
  ⟨{![0, 1884, 1800], ![0, 1884, 1848], ![0, 1956, 1800], ![0, 1956, 1848], ![8, 1929, 1832]}, false⟩
def key14 : VertexKey 3 :=
  ⟨{![1144, 1929, 1624], ![1152, 1884, 1608], ![1152, 1884, 1656], ![1152, 1956, 1608], ![1152, 1956, 1656]}, false⟩
def key15 : VertexKey 3 :=
  ⟨{![456, 2304, 1500], ![456, 2304, 1572], ![472, 2312, 1527], ![504, 2304, 1500], ![504, 2304, 1572]}, true⟩
def key16 : VertexKey 3 :=
  ⟨{![456, 1500, 2304], ![456, 1572, 2304], ![472, 1527, 2296], ![504, 1500, 2304], ![504, 1572, 2304]}, false⟩
def key17 : VertexKey 3 :=
  ⟨{![2296, 472, 375], ![2304, 456, 348], ![2304, 456, 420], ![2304, 504, 348], ![2304, 504, 420]}, false⟩
def key18 : VertexKey 3 :=
  ⟨{![2304, 348, 456], ![2304, 348, 504], ![2304, 420, 456], ![2304, 420, 504], ![2312, 375, 472]}, true⟩
def key19 : VertexKey 3 :=
  ⟨{![1800, 0, 732], ![1800, 0, 804], ![1832, 8, 777], ![1848, 0, 732], ![1848, 0, 804]}, false⟩
def key20 : VertexKey 3 :=
  ⟨{![1800, 732, 0], ![1800, 804, 0], ![1832, 777, -8], ![1848, 732, 0], ![1848, 804, 0]}, true⟩
def key21 : VertexKey 3 :=
  ⟨{![2296, 472, 1527], ![2304, 456, 1500], ![2304, 456, 1572], ![2304, 504, 1500], ![2304, 504, 1572]}, false⟩
def key22 : VertexKey 3 :=
  ⟨{![1800, 0, 1884], ![1800, 0, 1956], ![1832, 8, 1929], ![1848, 0, 1884], ![1848, 0, 1956]}, false⟩
def key23 : VertexKey 3 :=
  ⟨{![1884, 0, 1800], ![1884, 0, 1848], ![1929, -8, 1832], ![1956, 0, 1800], ![1956, 0, 1848]}, true⟩
def key24 : VertexKey 3 :=
  ⟨{![1884, 1152, 1608], ![1884, 1152, 1656], ![1929, 1160, 1624], ![1956, 1152, 1608], ![1956, 1152, 1656]}, true⟩
def key25 : VertexKey 3 :=
  ⟨{![1500, 456, 2304], ![1500, 504, 2304], ![1527, 472, 2312], ![1572, 456, 2304], ![1572, 504, 2304]}, true⟩
def key26 : VertexKey 3 :=
  ⟨{![2304, 1500, 456], ![2304, 1500, 504], ![2304, 1572, 456], ![2304, 1572, 504], ![2312, 1527, 472]}, true⟩
def key27 : VertexKey 3 :=
  ⟨{![1500, 2304, 456], ![1500, 2304, 504], ![1527, 2296, 472], ![1572, 2304, 456], ![1572, 2304, 504]}, false⟩
def key28 : VertexKey 3 :=
  ⟨{![1800, 1884, 0], ![1800, 1956, 0], ![1832, 1929, -8], ![1848, 1884, 0], ![1848, 1956, 0]}, true⟩
def key29 : VertexKey 3 :=
  ⟨{![1884, 1800, 0], ![1884, 1848, 0], ![1929, 1832, 8], ![1956, 1800, 0], ![1956, 1848, 0]}, false⟩
def key30 : VertexKey 3 :=
  ⟨{![1608, 1500, 1152], ![1608, 1572, 1152], ![1624, 1527, 1144], ![1656, 1500, 1152], ![1656, 1572, 1152]}, false⟩
def key31 : VertexKey 3 :=
  ⟨{![1500, 1608, 1152], ![1500, 1656, 1152], ![1527, 1624, 1160], ![1572, 1608, 1152], ![1572, 1656, 1152]}, true⟩
def facet0 : Facet 3 := ⟨![0, 0, 0], 0, false⟩
def facet1 : Facet 3 := ⟨![0, 0, 0], 1, false⟩
def facet2 : Facet 3 := ⟨![0, 0, 0], 2, false⟩
def facet3 : Facet 3 := ⟨![0, 0, 1], 0, false⟩
def facet4 : Facet 3 := ⟨![0, 0, 1], 1, false⟩
def facet5 : Facet 3 := ⟨![0, 0, 1], 2, true⟩
def facet6 : Facet 3 := ⟨![0, 1, 0], 0, false⟩
def facet7 : Facet 3 := ⟨![0, 1, 0], 1, true⟩
def facet8 : Facet 3 := ⟨![0, 1, 0], 2, false⟩
def facet9 : Facet 3 := ⟨![0, 1, 1], 0, false⟩
def facet10 : Facet 3 := ⟨![0, 1, 1], 0, true⟩
def facet11 : Facet 3 := ⟨![0, 1, 1], 1, true⟩
def facet12 : Facet 3 := ⟨![0, 1, 1], 2, true⟩
def facet13 : Facet 3 := ⟨![1, 0, 0], 0, true⟩
def facet14 : Facet 3 := ⟨![1, 0, 0], 1, false⟩
def facet15 : Facet 3 := ⟨![1, 0, 0], 2, false⟩
def facet16 : Facet 3 := ⟨![1, 0, 1], 0, true⟩
def facet17 : Facet 3 := ⟨![1, 0, 1], 1, false⟩
def facet18 : Facet 3 := ⟨![1, 0, 1], 1, true⟩
def facet19 : Facet 3 := ⟨![1, 0, 1], 2, true⟩
def facet20 : Facet 3 := ⟨![1, 1, 0], 0, true⟩
def facet21 : Facet 3 := ⟨![1, 1, 0], 1, true⟩
def facet22 : Facet 3 := ⟨![1, 1, 0], 2, false⟩
def facet23 : Facet 3 := ⟨![1, 1, 0], 2, true⟩
def geometry : Geometry 3 where
  denominator := 1152
  cells := {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0]}
  facets := {facet0, facet1, facet2, facet3, facet4, facet5, facet6, facet7, facet8, facet9, facet10, facet11, facet12, facet13, facet14, facet15, facet16, facet17, facet18, facet19, facet20, facet21, facet22, facet23}
  profile := fun f =>
    if f = facet0 then {key0} else
    if f = facet1 then {key1} else
    if f = facet2 then {key2, key3} else
    if f = facet3 then {key4} else
    if f = facet4 then {key5} else
    if f = facet5 then {key6, key7} else
    if f = facet6 then {key8} else
    if f = facet7 then {key9, key10} else
    if f = facet8 then {key11} else
    if f = facet9 then {key12, key13} else
    if f = facet10 then {key14} else
    if f = facet11 then {key15} else
    if f = facet12 then {key16} else
    if f = facet13 then {key17, key18} else
    if f = facet14 then {key19} else
    if f = facet15 then {key20} else
    if f = facet16 then {key21} else
    if f = facet17 then {key22, key23} else
    if f = facet18 then {key24} else
    if f = facet19 then {key25} else
    if f = facet20 then {key26} else
    if f = facet21 then {key27} else
    if f = facet22 then {key28, key29} else
    if f = facet23 then {key30, key31} else
    ∅

def chunk0 : List (Row 3) := [
  ⟨⟨perm0, ![true, false, false], ![0, 0, 0]⟩, some (.unmatchedRoot facet0 facet0 key0)⟩,
  ⟨⟨perm2, ![true, false, false], ![0, 0, 0]⟩, none⟩,
  ⟨⟨perm5, ![true, true, false], ![0, 1, 0]⟩, some (.unmatchedRoot facet0 facet2 key0)⟩,
  ⟨⟨perm4, ![true, true, false], ![0, 1, 0]⟩, some (.unmatchedSource facet0 facet2 key2)⟩,
  ⟨⟨perm0, ![true, false, true], ![0, 0, 2]⟩, some (.unmatchedRoot facet6 facet9 key8)⟩,
  ⟨⟨perm2, ![true, false, true], ![0, 0, 2]⟩, some (.unmatchedRoot facet0 facet4 key0)⟩,
  ⟨⟨perm5, ![false, true, false], ![-2, 1, 0]⟩, some (.unmatchedSource facet0 facet5 key7)⟩,
  ⟨⟨perm4, ![false, true, false], ![-2, 1, 0]⟩, some (.unmatchedRoot facet0 facet5 key0)⟩
]

theorem chunk0_checked : validate geometry chunk0 = true := by
  sorry

end SparseMonotiles.Contact.Calibration3
