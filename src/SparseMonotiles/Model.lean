module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.Isometry

@[expose] public section

/-!
The exact target is an unmarked body in Euclidean space. Arbitrary isometries,
including reflections, are allowed. No registration or hierarchy theorem is
assumed by these definitions.
-/
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

theorem body_isClosed {d : ℕ} (ks : List (KeyData d)) : IsClosed (body ks) :=
  isClosed_closure

end SparseMonotiles
