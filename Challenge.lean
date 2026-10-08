module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# HENRY: exact seven-dimensional physical statement

The body below uses all 1024 rational keys, in the exact pinned JSON order.
The carrier consists of the 127 binary unit cubes other than the all-one cube.
A literal palette of 28 rational coordinate triples and the 1024 ordered
seven-index records below determine every centre, radius, apex and bump flag.
The decoder constructs each rational vector explicitly; it asserts no theorem.
This independent statement imports only Mathlib. It imports no implementation,
contact catalogue, classification, tiling proof, or registration hypothesis.

The specification SHA-256 is
2d8a6562eb1ee4f7ebeb0af571c783d92fb5c3296bc638848aad13ebcd2230a2.
The hash documents provenance; it is not used as a mathematical definition.
-/
namespace PalomarMonotiles

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


set_option maxRecDepth 100000

/-- Coordinate palette: each entry is (centre, radius, apex) on one axis.
Every used index is in 0..27. The unused default makes the decoder total.
All rational values are explicit; this table contains no geometric premise. -/
def coordinate7 : ℕ → ℚ × ℚ × ℚ
  | 0 => (0, 0, (1 / 336))
  | 1 => ((11 / 28), (1 / 84), (41 / 105))
  | 2 => ((4 / 7), (1 / 96), (1543 / 2688))
  | 3 => ((15 / 28), (1 / 112), (181 / 336))
  | 4 => ((5 / 7), (11 / 672), (3851 / 5376))
  | 5 => ((19 / 28), (5 / 336), (1601 / 2352))
  | 6 => ((5 / 14), (3 / 224), (159 / 448))
  | 7 => (0, 0, (-1 / 336))
  | 8 => ((17 / 28), (1 / 84), (64 / 105))
  | 9 => ((9 / 14), (3 / 224), (289 / 448))
  | 10 => ((9 / 28), (5 / 336), (751 / 2352))
  | 11 => ((2 / 7), (11 / 672), (1525 / 5376))
  | 12 => ((39 / 28), (1 / 84), (146 / 105))
  | 13 => ((47 / 28), (5 / 336), (3953 / 2352))
  | 14 => ((37 / 28), (5 / 336), (3103 / 2352))
  | 15 => (2, 0, (673 / 336))
  | 16 => (2, 0, (671 / 336))
  | 17 => ((10 / 7), (1 / 96), (3833 / 2688))
  | 18 => ((12 / 7), (11 / 672), (9227 / 5376))
  | 19 => ((9 / 7), (11 / 672), (6901 / 5376))
  | 20 => ((41 / 28), (1 / 112), (491 / 336))
  | 21 => ((19 / 14), (3 / 224), (607 / 448))
  | 22 => ((23 / 14), (3 / 224), (737 / 448))
  | 23 => ((45 / 28), (1 / 84), (169 / 105))
  | 24 => (1, 0, (337 / 336))
  | 25 => ((11 / 7), (1 / 96), (4231 / 2688))
  | 26 => ((43 / 28), (1 / 112), (517 / 336))
  | 27 => (1, 0, (335 / 336))
  | _ => (0, 0, 0)

/-- Seven palette indices and a bump flag determine one closed pyramid.
The projections are inside the explicit vectors, so literal records reduce
definitionally to the uncompressed centre/radius/apex vectors. -/
def key7 (a b c d e f g : ℕ) (bump : Bool) : KeyData 7 :=
  ⟨![(coordinate7 a).1, (coordinate7 b).1, (coordinate7 c).1, (coordinate7 d).1, (coordinate7 e).1, (coordinate7 f).1, (coordinate7 g).1],
   ![(coordinate7 a).2.1, (coordinate7 b).2.1, (coordinate7 c).2.1, (coordinate7 d).2.1, (coordinate7 e).2.1, (coordinate7 f).2.1, (coordinate7 g).2.1],
   ![(coordinate7 a).2.2, (coordinate7 b).2.2, (coordinate7 c).2.2, (coordinate7 d).2.2, (coordinate7 e).2.2, (coordinate7 f).2.2, (coordinate7 g).2.2], bump⟩

def keys7Chunk0 : List (KeyData 7) := [
  key7 0 1 2 3 4 5 6 false, key7 7 6 5 4 3 2 1 true,
  key7 8 7 9 10 11 3 2 true, key7 10 9 7 8 2 3 4 true,
  key7 5 6 8 0 2 3 11 false, key7 5 11 3 2 7 8 6 true,
  key7 10 4 3 2 8 0 9 false, key7 8 2 3 11 10 9 0 false,
  key7 0 9 10 11 3 2 12 false, key7 9 0 8 2 3 4 13 false,
  key7 6 8 7 2 3 11 14 true, key7 11 3 2 0 8 6 14 false,
  key7 4 3 2 8 7 9 13 true, key7 2 3 11 10 9 7 12 true,
  key7 1 2 3 4 5 6 15 true, key7 6 5 4 3 2 1 16 false,
  key7 0 8 2 3 4 13 9 false, key7 8 7 2 3 11 14 6 true,
  key7 3 2 0 8 6 14 11 false, key7 3 2 8 7 9 13 4 true,
  key7 3 11 10 9 7 12 2 true, key7 2 3 4 5 6 15 1 true,
  key7 5 4 3 2 1 16 6 false, key7 9 10 11 3 2 12 0 false,
  key7 0 9 10 4 3 17 12 false, key7 9 0 8 2 3 18 13 false,
  key7 2 1 7 6 5 19 20 true, key7 5 6 0 1 2 20 19 false,
  key7 3 2 8 7 9 13 18 true, key7 3 4 10 9 7 12 17 true,
  key7 3 11 5 6 8 16 17 false, key7 8 6 5 11 3 17 15 true
]

def keys7Chunk1 : List (KeyData 7) := [
  key7 7 2 3 11 14 6 8 true, key7 2 0 8 6 14 11 3 false,
  key7 2 8 7 9 13 4 3 true, key7 11 10 9 7 12 2 3 true,
  key7 3 4 5 6 15 1 2 true, key7 4 3 2 1 16 6 5 false,
  key7 10 11 3 2 12 0 9 false, key7 8 2 3 4 13 9 0 false,
  key7 7 8 2 3 19 10 21 true, key7 8 0 2 3 18 5 22 false,
  key7 3 2 7 8 22 5 18 true, key7 3 2 8 0 21 10 19 false,
  key7 3 11 10 9 16 8 17 false, key7 2 3 4 5 22 0 23 false,
  key7 5 4 3 2 23 7 22 true, key7 9 10 11 3 17 8 15 true,
  key7 0 8 2 3 18 13 9 false, key7 1 7 6 5 19 20 2 true,
  key7 6 0 1 2 20 19 5 false, key7 2 8 7 9 13 18 3 true,
  key7 4 10 9 7 12 17 3 true, key7 11 5 6 8 16 17 3 false,
  key7 6 5 11 3 17 15 8 true, key7 9 10 4 3 17 12 0 false,
  key7 0 8 2 3 19 13 21 false, key7 8 7 2 3 18 14 22 true,
  key7 3 2 0 8 22 14 18 false, key7 3 2 8 7 21 13 19 true,
  key7 3 11 10 9 15 12 17 true, key7 2 3 4 5 22 15 23 true,
  key7 5 4 3 2 23 16 22 false, key7 9 10 11 3 17 12 16 false
]

def keys7Chunk2 : List (KeyData 7) := [
  key7 0 8 6 14 11 3 2 false, key7 8 7 9 13 4 3 2 true,
  key7 10 9 7 12 2 3 11 true, key7 3 2 1 16 6 5 4 false,
  key7 4 5 6 15 1 2 3 true, key7 11 3 2 12 0 9 10 false,
  key7 2 3 4 13 9 0 8 false, key7 2 3 11 14 6 8 7 true,
  key7 0 8 2 20 11 10 21 false, key7 1 7 6 14 4 3 17 true,
  key7 6 0 1 17 3 4 14 false, key7 2 8 7 21 10 11 20 true,
  key7 4 10 9 15 8 2 20 true, key7 11 5 6 12 0 2 20 false,
  key7 6 5 11 20 2 7 12 true, key7 9 10 4 20 2 8 16 false,
  key7 0 2 3 18 5 22 8 false, key7 2 7 8 22 5 18 3 true,
  key7 2 8 0 21 10 19 3 false, key7 11 10 9 16 8 17 3 false,
  key7 3 4 5 22 0 23 2 false, key7 4 3 2 23 7 22 5 true,
  key7 10 11 3 17 8 15 9 true, key7 8 2 3 19 10 21 7 true,
  key7 7 1 2 20 4 14 22 true, key7 0 6 5 19 3 17 23 false,
  key7 8 0 9 13 11 20 17 false, key7 10 9 0 12 2 20 19 false,
  key7 5 6 8 15 2 20 18 true, key7 5 11 3 17 0 12 22 false,
  key7 10 4 3 17 8 15 21 true, key7 8 2 3 18 10 21 15 true
]

def keys7Chunk3 : List (KeyData 7) := [
  key7 0 1 2 20 19 5 6 false, key7 7 6 5 19 20 2 1 true,
  key7 8 7 9 13 18 3 2 true, key7 10 9 7 12 17 3 4 true,
  key7 5 6 8 16 17 3 11 false, key7 5 11 3 17 15 8 6 true,
  key7 10 4 3 17 12 0 9 false, key7 8 2 3 18 13 9 0 false,
  key7 7 9 10 19 20 2 12 true, key7 9 7 8 17 20 11 13 true,
  key7 2 1 0 22 14 4 20 false, key7 5 6 7 23 17 3 19 true,
  key7 3 2 8 16 21 10 18 false, key7 3 4 10 21 16 8 17 false,
  key7 3 11 5 22 12 7 17 true, key7 8 6 5 18 20 2 16 false,
  key7 7 2 3 18 14 22 8 true, key7 2 0 8 22 14 18 3 false,
  key7 2 8 7 21 13 19 3 true, key7 11 10 9 15 12 17 3 true,
  key7 3 4 5 22 15 23 2 true, key7 4 3 2 23 16 22 5 false,
  key7 10 11 3 17 12 16 9 false, key7 8 2 3 19 13 21 0 false,
  key7 0 8 2 20 18 13 21 false, key7 1 7 6 14 19 20 17 true,
  key7 6 0 1 17 20 19 14 false, key7 2 8 7 21 13 18 20 true,
  key7 4 10 9 15 12 17 20 true, key7 11 5 6 12 16 17 20 false,
  key7 6 5 11 20 17 15 12 true, key7 9 10 4 20 17 12 16 false
]

def keys7Chunk4 : List (KeyData 7) := [
  key7 7 9 13 4 3 2 8 true, key7 9 7 12 2 3 11 10 true,
  key7 2 1 16 6 5 4 3 false, key7 5 6 15 1 2 3 4 true,
  key7 3 2 12 0 9 10 11 false, key7 3 4 13 9 0 8 2 false,
  key7 3 11 14 6 8 7 2 true, key7 8 6 14 11 3 2 0 false,
  key7 0 2 20 11 5 6 12 false, key7 2 7 12 6 5 11 20 true,
  key7 2 8 16 9 10 4 20 false, key7 11 10 21 0 8 2 20 false,
  key7 3 4 14 6 0 1 17 false, key7 4 3 17 1 7 6 14 true,
  key7 10 11 20 2 8 7 21 true, key7 8 2 20 4 10 9 15 true,
  key7 0 1 17 3 4 14 6 false, key7 7 6 14 4 3 17 1 true,
  key7 8 7 21 10 11 20 2 true, key7 10 9 15 8 2 20 4 true,
  key7 5 6 12 0 2 20 11 false, key7 5 11 20 2 7 12 6 true,
  key7 10 4 20 2 8 16 9 false, key7 8 2 20 11 10 21 0 false,
  key7 7 9 13 4 3 17 12 true, key7 9 7 12 2 3 18 13 true,
  key7 2 1 16 6 5 19 20 false, key7 5 6 15 1 2 20 19 true,
  key7 3 2 12 0 9 13 18 false, key7 3 4 13 9 0 12 17 false,
  key7 3 11 14 6 8 15 17 true, key7 8 6 14 11 3 17 16 false
]

def keys7Chunk5 : List (KeyData 7) := [
  key7 7 8 22 5 18 3 2 true, key7 8 0 21 10 19 3 2 false,
  key7 10 9 16 8 17 3 11 false, key7 3 2 23 7 22 5 4 true,
  key7 4 5 22 0 23 2 3 false, key7 11 3 17 8 15 9 10 true,
  key7 2 3 19 10 21 7 8 true, key7 2 3 18 5 22 8 0 false,
  key7 7 2 20 11 14 6 12 true, key7 2 0 12 6 14 11 20 false,
  key7 2 8 15 9 13 4 20 true, key7 11 10 21 7 12 2 20 true,
  key7 3 4 14 6 15 1 17 true, key7 4 3 17 1 16 6 14 false,
  key7 10 11 20 2 12 0 21 false, key7 8 2 20 4 13 9 16 false,
  key7 0 9 13 11 20 17 8 false, key7 9 0 12 2 20 19 10 false,
  key7 6 8 15 2 20 18 5 true, key7 11 3 17 0 12 22 5 false,
  key7 4 3 17 8 15 21 10 true, key7 2 3 18 10 21 15 8 true,
  key7 1 2 20 4 14 22 7 true, key7 6 5 19 3 17 23 0 false,
  key7 7 9 13 11 20 17 12 true, key7 9 7 12 2 20 19 13 true,
  key7 6 8 16 2 20 18 14 false, key7 11 3 17 7 12 22 14 true,
  key7 4 3 17 8 16 21 13 false, key7 2 3 18 10 21 16 12 false,
  key7 1 2 20 4 14 22 16 false, key7 6 5 19 3 17 23 15 true
]

def keys7Chunk6 : List (KeyData 7) := [
  key7 7 9 13 18 3 2 8 true, key7 9 7 12 17 3 4 10 true,
  key7 6 8 16 17 3 11 5 false, key7 11 3 17 15 8 6 5 true,
  key7 4 3 17 12 0 9 10 false, key7 2 3 18 13 9 0 8 false,
  key7 1 2 20 19 5 6 0 false, key7 6 5 19 20 2 1 7 true,
  key7 0 9 13 18 3 2 12 false, key7 9 0 12 17 3 4 13 false,
  key7 6 8 15 17 3 11 14 true, key7 11 3 17 16 8 6 14 false,
  key7 4 3 17 12 7 9 13 true, key7 2 3 18 13 9 7 12 true,
  key7 1 2 20 19 5 6 15 true, key7 6 5 19 20 2 1 16 false,
  key7 7 8 17 20 11 13 9 true, key7 1 0 22 14 4 20 2 false,
  key7 6 7 23 17 3 19 5 true, key7 2 8 16 21 10 18 3 false,
  key7 4 10 21 16 8 17 3 false, key7 11 5 22 12 7 17 3 true,
  key7 6 5 18 20 2 16 8 false, key7 9 10 19 20 2 12 7 true,
  key7 0 2 20 18 5 22 12 false, key7 2 7 12 22 5 18 20 true,
  key7 2 8 16 21 10 19 20 false, key7 11 10 21 16 8 17 20 false,
  key7 3 4 14 22 0 23 17 false, key7 4 3 17 23 7 22 14 true,
  key7 10 11 20 17 8 15 21 true, key7 8 2 20 19 10 21 15 true
]

def keys7Chunk7 : List (KeyData 7) := [
  key7 0 8 22 14 18 3 2 false, key7 8 7 21 13 19 3 2 true,
  key7 10 9 15 12 17 3 11 true, key7 3 2 23 16 22 5 4 false,
  key7 4 5 22 15 23 2 3 true, key7 11 3 17 12 16 9 10 false,
  key7 2 3 19 13 21 0 8 false, key7 2 3 18 14 22 8 7 true,
  key7 0 9 13 19 20 2 12 false, key7 9 0 12 17 20 11 13 false,
  key7 2 1 15 22 14 4 20 true, key7 5 6 16 23 17 3 19 false,
  key7 3 2 12 15 21 10 18 true, key7 3 4 13 21 15 8 17 true,
  key7 3 11 14 22 12 0 17 false, key7 8 6 14 18 20 2 15 true,
  key7 0 1 17 20 19 14 6 false, key7 7 6 14 19 20 17 1 true,
  key7 8 7 21 13 18 20 2 true, key7 10 9 15 12 17 20 4 true,
  key7 5 6 12 16 17 20 11 false, key7 5 11 20 17 15 12 6 true,
  key7 10 4 20 17 12 16 9 false, key7 8 2 20 18 13 21 0 false,
  key7 7 2 20 18 14 22 12 true, key7 2 0 12 22 14 18 20 false,
  key7 2 8 15 21 13 19 20 true, key7 11 10 21 15 12 17 20 true,
  key7 3 4 14 22 15 23 17 true, key7 4 3 17 23 16 22 14 false,
  key7 10 11 20 17 12 16 21 false, key7 8 2 20 19 13 21 16 false
]

def keys7Chunk8 : List (KeyData 7) := [
  key7 7 12 2 3 11 10 9 true, key7 1 16 6 5 4 3 2 false,
  key7 6 15 1 2 3 4 5 true, key7 2 12 0 9 10 11 3 false,
  key7 4 13 9 0 8 2 3 false, key7 11 14 6 8 7 2 3 true,
  key7 6 14 11 3 2 0 8 false, key7 9 13 4 3 2 8 7 true,
  key7 0 23 2 3 4 5 22 false, key7 7 22 5 4 3 2 23 true,
  key7 8 15 9 10 11 3 17 true, key7 10 21 7 8 2 3 19 true,
  key7 5 22 8 0 2 3 18 false, key7 5 18 3 2 7 8 22 true,
  key7 10 19 3 2 8 0 21 false, key7 8 17 3 11 10 9 16 false,
  key7 7 12 6 5 11 20 2 true, key7 8 16 9 10 4 20 2 false,
  key7 10 21 0 8 2 20 11 false, key7 3 17 1 7 6 14 4 true,
  key7 4 14 6 0 1 17 3 false, key7 11 20 2 8 7 21 10 true,
  key7 2 20 4 10 9 15 8 true, key7 2 20 11 5 6 12 0 false,
  key7 7 17 3 11 5 22 12 true, key7 2 16 8 6 5 18 20 false,
  key7 2 12 7 9 10 19 20 true, key7 11 13 9 7 8 17 20 true,
  key7 3 19 5 6 7 23 17 true, key7 4 20 2 1 0 22 14 false,
  key7 10 18 3 2 8 16 21 false, key7 8 17 3 4 10 21 16 false
]

def keys7Chunk9 : List (KeyData 7) := [
  key7 7 21 10 11 20 2 8 true, key7 9 15 8 2 20 4 10 true,
  key7 6 12 0 2 20 11 5 false, key7 11 20 2 7 12 6 5 true,
  key7 4 20 2 8 16 9 10 false, key7 2 20 11 10 21 0 8 false,
  key7 1 17 3 4 14 6 0 false, key7 6 14 4 3 17 1 7 true,
  key7 0 21 10 11 20 2 12 false, key7 9 16 8 2 20 4 13 false,
  key7 6 12 7 2 20 11 14 true, key7 11 20 2 0 12 6 14 false,
  key7 4 20 2 8 15 9 13 true, key7 2 20 11 10 21 7 12 true,
  key7 1 17 3 4 14 6 15 true, key7 6 14 4 3 17 1 16 false,
  key7 7 12 2 3 18 13 9 true, key7 1 16 6 5 19 20 2 false,
  key7 6 15 1 2 20 19 5 true, key7 2 12 0 9 13 18 3 false,
  key7 4 13 9 0 12 17 3 false, key7 11 14 6 8 15 17 3 true,
  key7 6 14 11 3 17 16 8 false, key7 9 13 4 3 17 12 7 true,
  key7 0 17 3 11 14 22 12 false, key7 2 15 8 6 14 18 20 true,
  key7 2 12 0 9 13 19 20 false, key7 11 13 9 0 12 17 20 false,
  key7 3 19 5 6 16 23 17 false, key7 4 20 2 1 15 22 14 true,
  key7 10 18 3 2 12 15 21 true, key7 8 17 3 4 13 21 15 true
]

def keys7Chunk10 : List (KeyData 7) := [
  key7 0 21 10 19 3 2 8 false, key7 9 16 8 17 3 11 10 false,
  key7 2 23 7 22 5 4 3 true, key7 5 22 0 23 2 3 4 false,
  key7 3 17 8 15 9 10 11 true, key7 3 19 10 21 7 8 2 true,
  key7 3 18 5 22 8 0 2 false, key7 8 22 5 18 3 2 7 true,
  key7 7 12 2 20 11 10 21 true, key7 1 16 6 14 4 3 17 false,
  key7 6 15 1 17 3 4 14 true, key7 2 12 0 21 10 11 20 false,
  key7 4 13 9 16 8 2 20 false, key7 11 14 6 12 7 2 20 true,
  key7 6 14 11 20 2 0 12 false, key7 9 13 4 20 2 8 15 true,
  key7 0 12 6 14 11 20 2 false, key7 8 15 9 13 4 20 2 true,
  key7 10 21 7 12 2 20 11 true, key7 3 17 1 16 6 14 4 false,
  key7 4 14 6 15 1 17 3 true, key7 11 20 2 12 0 21 10 false,
  key7 2 20 4 13 9 16 8 false, key7 2 20 11 14 6 12 7 true,
  key7 0 21 10 19 3 17 12 false, key7 9 16 8 17 3 18 13 false,
  key7 2 23 7 22 5 19 20 true, key7 5 22 0 23 2 20 19 false,
  key7 3 17 8 15 9 13 18 true, key7 3 19 10 21 7 12 17 true,
  key7 3 18 5 22 8 16 17 false, key7 8 22 5 18 3 17 15 true
]

def keys7Chunk11 : List (KeyData 7) := [
  key7 0 12 2 20 19 10 9 false, key7 8 15 2 20 18 5 6 true,
  key7 3 17 0 12 22 5 11 false, key7 3 17 8 15 21 10 4 true,
  key7 3 18 10 21 15 8 2 true, key7 2 20 4 14 22 7 1 true,
  key7 5 19 3 17 23 0 6 false, key7 9 13 11 20 17 8 0 false,
  key7 0 23 2 20 19 5 22 false, key7 7 22 5 19 20 2 23 true,
  key7 8 15 9 13 18 3 17 true, key7 10 21 7 12 17 3 19 true,
  key7 5 22 8 16 17 3 18 false, key7 5 18 3 17 15 8 22 true,
  key7 10 19 3 17 12 0 21 false, key7 8 17 3 18 13 9 16 false,
  key7 7 12 2 20 19 13 9 true, key7 8 16 2 20 18 14 6 false,
  key7 3 17 7 12 22 14 11 true, key7 3 17 8 16 21 13 4 false,
  key7 3 18 10 21 16 12 2 false, key7 2 20 4 14 22 16 1 false,
  key7 5 19 3 17 23 15 6 true, key7 9 13 11 20 17 12 7 true,
  key7 7 12 2 20 18 13 21 true, key7 1 16 6 14 19 20 17 false,
  key7 6 15 1 17 20 19 14 true, key7 2 12 0 21 13 18 20 false,
  key7 4 13 9 16 12 17 20 false, key7 11 14 6 12 15 17 20 true,
  key7 6 14 11 20 17 16 12 false, key7 9 13 4 20 17 12 15 true
]

def keys7Chunk12 : List (KeyData 7) := [
  key7 7 12 17 3 4 10 9 true, key7 8 16 17 3 11 5 6 false,
  key7 3 17 15 8 6 5 11 true, key7 3 17 12 0 9 10 4 false,
  key7 3 18 13 9 0 8 2 false, key7 2 20 19 5 6 0 1 false,
  key7 5 19 20 2 1 7 6 true, key7 9 13 18 3 2 8 7 true,
  key7 0 12 22 5 11 3 17 false, key7 8 15 21 10 4 3 17 true,
  key7 10 21 15 8 2 3 18 true, key7 3 17 23 0 6 5 19 false,
  key7 4 14 22 7 1 2 20 true, key7 11 20 17 8 0 9 13 false,
  key7 2 20 19 10 9 0 12 false, key7 2 20 18 5 6 8 15 true,
  key7 0 12 17 3 4 13 9 false, key7 8 15 17 3 11 14 6 true,
  key7 3 17 16 8 6 14 11 false, key7 3 17 12 7 9 13 4 true,
  key7 3 18 13 9 7 12 2 true, key7 2 20 19 5 6 15 1 true,
  key7 5 19 20 2 1 16 6 false, key7 9 13 18 3 2 12 0 false,
  key7 0 23 17 3 4 14 22 false, key7 7 22 14 4 3 17 23 true,
  key7 8 15 21 10 11 20 17 true, key7 10 21 15 8 2 20 19 true,
  key7 5 22 12 0 2 20 18 false, key7 5 18 20 2 7 12 22 true,
  key7 10 19 20 2 8 16 21 false, key7 8 17 20 11 10 21 16 false
]

def keys7Chunk13 : List (KeyData 7) := [
  key7 7 23 17 3 19 5 6 true, key7 0 22 14 4 20 2 1 false,
  key7 8 16 21 10 18 3 2 false, key7 10 21 16 8 17 3 4 false,
  key7 5 22 12 7 17 3 11 true, key7 5 18 20 2 16 8 6 false,
  key7 10 19 20 2 12 7 9 true, key7 8 17 20 11 13 9 7 true,
  key7 7 12 17 3 19 10 21 true, key7 8 16 17 3 18 5 22 false,
  key7 3 17 15 8 22 5 18 true, key7 3 17 12 0 21 10 19 false,
  key7 3 18 13 9 16 8 17 false, key7 2 20 19 5 22 0 23 false,
  key7 5 19 20 2 23 7 22 true, key7 9 13 18 3 17 8 15 true,
  key7 7 12 22 5 18 20 2 true, key7 8 16 21 10 19 20 2 false,
  key7 10 21 16 8 17 20 11 false, key7 3 17 23 7 22 14 4 true,
  key7 4 14 22 0 23 17 3 false, key7 11 20 17 8 15 21 10 true,
  key7 2 20 19 10 21 15 8 true, key7 2 20 18 5 22 12 0 false,
  key7 0 12 17 3 19 13 21 false, key7 8 15 17 3 18 14 22 true,
  key7 3 17 16 8 22 14 18 false, key7 3 17 12 7 21 13 19 true,
  key7 3 18 13 9 15 12 17 true, key7 2 20 19 5 22 15 23 true,
  key7 5 19 20 2 23 16 22 false, key7 9 13 18 3 17 12 16 false
]

def keys7Chunk14 : List (KeyData 7) := [
  key7 7 21 13 19 3 2 8 true, key7 9 15 12 17 3 11 10 true,
  key7 2 23 16 22 5 4 3 false, key7 5 22 15 23 2 3 4 true,
  key7 3 17 12 16 9 10 11 false, key7 3 19 13 21 0 8 2 false,
  key7 3 18 14 22 8 7 2 true, key7 8 22 14 18 3 2 0 false,
  key7 7 12 22 14 11 3 17 true, key7 8 16 21 13 4 3 17 false,
  key7 10 21 16 12 2 3 18 false, key7 3 17 23 15 6 5 19 true,
  key7 4 14 22 16 1 2 20 false, key7 11 20 17 12 7 9 13 true,
  key7 2 20 19 13 9 7 12 true, key7 2 20 18 14 6 8 16 false,
  key7 0 12 17 20 11 13 9 false, key7 1 15 22 14 4 20 2 true,
  key7 6 16 23 17 3 19 5 false, key7 2 12 15 21 10 18 3 true,
  key7 4 13 21 15 8 17 3 true, key7 11 14 22 12 0 17 3 false,
  key7 6 14 18 20 2 15 8 true, key7 9 13 19 20 2 12 0 false,
  key7 7 21 13 19 3 17 12 true, key7 9 15 12 17 3 18 13 true,
  key7 2 23 16 22 5 19 20 false, key7 5 22 15 23 2 20 19 true,
  key7 3 17 12 16 9 13 18 false, key7 3 19 13 21 0 12 17 false,
  key7 3 18 14 22 8 15 17 true, key7 8 22 14 18 3 17 16 false
]

def keys7Chunk15 : List (KeyData 7) := [
  key7 7 21 13 18 20 2 8 true, key7 9 15 12 17 20 4 10 true,
  key7 6 12 16 17 20 11 5 false, key7 11 20 17 15 12 6 5 true,
  key7 4 20 17 12 16 9 10 false, key7 2 20 18 13 21 0 8 false,
  key7 1 17 20 19 14 6 0 false, key7 6 14 19 20 17 1 7 true,
  key7 0 21 13 18 20 2 12 false, key7 9 16 12 17 20 4 13 false,
  key7 6 12 15 17 20 11 14 true, key7 11 20 17 16 12 6 14 false,
  key7 4 20 17 12 15 9 13 true, key7 2 20 18 13 21 7 12 true,
  key7 1 17 20 19 14 6 15 true, key7 6 14 19 20 17 1 16 false,
  key7 0 12 22 14 18 20 2 false, key7 8 15 21 13 19 20 2 true,
  key7 10 21 15 12 17 20 11 true, key7 3 17 23 16 22 14 4 false,
  key7 4 14 22 15 23 17 3 true, key7 11 20 17 12 16 21 10 false,
  key7 2 20 19 13 21 16 8 false, key7 2 20 18 14 22 12 7 true,
  key7 0 23 17 20 19 14 22 false, key7 7 22 14 19 20 17 23 true,
  key7 24 12 25 26 18 13 21 true, key7 27 21 13 18 26 25 12 false,
  key7 8 15 21 13 18 20 17 true, key7 10 21 15 12 17 20 19 true,
  key7 5 22 12 16 17 20 18 false, key7 5 18 20 17 15 12 22 true
]

def keys7Chunk16 : List (KeyData 7) := [
  key7 10 19 20 17 12 16 21 false, key7 8 17 20 18 13 21 16 false,
  key7 15 1 2 3 4 5 6 true, key7 16 6 5 4 3 2 1 false,
  key7 12 0 9 10 11 3 2 false, key7 13 9 0 8 2 3 4 false,
  key7 14 6 8 7 2 3 11 true, key7 14 11 3 2 0 8 6 false,
  key7 13 4 3 2 8 7 9 true, key7 12 2 3 11 10 9 7 true,
  key7 15 8 6 5 11 3 17 true, key7 12 0 9 10 4 3 17 false,
  key7 13 9 0 8 2 3 18 false, key7 20 2 1 7 6 5 19 true,
  key7 19 5 6 0 1 2 20 false, key7 18 3 2 8 7 9 13 true,
  key7 17 3 4 10 9 7 12 true, key7 17 3 11 5 6 8 16 false,
  key7 15 9 10 11 3 17 8 true, key7 21 7 8 2 3 19 10 true,
  key7 22 8 0 2 3 18 5 false, key7 18 3 2 7 8 22 5 true,
  key7 19 3 2 8 0 21 10 false, key7 17 3 11 10 9 16 8 false,
  key7 23 2 3 4 5 22 0 false, key7 22 5 4 3 2 23 7 true,
  key7 16 9 10 11 3 17 12 false, key7 21 0 8 2 3 19 13 false,
  key7 22 8 7 2 3 18 14 true, key7 18 3 2 0 8 22 14 false,
  key7 19 3 2 8 7 21 13 true, key7 17 3 11 10 9 15 12 true
]

def keys7Chunk17 : List (KeyData 7) := [
  key7 23 2 3 4 5 22 15 true, key7 22 5 4 3 2 23 16 false,
  key7 16 9 10 4 20 2 8 false, key7 21 0 8 2 20 11 10 false,
  key7 17 1 7 6 14 4 3 true, key7 14 6 0 1 17 3 4 false,
  key7 20 2 8 7 21 10 11 true, key7 20 4 10 9 15 8 2 true,
  key7 20 11 5 6 12 0 2 false, key7 12 6 5 11 20 2 7 true,
  key7 15 8 2 3 18 10 21 true, key7 23 0 6 5 19 3 17 false,
  key7 22 7 1 2 20 4 14 true, key7 17 8 0 9 13 11 20 false,
  key7 19 10 9 0 12 2 20 false, key7 18 5 6 8 15 2 20 true,
  key7 22 5 11 3 17 0 12 false, key7 21 10 4 3 17 8 15 true,
  key7 16 8 6 5 18 20 2 false, key7 12 7 9 10 19 20 2 true,
  key7 13 9 7 8 17 20 11 true, key7 20 2 1 0 22 14 4 false,
  key7 19 5 6 7 23 17 3 true, key7 18 3 2 8 16 21 10 false,
  key7 17 3 4 10 21 16 8 false, key7 17 3 11 5 22 12 7 true,
  key7 16 9 10 4 20 17 12 false, key7 21 0 8 2 20 18 13 false,
  key7 17 1 7 6 14 19 20 true, key7 14 6 0 1 17 20 19 false,
  key7 20 2 8 7 21 13 18 true, key7 20 4 10 9 15 12 17 true
]

def keys7Chunk18 : List (KeyData 7) := [
  key7 20 11 5 6 12 16 17 false, key7 12 6 5 11 20 17 15 true,
  key7 15 8 2 20 4 10 9 true, key7 12 0 2 20 11 5 6 false,
  key7 20 2 7 12 6 5 11 true, key7 20 2 8 16 9 10 4 false,
  key7 20 11 10 21 0 8 2 false, key7 17 3 4 14 6 0 1 false,
  key7 14 4 3 17 1 7 6 true, key7 21 10 11 20 2 8 7 true,
  key7 16 8 6 14 11 3 17 false, key7 12 7 9 13 4 3 17 true,
  key7 13 9 7 12 2 3 18 true, key7 20 2 1 16 6 5 19 false,
  key7 19 5 6 15 1 2 20 true, key7 18 3 2 12 0 9 13 false,
  key7 17 3 4 13 9 0 12 false, key7 17 3 11 14 6 8 15 true,
  key7 16 8 2 20 4 13 9 false, key7 12 7 2 20 11 14 6 true,
  key7 20 2 0 12 6 14 11 false, key7 20 2 8 15 9 13 4 true,
  key7 20 11 10 21 7 12 2 true, key7 17 3 4 14 6 15 1 true,
  key7 14 4 3 17 1 16 6 false, key7 21 10 11 20 2 12 0 false,
  key7 16 1 2 20 4 14 22 false, key7 15 6 5 19 3 17 23 true,
  key7 12 7 9 13 11 20 17 true, key7 13 9 7 12 2 20 19 true,
  key7 14 6 8 16 2 20 18 false, key7 14 11 3 17 7 12 22 true
]

def keys7Chunk19 : List (KeyData 7) := [
  key7 13 4 3 17 8 16 21 false, key7 12 2 3 18 10 21 16 false,
  key7 15 1 2 20 19 5 6 true, key7 16 6 5 19 20 2 1 false,
  key7 12 0 9 13 18 3 2 false, key7 13 9 0 12 17 3 4 false,
  key7 14 6 8 15 17 3 11 true, key7 14 11 3 17 16 8 6 false,
  key7 13 4 3 17 12 7 9 true, key7 12 2 3 18 13 9 7 true,
  key7 15 8 2 20 19 10 21 true, key7 12 0 2 20 18 5 22 false,
  key7 20 2 7 12 22 5 18 true, key7 20 2 8 16 21 10 19 false,
  key7 20 11 10 21 16 8 17 false, key7 17 3 4 14 22 0 23 false,
  key7 14 4 3 17 23 7 22 true, key7 21 10 11 20 17 8 15 true,
  key7 15 8 6 14 18 20 2 true, key7 12 0 9 13 19 20 2 false,
  key7 13 9 0 12 17 20 11 false, key7 20 2 1 15 22 14 4 true,
  key7 19 5 6 16 23 17 3 false, key7 18 3 2 12 15 21 10 true,
  key7 17 3 4 13 21 15 8 true, key7 17 3 11 14 22 12 0 false,
  key7 16 8 2 20 19 13 21 false, key7 12 7 2 20 18 14 22 true,
  key7 20 2 0 12 22 14 18 false, key7 20 2 8 15 21 13 19 true,
  key7 20 11 10 21 15 12 17 true, key7 17 3 4 14 22 15 23 true
]

def keys7Chunk20 : List (KeyData 7) := [
  key7 14 4 3 17 23 16 22 false, key7 21 10 11 20 17 12 16 false,
  key7 16 8 17 3 11 10 9 false, key7 23 7 22 5 4 3 2 true,
  key7 22 0 23 2 3 4 5 false, key7 17 8 15 9 10 11 3 true,
  key7 19 10 21 7 8 2 3 true, key7 18 5 22 8 0 2 3 false,
  key7 22 5 18 3 2 7 8 true, key7 21 10 19 3 2 8 0 false,
  key7 16 8 17 3 4 10 21 false, key7 12 7 17 3 11 5 22 true,
  key7 20 2 16 8 6 5 18 false, key7 20 2 12 7 9 10 19 true,
  key7 20 11 13 9 7 8 17 true, key7 17 3 19 5 6 7 23 true,
  key7 14 4 20 2 1 0 22 false, key7 21 10 18 3 2 8 16 false,
  key7 15 1 17 3 4 14 6 true, key7 16 6 14 4 3 17 1 false,
  key7 12 0 21 10 11 20 2 false, key7 13 9 16 8 2 20 4 false,
  key7 14 6 12 7 2 20 11 true, key7 14 11 20 2 0 12 6 false,
  key7 13 4 20 2 8 15 9 true, key7 12 2 20 11 10 21 7 true,
  key7 15 8 17 3 4 13 21 true, key7 12 0 17 3 11 14 22 false,
  key7 20 2 15 8 6 14 18 true, key7 20 2 12 0 9 13 19 false,
  key7 20 11 13 9 0 12 17 false, key7 17 3 19 5 6 16 23 false
]

def keys7Chunk21 : List (KeyData 7) := [
  key7 14 4 20 2 1 15 22 true, key7 21 10 18 3 2 12 15 true,
  key7 15 9 13 4 20 2 8 true, key7 21 7 12 2 20 11 10 true,
  key7 17 1 16 6 14 4 3 false, key7 14 6 15 1 17 3 4 true,
  key7 20 2 12 0 21 10 11 false, key7 20 4 13 9 16 8 2 false,
  key7 20 11 14 6 12 7 2 true, key7 12 6 14 11 20 2 0 false,
  key7 15 8 22 5 18 3 17 true, key7 12 0 21 10 19 3 17 false,
  key7 13 9 16 8 17 3 18 false, key7 20 2 23 7 22 5 19 true,
  key7 19 5 22 0 23 2 20 false, key7 18 3 17 8 15 9 13 true,
  key7 17 3 19 10 21 7 12 true, key7 17 3 18 5 22 8 16 false,
  key7 16 8 17 3 18 13 9 false, key7 23 7 22 5 19 20 2 true,
  key7 22 0 23 2 20 19 5 false, key7 17 8 15 9 13 18 3 true,
  key7 19 10 21 7 12 17 3 true, key7 18 5 22 8 16 17 3 false,
  key7 22 5 18 3 17 15 8 true, key7 21 10 19 3 17 12 0 false,
  key7 15 9 13 4 20 17 12 true, key7 21 7 12 2 20 18 13 true,
  key7 17 1 16 6 14 19 20 false, key7 14 6 15 1 17 20 19 true,
  key7 20 2 12 0 21 13 18 false, key7 20 4 13 9 16 12 17 false
]

def keys7Chunk22 : List (KeyData 7) := [
  key7 20 11 14 6 12 15 17 true, key7 12 6 14 11 20 17 16 false,
  key7 15 2 20 18 5 6 8 true, key7 17 0 12 22 5 11 3 false,
  key7 17 8 15 21 10 4 3 true, key7 18 10 21 15 8 2 3 true,
  key7 20 4 14 22 7 1 2 true, key7 19 3 17 23 0 6 5 false,
  key7 13 11 20 17 8 0 9 false, key7 12 2 20 19 10 9 0 false,
  key7 16 8 17 20 11 10 21 false, key7 23 7 22 14 4 3 17 true,
  key7 22 0 23 17 3 4 14 false, key7 17 8 15 21 10 11 20 true,
  key7 19 10 21 15 8 2 20 true, key7 18 5 22 12 0 2 20 false,
  key7 22 5 18 20 2 7 12 true, key7 21 10 19 20 2 8 16 false,
  key7 15 9 13 18 3 17 8 true, key7 21 7 12 17 3 19 10 true,
  key7 22 8 16 17 3 18 5 false, key7 18 3 17 15 8 22 5 true,
  key7 19 3 17 12 0 21 10 false, key7 17 3 18 13 9 16 8 false,
  key7 23 2 20 19 5 22 0 false, key7 22 5 19 20 2 23 7 true,
  key7 16 9 13 18 3 17 12 false, key7 21 0 12 17 3 19 13 false,
  key7 22 8 15 17 3 18 14 true, key7 18 3 17 16 8 22 14 false,
  key7 19 3 17 12 7 21 13 true, key7 17 3 18 13 9 15 12 true
]

def keys7Chunk23 : List (KeyData 7) := [
  key7 23 2 20 19 5 22 15 true, key7 22 5 19 20 2 23 16 false,
  key7 16 2 20 18 14 6 8 false, key7 17 7 12 22 14 11 3 true,
  key7 17 8 16 21 13 4 3 false, key7 18 10 21 16 12 2 3 false,
  key7 20 4 14 22 16 1 2 false, key7 19 3 17 23 15 6 5 true,
  key7 13 11 20 17 12 7 9 true, key7 12 2 20 19 13 9 7 true,
  key7 16 8 22 14 18 3 17 false, key7 12 7 21 13 19 3 17 true,
  key7 13 9 15 12 17 3 18 true, key7 20 2 23 16 22 5 19 false,
  key7 19 5 22 15 23 2 20 true, key7 18 3 17 12 16 9 13 false,
  key7 17 3 19 13 21 0 12 false, key7 17 3 18 14 22 8 15 true,
  key7 15 1 17 20 19 14 6 true, key7 16 6 14 19 20 17 1 false,
  key7 12 0 21 13 18 20 2 false, key7 13 9 16 12 17 20 4 false,
  key7 14 6 12 15 17 20 11 true, key7 14 11 20 17 16 12 6 false,
  key7 13 4 20 17 12 15 9 true, key7 12 2 20 18 13 21 7 true,
  key7 16 8 17 20 18 13 21 false, key7 23 7 22 14 19 20 17 true,
  key7 22 0 23 17 20 19 14 false, key7 23 27 22 14 19 26 25 false,
  key7 17 8 15 21 13 18 20 true, key7 19 10 21 15 12 17 20 true
]

def keys7Chunk24 : List (KeyData 7) := [
  key7 18 5 22 12 16 17 20 false, key7 22 5 18 20 17 15 12 true,
  key7 21 10 19 20 17 12 16 false, key7 16 17 3 11 5 6 8 false,
  key7 17 15 8 6 5 11 3 true, key7 17 12 0 9 10 4 3 false,
  key7 18 13 9 0 8 2 3 false, key7 20 19 5 6 0 1 2 false,
  key7 19 20 2 1 7 6 5 true, key7 13 18 3 2 8 7 9 true,
  key7 12 17 3 4 10 9 7 true, key7 15 23 2 3 4 5 22 true,
  key7 16 22 5 4 3 2 23 false, key7 12 16 9 10 11 3 17 false,
  key7 13 21 0 8 2 3 19 false, key7 14 22 8 7 2 3 18 true,
  key7 14 18 3 2 0 8 22 false, key7 13 19 3 2 8 7 21 true,
  key7 12 17 3 11 10 9 15 true, key7 15 21 10 4 3 17 8 true,
  key7 21 15 8 2 3 18 10 true, key7 17 23 0 6 5 19 3 false,
  key7 14 22 7 1 2 20 4 true, key7 20 17 8 0 9 13 11 false,
  key7 20 19 10 9 0 12 2 false, key7 20 18 5 6 8 15 2 true,
  key7 12 22 5 11 3 17 0 false, key7 15 12 6 5 11 20 17 true,
  key7 12 16 9 10 4 20 17 false, key7 13 21 0 8 2 20 18 false,
  key7 20 17 1 7 6 14 19 true, key7 19 14 6 0 1 17 20 false
]

def keys7Chunk25 : List (KeyData 7) := [
  key7 18 20 2 8 7 21 13 true, key7 17 20 4 10 9 15 12 true,
  key7 17 20 11 5 6 12 16 false, key7 15 17 3 11 14 6 8 true,
  key7 17 16 8 6 14 11 3 false, key7 17 12 7 9 13 4 3 true,
  key7 18 13 9 7 12 2 3 true, key7 20 19 5 6 15 1 2 true,
  key7 19 20 2 1 16 6 5 false, key7 13 18 3 2 12 0 9 false,
  key7 12 17 3 4 13 9 0 false, key7 16 12 2 3 18 10 21 false,
  key7 23 15 6 5 19 3 17 true, key7 22 16 1 2 20 4 14 false,
  key7 17 12 7 9 13 11 20 true, key7 19 13 9 7 12 2 20 true,
  key7 18 14 6 8 16 2 20 false, key7 22 14 11 3 17 7 12 true,
  key7 21 13 4 3 17 8 16 false, key7 15 21 10 11 20 17 8 true,
  key7 21 15 8 2 20 19 10 true, key7 22 12 0 2 20 18 5 false,
  key7 18 20 2 7 12 22 5 true, key7 19 20 2 8 16 21 10 false,
  key7 17 20 11 10 21 16 8 false, key7 23 17 3 4 14 22 0 false,
  key7 22 14 4 3 17 23 7 true, key7 16 21 10 11 20 17 12 false,
  key7 21 16 8 2 20 19 13 false, key7 22 12 7 2 20 18 14 true,
  key7 18 20 2 0 12 22 14 false, key7 19 20 2 8 15 21 13 true
]

def keys7Chunk26 : List (KeyData 7) := [
  key7 17 20 11 10 21 15 12 true, key7 23 17 3 4 14 22 15 true,
  key7 22 14 4 3 17 23 16 false, key7 16 21 10 18 3 2 8 false,
  key7 21 16 8 17 3 4 10 false, key7 22 12 7 17 3 11 5 true,
  key7 18 20 2 16 8 6 5 false, key7 19 20 2 12 7 9 10 true,
  key7 17 20 11 13 9 7 8 true, key7 23 17 3 19 5 6 7 true,
  key7 22 14 4 20 2 1 0 false, key7 15 21 10 18 3 2 12 true,
  key7 21 15 8 17 3 4 13 true, key7 22 12 0 17 3 11 14 false,
  key7 18 20 2 15 8 6 14 true, key7 19 20 2 12 0 9 13 false,
  key7 17 20 11 13 9 0 12 false, key7 23 17 3 19 5 6 16 false,
  key7 22 14 4 20 2 1 15 true, key7 16 17 3 18 5 22 8 false,
  key7 17 15 8 22 5 18 3 true, key7 17 12 0 21 10 19 3 false,
  key7 18 13 9 16 8 17 3 false, key7 20 19 5 22 0 23 2 false,
  key7 19 20 2 23 7 22 5 true, key7 13 18 3 17 8 15 9 true,
  key7 12 17 3 19 10 21 7 true, key7 16 12 6 14 11 20 17 false,
  key7 12 15 9 13 4 20 17 true, key7 13 21 7 12 2 20 18 true,
  key7 20 17 1 16 6 14 19 false, key7 19 14 6 15 1 17 20 true
]

def keys7Chunk27 : List (KeyData 7) := [
  key7 18 20 2 12 0 21 13 false, key7 17 20 4 13 9 16 12 false,
  key7 17 20 11 14 6 12 15 true, key7 16 21 10 19 20 2 8 false,
  key7 21 16 8 17 20 11 10 false, key7 17 23 7 22 14 4 3 true,
  key7 14 22 0 23 17 3 4 false, key7 20 17 8 15 21 10 11 true,
  key7 20 19 10 21 15 8 2 true, key7 20 18 5 22 12 0 2 false,
  key7 12 22 5 18 20 2 7 true, key7 15 23 2 20 19 5 22 true,
  key7 16 22 5 19 20 2 23 false, key7 12 16 9 13 18 3 17 false,
  key7 13 21 0 12 17 3 19 false, key7 14 22 8 15 17 3 18 true,
  key7 14 18 3 17 16 8 22 false, key7 13 19 3 17 12 7 21 true,
  key7 12 17 3 18 13 9 15 true, key7 15 17 3 18 14 22 8 true,
  key7 17 16 8 22 14 18 3 false, key7 17 12 7 21 13 19 3 true,
  key7 18 13 9 15 12 17 3 true, key7 20 19 5 22 15 23 2 true,
  key7 19 20 2 23 16 22 5 false, key7 13 18 3 17 12 16 9 false,
  key7 12 17 3 19 13 21 0 false, key7 16 21 10 19 20 17 12 false,
  key7 21 16 8 17 20 18 13 false, key7 17 23 7 22 14 19 20 true,
  key7 14 22 0 23 17 20 19 false, key7 14 22 27 23 25 26 18 false
]

def keys7Chunk28 : List (KeyData 7) := [
  key7 20 17 8 15 21 13 18 true, key7 20 19 10 21 15 12 17 true,
  key7 20 18 5 22 12 16 17 false, key7 12 22 5 18 20 17 15 true,
  key7 15 12 17 3 11 10 9 true, key7 23 16 22 5 4 3 2 false,
  key7 22 15 23 2 3 4 5 true, key7 17 12 16 9 10 11 3 false,
  key7 19 13 21 0 8 2 3 false, key7 18 14 22 8 7 2 3 true,
  key7 22 14 18 3 2 0 8 false, key7 21 13 19 3 2 8 7 true,
  key7 16 17 20 11 5 6 12 false, key7 17 15 12 6 5 11 20 true,
  key7 17 12 16 9 10 4 20 false, key7 18 13 21 0 8 2 20 false,
  key7 20 19 14 6 0 1 17 false, key7 19 20 17 1 7 6 14 true,
  key7 13 18 20 2 8 7 21 true, key7 12 17 20 4 10 9 15 true,
  key7 16 21 13 4 3 17 8 false, key7 21 16 12 2 3 18 10 false,
  key7 17 23 15 6 5 19 3 true, key7 14 22 16 1 2 20 4 false,
  key7 20 17 12 7 9 13 11 true, key7 20 19 13 9 7 12 2 true,
  key7 20 18 14 6 8 16 2 false, key7 12 22 14 11 3 17 7 true,
  key7 15 23 17 3 4 14 22 true, key7 16 22 14 4 3 17 23 false,
  key7 12 16 21 10 11 20 17 false, key7 13 21 16 8 2 20 19 false
]

def keys7Chunk29 : List (KeyData 7) := [
  key7 14 22 12 7 2 20 18 true, key7 14 18 20 2 0 12 22 false,
  key7 13 19 20 2 8 15 21 true, key7 12 17 20 11 10 21 15 true,
  key7 16 23 17 3 19 5 6 false, key7 15 22 14 4 20 2 1 true,
  key7 12 15 21 10 18 3 2 true, key7 13 21 15 8 17 3 4 true,
  key7 14 22 12 0 17 3 11 false, key7 14 18 20 2 15 8 6 true,
  key7 13 19 20 2 12 0 9 false, key7 12 17 20 11 13 9 0 false,
  key7 15 17 20 11 14 6 12 true, key7 17 16 12 6 14 11 20 false,
  key7 17 12 15 9 13 4 20 true, key7 18 13 21 7 12 2 20 true,
  key7 20 19 14 6 15 1 17 true, key7 19 20 17 1 16 6 14 false,
  key7 13 18 20 2 12 0 21 false, key7 12 17 20 4 13 9 16 false,
  key7 15 12 17 3 18 13 9 true, key7 23 16 22 5 19 20 2 false,
  key7 22 15 23 2 20 19 5 true, key7 17 12 16 9 13 18 3 false,
  key7 19 13 21 0 12 17 3 false, key7 18 14 22 8 15 17 3 true,
  key7 22 14 18 3 17 16 8 false, key7 21 13 19 3 17 12 7 true,
  key7 15 12 22 5 18 20 17 true, key7 12 16 21 10 19 20 17 false,
  key7 13 21 16 8 17 20 18 false, key7 20 17 23 7 22 14 19 true
]

def keys7Chunk30 : List (KeyData 7) := [
  key7 19 14 22 0 23 17 20 false, key7 13 21 23 24 25 26 19 true,
  key7 18 20 17 8 15 21 13 true, key7 17 20 19 10 21 15 12 true,
  key7 17 20 18 5 22 12 16 false, key7 15 12 17 20 4 10 9 true,
  key7 12 16 17 20 11 5 6 false, key7 20 17 15 12 6 5 11 true,
  key7 20 17 12 16 9 10 4 false, key7 20 18 13 21 0 8 2 false,
  key7 17 20 19 14 6 0 1 false, key7 14 19 20 17 1 7 6 true,
  key7 21 13 18 20 2 8 7 true, key7 15 12 17 20 11 10 21 true,
  key7 23 16 22 14 4 3 17 false, key7 22 15 23 17 3 4 14 true,
  key7 17 12 16 21 10 11 20 false, key7 19 13 21 16 8 2 20 false,
  key7 18 14 22 12 7 2 20 true, key7 22 14 18 20 2 0 12 false,
  key7 21 13 19 20 2 8 15 true, key7 16 12 17 20 4 13 9 false,
  key7 12 15 17 20 11 14 6 true, key7 20 17 16 12 6 14 11 false,
  key7 20 17 12 15 9 13 4 true, key7 20 18 13 21 7 12 2 true,
  key7 17 20 19 14 6 15 1 true, key7 14 19 20 17 1 16 6 false,
  key7 21 13 18 20 2 12 0 false, key7 16 17 20 18 5 22 12 false,
  key7 17 15 12 22 5 18 20 true, key7 17 12 16 21 10 19 20 false
]

def keys7Chunk31 : List (KeyData 7) := [
  key7 18 13 21 16 8 17 20 false, key7 20 19 14 22 0 23 17 false,
  key7 19 20 17 23 7 22 14 true, key7 13 19 26 25 27 23 21 false,
  key7 13 18 20 17 8 15 21 true, key7 12 17 20 19 10 21 15 true,
  key7 15 21 13 19 20 2 8 true, key7 21 15 12 17 20 11 10 true,
  key7 17 23 16 22 14 4 3 false, key7 14 22 15 23 17 3 4 true,
  key7 20 17 12 16 21 10 11 false, key7 20 19 13 21 16 8 2 false,
  key7 20 18 14 22 12 7 2 true, key7 12 22 14 18 20 2 0 false,
  key7 15 12 17 20 19 10 21 true, key7 12 16 17 20 18 5 22 false,
  key7 20 17 15 12 22 5 18 true, key7 20 17 12 16 21 10 19 false,
  key7 20 18 13 21 16 8 17 false, key7 17 20 19 14 22 0 23 false,
  key7 14 19 20 17 23 7 22 true, key7 14 18 26 25 23 24 22 true,
  key7 21 13 18 20 17 8 15 true, key7 15 21 13 18 20 17 8 true,
  key7 21 15 12 17 20 19 10 true, key7 22 12 16 17 20 18 5 false,
  key7 18 20 17 15 12 22 5 true, key7 19 20 17 12 16 21 10 false,
  key7 17 20 18 13 21 16 8 false, key7 23 17 20 19 14 22 0 false,
  key7 22 14 19 20 17 23 7 true, key7 23 25 26 19 14 22 24 true
]

def keys7 : List (KeyData 7) := keys7Chunk0 ++ keys7Chunk1 ++ keys7Chunk2 ++ keys7Chunk3 ++ keys7Chunk4 ++ keys7Chunk5 ++ keys7Chunk6 ++ keys7Chunk7 ++ keys7Chunk8 ++ keys7Chunk9 ++ keys7Chunk10 ++ keys7Chunk11 ++ keys7Chunk12 ++ keys7Chunk13 ++ keys7Chunk14 ++ keys7Chunk15 ++ keys7Chunk16 ++ keys7Chunk17 ++ keys7Chunk18 ++ keys7Chunk19 ++ keys7Chunk20 ++ keys7Chunk21 ++ keys7Chunk22 ++ keys7Chunk23 ++ keys7Chunk24 ++ keys7Chunk25 ++ keys7Chunk26 ++ keys7Chunk27 ++ keys7Chunk28 ++ keys7Chunk29 ++ keys7Chunk30 ++ keys7Chunk31

def T7 : Set (Point 7) := body keys7

/-- Compactness, physical tiling existence, and absence of nonzero periods. -/
def T7Claim : Prop := IsAperiodicMonotile T7

/-- Every Euclidean isometry preserving the physical tile collection is included.
No centre, orientation, lattice, or registered frame is prescribed. -/
def IsEuclideanSymmetry {d : ℕ} (tiles : Set (Set (Point d)))
    (f : Point d ≃ᵢ Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ f '' A ∈ tiles

/-- All translations, rotations, reflections, and their compositions. -/
def EuclideanSymmetries {d : ℕ} (tiles : Set (Set (Point d))) :=
  {f : Point d ≃ᵢ Point d // IsEuclideanSymmetry tiles f}

/-- The exact HENRY target, including actual existence and a uniform bound
2^7 * 7! = 645120 on the full symmetry type of every arbitrary-placement tiling.
Here finite symmetry is asserted; a trivial symmetry group is not asserted. -/
def T7StrongClaim : Prop :=
  T7Claim ∧ ∀ tiles : Set (Set (Point 7)), IsTiling T7 tiles →
    Finite (EuclideanSymmetries tiles) ∧ Nat.card (EuclideanSymmetries tiles) ≤ 645120

/-- The sole deliberate theorem placeholder in the independent Challenge. -/
theorem T7_strongAperiodicity : T7StrongClaim := by
  sorry

end PalomarMonotiles
