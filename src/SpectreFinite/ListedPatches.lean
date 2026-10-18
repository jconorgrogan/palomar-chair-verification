module

public import Init

@[expose] public section


/-!
Exact finite marked-hexagon tables from arXiv:2305.17743v2, figures 4/5.
This module proves local properties of nine specified finite patches only.
It makes no completeness, universal hierarchy, physical tiling existence,
or aperiodicity claim. Mathematical data attributed to David Smith,
Joseph Samuel Myers, Craig S. Kaplan and Chaim Goodman-Strauss, CC BY 4.0.
See SOURCE_PROVENANCE.md for byte-pinned author sources and extraction.
-/

namespace SpectreFinite
abbrev TileKind := Fin 9
-- Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Phi, Psi, in that order.
-- Edge letters encode alpha=1, beta=2, gamma=3, delta=4, epsilon=5,
-- zeta=6, eta=0, theta=8. Sign encodes plus/minus; eta is self-complementary.
def edgeWords : List (List Int) := [
  [(-1), 1, (-3), (-4), 2, (-2)],
  [3, 2, (-5), 1, (-3), (-6)],
  [3, 2, 8, 2, 0, (-2)],
  [3, 2, (-5), 1, (-8), (-2)],
  [(-1), 5, 8, 2, 0, (-2)],
  [(-1), 5, (-5), 1, (-8), (-2)],
  [6, 2, (-5), 1, (-3), 4],
  [3, 2, (-5), 5, 0, (-2)],
  [(-1), 5, (-5), 5, 0, (-2)]
]

structure PlacedHex where
  kind : TileKind
  turn : Fin 6
  q : Int
  r : Int
  deriving DecidableEq

def pos (a : PlacedHex) : Int × Int := (a.q, a.r)
def addPos (a b : Int × Int) : Int × Int := (a.1 + b.1, a.2 + b.2)
def direction (d : Fin 6) : Int × Int :=
  [(-1,0), (0,-1), (1,-1), (1,0), (0,1), (-1,1)].getD d.val (0,0)
def opposite (d : Fin 6) : Fin 6 := ⟨(d.val + 3) % 6, Nat.mod_lt _ (by decide)⟩
def facingMark (a : PlacedHex) (d : Fin 6) : Int :=
  (edgeWords.getD a.kind.val []).getD ((d.val + 6 - a.turn.val) % 6) 0

def CompatiblePair (a b : PlacedHex) : Prop :=
  pos a ≠ pos b ∧ ∀ d : Fin 6,
    pos b = addPos (pos a) (direction d) →
    facingMark a d = -(facingMark b (opposite d))
instance (a b : PlacedHex) : Decidable (CompatiblePair a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

def LocallyValid (patch : List PlacedHex) : Prop := patch.Pairwise CompatiblePair
instance (patch : List PlacedHex) : Decidable (LocallyValid patch) :=
  inferInstanceAs (Decidable (patch.Pairwise CompatiblePair))

def childrenTable : List (List PlacedHex) := [
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨4, 1, 1, 1⟩, ⟨5, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨2, 0, 2, (-1)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨5, 1, 1, 1⟩, ⟨4, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨4, 5, 2, (-2)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨5, 1, 1, 1⟩, ⟨8, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨5, 5, 2, (-2)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨5, 1, 1, 1⟩, ⟨8, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨4, 5, 2, (-2)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨8, 1, 1, 1⟩, ⟨8, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨5, 5, 2, (-2)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨8, 1, 1, 1⟩, ⟨8, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨4, 5, 2, (-2)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨3, 2, 0, 1⟩, ⟨5, 1, 1, 1⟩, ⟨4, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨4, 5, 2, (-2)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨5, 1, 1, 1⟩, ⟨8, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨8, 5, 2, (-2)⟩],
  [⟨0, 0, 0, 0⟩, ⟨6, 1, 1, 0⟩, ⟨7, 2, 0, 1⟩, ⟨8, 1, 1, 1⟩, ⟨8, 4, 0, (-1)⟩, ⟨1, 5, 1, (-1)⟩, ⟨7, 0, 2, (-1)⟩, ⟨8, 5, 2, (-2)⟩]
]

def children (k : TileKind) : List PlacedHex := childrenTable.getD k.val []

-- Finite statements proved by ordinary kernel reduction.
-- Seven Gamma-patch cells; no infinite-world hypothesis or conclusion.
set_option maxRecDepth 100000 in
theorem listedGamma_locallyValid : LocallyValid (children 0) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nineListedSupertiles_locallyValid :
    ∀ k : TileKind, LocallyValid (children k) := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

theorem nineListedSupertiles_size :
    ∀ k : TileKind, (children k).length = if k.val = 0 then 7 else 8 := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

theorem nineListedSupertiles_oneGamma :
    ∀ k : TileKind, ((children k).filter (fun a => a.kind.val == 0)).length = 1 := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))


/-- All kind indices address a real six-letter word; no default row is used. -/
theorem edgeWords_count : edgeWords.length = 9 := rfl

theorem edgeWords_six_marks :
    ∀ k : TileKind, (edgeWords.getD k.val []).length = 6 := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

theorem childrenTable_count : childrenTable.length = 9 := rfl

theorem opposite_involutive : ∀ d : Fin 6, opposite (opposite d) = d := by decide

theorem direction_opposite : ∀ d : Fin 6,
    direction (opposite d) = (-(direction d).1, -(direction d).2) := by decide

#print axioms listedGamma_locallyValid
#print axioms nineListedSupertiles_locallyValid
#print axioms nineListedSupertiles_size
#print axioms nineListedSupertiles_oneGamma
#print axioms edgeWords_count
#print axioms edgeWords_six_marks
#print axioms childrenTable_count
#print axioms opposite_involutive
#print axioms direction_opposite
end SpectreFinite
