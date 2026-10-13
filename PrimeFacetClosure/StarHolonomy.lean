module

public import PrimeFacetClosure.Transport
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
# Exact star-gauged path holonomy

This file proves the finite graph path argument, without assuming a graph
closure theorem and without enumerating the graph. `StarGauge` contains only
local generator-edge obligations: the hole edges join a star center to a leaf
with identity gauged transport, and wall edges join leaves with the indicated
bridge. Establishing those obligations for the concrete chair contact language
is a separate geometric task. Neither that classification, the star cardinalities,
nor existence of a bridge path is asserted here.

All transport equations are equalities of complete `RegisteredFrame`s, including
the entire index permutation and all signs. An edge `(u,v)` transports from `v`
to `u`, consistently with the row-matrix convention of `RegisteredFrame.comp`.
-/
namespace RegisteredPrime.PrimeFacetClosure.StarHolonomy

theorem frame_ext {p : Nat} (F G : RegisteredFrame p)
    (hp : F.perm = G.perm) (hn : F.negative = G.negative) : F = G := by
  have hi : F.inverse = G.inverse := by
    funext i
    calc
      F.inverse i = F.inverse (G.perm (G.inverse i)) := by rw [G.right_inverse]
      _ = F.inverse (F.perm (G.inverse i)) := by rw [hp]
      _ = G.inverse i := F.left_inverse _
  cases F; cases G; cases hp; cases hn; cases hi; rfl

abbrev oneFrame (p : Nat) := (identityPose p).frame

theorem frame_comp_assoc {p : Nat} (F G H : RegisteredFrame p) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  apply frame_ext
  · rfl
  · funext i
    exact Bool.xor_assoc _ _ _

@[simp] theorem frame_comp_one {p : Nat} (F : RegisteredFrame p) :
    F.comp (oneFrame p) = F := by
  apply frame_ext
  · rfl
  · funext i; simp [RegisteredFrame.comp, oneFrame, identityPose]

@[simp] theorem frame_one_comp {p : Nat} (F : RegisteredFrame p) :
    (oneFrame p).comp F = F := by
  apply frame_ext
  · rfl
  · funext i; simp [RegisteredFrame.comp, oneFrame, identityPose]

@[simp] theorem frame_inv_comp {p : Nat} (F : RegisteredFrame p) :
    F.inv.comp F = oneFrame p := by
  apply frame_ext
  · funext i; exact F.right_inverse i
  · funext i; simp [RegisteredFrame.comp, RegisteredFrame.inv, oneFrame, identityPose]

@[simp] theorem frame_comp_inv {p : Nat} (F : RegisteredFrame p) :
    F.comp F.inv = oneFrame p := by
  apply frame_ext
  · funext i; exact F.left_inverse i
  · funext i; simp [RegisteredFrame.comp, RegisteredFrame.inv, oneFrame, identityPose, F.left_inverse]

/-- A frame in the gauge at `v`, expressed in the gauge at `u`. -/
def gauged {p : Nat} (U E V : RegisteredFrame p) : RegisteredFrame p :=
  (U.inv.comp E).comp V

theorem gauged_comp {p : Nat} (U V W E D : RegisteredFrame p) :
    gauged U (E.comp D) W = (gauged U E V).comp (gauged V D W) := by
  simp only [gauged, frame_comp_assoc]
  rw [← frame_comp_assoc V, frame_comp_inv, frame_one_comp]

theorem ungauge {p : Nat} (U E V H : RegisteredFrame p)
    (h : gauged U E V = H) : E = (U.comp H).comp V.inv := by
  rw [← h]
  simp only [gauged, frame_comp_assoc]
  rw [← frame_comp_assoc U, frame_comp_inv, frame_one_comp]
  rw [frame_comp_inv, frame_comp_one]

variable {V : Type*} {p : Nat} {G : SimpleGraph V}

/-- Data and local geometric obligations for the star gauge. `outer=false`
means an inner center and `outer=true` an outer leaf. `F.perm` is the involution
of star labels (multiplication by -1 in the intended application).

The last field is an edge classification obligation, not a conclusion about
reachable pairs or path products. -/
structure StarGauge (G : SimpleGraph V) (F : RegisteredFrame p) where
  involutive : ∀ k, F.perm (F.perm k) = k
  label : V → Fin p
  outer : V → Bool
  gauge : V → RegisteredFrame p
  edgeFrame : ∀ {u v}, G.Adj u v → RegisteredFrame p
  edge_classification : ∀ {u v} (h : G.Adj u v),
    (outer v = !outer u ∧ label v = label u ∧
      gauged (gauge u) (edgeFrame h) (gauge v) = oneFrame p) ∨
    (outer u = true ∧ outer v = true ∧ label v = F.perm (label u) ∧
      gauged (gauge u) (edgeFrame h) (gauge v) = bridge F (label u))

namespace StarGauge
variable {F : RegisteredFrame p} (S : StarGauge G F)

/-- The literal ordered product of the generating ambient edge frames. -/
def transport {u v : V} : G.Walk u v → RegisteredFrame p
  | .nil => oneFrame p
  | .cons h w => (S.edgeFrame h).comp (transport w)

/-- Parity of the number of wall edges, computed on an actual finite walk. -/
def wallOdd {u v : V} : G.Walk u v → Bool
  | .nil => false
  | .cons (u := u) (v := v) _ w => (S.outer u && S.outer v) ^^ wallOdd w

/-- The parity of all edges, independently of their classification. -/
def lengthOdd {u v : V} : G.Walk u v → Bool
  | .nil => false
  | .cons _ w => !(lengthOdd w)

include S in
/-- Multiplying normal forms genuinely cancels the two successive odd bridges.
In particular this uses the whole-frame involution, not just normal signs. -/
theorem normal_form_comp (k : Fin p) (a b : Bool) :
    (if a then bridge F k else oneFrame p).comp
        (if b then bridge F (if a then F.perm k else k) else oneFrame p) =
      (if a ^^ b then bridge F k else oneFrame p) := by
  cases a <;> cases b <;> simp [involutive_bridge_cancellation F S.involutive]

/-- Exact finite-path induction: both the terminal star label and the complete
ambient frame are determined by wall parity. -/
theorem path_normal_form {u v : V} (w : G.Walk u v) :
    S.label v = (if S.wallOdd w then F.perm (S.label u) else S.label u) ∧
    gauged (S.gauge u) (S.transport w) (S.gauge v) =
      (if S.wallOdd w then bridge F (S.label u) else oneFrame p) := by
  induction w with
  | nil => simp [wallOdd, transport, gauged]
  | @cons u v z h w ih =>
    rcases S.edge_classification h with hh | hw
    · have he : (S.outer u && S.outer v) = false := by
        rw [hh.1]; cases S.outer u <;> rfl
      simp only [wallOdd, he, Bool.false_xor]
      constructor
      · simpa only [hh.2.1] using ih.1
      · rw [transport, gauged_comp (S.gauge u) (S.gauge v), hh.2.2,
          frame_one_comp, ih.2, hh.2.1]
    · have he : (S.outer u && S.outer v) = true := by rw [hw.1, hw.2.1]; rfl
      simp only [wallOdd, he]
      constructor
      · rw [ih.1, hw.2.2.1]
        cases S.wallOdd w <;> simp [S.involutive]
      · rw [transport, gauged_comp (S.gauge u) (S.gauge v), hw.2.2.2,
          ih.2, hw.2.2.1]
        simpa only [Bool.true_eq, ↓reduceIte] using
          S.normal_form_comp (S.label u) true (S.wallOdd w)

/-- Hole edges toggle center/leaf status; wall edges do not. Hence wall parity
is total path parity corrected by the endpoint types. -/
theorem parity_identity {u v : V} (w : G.Walk u v) :
    (S.wallOdd w ^^ (S.outer u ^^ S.outer v)) = lengthOdd w := by
  induction w with
  | nil => simp [wallOdd, lengthOdd]
  | @cons u v z h w ih =>
    rcases S.edge_classification h with hh | hw
    · simp only [wallOdd, lengthOdd]
      rw [← ih, hh.1]
      cases S.outer u <;> cases S.outer z <;> cases S.wallOdd w <;> rfl
    · simp only [wallOdd, lengthOdd]
      rw [← ih, hw.1, hw.2.1]
      cases S.outer z <;> cases S.wallOdd w <;> rfl

/-- The recursive Boolean parity is the usual arithmetic parity of length. -/
theorem lengthOdd_eq_true_iff {u v : V} (w : G.Walk u v) :
    lengthOdd w = true ↔ w.length % 2 = 1 := by
  induction w with
  | nil => simp [lengthOdd]
  | @cons u v z h w ih =>
    simp only [lengthOdd, SimpleGraph.Walk.length_cons]
    cases hb : lengthOdd w
    · have hn : w.length % 2 ≠ 1 := by simpa only [hb, Bool.false_eq_true, false_iff] using ih
      simp only [Bool.not_false, true_iff]
      omega
    · have hn : w.length % 2 = 1 := ih.mp hb
      simp only [Bool.not_true, Bool.false_eq_true, false_iff]
      omega

/-- Same-type endpoints have wall parity equal to ordinary path parity. -/
theorem wallOdd_of_same_type {u v : V} (w : G.Walk u v)
    (ht : S.outer u = S.outer v) : S.wallOdd w = lengthOdd w := by
  have h := S.parity_identity w
  simpa only [ht, Bool.xor_self, Bool.xor_false] using h

/-- In particular, an odd inner-to-inner path has exactly the bridge `L_k`
from label `F.perm k` to label `k`, with no residual permutation. -/
theorem odd_same_type {u v : V} (w : G.Walk u v)
    (ht : S.outer u = S.outer v) (ho : w.length % 2 = 1) :
    S.label v = F.perm (S.label u) ∧
      gauged (S.gauge u) (S.transport w) (S.gauge v) = bridge F (S.label u) := by
  have hb : S.wallOdd w = true := by
    rw [S.wallOdd_of_same_type w ht]
    exact (lengthOdd_eq_true_iff w).mpr ho
  simpa only [hb, Bool.true_eq, ↓reduceIte] using S.path_normal_form w

/-- The full ambient transport of an even same-type path is identity in the
star gauges. It is not merely a diagonal sign cancellation. -/
theorem even_same_type {u v : V} (w : G.Walk u v)
    (ht : S.outer u = S.outer v) (he : w.length % 2 = 0) :
    S.label v = S.label u ∧
      gauged (S.gauge u) (S.transport w) (S.gauge v) = oneFrame p := by
  have hb : S.wallOdd w = false := by
    rw [S.wallOdd_of_same_type w ht]
    cases h : lengthOdd w
    · rfl
    · have := (lengthOdd_eq_true_iff w).mp h
      omega
  simpa only [hb, Bool.false_eq_true, ↓reduceIte] using S.path_normal_form w

/-- The explicit ambient matrix after undoing the star gauges. -/
theorem odd_same_type_ambient {u v : V} (w : G.Walk u v)
    (ht : S.outer u = S.outer v) (ho : w.length % 2 = 1) :
    S.transport w = ((S.gauge u).comp (bridge F (S.label u))).comp (S.gauge v).inv :=
  ungauge _ _ _ _ (S.odd_same_type w ht ho).2


/-- An odd path between unlike endpoint types has identity gauged transport:
one uncancelled hole edge accounts for its odd length. -/
theorem odd_different_type {u v : V} (w : G.Walk u v)
    (ht : S.outer u ≠ S.outer v) (ho : w.length % 2 = 1) :
    S.label v = S.label u ∧
      gauged (S.gauge u) (S.transport w) (S.gauge v) = oneFrame p := by
  have hp := S.parity_identity w
  have hl := (lengthOdd_eq_true_iff w).mpr ho
  have hx : (S.outer u ^^ S.outer v) = true := by
    cases hu : S.outer u <;> cases hv : S.outer v <;> simp_all
  have hb : S.wallOdd w = false := by
    rw [hx, hl] at hp
    cases hw : S.wallOdd w <;> simp_all
  simpa only [hb, Bool.false_eq_true, ↓reduceIte] using S.path_normal_form w

/-- A cycle based at a nonfixed star label has trivial complete ambient
holonomy, regardless of the length of the cycle. -/
theorem loop_holonomy_of_nonfixed {u : V} (w : G.Walk u u)
    (hn : F.perm (S.label u) ≠ S.label u) :
    gauged (S.gauge u) (S.transport w) (S.gauge u) = oneFrame p := by
  have h := S.path_normal_form w
  cases hb : S.wallOdd w
  · simpa only [hb, Bool.false_eq_true, ↓reduceIte] using h.2
  · have he : S.label u = F.perm (S.label u) := by
      simpa only [hb, Bool.true_eq, ↓reduceIte] using h.1
    exact False.elim (hn he.symm)

/-- At a fixed label (zero in the intended application), every cycle has
holonomy of order dividing two. Nontriviality and existence are separate
geometric obligations, rather than conclusions from the abstract graph. -/
theorem loop_holonomy_square {u : V} (w : G.Walk u u) :
    (gauged (S.gauge u) (S.transport w) (S.gauge u)).comp
      (gauged (S.gauge u) (S.transport w) (S.gauge u)) = oneFrame p := by
  have h := S.path_normal_form w
  cases hb : S.wallOdd w
  · simpa only [hb, Bool.false_eq_true, ↓reduceIte, frame_one_comp] using
      congrArg (fun H => H.comp H) h.2
  · have hk : S.label u = F.perm (S.label u) := by
      simpa only [hb, Bool.true_eq, ↓reduceIte] using h.1
    have he : gauged (S.gauge u) (S.transport w) (S.gauge u) = bridge F (S.label u) := by
      simpa only [hb, Bool.true_eq, ↓reduceIte] using h.2
    rw [he]
    simpa only [← hk] using involutive_bridge_cancellation F S.involutive (S.label u)

/-- The orientation character flips at each literal generating edge. -/
theorem orientation_along_walk (χ : V → ℤ)
    (hχ : ∀ {u v}, G.Adj u v → χ v = -χ u) {u v : V} (w : G.Walk u v) :
    χ v = (if lengthOdd w then -χ u else χ u) := by
  induction w with
  | nil => simp [lengthOdd]
  | @cons u v z h w ih =>
    simp only [lengthOdd]
    rw [ih, hχ h]
    by_cases hb : lengthOdd w = true <;> simp_all

/-- Nonzero opposite orientations force every connecting walk to be odd.
This converts the compiler's opposite-coefficient condition into path parity. -/
theorem odd_length_of_opposite (χ : V → ℤ)
    (hχ : ∀ {u v}, G.Adj u v → χ v = -χ u) {u v : V} (w : G.Walk u v)
    (hn : χ u ≠ 0) (hop : χ v = -χ u) : w.length % 2 = 1 := by
  apply (lengthOdd_eq_true_iff w).mp
  have hh := orientation_along_walk χ hχ w
  cases hb : lengthOdd w
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hh
    omega
  · rfl

/-- Graph reachability and opposite orientations suffice: no path transport
or graph-closure conclusion is supplied as a hypothesis. -/
theorem reachable_opposite_same_type (χ : V → ℤ)
    (hχ : ∀ {u v}, G.Adj u v → χ v = -χ u) {u v : V}
    (hr : G.Reachable u v) (hn : χ u ≠ 0) (hop : χ v = -χ u)
    (ht : S.outer u = S.outer v) :
    ∃ w : G.Walk u v, w.length % 2 = 1 ∧
      S.label v = F.perm (S.label u) ∧
      S.transport w = ((S.gauge u).comp (bridge F (S.label u))).comp (S.gauge v).inv := by
  obtain ⟨w⟩ := hr
  have hw := odd_length_of_opposite χ hχ w hn hop
  exact ⟨w, hw, (S.odd_same_type w ht hw).1, S.odd_same_type_ambient w ht hw⟩

end StarGauge

#print axioms StarGauge.path_normal_form
#print axioms StarGauge.parity_identity
#print axioms StarGauge.odd_same_type_ambient
#print axioms StarGauge.odd_different_type
#print axioms StarGauge.loop_holonomy_of_nonfixed
#print axioms StarGauge.loop_holonomy_square
#print axioms StarGauge.reachable_opposite_same_type
end RegisteredPrime.PrimeFacetClosure.StarHolonomy
