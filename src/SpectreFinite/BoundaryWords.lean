module

public import SpectreFinite.ListedPatches

@[expose] public section


/-!
Exact exposed-side boundary certificates for the nine literal Figure 5 patches.
The six marked vertices are transcribed from the author TeX. This proves only
finite boundary/cancellation/interface facts, not arbitrary parent completeness,
universal composition, plane existence, or aperiodicity. The parent-side order
is reflected: macro side i carries original parent mark (-i mod 6).
Mathematical data: Smith, Myers, Kaplan, Goodman-Strauss, arXiv:2305.17743v2,
CC BY 4.0. See boundary_20261013/BOUNDARY_PROVENANCE.md.
-/

namespace SpectreFinite
namespace Boundary

abbrev Vertex := Int × Int
structure SideRef where
  child : Nat
  side : Fin 6
  deriving DecidableEq

def allSides (p : List PlacedHex) : List SideRef :=
  (List.range p.length).flatMap fun i => (List.finRange 6).map fun d => ⟨i,d⟩
def defaultHex : PlacedHex := ⟨0,0,0,0⟩
def hexAt (p : List PlacedHex) (e : SideRef) : PlacedHex := p.getD e.child defaultHex
/-- Author hcoords expressed in exact integer vcoords. -/
def center (a : PlacedHex) : Vertex := (4*a.q + 2*a.r + 2, 2*a.r - 2*a.q)
def corners : List Vertex := [(-2,2),(-2,0),(0,-2),(2,-2),(2,0),(0,2)]
def start (p : List PlacedHex) (e : SideRef) : Vertex :=
  addPos (center (hexAt p e)) (corners.getD e.side.val (0,0))
def finish (p : List PlacedHex) (e : SideRef) : Vertex :=
  addPos (center (hexAt p e)) (corners.getD ((e.side.val+1)%6) (0,0))
def mark (p : List PlacedHex) (e : SideRef) : Int := facingMark (hexAt p e) e.side
/-- A child side is exposed precisely when its axial neighbor is absent. -/
def exposedSides (p : List PlacedHex) : List SideRef :=
  (allSides p).filter fun e => !(p.any fun a =>
    pos a == addPos (pos (hexAt p e)) (direction e.side))
/-- Independent geometric cancellation test: no reversed coincident child side. -/
def uncancelledSides (p : List PlacedHex) : List SideRef :=
  (allSides p).filter fun e => !((allSides p).any fun f =>
    start p e == finish p f && finish p e == start p f)

/-- Explicit certificates list every exposed side in oriented cyclic order. -/
def traceTable : List (List SideRef) := [
  [⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨5,2⟩, ⟨6,1⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨3,5⟩, ⟨2,4⟩],
  [⟨3,5⟩, ⟨2,4⟩, ⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩],
  [⟨3,5⟩, ⟨2,4⟩, ⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩],
  [⟨3,5⟩, ⟨2,4⟩, ⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩],
  [⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨3,5⟩, ⟨2,4⟩],
  [⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨3,5⟩, ⟨2,4⟩],
  [⟨3,5⟩, ⟨2,4⟩, ⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩],
  [⟨3,5⟩, ⟨2,4⟩, ⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩],
  [⟨2,5⟩, ⟨2,0⟩, ⟨0,5⟩, ⟨0,0⟩, ⟨4,5⟩, ⟨4,0⟩, ⟨4,1⟩, ⟨4,2⟩, ⟨5,1⟩, ⟨7,0⟩, ⟨7,1⟩, ⟨7,2⟩, ⟨7,3⟩, ⟨6,2⟩, ⟨6,3⟩, ⟨6,4⟩, ⟨1,3⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨3,4⟩, ⟨3,5⟩, ⟨2,4⟩]
]

def markerTable : List (List Vertex) := [
  [(4, 4), (0, 2), ((-2), 0), (0, (-4)), (10, (-8)), (10, 0)],
  [(8, 2), (0, 2), ((-2), (-2)), (6, (-10)), (10, (-8)), (10, (-2))],
  [(8, 2), (0, 2), ((-2), 0), (4, (-8)), (8, (-10)), (10, (-2))],
  [(8, 2), (0, 2), ((-2), 0), (6, (-10)), (10, (-8)), (10, (-2))],
  [(4, 4), (0, 2), ((-2), 0), (4, (-8)), (8, (-10)), (10, (-2))],
  [(4, 4), (0, 2), ((-2), 0), (6, (-10)), (10, (-8)), (10, (-2))],
  [(8, 2), (2, 4), ((-2), (-2)), (6, (-10)), (10, (-8)), (10, (-2))],
  [(8, 2), (0, 2), ((-2), 0), (4, (-8)), (10, (-8)), (10, (-2))],
  [(4, 4), (0, 2), ((-2), 0), (4, (-8)), (10, (-8)), (10, (-2))]
]

def cutTable : List (List Nat) := [
  [0, 3, 5, 7, 12, 17, 20],
  [0, 5, 8, 13, 16, 20, 22],
  [0, 5, 7, 12, 14, 20, 22],
  [0, 5, 7, 13, 16, 20, 22],
  [0, 3, 5, 10, 12, 18, 22],
  [0, 3, 5, 11, 14, 18, 22],
  [0, 3, 8, 13, 16, 20, 22],
  [0, 5, 7, 12, 16, 20, 22],
  [0, 3, 5, 10, 14, 18, 22]
]

def trace (k : TileKind) : List SideRef := traceTable.getD k.val []
def markers (k : TileKind) : List Vertex := markerTable.getD k.val []
def cuts (k : TileKind) : List Nat := cutTable.getD k.val []
def segment (k : TileKind) (s : Fin 6) : List SideRef :=
  ((trace k).drop ((cuts k).getD s.val 0)).take
    ((cuts k).getD (s.val+1) 0 - (cuts k).getD s.val 0)
def macroLabel (k : TileKind) (s : Fin 6) : Int :=
  (edgeWords.getD k.val []).getD ((6 - s.val)%6) 0
/-- One nonrepeating endpoint cycle containing exactly the uncancelled sides. -/
def BoundaryCertificate (k : TileKind) : Prop :=
  (trace k).Perm (exposedSides (children k)) ∧
  exposedSides (children k) = uncancelledSides (children k) ∧
  ((trace k).map (start (children k))).Nodup ∧
  (trace k).map (finish (children k)) =
    ((trace k).map (start (children k))).rotateLeft 1 ∧
  (∀ e ∈ trace k, e.child < (children k).length) ∧
  (trace k).length = if k.val = 0 then 20 else 22
instance (k : TileKind) : Decidable (BoundaryCertificate k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The author's six vertices partition the full oriented side cycle. -/
def MarkerCertificate (k : TileKind) : Prop :=
  (markers k).length = 6 ∧ (markers k).Nodup ∧
  (cuts k).length = 7 ∧ (cuts k).Pairwise (· < ·) ∧
  ((List.finRange 6).map (segment k)).flatten = trace k ∧
  ∀ s : Fin 6,
    (segment k s) ≠ [] ∧
    ((segment k s).map (start (children k))).head? =
      some ((markers k).getD s.val (0,0)) ∧
    ((segment k s).map (finish (children k))).getLast? =
      some ((markers k).getD ((s.val+1)%6) (0,0))
instance (k : TileKind) : Decidable (MarkerCertificate k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Relative directions (mod 6) and signed child marks, in traversal order. -/
abbrev Signature := List (Nat × Int)
def normalize (w : Signature) : Signature :=
  w.map fun x => ((x.1 + 6 - (w.getD 0 (0,0)).1)%6, x.2)
def actualSignature (k : TileKind) (s : Fin 6) : Signature :=
  normalize ((segment k s).map fun e => (e.side.val, mark (children k) e))
/-- Opposite traversal reverses order, reverses each direction, and complements marks. -/
def reverseComplement (w : Signature) : Signature :=
  normalize (w.reverse.map fun x => ((x.1+3)%6, -x.2))

def signatureTable : List (Int × Signature) := [
  ((-8), [(0, (-5)), (1, 5), (2, 0), (1, (-5)), (0, 5), (1, 8)]),
  ((-6), [(0, (-1)), (5, 5), (0, 8)]),
  ((-5), [(0, 5), (1, 0), (0, (-5)), (5, 5)]),
  ((-4), [(0, (-8)), (5, (-5)), (0, 1), (5, 2), (0, 8)]),
  ((-3), [(0, 2), (1, 0), (0, (-5)), (5, 5), (0, 8)]),
  ((-2), [(0, (-1)), (5, 5)]),
  ((-1), [(0, 5), (1, 0), (0, (-2))]),
  (0, [(0, (-5)), (1, 5), (2, 0), (1, (-5)), (0, 5)]),
  (1, [(0, 2), (1, 0), (0, (-5))]),
  (2, [(0, (-5)), (1, 1)]),
  (3, [(0, (-8)), (5, (-5)), (0, 5), (1, 0), (0, (-2))]),
  (4, [(0, (-8)), (5, (-2)), (0, (-1)), (5, 5), (0, 8)]),
  (5, [(0, (-5)), (1, 5), (2, 0), (1, (-5))]),
  (6, [(0, (-8)), (5, (-5)), (0, 1)]),
  (8, [(0, (-8)), (5, (-5)), (0, 5), (1, 0), (0, (-5)), (5, 5)])
 ]
def labelAlphabet : List Int := signatureTable.map Prod.fst
def canonicalSignature (m : Int) : Signature :=
  ((signatureTable.find? fun p => p.1 == m).getD (0,[])).2

/-- Exact counterclockwise 60-degree rotation in the author's vcoords. -/
def rotateVertex : Nat → Vertex → Vertex
  | 0, v => v
  | n+1, v => rotateVertex n (-v.2, v.1+v.2)
def subVertex (v w : Vertex) : Vertex := (v.1-w.1, v.2-w.2)
def stepVector (d : Nat) : Vertex :=
  subVertex (corners.getD ((d+1)%6) (0,0)) (corners.getD d (0,0))
def geometricSignature (w : Signature) : List (Vertex × Int) :=
  w.map fun x => (stepVector x.1, x.2)
/-- Actual endpoint differences, rotated so the first boundary side is side zero. -/
def normalizedGeometry (k : TileKind) (s : Fin 6) : List (Vertex × Int) :=
  let es := segment k s
  es.map fun e =>
    (rotateVertex (6 - (es.getD 0 ⟨0,0⟩).side.val)
      (subVertex (finish (children k) e) (start (children k) e)), mark (children k) e)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem boundary_0 : BoundaryCertificate 0 := by decide
private theorem boundary_1 : BoundaryCertificate 1 := by decide
private theorem boundary_2 : BoundaryCertificate 2 := by decide
private theorem boundary_3 : BoundaryCertificate 3 := by decide
private theorem boundary_4 : BoundaryCertificate 4 := by decide
private theorem boundary_5 : BoundaryCertificate 5 := by decide
private theorem boundary_6 : BoundaryCertificate 6 := by decide
private theorem boundary_7 : BoundaryCertificate 7 := by decide
private theorem boundary_8 : BoundaryCertificate 8 := by decide

/-- Complete finite oriented boundaries, with independently checked cancellation. -/
theorem nine_boundaries : ∀ k : TileKind, BoundaryCertificate k := by
  exact Fin.cases boundary_0 (Fin.cases boundary_1 (Fin.cases boundary_2 (Fin.cases boundary_3 (Fin.cases boundary_4 (Fin.cases boundary_5 (Fin.cases boundary_6 (Fin.cases boundary_7 (Fin.cases boundary_8 (fun i => Fin.elim0 i)))))))))

private theorem markers_0 : MarkerCertificate 0 := by decide
private theorem markers_1 : MarkerCertificate 1 := by decide
private theorem markers_2 : MarkerCertificate 2 := by decide
private theorem markers_3 : MarkerCertificate 3 := by decide
private theorem markers_4 : MarkerCertificate 4 := by decide
private theorem markers_5 : MarkerCertificate 5 := by decide
private theorem markers_6 : MarkerCertificate 6 := by decide
private theorem markers_7 : MarkerCertificate 7 := by decide
private theorem markers_8 : MarkerCertificate 8 := by decide

/-- All six marked vertices lie on the cycle and delimit its six nonempty pieces. -/
theorem nine_marker_partitions : ∀ k : TileKind, MarkerCertificate k := by
  exact Fin.cases markers_0 (Fin.cases markers_1 (Fin.cases markers_2 (Fin.cases markers_3 (Fin.cases markers_4 (Fin.cases markers_5 (Fin.cases markers_6 (Fin.cases markers_7 (Fin.cases markers_8 (fun i => Fin.elim0 i)))))))))

/-- All 54 marked macro-sides have the claimed label-specific signature. -/
theorem nine_signatures : ∀ k : TileKind, ∀ s : Fin 6,
    actualSignature k s = canonicalSignature (macroLabel k s) := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

theorem nine_labels_in_alphabet : ∀ k : TileKind, ∀ s : Fin 6,
    macroLabel k s ∈ labelAlphabet := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

/-- The combinatorial signatures are the normalized exact geometric edge vectors. -/
theorem nine_geometric_signatures : ∀ k : TileKind, ∀ s : Fin 6,
    normalizedGeometry k s = geometricSignature (canonicalSignature (macroLabel k s)) := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

/-- The finite label dictionary respects reversed complementary traversal. -/
theorem canonical_complements : ∀ m ∈ labelAlphabet,
    canonicalSignature (-m) = reverseComplement (canonicalSignature m) := by decide

/-- Same parent marks determine equal normalized finite child boundary signatures. -/
theorem same_label_same_signature (k l : TileKind) (s t : Fin 6)
    (h : macroLabel k s = macroLabel l t) :
    actualSignature k s = actualSignature l t := by
  rw [nine_signatures, nine_signatures, h]

/-- Same parent mark gives equal rotated endpoint-displacement and child-mark lists. -/
theorem same_label_same_geometry (k l : TileKind) (s t : Fin 6)
    (h : macroLabel k s = macroLabel l t) :
    normalizedGeometry k s = normalizedGeometry l t := by
  rw [nine_geometric_signatures, nine_geometric_signatures, h]

/-- Complementary parent marks yield reversed complementary child interfaces.
This does not assert that arbitrary arrangements of the patches can be composed. -/
theorem matching_labels_matching_signatures (k l : TileKind) (s t : Fin 6)
    (h : macroLabel k s = -macroLabel l t) :
    actualSignature k s = reverseComplement (actualSignature l t) := by
  rw [nine_signatures, nine_signatures, h]
  exact canonical_complements _ (nine_labels_in_alphabet l t)

#print axioms nine_boundaries
#print axioms nine_marker_partitions
#print axioms nine_signatures
#print axioms nine_labels_in_alphabet
#print axioms nine_geometric_signatures
#print axioms same_label_same_geometry
#print axioms canonical_complements
#print axioms same_label_same_signature
#print axioms matching_labels_matching_signatures

end Boundary
end SpectreFinite
