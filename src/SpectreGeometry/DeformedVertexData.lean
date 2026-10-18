module

public import SpectreGeometry.CornerSteps

@[expose] public section


/-! Exact integer coordinates after stretching global even C12 directions
by sqrt(3). These data identify the deformation on boundary edges; the
existence of a globally realized deformed tiling remains separate. -/
namespace SpectreGeometry

abbrev KiteVertexPoint := Int × Int

def kiteVertexAdd (a b : KiteVertexPoint) : KiteVertexPoint := (a.1+b.1,a.2+b.2)
def kiteVertexSub (a b : KiteVertexPoint) : KiteVertexPoint := (a.1-b.1,a.2-b.2)
def kiteVertexTurn (p : KiteVertexPoint) : KiteVertexPoint := (-p.2,p.1+p.2)
def kiteVertexRotate (n : Nat) (p : KiteVertexPoint) : KiteVertexPoint :=
  match n%6 with
  | 0 => p
  | 1 => (-p.2,p.1+p.2)
  | 2 => (-p.1-p.2,p.1)
  | 3 => (-p.1,-p.2)
  | 4 => (p.2,-p.1-p.2)
  | _ => (p.1+p.2,-p.1)

def deformedEvenVertices : List KiteVertexPoint :=
  [(0,0),(2,-1),(3,-3),(4,-3),(4,-2),(6,-3),(7,-2),(6,-1),(5,-1),(4,1),(2,2),(0,3),(-1,2),(0,1)]
def deformedOddVertices : List KiteVertexPoint :=
  [(0,0),(1,0),(2,-1),(3,0),(2,2),(3,2),(3,3),(1,4),(0,3),(-1,4),(-2,4),(-3,4),(-3,3),(-1,2)]
def deformedVertex (k : Fin 12) (i : Fin 14) : KiteVertexPoint :=
  kiteVertexRotate (k.val/2) ((if k.val%2=0 then deformedEvenVertices else deformedOddVertices).getD i.val (0,0))
def deformedOffset (k : Fin 12) : KiteVertexPoint :=
  kiteVertexRotate (k.val/2) (if k.val%2=0 then (2,-1) else (-1,2))
def deformedDirections : List KiteVertexPoint :=
  [(2,-1),(1,0),(1,1),(0,1),(-1,2),(-1,1),(-2,1),(-1,0),(-1,-1),(0,-1),(1,-2),(1,-1)]
def deformedDirection (d : Fin 12) : KiteVertexPoint := deformedDirections.getD d.val (0,0)

theorem deformed_vertex_zero : ∀ k : Fin 12, deformedVertex k 0 = (0,0) := by decide

theorem deformed_boundary_steps : ∀ (k : Fin 12) (i : Fin 14),
    kiteVertexSub (deformedVertex k (next i)) (deformedVertex k i) =
      deformedDirection (directionAdd k (edgeTurn i)) := by decide

def AllowedCornerPair (a b : Fin 14) : Prop :=
  cornerSteps a + cornerSteps b = 6 ∨ cornerSteps a + cornerSteps b = 8 ∨
  cornerSteps a + cornerSteps b = 9 ∨ cornerSteps a + cornerSteps b = 12
instance (a b : Fin 14) : Decidable (AllowedCornerPair a b) := inferInstanceAs (Decidable (_ ∨ _))
def AllowedReversedEdgePair (e j : Fin 14) : Prop :=
  AllowedCornerPair e (next j) ∧ AllowedCornerPair (next e) j
instance (e j : Fin 14) : Decidable (AllowedReversedEdgePair e j) := inferInstanceAs (Decidable (_ ∧ _))
def opposedFrame (r : Fin 12) (e j : Fin 14) : Fin 12 :=
  directionAdd (directionAdd (directionAdd r (edgeTurn e)) 6) (directionInverse (edgeTurn j))
def deformedAnchorShift (r s : Fin 12) (e j : Fin 14) : KiteVertexPoint :=
  kiteVertexSub (kiteVertexAdd (kiteVertexSub (deformedVertex r e) (deformedVertex s (next j)))
    (deformedOffset s)) (deformedOffset r)
def InKiteCenterLattice (p : KiteVertexPoint) : Prop :=
  (p.1-p.2)%6 = 0 ∧ (p.1+2*p.2)%6 = 0
instance (p : KiteVertexPoint) : Decidable (InKiteCenterLattice p) := inferInstanceAs (Decidable (_ ∧ _))

theorem allowed_edge_pair_count : ((List.finRange 14).flatMap fun e =>
    (List.finRange 14).filter (fun j => decide (AllowedReversedEdgePair e j))).length = 74 := by decide

end SpectreGeometry
