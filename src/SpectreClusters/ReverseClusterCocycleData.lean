module

public import SpectreClusters.ReverseMarkedBoundaries
public import SpectreFinite.HexRotationComposition

@[expose] public section


/-! Exact marked-cluster corners and matching displacement certificates.
These are local finite geometric statements, not global coverage. -/
namespace SpectreClusters.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch

def clusterCorners : List (List Point) := [
  [(-5,4),(-4,-4),(4,-11),(11,-7),(3,3),(-2,6)],
  [(-5,4),(-1,-7),(4,-10),(10,-8),(9,0),(-2,7)],
  [(-5,4),(-1,-7),(4,-10),(10,-5),(8,0),(-2,6)],
  [(-5,4),(-1,-7),(4,-10),(10,-8),(9,0),(-2,6)],
  [(-5,4),(-4,-4),(4,-10),(10,-5),(8,0),(-2,6)],
  [(-5,4),(-4,-4),(4,-10),(10,-8),(9,0),(-2,6)],
  [(-4,-1),(-1,-7),(4,-10),(10,-8),(9,0),(-2,7)],
  [(-5,4),(-1,-7),(4,-10),(10,-8),(8,0),(-2,6)],
  [(-5,4),(-4,-4),(4,-10),(10,-8),(8,0),(-2,6)]
]

def corner (k : Fin 9) (d : Fin 6) : Point :=
  (clusterCorners.getD k.val []).getD d.val (0,0)

def sideTurn (r d : Fin 6) : Fin 6 := ⟨(d.val+6-r.val)%6, Nat.mod_lt _ (by decide)⟩

def stateCorner (a : State) (d : Fin 6) : Point :=
  rotate a.2 (corner a.1 (sideTurn a.2 d))

def sideMatch (a b : State) (d : Fin 6) : Prop :=
  facingMark (placed ((0,0),a)) d = -facingMark (placed ((0,0),b)) (opposite d)
instance (a b : State) (d : Fin 6) : Decidable (sideMatch a b d) :=
  inferInstanceAs (Decidable (_ = _))

def vertexDelta (a b : State) (d : Fin 6) : Point :=
  sub (stateCorner a d) (stateCorner b (rotateTurn 4 d))

def centerDelta (a b : State) (d : Fin 6) : Point :=
  let p := vertexDelta a b d
  ((p.1-p.2)/6,(p.1+2*p.2)/6)

set_option maxRecDepth 100000 in
theorem corner_path_binding : ∀ k : Fin 9, ∀ d : Fin 6,
    corner k d = ((markedPaths k).getD d.val []).headD (0,0) ∧
    corner k (rotateTurn 1 d) = ((markedPaths k).getD d.val []).getLast! := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i)))))))))

def PairCertificate (k : Fin 9) : Prop :=
  ∀ (r : Fin 6) (j : Fin 9) (t : Fin 6) (d : Fin 6), sideMatch (k,r) (j,t) d →
    vertexDelta (k,r) (j,t) d = sub (stateCorner (k,r) (rotateTurn 1 d))
      (stateCorner (j,t) (opposite d)) ∧
    lattice (centerDelta (k,r) (j,t) d) = vertexDelta (k,r) (j,t) d

end SpectreClusters.ReverseExistence
