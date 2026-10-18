module

public import SpectreClusters.LiteralData

@[expose] public section


/-! Finite certificates for neighboring literal cluster interfaces. -/
namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters

structure Configuration where
  rootKind : ClusterKind
  neighborKind : ClusterKind
  turn : Turn
  centerShift : Point
  sharedPath : List Point

def rootCells (c : Configuration) : List Cell := clusterCells c.rootKind
def neighborCells (c : Configuration) : List Cell :=
  (clusterCells c.neighborKind).map (moveCell c.turn c.centerShift)
def pathEdges (path : List Point) : List (Point × Point) := path.zip path.tail

def cellPairCheckedB (path : List Point) (a b : Cell) : Bool :=
  decide (a ≠ b) && (pathEdges path).any fun edge =>
    (cellVertices a).all fun v =>
      decide (v ∉ cellVertices b ∨ v = edge.1 ∨ v = edge.2)

def configurationCheckedB (c : Configuration) : Bool :=
  (rootCells c).all fun a => (neighborCells c).all (cellPairCheckedB c.sharedPath a)

theorem cellPairCheckedB_sound (path : List Point) (a b : Cell)
    (hc : cellPairCheckedB path a b = true) :
    a ≠ b ∧ ∃ edge ∈ pathEdges path,
      ∀ v ∈ cellVertices a, v ∈ cellVertices b → v = edge.1 ∨ v = edge.2 := by
  have h := Bool.and_eq_true_iff.mp hc
  obtain ⟨edge,he,hcheck⟩ := List.any_eq_true.mp h.2
  refine ⟨of_decide_eq_true h.1,edge,he,?_⟩
  intro v hva hvb
  have hv : v ∉ cellVertices b ∨ v = edge.1 ∨ v = edge.2 :=
    of_decide_eq_true (List.all_eq_true.mp hcheck v hva)
  exact hv.resolve_left (fun hn => hn hvb)

theorem configurationCheckedB_sound (c : Configuration)
    (hc : configurationCheckedB c = true) :
    ∀ a ∈ rootCells c, ∀ b ∈ neighborCells c,
      a ≠ b ∧ ∃ edge ∈ pathEdges c.sharedPath,
        ∀ v ∈ cellVertices a, v ∈ cellVertices b → v = edge.1 ∨ v = edge.2 := by
  intro a ha b hb
  exact cellPairCheckedB_sound c.sharedPath a b
    (List.all_eq_true.mp (List.all_eq_true.mp hc a ha) b hb)

end SpectreGeometry.ReverseClusterNeighborCells
