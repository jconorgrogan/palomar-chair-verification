module

public import SpectreClusters.LiteralBoundaries

@[expose] public section


/-! Proof-free Boolean edge comparisons are extensionally equal to the
ordinary list-membership boundary operation. -/
namespace SpectreClusters

def edgeEqB (a b : Edge) : Bool :=
  a.1.1 == b.1.1 && a.1.2 == b.1.2 && a.2.1 == b.2.1 && a.2.2 == b.2.2

theorem edgeEqB_iff (a b : Edge) : edgeEqB a b = true ↔ a = b := by
  simp [edgeEqB,Prod.ext_iff,and_assoc]

def fastExterior (edges : List Edge) : List Edge :=
  edges.filter (fun e => !(edges.any (edgeEqB (reverseEdge e))))

theorem any_edgeEqB (edges : List Edge) (e : Edge) :
    edges.any (edgeEqB e) = edges.contains e := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,edgeEqB_iff,List.contains_iff_mem]
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ha
  · intro h
    exact ⟨e,h,rfl⟩

theorem exteriorEdges_fast (cells : List Cell) :
    exteriorEdges cells = fastExterior (shapeEdges cells) := by
  simp only [exteriorEdges,fastExterior,any_edgeEqB]

end SpectreClusters
