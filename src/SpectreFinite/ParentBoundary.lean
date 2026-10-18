module

public import SpectreFinite.BoundaryWords
public import SpectreFinite.ParentOwnershipFiniteEncoding

@[expose] public section


/-!
Native boundary and vertex queries for the paper's actual parent assignment.
All results about a field remain conditional on finite occurrence certificates.
No graph-flatness, lattice realization, global existence or hierarchy is assumed.
-/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

/-- The actual axial cell on the other side of an exposed child edge. -/
def outsideCell (k : TileKind) (e : SideRef) : Position :=
  addPos (pos (hexAt (children k) e)) (direction e.side)

/-- Native hexagon corner, with the exact author coordinate convention. -/
def cellCorner (x : Position) (d : Fin 6) : Vertex :=
  addPos (4*x.1+2*x.2+2, 2*x.2-2*x.1) (corners.getD d.val (0,0))

def Incident (x : Position) (v : Vertex) : Prop :=
  ∃ d : Fin 6, cellCorner x d = v
instance (x : Position) (v : Vertex) : Decidable (Incident x v) :=
  inferInstanceAs (Decidable (∃ d : Fin 6, cellCorner x d = v))

/-- Invert the native corner equations. The final incidence filter removes
candidates where division did not give an actual integral corner. -/
def cornerCandidate (v : Vertex) (d : Fin 6) : Position :=
  let c := corners.getD d.val (0,0)
  ((v.1-v.2-c.1+c.2-2)/6, (v.1+2*v.2-c.1-2*c.2-2)/6)

def incidentCells (v : Vertex) : List Position :=
  (((List.finRange 6).filter (fun d =>
    decide (cellCorner (cornerCandidate v d) d = v))).map (cornerCandidate v)).eraseDups

/-- Exact completeness over all axial cells, not a bounded-radius definition. -/
theorem mem_incidentCells_iff (x : Position) (v : Vertex) :
    x ∈ incidentCells v ↔ Incident x v := by
  simp only [incidentCells, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨d,hd,he⟩
    have hc := of_decide_eq_true (List.mem_filter.mp hd).2
    exact ⟨d,by rw [← he]; exact hc⟩
  · rintro ⟨d,hd⟩
    have hx : cornerCandidate v d = x := by
      apply Prod.ext
      · have he := congrArg Prod.fst hd
        have he' := congrArg Prod.snd hd
        simp only [cellCorner, addPos] at he he'
        simp only [cornerCandidate]
        omega
      · have he := congrArg Prod.fst hd
        have he' := congrArg Prod.snd hd
        simp only [cellCorner, addPos] at he he'
        simp only [cornerCandidate]
        omega
    exact ⟨d,List.mem_filter.mpr ⟨by simp,decide_eq_true (by rw [hx]; exact hd)⟩,hx⟩

def incidentOwners (own : Position → List Position) (v : Vertex) : List Position :=
  ((incidentCells v).flatMap own).eraseDups

/-- Every possible owner of any cell incident to this exact vertex. -/
theorem mem_incidentOwners_iff (own : Position → List Position) (v : Vertex)
    (a : Position) : a ∈ incidentOwners own v ↔
      ∃ x, Incident x v ∧ a ∈ own x := by
  simp only [incidentOwners, List.mem_eraseDups, List.mem_flatMap, mem_incidentCells_iff]

/-- All actual cells queried by the boundary and native-vertex certificate. -/
def support (k : TileKind) : List Position :=
  ((trace k).map (outsideCell k) ++
    ((trace k).flatMap (fun e => incidentCells (start (children k) e)))).eraseDups


def vertexAt (k : TileKind) (s : Fin 6) : Vertex := (markers k).getD s.val (0,0)
def previous (s : Fin 6) : Nat := (s.val+5)%6

def edgeAt (k : TileKind) (i : Nat) : SideRef := (trace k).getD i ⟨0,0⟩
def previousEdge (k : TileKind) (i : Nat) : SideRef :=
  edgeAt k ((i+(trace k).length-1)%(trace k).length)

/-- Six constant, distinct outside owners, exactly three parents at each
author vertex, and exactly two parents at every other native boundary vertex.
The last clause certifies changes of outside owner exactly at author markers. -/
def Structure (own : Position → List Position) (k : TileKind)
    (neighbors : List Position) : Prop :=
  neighbors.length = 6 ∧ neighbors.Nodup ∧ (0,0) ∉ neighbors ∧
  (∀ s : Fin 6, ∀ e ∈ segment k s,
    own (outsideCell k e) = [neighbors.getD s.val (0,0)]) ∧
  (∀ s : Fin 6,
    (incidentOwners own (vertexAt k s)).Perm
      [(0,0),neighbors.getD (previous s) (0,0),neighbors.getD s.val (0,0)]) ∧
  (∀ e ∈ trace k,
    (incidentOwners own (start (children k) e)).length =
      if start (children k) e ∈ markers k then 3 else 2) ∧
  (∀ i : Fin (trace k).length,
    (own (outsideCell k (previousEdge k i.val)) ≠
      own (outsideCell k (edgeAt k i.val))) ↔
      start (children k) (edgeAt k i.val) ∈ markers k)
instance (own : Position → List Position) (k : TileKind) (ns : List Position) :
    Decidable (Structure own k ns) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The actual selected parent shape and the actual boundary assignment. -/
def RootStructure (f : Position → State) : Prop :=
  ∃ k : TileKind, ∃ ns : List Position,
    rootParent f = childPatch k ∧ Structure (owners f) k ns

abbrev OwnerTable := List (Position × Position)
def tableOwners (table : OwnerTable) (x : Position) : List Position :=
  match table.find? (fun a => a.1 == x) with
  | none => []
  | some a => [a.2]

def TableSound (f : Position → State) (table : OwnerTable) : Prop :=
  ∀ a ∈ table, owners f a.1 = [a.2]
instance (f : Position → State) (table : OwnerTable) : Decidable (TableSound f table) :=
  inferInstanceAs (Decidable (∀ a ∈ table, owners f a.1 = [a.2]))

#print axioms mem_incidentCells_iff
#print axioms mem_incidentOwners_iff

end SpectreFinite.HexSearch.ParentBoundary
