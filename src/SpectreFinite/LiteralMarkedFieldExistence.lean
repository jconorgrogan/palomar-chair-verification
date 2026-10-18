module

public import SpectreFinite.TaggedHexExistenceTransfer
public import SpectreFinite.ForwardPairPortTriangles
public import SpectreFinite.ForwardTriplePortTriangles

@[expose] public section


/-! Existence of a globally legal marked field from actual iterated literal
forward substitution. Every finite routing premise is discharged here.
No physical tiling correspondence is asserted. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

theorem taggedStep_triangle (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (x y z : ChildTag S)
    (hy : S.taggedStep d x = some y)
    (hz : S.taggedStep (rotateTurn 1 d) x = some z) :
    S.taggedStep (rotateTurn 2 d) y = some z :=
  taggedStep_triangle_of_port_laws all_pair_port_triangles all_root_port_triangles
    S hs d x y z hy hz

theorem refine_triangle (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (v w z : S.refine.Cell)
    (hw : S.refine.step d v = some w)
    (hz : S.refine.step (rotateTurn 1 d) v = some z) :
    S.refine.step (rotateTurn 2 d) w = some z :=
  refine_triangle_from_port_laws all_pair_port_triangles all_root_port_triangles
    S hs d v w z hw hz

theorem refine_wellFormed (S : PartialMarkedHexSystem) (hs : S.WellFormed) :
    S.refine.WellFormed :=
  refine_wellFormed_from_port_laws all_pair_port_triangles all_root_port_triangles S hs

theorem iterateRefinement_wellFormed (s : State) (n : Nat) :
    (iterateRefinement s n).WellFormed :=
  iterateRefinement_wellFormed_from_port_laws all_pair_port_triangles all_root_port_triangles s n

theorem iterateRefinement_boundary (s : State) (n : Nat) :
    (iterateRefinement s n).boundaryPorts.length ≤ 6*6^n :=
  iterateRefinement_boundary_from_port_laws all_pair_port_triangles all_root_port_triangles s n

/-- An explicit finite iterate contains a root with every port available
through any requested radius. The depth bound uses actual computed boundary. -/
theorem iterateRefinement_deep (s : State) (R : Nat) :
    ∃ root : (iterateRefinement s (6*(7^R*6))).Cell,
      (iterateRefinement s (6*(7^R*6))).Deep R root :=
  growing_systems_have_deep_roots (iterateRefinement s) 6 R
    (iterateRefinement_wellFormed s) (iterateRefinement_area s) (iterateRefinement_boundary s)

/-- The nine-type literal substitution has a globally legal axial marked
field. This is a discrete field-existence theorem, not a physical realization. -/
theorem exists_globallyLegal_from_literal_substitution :
    ∃ f : Position → State, GloballyLegal f :=
  exists_globallyLegal_from_port_laws all_pair_port_triangles all_root_port_triangles

end SpectreFinite.HexSearch.PartialMarkedHexSystem
