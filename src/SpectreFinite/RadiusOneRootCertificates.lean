module

public import SpectreFinite.RadiusOneSearch

@[expose] public section

/-! Generic per-tail certificate interface, independent of all concrete roots. -/
namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def extendRoot (root : State) (p : Position) (tail : List (Position × State)) :
    List (List (Position × State)) :=
  (choices root p).flatMap (fun a =>
    if Search.compatibleWith Matches (p,a) tail then [(p,a) :: tail] else [])

theorem enumerate_consRoot (root : State) (p : Position) (ps : List Position) :
    Search.enumerate (choices root) Matches (p :: ps) =
      (Search.enumerate (choices root) Matches ps).flatMap (extendRoot root p) := rfl
#print axioms enumerate_consRoot
end SpectreFinite.HexSearch.RadiusOne
