module

public import SpectreFinite.RadiusOneSearch

@[expose] public section


/-! Per-extension kernel certificates for raw radius-one compatibility. -/
namespace SpectreFinite.HexSearch.RadiusOne
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def extend (root : State) (p : Position) (tail : List (Position × State)) :
    List (List (Position × State)) :=
  (choices root p).flatMap (fun a =>
    if Search.compatibleWith Matches (p,a) tail then [(p,a) :: tail] else [])

theorem enumerate_cons (root : State) (p : Position) (ps : List Position) :
    Search.enumerate (choices root) Matches (p :: ps) =
      (Search.enumerate (choices root) Matches ps).flatMap (extend root p) := rfl
def gammaStage0 : List (List (Position × State)) := [[((0,0),(0,0))]]
theorem gammaStage0_exact : Search.enumerate (choices (0,0)) Matches [(0,0)] = gammaStage0 := by decide
#print axioms gammaStage0_exact
end SpectreFinite.HexSearch.RadiusOne
