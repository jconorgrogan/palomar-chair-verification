module

public import SpectreFinite.ParentBoundaryFrames
public import SpectreFinite.NativeCoarseNeighbors

@[expose] public section


/-! Forward substitution seams for every pair of complementary parent
labels, independently of the existence of any global parent field. These
finite data prove exact boundary-side mating, not global substitution
nonoverlap, interior vertex consistency or infinite field existence. -/
namespace SpectreFinite.HexSearch.ForwardSubstitution
open ParentOwnership ParentBoundary NativeCoarse Boundary

def seamTurn (s t : Fin 6) : Fin 6 := rotateTurn (opposite s) (inverseTurn t)

def seamAnchor (k l : TileKind) (s t : Fin 6) : Position :=
  let e := (segment k s).reverse.getD 0 ⟨0,0⟩
  let c := hexAt (children l) (firstSide l t)
  subPos (outsideCell k e) (rotatePosition (seamTurn s t) (pos c))

def SeamCertificate (k l : TileKind) (s t : Fin 6) : Prop :=
  macroLabel k s = -macroLabel l t →
    placedSegment l (seamAnchor k l s t) (seamTurn s t) t =
      matingSegment (placedSegment k (0,0) 0 s)
instance (k l : TileKind) (s t : Fin 6) : Decidable (SeamCertificate k l s t) :=
  inferInstanceAs (Decidable (_ → _))

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem all_forward_seams : ∀ k l : TileKind, ∀ s t : Fin 6, SeamCertificate k l s t := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (fun i => Fin.elim0 i)))))))))

theorem seamTurn_opposite (s t : Fin 6) : rotateTurn (seamTurn s t) t = opposite s := by
  revert s t
  decide

end SpectreFinite.HexSearch.ForwardSubstitution
