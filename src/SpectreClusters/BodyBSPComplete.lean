module

public import SpectreClusters.BodyBSPHatForward
public import SpectreClusters.BodyBSPHatReverse
public import SpectreClusters.BodyBSPTurtleForward
public import SpectreClusters.BodyBSPTurtleReverse

@[expose] public section


namespace SpectreClusters.BodyBSP
open SpectreGeometry.HalfplaneCertificate

def forwardTree (kind : HTKind) (i : Fin 12) : CoverTree :=
  (match kind with | .hat => hatForwardTrees | .turtle => turtleForwardTrees).getD i.val (.empty [])

def reverseTree (kind : HTKind) (i : Fin (htCells kind).length) : CoverTree :=
  (match kind with | .hat => hatReverseTrees | .turtle => turtleReverseTrees).getD i.val (.empty [])

theorem forward_checked (kind : HTKind) (i : Fin 12) :
    checkTree (((targetFacets kind).getD i.val []) ++ [unitFacet])
      (kiteFacets kind) (forwardTree kind i) = true := by
  cases kind
  · exact hatForward_checked i
  · exact turtleForward_checked i

theorem reverse_checked (kind : HTKind) (i : Fin (htCells kind).length) :
    checkTree (((kiteFacets kind).getD i.val []) ++ [unitFacet])
      (targetFacets kind) (reverseTree kind i) = true := by
  cases kind
  · exact hatReverse_checked i
  · exact turtleReverse_checked i

end SpectreClusters.BodyBSP
