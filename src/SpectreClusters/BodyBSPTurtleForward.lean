module

public import SpectreClusters.BodyBSPData

@[expose] public section

namespace SpectreClusters.BodyBSP
open SpectreGeometry.HalfplaneCertificate
set_option maxRecDepth 100000
def turtleForward0 : CoverTree := (.leaf 2 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,3)]⟩])
theorem turtleForward0_checked : checkTree
    (((targetFacets .turtle).getD 0 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward0 = true := by rfl
def turtleForward1 : CoverTree := (.leaf 2 [⟨1,[(0,1)]⟩,⟨3,[(0,1),(1,2)]⟩,⟨3,[(1,2),(2,1)]⟩,⟨1,[(2,1)]⟩])
theorem turtleForward1_checked : checkTree
    (((targetFacets .turtle).getD 1 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward1 = true := by rfl
def turtleForward2 : CoverTree := (.split (1,-1,-6) (.leaf 9 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(1,1)]⟩]) (.leaf 8 [⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(4,1)]⟩]))
theorem turtleForward2_checked : checkTree
    (((targetFacets .turtle).getD 2 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward2 = true := by rfl
def turtleForward3 : CoverTree := (.leaf 9 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,3)]⟩])
theorem turtleForward3_checked : checkTree
    (((targetFacets .turtle).getD 3 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward3 = true := by rfl
def turtleForward4 : CoverTree := (.split (1,-1,-6) (.leaf 9 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨1,[(1,1),(2,3)]⟩]) (.leaf 8 [⟨1,[(0,1),(2,3)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]))
theorem turtleForward4_checked : checkTree
    (((targetFacets .turtle).getD 4 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward4 = true := by rfl
def turtleForward5 : CoverTree := (.split (1,0,-2) (.leaf 8 [⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,3),(1,2)]⟩]) (.leaf 5 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,1),(4,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩]))
theorem turtleForward5_checked : checkTree
    (((targetFacets .turtle).getD 5 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward5 = true := by rfl
def turtleForward6 : CoverTree := (.split (2,1,0) (.leaf 6 [⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 7 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(1,1)]⟩]))
theorem turtleForward6_checked : checkTree
    (((targetFacets .turtle).getD 6 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward6 = true := by rfl
def turtleForward7 : CoverTree := (.split (1,-1,0) (.leaf 0 [⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 1 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(1,1)]⟩]))
theorem turtleForward7_checked : checkTree
    (((targetFacets .turtle).getD 7 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward7 = true := by rfl
def turtleForward8 : CoverTree := (.split (1,0,2) (.split (1,-1,0) (.leaf 0 [⟨1,[(0,1),(2,4)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨2,[(0,1),(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 1 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(4,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(1,1),(2,2)]⟩])) (.leaf 1 [⟨1,[(2,1),(3,1),(4,2)]⟩,⟨1,[(1,1),(4,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(1,1),(2,2)]⟩]))
theorem turtleForward8_checked : checkTree
    (((targetFacets .turtle).getD 8 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward8 = true := by rfl
def turtleForward9 : CoverTree := (.split (0,1,2) (.split (1,1,2) (.split (1,0,0) (.split (2,1,0) (.leaf 5 [⟨1,[(7,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,1),(3,2),(4,5)]⟩,⟨2,[(0,1),(3,4),(5,1)]⟩]) (.leaf 4 [⟨1,[(6,3),(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(7,1)]⟩])) (.split (1,-1,0) (.leaf 4 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,3),(7,1)]⟩]) (.leaf 3 [⟨2,[(0,1),(3,4),(5,1)]⟩,⟨2,[(0,1),(5,5)]⟩,⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩]))) (.split (1,-1,0) (.leaf 0 [⟨1,[(4,3),(6,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 1 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(1,1),(5,3)]⟩,⟨1,[(1,1),(3,2),(5,1)]⟩]))) (.split (2,1,0) (.leaf 6 [⟨3,[(0,1),(2,8)]⟩,⟨3,[(0,1),(2,2)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.split (1,1,2) (.leaf 7 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(2,1),(3,1),(6,1)]⟩]) (.split (1,0,0) (.leaf 7 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(2,2),(7,1)]⟩]) (.leaf 0 [⟨1,[(1,1),(7,2)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨3,[(1,1),(3,4),(4,5)]⟩])))))
theorem turtleForward9_checked : checkTree
    (((targetFacets .turtle).getD 9 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward9 = true := by rfl
def turtleForward10 : CoverTree := (.split (2,1,0) (.split (0,1,2) (.leaf 5 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,1),(5,1)]⟩,⟨1,[(0,1),(2,1)]⟩]) (.leaf 6 [⟨1,[(1,1),(2,4)]⟩,⟨1,[(2,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.split (1,-1,0) (.leaf 4 [⟨1,[(5,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨7,[(1,2),(3,2),(4,3)]⟩,⟨1,[(4,1)]⟩]) (.leaf 3 [⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,5),(1,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨1,[(5,1)]⟩])))
theorem turtleForward10_checked : checkTree
    (((targetFacets .turtle).getD 10 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward10 = true := by rfl
def turtleForward11 : CoverTree := (.leaf 3 [⟨1,[(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(1,3),(2,1)]⟩])
theorem turtleForward11_checked : checkTree
    (((targetFacets .turtle).getD 11 []) ++ [unitFacet])
    (kiteFacets .turtle) turtleForward11 = true := by rfl
def turtleForwardTrees : List CoverTree := [turtleForward0,turtleForward1,turtleForward2,turtleForward3,turtleForward4,turtleForward5,turtleForward6,turtleForward7,turtleForward8,turtleForward9,turtleForward10,turtleForward11]
theorem turtleForward_checked : ∀ i : Fin 12, checkTree
    (((targetFacets .turtle).getD i.val []) ++ [unitFacet])
    (kiteFacets .turtle) (turtleForwardTrees.getD i.val (.empty [])) = true := by decide
end SpectreClusters.BodyBSP
