module

public import SpectreClusters.BodyBSPData

@[expose] public section

namespace SpectreClusters.BodyBSP
open SpectreGeometry.HalfplaneCertificate
set_option maxRecDepth 100000
def turtleReverse0 : CoverTree := (.split (3,2,6) (.leaf 9 [⟨1,[(2,4),(3,1),(4,2)]⟩,⟨1,[(5,1)]⟩,⟨2,[(0,1),(1,1)]⟩]) (.split (1,1,3) (.leaf 8 [⟨1,[(5,1)]⟩,⟨1,[(1,1),(3,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 7 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩])))
theorem turtleReverse0_checked : checkTree
    (((kiteFacets .turtle).getD 0 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse0 = true := by rfl
def turtleReverse1 : CoverTree := (.split (1,0,2) (.split (1,2,3) (.split (3,2,6) (.leaf 9 [⟨1,[(1,3),(2,2)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,1),(4,1),(5,1)]⟩]) (.leaf 8 [⟨1,[(7,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(2,1),(6,1)]⟩])) (.split (1,1,3) (.split (3,2,6) (.leaf 9 [⟨1,[(1,3),(2,2)]⟩,⟨1,[(8,1)]⟩,⟨1,[(0,1),(4,1),(5,1)]⟩]) (.leaf 8 [⟨1,[(8,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(7,1)]⟩])) (.leaf 7 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩]))) (.split (1,1,3) (.leaf 8 [⟨1,[(1,2),(5,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 7 [⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩])))
theorem turtleReverse1_checked : checkTree
    (((kiteFacets .turtle).getD 1 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse1 = true := by rfl
def turtleReverse2 : CoverTree := (.split (0,1,0) (.split (2,1,-3) (.leaf 0 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩]) (.leaf 1 [⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩])) (.split (1,1,-1) (.split (2,1,-3) (.leaf 0 [⟨1,[(7,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩]) (.leaf 1 [⟨1,[(0,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩])) (.leaf 1 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(6,3)]⟩,⟨1,[(3,1)]⟩])))
theorem turtleReverse2_checked : checkTree
    (((kiteFacets .turtle).getD 2 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse2 = true := by rfl
def turtleReverse3 : CoverTree := (.split (0,1,0) (.leaf 11 [⟨1,[(1,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1)]⟩]) (.split (3,5,6) (.leaf 10 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1),(5,2)]⟩]) (.leaf 9 [⟨1,[(6,1)]⟩,⟨1,[(1,1),(2,2)]⟩,⟨1,[(1,1),(3,1),(4,1)]⟩])))
theorem turtleReverse3_checked : checkTree
    (((kiteFacets .turtle).getD 3 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse3 = true := by rfl
def turtleReverse4 : CoverTree := (.split (3,5,6) (.leaf 10 [⟨3,[(0,2),(3,1)]⟩,⟨1,[(5,1)]⟩,⟨3,[(0,1),(3,2)]⟩]) (.leaf 9 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(1,5),(4,2)]⟩,⟨1,[(2,1),(4,1)]⟩]))
theorem turtleReverse4_checked : checkTree
    (((kiteFacets .turtle).getD 4 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse4 = true := by rfl
def turtleReverse5 : CoverTree := (.split (1,1,0) (.leaf 5 [⟨1,[(5,1)]⟩,⟨2,[(2,3),(3,1)]⟩,⟨1,[(3,1)]⟩]) (.split (3,5,6) (.leaf 10 [⟨1,[(0,1),(5,2)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 9 [⟨1,[(6,1)]⟩,⟨1,[(0,2),(2,1),(4,4)]⟩,⟨1,[(1,1),(4,1)]⟩])))
theorem turtleReverse5_checked : checkTree
    (((kiteFacets .turtle).getD 5 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse5 = true := by rfl
def turtleReverse6 : CoverTree := (.split (-1,0,2) (.split (1,2,3) (.split (3,5,6) (.leaf 10 [⟨1,[(2,1),(4,2)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,1)]⟩]) (.leaf 9 [⟨1,[(7,1)]⟩,⟨1,[(2,4),(4,5),(6,3)]⟩,⟨1,[(1,1),(6,1)]⟩])) (.split (0,1,3) (.leaf 9 [⟨1,[(1,1),(6,2)]⟩,⟨1,[(3,2),(4,4),(5,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 6 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩]))) (.split (0,1,3) (.split (1,2,3) (.split (3,5,6) (.leaf 10 [⟨1,[(2,1),(4,2)]⟩,⟨1,[(8,1)]⟩,⟨1,[(1,1)]⟩]) (.leaf 9 [⟨1,[(8,1)]⟩,⟨1,[(0,2),(4,4),(5,5)]⟩,⟨1,[(6,1)]⟩])) (.leaf 9 [⟨1,[(1,1),(7,2)]⟩,⟨1,[(0,2),(4,4),(5,5)]⟩,⟨1,[(6,1)]⟩])) (.leaf 6 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩])))
theorem turtleReverse6_checked : checkTree
    (((kiteFacets .turtle).getD 6 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse6 = true := by rfl
def turtleReverse7 : CoverTree := (.split (0,1,3) (.leaf 9 [⟨2,[(0,3),(1,7),(4,2)]⟩,⟨1,[(2,2),(3,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 6 [⟨1,[(5,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩]))
theorem turtleReverse7_checked : checkTree
    (((kiteFacets .turtle).getD 7 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse7 = true := by rfl
def turtleReverse8 : CoverTree := (.split (1,1,-1) (.leaf 2 [⟨1,[(5,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩]) (.split (2,1,-3) (.leaf 4 [⟨1,[(6,1)]⟩,⟨1,[(3,1),(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 5 [⟨1,[(2,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1)]⟩])))
theorem turtleReverse8_checked : checkTree
    (((kiteFacets .turtle).getD 8 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse8 = true := by rfl
def turtleReverse9 : CoverTree := (.split (1,1,-1) (.leaf 2 [⟨1,[(5,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩]) (.split (1,2,3) (.leaf 4 [⟨1,[(0,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 3 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩])))
theorem turtleReverse9_checked : checkTree
    (((kiteFacets .turtle).getD 9 []) ++ [unitFacet])
    (targetFacets .turtle) turtleReverse9 = true := by rfl
def turtleReverseTrees : List CoverTree := [turtleReverse0,turtleReverse1,turtleReverse2,turtleReverse3,turtleReverse4,turtleReverse5,turtleReverse6,turtleReverse7,turtleReverse8,turtleReverse9]
theorem turtleReverse_checked : ∀ i : Fin 10, checkTree
    (((kiteFacets .turtle).getD i.val []) ++ [unitFacet])
    (targetFacets .turtle) (turtleReverseTrees.getD i.val (.empty [])) = true := by decide
end SpectreClusters.BodyBSP
