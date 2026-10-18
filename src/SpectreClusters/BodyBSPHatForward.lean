module

public import SpectreClusters.BodyBSPData

@[expose] public section

namespace SpectreClusters.BodyBSP
open SpectreGeometry.HalfplaneCertificate
set_option maxRecDepth 100000
def hatForward0 : CoverTree := (.split (1,2,0) (.leaf 6 [⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 7 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(1,1)]⟩]))
theorem hatForward0_checked : checkTree
    (((targetFacets .hat).getD 0 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward0 = true := by rfl
def hatForward1 : CoverTree := (.split (-1,-1,2) (.split (1,2,0) (.leaf 6 [⟨1,[(1,2),(2,1)]⟩,⟨1,[(2,1)]⟩,⟨2,[(0,1),(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 7 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(4,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(0,1),(1,4)]⟩])) (.leaf 6 [⟨1,[(1,2),(2,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(2,1),(4,1)]⟩,⟨1,[(1,1),(3,1),(4,2)]⟩]))
theorem hatForward1_checked : checkTree
    (((targetFacets .hat).getD 1 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward1 = true := by rfl
def hatForward2 : CoverTree := (.leaf 4 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,3)]⟩])
theorem hatForward2_checked : checkTree
    (((targetFacets .hat).getD 2 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward2 = true := by rfl
def hatForward3 : CoverTree := (.split (1,-1,-6) (.leaf 4 [⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 5 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(1,1)]⟩]))
theorem hatForward3_checked : checkTree
    (((targetFacets .hat).getD 3 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward3 = true := by rfl
def hatForward4 : CoverTree := (.split (1,-1,-6) (.leaf 4 [⟨1,[(1,3),(2,1)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨3,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 5 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(2,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(0,1),(1,3)]⟩]))
theorem hatForward4_checked : checkTree
    (((targetFacets .hat).getD 4 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward4 = true := by rfl
def hatForward5 : CoverTree := (.split (1,0,-2) (.split (0,1,2) (.split (1,2,0) (.leaf 6 [⟨1,[(2,1),(3,2),(4,1)]⟩,⟨1,[(2,1),(4,3)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 7 [⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨1,[(5,3),(6,1)]⟩])) (.split (1,1,0) (.leaf 7 [⟨3,[(2,1),(3,4),(5,5)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(2,1),(6,2)]⟩]) (.leaf 5 [⟨1,[(1,2),(6,3)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(1,2),(5,3)]⟩]))) (.split (1,1,0) (.split (1,2,0) (.leaf 0 [⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(4,3)]⟩,⟨1,[(0,1),(3,2),(4,1)]⟩]) (.leaf 3 [⟨1,[(5,3),(6,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩])) (.split (0,1,2) (.leaf 3 [⟨1,[(0,1),(6,2)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,1),(3,4),(5,5)]⟩]) (.leaf 5 [⟨1,[(1,2),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,2),(6,3)]⟩]))))
theorem hatForward5_checked : checkTree
    (((targetFacets .hat).getD 5 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward5 = true := by rfl
def hatForward6 : CoverTree := (.leaf 2 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,3)]⟩])
theorem hatForward6_checked : checkTree
    (((targetFacets .hat).getD 6 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward6 = true := by rfl
def hatForward7 : CoverTree := (.leaf 1 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,2),(2,3)]⟩])
theorem hatForward7_checked : checkTree
    (((targetFacets .hat).getD 7 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward7 = true := by rfl
def hatForward8 : CoverTree := (.leaf 1 [⟨1,[(1,1)]⟩,⟨3,[(1,1),(2,2)]⟩,⟨3,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩])
theorem hatForward8_checked : checkTree
    (((targetFacets .hat).getD 8 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward8 = true := by rfl
def hatForward9 : CoverTree := (.leaf 2 [⟨1,[(1,1)]⟩,⟨3,[(1,1),(2,2)]⟩,⟨3,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩])
theorem hatForward9_checked : checkTree
    (((targetFacets .hat).getD 9 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward9 = true := by rfl
def hatForward10 : CoverTree := (.split (1,2,0) (.leaf 0 [⟨1,[(4,1)]⟩,⟨2,[(0,1),(2,1)]⟩,⟨2,[(0,3),(2,1)]⟩,⟨1,[(0,3),(4,1)]⟩]) (.leaf 3 [⟨1,[(1,1)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨2,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩]))
theorem hatForward10_checked : checkTree
    (((targetFacets .hat).getD 10 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward10 = true := by rfl
def hatForward11 : CoverTree := (.leaf 0 [⟨1,[(0,1),(1,3)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,1)]⟩])
theorem hatForward11_checked : checkTree
    (((targetFacets .hat).getD 11 []) ++ [unitFacet])
    (kiteFacets .hat) hatForward11 = true := by rfl
def hatForwardTrees : List CoverTree := [hatForward0,hatForward1,hatForward2,hatForward3,hatForward4,hatForward5,hatForward6,hatForward7,hatForward8,hatForward9,hatForward10,hatForward11]
theorem hatForward_checked : ∀ i : Fin 12, checkTree
    (((targetFacets .hat).getD i.val []) ++ [unitFacet])
    (kiteFacets .hat) (hatForwardTrees.getD i.val (.empty [])) = true := by decide
end SpectreClusters.BodyBSP
