module

public import SpectreClusters.BodyBSPData

@[expose] public section

namespace SpectreClusters.BodyBSP
open SpectreGeometry.HalfplaneCertificate
set_option maxRecDepth 100000
def hatReverse0 : CoverTree := (.split (0,1,0) (.leaf 11 [⟨1,[(3,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,1)]⟩]) (.split (2,1,-3) (.split (2,-1,-4) (.leaf 5 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(4,3)]⟩,⟨1,[(1,2),(2,1)]⟩]) (.leaf 10 [⟨1,[(5,1)]⟩,⟨1,[(4,3),(6,1)]⟩,⟨1,[(7,1)]⟩])) (.split (2,-1,-4) (.leaf 5 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(4,3)]⟩,⟨1,[(1,2),(2,1)]⟩]) (.leaf 10 [⟨1,[(5,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(7,1)]⟩]))))
theorem hatReverse0_checked : checkTree
    (((kiteFacets .hat).getD 0 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse0 = true := by rfl
def hatReverse1 : CoverTree := (.split (0,1,0) (.split (1,1,1) (.leaf 8 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(6,3)]⟩]) (.split (2,1,3) (.leaf 8 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 7 [⟨1,[(7,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩]))) (.split (2,1,3) (.leaf 8 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 7 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩])))
theorem hatReverse1_checked : checkTree
    (((kiteFacets .hat).getD 1 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse1 = true := by rfl
def hatReverse2 : CoverTree := (.split (1,1,1) (.leaf 9 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(2,1),(5,1)]⟩]) (.split (1,2,3) (.leaf 9 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 6 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩])))
theorem hatReverse2_checked : checkTree
    (((kiteFacets .hat).getD 2 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse2 = true := by rfl
def hatReverse3 : CoverTree := (.split (-1,-1,0) (.split (2,-1,-4) (.leaf 5 [⟨1,[(6,1)]⟩,⟨2,[(0,1),(1,3)]⟩,⟨1,[(1,2),(4,2),(5,3)]⟩]) (.leaf 10 [⟨1,[(0,1),(5,2)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩])) (.split (2,-1,-4) (.leaf 5 [⟨1,[(6,1)]⟩,⟨1,[(1,1),(4,1),(5,1)]⟩,⟨1,[(2,5),(6,1)]⟩]) (.leaf 10 [⟨1,[(3,1),(5,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩])))
theorem hatReverse3_checked : checkTree
    (((kiteFacets .hat).getD 3 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse3 = true := by rfl
def hatReverse4 : CoverTree := (.split (3,1,-6) (.split (2,1,-3) (.leaf 2 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(2,1)]⟩]) (.split (1,1,1) (.leaf 4 [⟨1,[(3,1),(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 3 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩]))) (.split (1,1,1) (.leaf 4 [⟨2,[(2,3),(3,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(2,1),(5,1)]⟩]) (.leaf 3 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩])))
theorem hatReverse4_checked : checkTree
    (((kiteFacets .hat).getD 4 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse4 = true := by rfl
def hatReverse5 : CoverTree := (.split (1,1,1) (.split (1,2,3) (.leaf 5 [⟨1,[(2,2),(3,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1),(1,2)]⟩]) (.leaf 4 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1),(6,1)]⟩])) (.leaf 3 [⟨1,[(5,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩]))
theorem hatReverse5_checked : checkTree
    (((kiteFacets .hat).getD 5 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse5 = true := by rfl
def hatReverse6 : CoverTree := (.split (-1,-1,2) (.split (1,0,-3) (.leaf 0 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩]) (.split (3,1,-6) (.leaf 1 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩]) (.leaf 5 [⟨1,[(1,1),(2,2)]⟩,⟨1,[(3,1),(4,3)]⟩,⟨1,[(7,1)]⟩]))) (.split (1,0,-3) (.leaf 0 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩]) (.leaf 1 [⟨1,[(1,2),(5,3)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩])))
theorem hatReverse6_checked : checkTree
    (((kiteFacets .hat).getD 6 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse6 = true := by rfl
def hatReverse7 : CoverTree := (.split (0,1,2) (.split (3,1,-6) (.split (1,0,-3) (.leaf 0 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩]) (.leaf 1 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,1),(2,1)]⟩])) (.leaf 5 [⟨1,[(1,5),(6,1)]⟩,⟨1,[(1,1),(4,1),(5,2)]⟩,⟨1,[(6,1)]⟩])) (.split (1,0,-3) (.leaf 0 [⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩]) (.split (2,1,-3) (.split (3,1,-6) (.leaf 1 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,2),(5,1)]⟩]) (.leaf 5 [⟨1,[(1,2),(4,2),(5,1)]⟩,⟨1,[(2,2),(6,1)]⟩,⟨1,[(8,1)]⟩])) (.leaf 5 [⟨1,[(1,2),(4,2),(5,1)]⟩,⟨1,[(2,2),(6,1)]⟩,⟨1,[(2,1),(7,2)]⟩]))))
theorem hatReverse7_checked : checkTree
    (((kiteFacets .hat).getD 7 []) ++ [unitFacet])
    (targetFacets .hat) hatReverse7 = true := by rfl
def hatReverseTrees : List CoverTree := [hatReverse0,hatReverse1,hatReverse2,hatReverse3,hatReverse4,hatReverse5,hatReverse6,hatReverse7]
theorem hatReverse_checked : ∀ i : Fin 8, checkTree
    (((kiteFacets .hat).getD i.val []) ++ [unitFacet])
    (targetFacets .hat) (hatReverseTrees.getD i.val (.empty [])) = true := by decide
end SpectreClusters.BodyBSP
