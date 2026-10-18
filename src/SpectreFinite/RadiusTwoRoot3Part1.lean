module

public import SpectreFinite.RadiusTwoRoot3Part0

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def root3Node5Domains0 : Domains 19 State := restrict root3Node4Domains1 7 (5,3)
theorem root3Node5Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node5Domains0 (.output 2) = true := by decide
def root3Node6Domains0 : Domains 19 State := restrict root3Node4Domains1 7 (8,3)
theorem root3Node6Leaf_checked :
    checkCover 1 constraints root3Outputs root3Node6Domains0 (.output 3) = true := by decide
end SpectreFinite.HexSearch.RadiusTwo
