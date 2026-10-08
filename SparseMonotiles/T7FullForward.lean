module
public import SparseMonotiles.T7FullCrossGroup0
public import SparseMonotiles.T7FullCrossGroup1
public import SparseMonotiles.T7FullCrossGroup2
public import SparseMonotiles.T7FullCrossGroup3
public import SparseMonotiles.T7FullCrossGroup4
public import SparseMonotiles.T7FullCrossGroup5
public import SparseMonotiles.T7FullCrossGroup6
public import SparseMonotiles.T7FullCrossGroup7
public import SparseMonotiles.T7FullCrossGroup8
public import SparseMonotiles.T7FullCrossGroup9
public import SparseMonotiles.T7FullCrossGroup10
public import SparseMonotiles.T7FullCrossGroup11
public import SparseMonotiles.T7FullCrossGroup12
public import SparseMonotiles.T7AllSiblings
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Complete408×128 cross checks, without any remaining finite hypothesis. -/
theorem crosses_checked : CrossChecks (crossRows crossMate) := by
  intro k a
  by_cases h0 : k.val < 32
  · exact cross_checks_group0 k (by omega) h0 a
  by_cases h1 : k.val < 64
  · exact cross_checks_group1 k (by omega) h1 a
  by_cases h2 : k.val < 96
  · exact cross_checks_group2 k (by omega) h2 a
  by_cases h3 : k.val < 128
  · exact cross_checks_group3 k (by omega) h3 a
  by_cases h4 : k.val < 160
  · exact cross_checks_group4 k (by omega) h4 a
  by_cases h5 : k.val < 192
  · exact cross_checks_group5 k (by omega) h5 a
  by_cases h6 : k.val < 224
  · exact cross_checks_group6 k (by omega) h6 a
  by_cases h7 : k.val < 256
  · exact cross_checks_group7 k (by omega) h7 a
  by_cases h8 : k.val < 288
  · exact cross_checks_group8 k (by omega) h8 a
  by_cases h9 : k.val < 320
  · exact cross_checks_group9 k (by omega) h9 a
  by_cases h10 : k.val < 352
  · exact cross_checks_group10 k (by omega) h10 a
  by_cases h11 : k.val < 384
  · exact cross_checks_group11 k (by omega) h11 a
  exact cross_checks_group12 k (by omega) k.isLt a

/-- Full compact T7 forward rules: all sibling and cross-parent cases discharged. -/
theorem forward_rules : ForwardRules children7 M7 :=
  T7AllSiblings.forwardRules_of_cross_checks crossMate crosses_checked

#print axioms crosses_checked
#print axioms forward_rules
end SparseMonotiles.CarrierHierarchy.T7FullForward
