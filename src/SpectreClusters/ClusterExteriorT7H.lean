module

public import SpectreClusters.ClusterExteriorCore

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem t7h_allEdges_eq : shapeEdges (clusterCells .t7h) = clusterAllEdges .t7h := rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part0 : clusterFilter .t7h t7hAllEdgesPart0 = [] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part1 : clusterFilter .t7h t7hAllEdgesPart1 = [] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part2 : clusterFilter .t7h t7hAllEdgesPart2 = [((6, -3), (6, -2)), ((6, -2), (5, -1)), ((6, 0), (5, 2)), ((5, 2), (4, 2)), ((5, -1), (6, 0))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part3 : clusterFilter .t7h t7hAllEdgesPart3 = [((4, 2), (3, 3)), ((3, 3), (2, 4)), ((2, 4), (1, 4)), ((0, 6), (-2, 7)), ((-2, 7), (-2, 6)), ((-2, 6), (-1, 5)), ((1, 4), (0, 6))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part4 : clusterFilter .t7h t7hAllEdgesPart4 = [((-1, 5), (-2, 4)), ((-4, 4), (-5, 4)), ((-5, 4), (-4, 2)), ((-4, 2), (-5, 1)), ((-5, 1), (-4, 0))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part5 : clusterFilter .t7h t7hAllEdgesPart5 = [((-2, 4), (-4, 5)), ((-4, 5), (-4, 4)), ((-4, 0), (-4, -1))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part6 : clusterFilter .t7h t7hAllEdgesPart6 = [((-4, -1), (-4, -2)), ((-4, -2), (-3, -3)), ((-4, -4), (-3, -6)), ((-3, -6), (-2, -6)), ((-3, -3), (-4, -4))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part7 : clusterFilter .t7h t7hAllEdgesPart7 = [((4, -8), (6, -9)), ((6, -9), (6, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part8 : clusterFilter .t7h t7hAllEdgesPart8 = [((-2, -6), (-1, -7)), ((-1, -7), (0, -8)), ((0, -8), (1, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part9 : clusterFilter .t7h t7hAllEdgesPart9 = [((2, -10), (4, -11)), ((4, -11), (4, -10)), ((4, -10), (3, -9)), ((1, -8), (2, -10)), ((3, -9), (4, -8)), ((6, -8), (7, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_filter_part10 : clusterFilter .t7h t7hAllEdgesPart10 = [((7, -8), (8, -8)), ((8, -8), (8, -7)), ((10, -8), (11, -7)), ((11, -7), (10, -6)), ((10, -6), (9, -6)), ((8, -7), (10, -8)), ((8, -4), (6, -3)), ((9, -6), (8, -4))] := by rfl
set_option maxRecDepth 100000 in
theorem t7h_exterior_eq : exteriorEdges (clusterCells .t7h) = clusterExterior .t7h := by
  rw [exteriorEdges_fast,t7h_allEdges_eq]
  change clusterFilter .t7h (t7hAllEdgesPart0 ++ t7hAllEdgesPart1 ++ t7hAllEdgesPart2 ++ t7hAllEdgesPart3 ++ t7hAllEdgesPart4 ++ t7hAllEdgesPart5 ++ t7hAllEdgesPart6 ++ t7hAllEdgesPart7 ++ t7hAllEdgesPart8 ++ t7hAllEdgesPart9 ++ t7hAllEdgesPart10) = clusterExterior .t7h
  simp only [clusterFilter_append,t7h_filter_part0, t7h_filter_part1, t7h_filter_part2, t7h_filter_part3, t7h_filter_part4, t7h_filter_part5, t7h_filter_part6, t7h_filter_part7, t7h_filter_part8, t7h_filter_part9, t7h_filter_part10]
  rfl
end SpectreClusters
