module

public import SpectreClusters.ClusterExteriorCore

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem t6h_allEdges_eq : shapeEdges (clusterCells .t6h) = clusterAllEdges .t6h := rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part0 : clusterFilter .t6h t6hAllEdgesPart0 = [] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part1 : clusterFilter .t6h t6hAllEdgesPart1 = [] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part2 : clusterFilter .t6h t6hAllEdgesPart2 = [((6, -3), (6, -2)), ((6, -2), (5, -1)), ((6, 0), (5, 2)), ((5, 2), (4, 2)), ((5, -1), (6, 0))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part3 : clusterFilter .t6h t6hAllEdgesPart3 = [((4, 2), (3, 3)), ((3, 3), (2, 4)), ((2, 4), (1, 4)), ((0, 6), (-2, 7)), ((-2, 7), (-2, 6)), ((-2, 6), (-1, 5)), ((1, 4), (0, 6))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part4 : clusterFilter .t6h t6hAllEdgesPart4 = [((-1, 5), (-2, 4)), ((-4, 4), (-5, 4)), ((-5, 4), (-4, 2)), ((-4, 2), (-5, 1)), ((-5, 1), (-4, 0))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part5 : clusterFilter .t6h t6hAllEdgesPart5 = [((-2, 4), (-4, 5)), ((-4, 5), (-4, 4)), ((-4, 0), (-4, -1))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part6 : clusterFilter .t6h t6hAllEdgesPart6 = [((-4, -1), (-4, -2)), ((-4, -2), (-3, -3)), ((-4, -4), (-3, -6)), ((-3, -6), (-2, -6)), ((-2, -6), (-2, -5)), ((-3, -3), (-4, -4)), ((0, -6), (1, -5)), ((-2, -5), (0, -6))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part7 : clusterFilter .t6h t6hAllEdgesPart7 = [((1, -5), (2, -6)), ((2, -6), (3, -6)), ((4, -8), (6, -9)), ((6, -9), (6, -8)), ((3, -6), (4, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part8 : clusterFilter .t6h t6hAllEdgesPart8 = [((6, -8), (7, -8)), ((7, -8), (8, -8)), ((8, -8), (8, -7))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_filter_part9 : clusterFilter .t6h t6hAllEdgesPart9 = [((10, -8), (11, -7)), ((11, -7), (10, -6)), ((10, -6), (9, -6)), ((8, -7), (10, -8)), ((8, -4), (6, -3)), ((9, -6), (8, -4))] := by rfl
set_option maxRecDepth 100000 in
theorem t6h_exterior_eq : exteriorEdges (clusterCells .t6h) = clusterExterior .t6h := by
  rw [exteriorEdges_fast,t6h_allEdges_eq]
  change clusterFilter .t6h (t6hAllEdgesPart0 ++ t6hAllEdgesPart1 ++ t6hAllEdgesPart2 ++ t6hAllEdgesPart3 ++ t6hAllEdgesPart4 ++ t6hAllEdgesPart5 ++ t6hAllEdgesPart6 ++ t6hAllEdgesPart7 ++ t6hAllEdgesPart8 ++ t6hAllEdgesPart9) = clusterExterior .t6h
  simp only [clusterFilter_append,t6h_filter_part0, t6h_filter_part1, t6h_filter_part2, t6h_filter_part3, t6h_filter_part4, t6h_filter_part5, t6h_filter_part6, t6h_filter_part7, t6h_filter_part8, t6h_filter_part9]
  rfl
end SpectreClusters
