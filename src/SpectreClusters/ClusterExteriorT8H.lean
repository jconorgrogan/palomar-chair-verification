module

public import SpectreClusters.ClusterExteriorCore

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem t8h_allEdges_eq : shapeEdges (clusterCells .t8h) = clusterAllEdges .t8h := rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part0 : clusterFilter .t8h t8hAllEdgesPart0 = [] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part1 : clusterFilter .t8h t8hAllEdgesPart1 = [] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part2 : clusterFilter .t8h t8hAllEdgesPart2 = [((6, 0), (5, 2)), ((5, 2), (4, 2))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part3 : clusterFilter .t8h t8hAllEdgesPart3 = [((4, 2), (3, 3)), ((3, 3), (2, 4)), ((2, 4), (1, 4)), ((0, 6), (-2, 7)), ((-2, 7), (-2, 6)), ((-2, 6), (-1, 5)), ((1, 4), (0, 6))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part4 : clusterFilter .t8h t8hAllEdgesPart4 = [((-1, 5), (-2, 4)), ((-4, 4), (-5, 4)), ((-5, 4), (-4, 2)), ((-4, 2), (-5, 1)), ((-5, 1), (-4, 0))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part5 : clusterFilter .t8h t8hAllEdgesPart5 = [((-2, 4), (-4, 5)), ((-4, 5), (-4, 4)), ((-4, 0), (-4, -1))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part6 : clusterFilter .t8h t8hAllEdgesPart6 = [((-4, -1), (-4, -2)), ((-4, -2), (-3, -3)), ((-4, -4), (-3, -6)), ((-3, -6), (-2, -6)), ((-3, -3), (-4, -4))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part7 : clusterFilter .t8h t8hAllEdgesPart7 = [((4, -8), (6, -9)), ((6, -9), (6, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part8 : clusterFilter .t8h t8hAllEdgesPart8 = [((-2, -6), (-1, -7)), ((-1, -7), (0, -8)), ((0, -8), (1, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part9 : clusterFilter .t8h t8hAllEdgesPart9 = [((2, -10), (4, -11)), ((4, -11), (4, -10)), ((4, -10), (3, -9)), ((1, -8), (2, -10)), ((3, -9), (4, -8)), ((6, -8), (7, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part10 : clusterFilter .t8h t8hAllEdgesPart10 = [((7, -8), (8, -8)), ((8, -8), (8, -7)), ((10, -8), (11, -7)), ((11, -7), (10, -6)), ((8, -7), (10, -8))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part11 : clusterFilter .t8h t8hAllEdgesPart11 = [((10, -6), (10, -5)), ((10, -5), (10, -4)), ((10, -4), (9, -3)), ((10, -2), (9, 0)), ((9, 0), (8, 0)), ((8, 0), (8, -1)), ((9, -3), (10, -2))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_filter_part12 : clusterFilter .t8h t8hAllEdgesPart12 = [((8, -1), (6, 0))] := by rfl
set_option maxRecDepth 100000 in
theorem t8h_exterior_eq : exteriorEdges (clusterCells .t8h) = clusterExterior .t8h := by
  rw [exteriorEdges_fast,t8h_allEdges_eq]
  change clusterFilter .t8h (t8hAllEdgesPart0 ++ t8hAllEdgesPart1 ++ t8hAllEdgesPart2 ++ t8hAllEdgesPart3 ++ t8hAllEdgesPart4 ++ t8hAllEdgesPart5 ++ t8hAllEdgesPart6 ++ t8hAllEdgesPart7 ++ t8hAllEdgesPart8 ++ t8hAllEdgesPart9 ++ t8hAllEdgesPart10 ++ t8hAllEdgesPart11 ++ t8hAllEdgesPart12) = clusterExterior .t8h
  simp only [clusterFilter_append,t8h_filter_part0, t8h_filter_part1, t8h_filter_part2, t8h_filter_part3, t8h_filter_part4, t8h_filter_part5, t8h_filter_part6, t8h_filter_part7, t8h_filter_part8, t8h_filter_part9, t8h_filter_part10, t8h_filter_part11, t8h_filter_part12]
  rfl
end SpectreClusters
