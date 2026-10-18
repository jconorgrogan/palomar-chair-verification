module

public import SpectreGeometry.ReverseLocalStarGeometrySideBinding0
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding1
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding2
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding3
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding4
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding5
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding6
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding7
public import SpectreGeometry.ReverseLocalStarGeometrySideBinding8
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding0
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding1
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding2
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding3
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding4
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding5
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding6
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding7
public import SpectreGeometry.ReverseLocalStarGeometryTripleBinding8

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
set_option maxRecDepth 100000
theorem all_side_geometry_bindings_0 : ∀ d : Fin 6, SideGeometryBinding 0 d := by
  exact Fin.cases side_geometry_binding_0_0 (Fin.cases side_geometry_binding_0_1 (Fin.cases side_geometry_binding_0_2 (Fin.cases side_geometry_binding_0_3 (Fin.cases side_geometry_binding_0_4 (Fin.cases side_geometry_binding_0_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_1 : ∀ d : Fin 6, SideGeometryBinding 1 d := by
  exact Fin.cases side_geometry_binding_1_0 (Fin.cases side_geometry_binding_1_1 (Fin.cases side_geometry_binding_1_2 (Fin.cases side_geometry_binding_1_3 (Fin.cases side_geometry_binding_1_4 (Fin.cases side_geometry_binding_1_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_2 : ∀ d : Fin 6, SideGeometryBinding 2 d := by
  exact Fin.cases side_geometry_binding_2_0 (Fin.cases side_geometry_binding_2_1 (Fin.cases side_geometry_binding_2_2 (Fin.cases side_geometry_binding_2_3 (Fin.cases side_geometry_binding_2_4 (Fin.cases side_geometry_binding_2_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_3 : ∀ d : Fin 6, SideGeometryBinding 3 d := by
  exact Fin.cases side_geometry_binding_3_0 (Fin.cases side_geometry_binding_3_1 (Fin.cases side_geometry_binding_3_2 (Fin.cases side_geometry_binding_3_3 (Fin.cases side_geometry_binding_3_4 (Fin.cases side_geometry_binding_3_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_4 : ∀ d : Fin 6, SideGeometryBinding 4 d := by
  exact Fin.cases side_geometry_binding_4_0 (Fin.cases side_geometry_binding_4_1 (Fin.cases side_geometry_binding_4_2 (Fin.cases side_geometry_binding_4_3 (Fin.cases side_geometry_binding_4_4 (Fin.cases side_geometry_binding_4_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_5 : ∀ d : Fin 6, SideGeometryBinding 5 d := by
  exact Fin.cases side_geometry_binding_5_0 (Fin.cases side_geometry_binding_5_1 (Fin.cases side_geometry_binding_5_2 (Fin.cases side_geometry_binding_5_3 (Fin.cases side_geometry_binding_5_4 (Fin.cases side_geometry_binding_5_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_6 : ∀ d : Fin 6, SideGeometryBinding 6 d := by
  exact Fin.cases side_geometry_binding_6_0 (Fin.cases side_geometry_binding_6_1 (Fin.cases side_geometry_binding_6_2 (Fin.cases side_geometry_binding_6_3 (Fin.cases side_geometry_binding_6_4 (Fin.cases side_geometry_binding_6_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_7 : ∀ d : Fin 6, SideGeometryBinding 7 d := by
  exact Fin.cases side_geometry_binding_7_0 (Fin.cases side_geometry_binding_7_1 (Fin.cases side_geometry_binding_7_2 (Fin.cases side_geometry_binding_7_3 (Fin.cases side_geometry_binding_7_4 (Fin.cases side_geometry_binding_7_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings_8 : ∀ d : Fin 6, SideGeometryBinding 8 d := by
  exact Fin.cases side_geometry_binding_8_0 (Fin.cases side_geometry_binding_8_1 (Fin.cases side_geometry_binding_8_2 (Fin.cases side_geometry_binding_8_3 (Fin.cases side_geometry_binding_8_4 (Fin.cases side_geometry_binding_8_5 ((fun i => Fin.elim0 i)))))))
theorem all_side_geometry_bindings : ∀ k d, SideGeometryBinding k d := by
  exact Fin.cases all_side_geometry_bindings_0 (Fin.cases all_side_geometry_bindings_1 (Fin.cases all_side_geometry_bindings_2 (Fin.cases all_side_geometry_bindings_3 (Fin.cases all_side_geometry_bindings_4 (Fin.cases all_side_geometry_bindings_5 (Fin.cases all_side_geometry_bindings_6 (Fin.cases all_side_geometry_bindings_7 (Fin.cases all_side_geometry_bindings_8 ((fun i => Fin.elim0 i))))))))))
theorem all_triple_geometry_bindings_0 : ∀ d : Fin 6, TripleGeometryBinding 0 d := by
  exact Fin.cases triple_geometry_binding_0_0 (Fin.cases triple_geometry_binding_0_1 (Fin.cases triple_geometry_binding_0_2 (Fin.cases triple_geometry_binding_0_3 (Fin.cases triple_geometry_binding_0_4 (Fin.cases triple_geometry_binding_0_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_1 : ∀ d : Fin 6, TripleGeometryBinding 1 d := by
  exact Fin.cases triple_geometry_binding_1_0 (Fin.cases triple_geometry_binding_1_1 (Fin.cases triple_geometry_binding_1_2 (Fin.cases triple_geometry_binding_1_3 (Fin.cases triple_geometry_binding_1_4 (Fin.cases triple_geometry_binding_1_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_2 : ∀ d : Fin 6, TripleGeometryBinding 2 d := by
  exact Fin.cases triple_geometry_binding_2_0 (Fin.cases triple_geometry_binding_2_1 (Fin.cases triple_geometry_binding_2_2 (Fin.cases triple_geometry_binding_2_3 (Fin.cases triple_geometry_binding_2_4 (Fin.cases triple_geometry_binding_2_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_3 : ∀ d : Fin 6, TripleGeometryBinding 3 d := by
  exact Fin.cases triple_geometry_binding_3_0 (Fin.cases triple_geometry_binding_3_1 (Fin.cases triple_geometry_binding_3_2 (Fin.cases triple_geometry_binding_3_3 (Fin.cases triple_geometry_binding_3_4 (Fin.cases triple_geometry_binding_3_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_4 : ∀ d : Fin 6, TripleGeometryBinding 4 d := by
  exact Fin.cases triple_geometry_binding_4_0 (Fin.cases triple_geometry_binding_4_1 (Fin.cases triple_geometry_binding_4_2 (Fin.cases triple_geometry_binding_4_3 (Fin.cases triple_geometry_binding_4_4 (Fin.cases triple_geometry_binding_4_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_5 : ∀ d : Fin 6, TripleGeometryBinding 5 d := by
  exact Fin.cases triple_geometry_binding_5_0 (Fin.cases triple_geometry_binding_5_1 (Fin.cases triple_geometry_binding_5_2 (Fin.cases triple_geometry_binding_5_3 (Fin.cases triple_geometry_binding_5_4 (Fin.cases triple_geometry_binding_5_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_6 : ∀ d : Fin 6, TripleGeometryBinding 6 d := by
  exact Fin.cases triple_geometry_binding_6_0 (Fin.cases triple_geometry_binding_6_1 (Fin.cases triple_geometry_binding_6_2 (Fin.cases triple_geometry_binding_6_3 (Fin.cases triple_geometry_binding_6_4 (Fin.cases triple_geometry_binding_6_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_7 : ∀ d : Fin 6, TripleGeometryBinding 7 d := by
  exact Fin.cases triple_geometry_binding_7_0 (Fin.cases triple_geometry_binding_7_1 (Fin.cases triple_geometry_binding_7_2 (Fin.cases triple_geometry_binding_7_3 (Fin.cases triple_geometry_binding_7_4 (Fin.cases triple_geometry_binding_7_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings_8 : ∀ d : Fin 6, TripleGeometryBinding 8 d := by
  exact Fin.cases triple_geometry_binding_8_0 (Fin.cases triple_geometry_binding_8_1 (Fin.cases triple_geometry_binding_8_2 (Fin.cases triple_geometry_binding_8_3 (Fin.cases triple_geometry_binding_8_4 (Fin.cases triple_geometry_binding_8_5 ((fun i => Fin.elim0 i)))))))
theorem all_triple_geometry_bindings : ∀ k d, TripleGeometryBinding k d := by
  exact Fin.cases all_triple_geometry_bindings_0 (Fin.cases all_triple_geometry_bindings_1 (Fin.cases all_triple_geometry_bindings_2 (Fin.cases all_triple_geometry_bindings_3 (Fin.cases all_triple_geometry_bindings_4 (Fin.cases all_triple_geometry_bindings_5 (Fin.cases all_triple_geometry_bindings_6 (Fin.cases all_triple_geometry_bindings_7 (Fin.cases all_triple_geometry_bindings_8 ((fun i => Fin.elim0 i))))))))))
end SpectreGeometry.ReverseLocalStarOccurrences
