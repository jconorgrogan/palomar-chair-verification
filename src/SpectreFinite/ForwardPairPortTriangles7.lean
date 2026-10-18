module

public import SpectreFinite.ForwardTrianglePortDefinitions

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem pair_port_triangles_7_0_0_4 : PairPortTriangles 7 0 0 4 := by decide

theorem pair_port_triangles_7_0_1_2 : PairPortTriangles 7 1 0 2 := by decide

theorem pair_port_triangles_7_0_6_2 : PairPortTriangles 7 6 0 2 := by decide

theorem all_pair_port_triangles_7_0 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 7 l 0 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_0_0_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_0_1_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_0_6_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_7_1_0_2 : PairPortTriangles 7 0 1 2 := by decide

theorem pair_port_triangles_7_1_1_5 : PairPortTriangles 7 1 1 5 := by decide

theorem pair_port_triangles_7_1_2_3 : PairPortTriangles 7 2 1 3 := by decide

theorem pair_port_triangles_7_1_2_5 : PairPortTriangles 7 2 1 5 := by decide

theorem pair_port_triangles_7_1_3_5 : PairPortTriangles 7 3 1 5 := by decide

theorem pair_port_triangles_7_1_4_3 : PairPortTriangles 7 4 1 3 := by decide

theorem pair_port_triangles_7_1_6_5 : PairPortTriangles 7 6 1 5 := by decide

theorem pair_port_triangles_7_1_7_5 : PairPortTriangles 7 7 1 5 := by decide

theorem all_pair_port_triangles_7_1 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 7 l 1 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_0_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_1_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_2_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_2_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_3_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_4_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_6_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_1_7_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_7_2_2_2 : PairPortTriangles 7 2 2 2 := by decide

theorem pair_port_triangles_7_2_4_2 : PairPortTriangles 7 4 2 2 := by decide

theorem pair_port_triangles_7_2_7_2 : PairPortTriangles 7 7 2 2 := by decide

theorem pair_port_triangles_7_2_8_2 : PairPortTriangles 7 8 2 2 := by decide

theorem all_pair_port_triangles_7_2 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 7 l 2 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_2_2_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_2_4_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_2_7_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_2_8_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_7_3_1_4 : PairPortTriangles 7 1 3 4 := by decide

theorem pair_port_triangles_7_3_3_4 : PairPortTriangles 7 3 3 4 := by decide

theorem pair_port_triangles_7_3_5_4 : PairPortTriangles 7 5 3 4 := by decide

theorem pair_port_triangles_7_3_6_4 : PairPortTriangles 7 6 3 4 := by decide

theorem pair_port_triangles_7_3_7_4 : PairPortTriangles 7 7 3 4 := by decide

theorem pair_port_triangles_7_3_8_4 : PairPortTriangles 7 8 3 4 := by decide

theorem all_pair_port_triangles_7_3 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 7 l 3 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_3_1_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_3_3_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_3_5_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_3_6_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_3_7_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_3_8_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_7_4_4_5 : PairPortTriangles 7 4 4 5 := by decide

theorem pair_port_triangles_7_4_5_5 : PairPortTriangles 7 5 4 5 := by decide

theorem pair_port_triangles_7_4_7_3 : PairPortTriangles 7 7 4 3 := by decide

theorem pair_port_triangles_7_4_8_3 : PairPortTriangles 7 8 4 3 := by decide

theorem pair_port_triangles_7_4_8_5 : PairPortTriangles 7 8 4 5 := by decide

theorem all_pair_port_triangles_7_4 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 7 l 4 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_4_4_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_4_5_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_4_7_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_4_8_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_4_8_5) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_7_5_0_1 : PairPortTriangles 7 0 5 1 := by decide

theorem pair_port_triangles_7_5_2_1 : PairPortTriangles 7 2 5 1 := by decide

theorem pair_port_triangles_7_5_3_1 : PairPortTriangles 7 3 5 1 := by decide

theorem pair_port_triangles_7_5_4_1 : PairPortTriangles 7 4 5 1 := by decide

theorem pair_port_triangles_7_5_5_1 : PairPortTriangles 7 5 5 1 := by decide

theorem pair_port_triangles_7_5_7_1 : PairPortTriangles 7 7 5 1 := by decide

theorem pair_port_triangles_7_5_8_1 : PairPortTriangles 7 8 5 1 := by decide

theorem all_pair_port_triangles_7_5 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 7 l 5 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_5_0_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_5_2_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_5_3_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_5_4_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_5_5_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_5_7_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_7_5_8_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

end SpectreFinite.HexSearch.ForwardSubstitution
