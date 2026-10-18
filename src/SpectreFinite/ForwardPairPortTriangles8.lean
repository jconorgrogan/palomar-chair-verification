module

public import SpectreFinite.ForwardTrianglePortDefinitions

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem pair_port_triangles_8_0_0_5 : PairPortTriangles 8 0 0 5 := by decide

theorem pair_port_triangles_8_0_1_3 : PairPortTriangles 8 1 0 3 := by decide

theorem pair_port_triangles_8_0_3_3 : PairPortTriangles 8 3 0 3 := by decide

theorem pair_port_triangles_8_0_5_3 : PairPortTriangles 8 5 0 3 := by decide

theorem pair_port_triangles_8_0_6_3 : PairPortTriangles 8 6 0 3 := by decide

theorem all_pair_port_triangles_8_0 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 8 l 0 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_0_0_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_0_1_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_0_3_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_0_5_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_0_6_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_8_1_0_2 : PairPortTriangles 8 0 1 2 := by decide

theorem pair_port_triangles_8_1_1_5 : PairPortTriangles 8 1 1 5 := by decide

theorem pair_port_triangles_8_1_2_3 : PairPortTriangles 8 2 1 3 := by decide

theorem pair_port_triangles_8_1_2_5 : PairPortTriangles 8 2 1 5 := by decide

theorem pair_port_triangles_8_1_3_5 : PairPortTriangles 8 3 1 5 := by decide

theorem pair_port_triangles_8_1_4_3 : PairPortTriangles 8 4 1 3 := by decide

theorem pair_port_triangles_8_1_6_5 : PairPortTriangles 8 6 1 5 := by decide

theorem pair_port_triangles_8_1_7_5 : PairPortTriangles 8 7 1 5 := by decide

theorem all_pair_port_triangles_8_1 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 8 l 1 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_0_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_1_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_2_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_2_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_3_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_4_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_6_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_1_7_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_8_2_2_2 : PairPortTriangles 8 2 2 2 := by decide

theorem pair_port_triangles_8_2_4_2 : PairPortTriangles 8 4 2 2 := by decide

theorem pair_port_triangles_8_2_7_2 : PairPortTriangles 8 7 2 2 := by decide

theorem pair_port_triangles_8_2_8_2 : PairPortTriangles 8 8 2 2 := by decide

theorem all_pair_port_triangles_8_2 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 8 l 2 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_2_2_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_2_4_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_2_7_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_2_8_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_8_3_1_4 : PairPortTriangles 8 1 3 4 := by decide

theorem pair_port_triangles_8_3_3_4 : PairPortTriangles 8 3 3 4 := by decide

theorem pair_port_triangles_8_3_5_4 : PairPortTriangles 8 5 3 4 := by decide

theorem pair_port_triangles_8_3_6_4 : PairPortTriangles 8 6 3 4 := by decide

theorem pair_port_triangles_8_3_7_4 : PairPortTriangles 8 7 3 4 := by decide

theorem pair_port_triangles_8_3_8_4 : PairPortTriangles 8 8 3 4 := by decide

theorem all_pair_port_triangles_8_3 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 8 l 3 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_3_1_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_3_3_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_3_5_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_3_6_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_3_7_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_3_8_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_8_4_4_5 : PairPortTriangles 8 4 4 5 := by decide

theorem pair_port_triangles_8_4_5_5 : PairPortTriangles 8 5 4 5 := by decide

theorem pair_port_triangles_8_4_7_3 : PairPortTriangles 8 7 4 3 := by decide

theorem pair_port_triangles_8_4_8_3 : PairPortTriangles 8 8 4 3 := by decide

theorem pair_port_triangles_8_4_8_5 : PairPortTriangles 8 8 4 5 := by decide

theorem all_pair_port_triangles_8_4 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 8 l 4 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_4_4_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_4_5_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_4_7_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_4_8_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_4_8_5) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_8_5_1_4 : PairPortTriangles 8 1 5 4 := by decide

theorem pair_port_triangles_8_5_3_4 : PairPortTriangles 8 3 5 4 := by decide

theorem pair_port_triangles_8_5_5_4 : PairPortTriangles 8 5 5 4 := by decide

theorem pair_port_triangles_8_5_6_4 : PairPortTriangles 8 6 5 4 := by decide

theorem pair_port_triangles_8_5_7_4 : PairPortTriangles 8 7 5 4 := by decide

theorem pair_port_triangles_8_5_8_4 : PairPortTriangles 8 8 5 4 := by decide

theorem all_pair_port_triangles_8_5 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 8 l 5 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_5_1_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_5_3_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_5_5_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_5_6_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_5_7_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_8_5_8_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

end SpectreFinite.HexSearch.ForwardSubstitution
