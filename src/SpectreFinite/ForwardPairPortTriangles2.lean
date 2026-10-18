module

public import SpectreFinite.ForwardTrianglePortDefinitions

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem pair_port_triangles_2_0_0_4 : PairPortTriangles 2 0 0 4 := by decide

theorem pair_port_triangles_2_0_1_2 : PairPortTriangles 2 1 0 2 := by decide

theorem pair_port_triangles_2_0_6_2 : PairPortTriangles 2 6 0 2 := by decide

theorem all_pair_port_triangles_2_0 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 2 l 0 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_0_0_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_0_1_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_0_6_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_2_1_0_2 : PairPortTriangles 2 0 1 2 := by decide

theorem pair_port_triangles_2_1_1_5 : PairPortTriangles 2 1 1 5 := by decide

theorem pair_port_triangles_2_1_2_3 : PairPortTriangles 2 2 1 3 := by decide

theorem pair_port_triangles_2_1_2_5 : PairPortTriangles 2 2 1 5 := by decide

theorem pair_port_triangles_2_1_3_5 : PairPortTriangles 2 3 1 5 := by decide

theorem pair_port_triangles_2_1_4_3 : PairPortTriangles 2 4 1 3 := by decide

theorem pair_port_triangles_2_1_6_5 : PairPortTriangles 2 6 1 5 := by decide

theorem pair_port_triangles_2_1_7_5 : PairPortTriangles 2 7 1 5 := by decide

theorem all_pair_port_triangles_2_1 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 2 l 1 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_0_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_1_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_2_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_2_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_3_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_4_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_6_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_1_7_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_2_2_2_2 : PairPortTriangles 2 2 2 2 := by decide

theorem pair_port_triangles_2_2_4_2 : PairPortTriangles 2 4 2 2 := by decide

theorem pair_port_triangles_2_2_7_2 : PairPortTriangles 2 7 2 2 := by decide

theorem pair_port_triangles_2_2_8_2 : PairPortTriangles 2 8 2 2 := by decide

theorem all_pair_port_triangles_2_2 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 2 l 2 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_2_2_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_2_4_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_2_7_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_2_8_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_2_3_0_1 : PairPortTriangles 2 0 3 1 := by decide

theorem pair_port_triangles_2_3_2_1 : PairPortTriangles 2 2 3 1 := by decide

theorem pair_port_triangles_2_3_3_1 : PairPortTriangles 2 3 3 1 := by decide

theorem pair_port_triangles_2_3_4_1 : PairPortTriangles 2 4 3 1 := by decide

theorem pair_port_triangles_2_3_5_1 : PairPortTriangles 2 5 3 1 := by decide

theorem pair_port_triangles_2_3_7_1 : PairPortTriangles 2 7 3 1 := by decide

theorem pair_port_triangles_2_3_8_1 : PairPortTriangles 2 8 3 1 := by decide

theorem all_pair_port_triangles_2_3 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 2 l 3 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_3_0_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_3_2_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_3_3_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_3_4_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_3_5_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_3_7_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_3_8_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_2_4_3_2 : PairPortTriangles 2 3 4 2 := by decide

theorem pair_port_triangles_2_4_5_2 : PairPortTriangles 2 5 4 2 := by decide

theorem all_pair_port_triangles_2_4 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 2 l 4 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_4_3_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_4_5_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_2_5_0_1 : PairPortTriangles 2 0 5 1 := by decide

theorem pair_port_triangles_2_5_2_1 : PairPortTriangles 2 2 5 1 := by decide

theorem pair_port_triangles_2_5_3_1 : PairPortTriangles 2 3 5 1 := by decide

theorem pair_port_triangles_2_5_4_1 : PairPortTriangles 2 4 5 1 := by decide

theorem pair_port_triangles_2_5_5_1 : PairPortTriangles 2 5 5 1 := by decide

theorem pair_port_triangles_2_5_7_1 : PairPortTriangles 2 7 5 1 := by decide

theorem pair_port_triangles_2_5_8_1 : PairPortTriangles 2 8 5 1 := by decide

theorem all_pair_port_triangles_2_5 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 2 l 5 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_5_0_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_5_2_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_5_3_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_5_4_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_5_5_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_5_7_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_2_5_8_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

end SpectreFinite.HexSearch.ForwardSubstitution
