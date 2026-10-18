module

public import SpectreFinite.ForwardTrianglePortDefinitions

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem pair_port_triangles_3_0_0_4 : PairPortTriangles 3 0 0 4 := by decide

theorem pair_port_triangles_3_0_1_2 : PairPortTriangles 3 1 0 2 := by decide

theorem pair_port_triangles_3_0_6_2 : PairPortTriangles 3 6 0 2 := by decide

theorem all_pair_port_triangles_3_0 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 3 l 0 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_0_0_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_0_1_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_0_6_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_3_1_0_2 : PairPortTriangles 3 0 1 2 := by decide

theorem pair_port_triangles_3_1_1_5 : PairPortTriangles 3 1 1 5 := by decide

theorem pair_port_triangles_3_1_2_3 : PairPortTriangles 3 2 1 3 := by decide

theorem pair_port_triangles_3_1_2_5 : PairPortTriangles 3 2 1 5 := by decide

theorem pair_port_triangles_3_1_3_5 : PairPortTriangles 3 3 1 5 := by decide

theorem pair_port_triangles_3_1_4_3 : PairPortTriangles 3 4 1 3 := by decide

theorem pair_port_triangles_3_1_6_5 : PairPortTriangles 3 6 1 5 := by decide

theorem pair_port_triangles_3_1_7_5 : PairPortTriangles 3 7 1 5 := by decide

theorem all_pair_port_triangles_3_1 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 3 l 1 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_0_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_1_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_2_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_2_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_3_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_4_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_6_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_1_7_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_3_2_2_4 : PairPortTriangles 3 2 2 4 := by decide

theorem pair_port_triangles_3_2_4_4 : PairPortTriangles 3 4 2 4 := by decide

theorem all_pair_port_triangles_3_2 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 3 l 2 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_2_2_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_2_4_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_3_3_0_0 : PairPortTriangles 3 0 3 0 := by decide

theorem pair_port_triangles_3_3_4_0 : PairPortTriangles 3 4 3 0 := by decide

theorem pair_port_triangles_3_3_5_0 : PairPortTriangles 3 5 3 0 := by decide

theorem pair_port_triangles_3_3_8_0 : PairPortTriangles 3 8 3 0 := by decide

theorem all_pair_port_triangles_3_3 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 3 l 3 t := by
  exact (Fin.cases (Fin.cases (fun _ => pair_port_triangles_3_3_0_0) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (fun _ => pair_port_triangles_3_3_4_0) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (fun _ => pair_port_triangles_3_3_5_0) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (fun _ => pair_port_triangles_3_3_8_0) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_3_4_4_5 : PairPortTriangles 3 4 4 5 := by decide

theorem pair_port_triangles_3_4_5_5 : PairPortTriangles 3 5 4 5 := by decide

theorem pair_port_triangles_3_4_7_3 : PairPortTriangles 3 7 4 3 := by decide

theorem pair_port_triangles_3_4_8_3 : PairPortTriangles 3 8 4 3 := by decide

theorem pair_port_triangles_3_4_8_5 : PairPortTriangles 3 8 4 5 := by decide

theorem all_pair_port_triangles_3_4 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 3 l 4 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_4_4_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_4_5_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_4_7_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_4_8_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_4_8_5) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_3_5_0_1 : PairPortTriangles 3 0 5 1 := by decide

theorem pair_port_triangles_3_5_2_1 : PairPortTriangles 3 2 5 1 := by decide

theorem pair_port_triangles_3_5_3_1 : PairPortTriangles 3 3 5 1 := by decide

theorem pair_port_triangles_3_5_4_1 : PairPortTriangles 3 4 5 1 := by decide

theorem pair_port_triangles_3_5_5_1 : PairPortTriangles 3 5 5 1 := by decide

theorem pair_port_triangles_3_5_7_1 : PairPortTriangles 3 7 5 1 := by decide

theorem pair_port_triangles_3_5_8_1 : PairPortTriangles 3 8 5 1 := by decide

theorem all_pair_port_triangles_3_5 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 3 l 5 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_5_0_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_5_2_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_5_3_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_5_4_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_5_5_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_5_7_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_3_5_8_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

end SpectreFinite.HexSearch.ForwardSubstitution
