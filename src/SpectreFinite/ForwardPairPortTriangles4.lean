module

public import SpectreFinite.ForwardTrianglePortDefinitions

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem pair_port_triangles_4_0_0_5 : PairPortTriangles 4 0 0 5 := by decide

theorem pair_port_triangles_4_0_1_3 : PairPortTriangles 4 1 0 3 := by decide

theorem pair_port_triangles_4_0_3_3 : PairPortTriangles 4 3 0 3 := by decide

theorem pair_port_triangles_4_0_5_3 : PairPortTriangles 4 5 0 3 := by decide

theorem pair_port_triangles_4_0_6_3 : PairPortTriangles 4 6 0 3 := by decide

theorem all_pair_port_triangles_4_0 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 4 l 0 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_0_0_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_0_1_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_0_3_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_0_5_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_0_6_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_4_1_0_2 : PairPortTriangles 4 0 1 2 := by decide

theorem pair_port_triangles_4_1_1_5 : PairPortTriangles 4 1 1 5 := by decide

theorem pair_port_triangles_4_1_2_3 : PairPortTriangles 4 2 1 3 := by decide

theorem pair_port_triangles_4_1_2_5 : PairPortTriangles 4 2 1 5 := by decide

theorem pair_port_triangles_4_1_3_5 : PairPortTriangles 4 3 1 5 := by decide

theorem pair_port_triangles_4_1_4_3 : PairPortTriangles 4 4 1 3 := by decide

theorem pair_port_triangles_4_1_6_5 : PairPortTriangles 4 6 1 5 := by decide

theorem pair_port_triangles_4_1_7_5 : PairPortTriangles 4 7 1 5 := by decide

theorem all_pair_port_triangles_4_1 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 4 l 1 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_0_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_1_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_2_3) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_2_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_3_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_4_3) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_6_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_1_7_5) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_4_2_2_2 : PairPortTriangles 4 2 2 2 := by decide

theorem pair_port_triangles_4_2_4_2 : PairPortTriangles 4 4 2 2 := by decide

theorem pair_port_triangles_4_2_7_2 : PairPortTriangles 4 7 2 2 := by decide

theorem pair_port_triangles_4_2_8_2 : PairPortTriangles 4 8 2 2 := by decide

theorem all_pair_port_triangles_4_2 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 4 l 2 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_2_2_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_2_4_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_2_7_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_2_8_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_4_3_0_1 : PairPortTriangles 4 0 3 1 := by decide

theorem pair_port_triangles_4_3_2_1 : PairPortTriangles 4 2 3 1 := by decide

theorem pair_port_triangles_4_3_3_1 : PairPortTriangles 4 3 3 1 := by decide

theorem pair_port_triangles_4_3_4_1 : PairPortTriangles 4 4 3 1 := by decide

theorem pair_port_triangles_4_3_5_1 : PairPortTriangles 4 5 3 1 := by decide

theorem pair_port_triangles_4_3_7_1 : PairPortTriangles 4 7 3 1 := by decide

theorem pair_port_triangles_4_3_8_1 : PairPortTriangles 4 8 3 1 := by decide

theorem all_pair_port_triangles_4_3 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 4 l 3 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_3_0_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_3_2_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_3_3_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_3_4_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_3_5_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_3_7_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_3_8_1) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_4_4_3_2 : PairPortTriangles 4 3 4 2 := by decide

theorem pair_port_triangles_4_4_5_2 : PairPortTriangles 4 5 4 2 := by decide

theorem all_pair_port_triangles_4_4 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 4 l 4 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_4_3_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_4_5_2) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

theorem pair_port_triangles_4_5_1_4 : PairPortTriangles 4 1 5 4 := by decide

theorem pair_port_triangles_4_5_3_4 : PairPortTriangles 4 3 5 4 := by decide

theorem pair_port_triangles_4_5_5_4 : PairPortTriangles 4 5 5 4 := by decide

theorem pair_port_triangles_4_5_6_4 : PairPortTriangles 4 6 5 4 := by decide

theorem pair_port_triangles_4_5_7_4 : PairPortTriangles 4 7 5 4 := by decide

theorem pair_port_triangles_4_5_8_4 : PairPortTriangles 4 8 5 4 := by decide

theorem all_pair_port_triangles_4_5 : ∀ l : TileKind, ∀ t : Fin 6, PairPortTriangleCertificate 4 l 5 t := by
  exact (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_5_1_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_5_3_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_5_5_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_5_6_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_5_7_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (fun _ => pair_port_triangles_4_5_8_4) (Fin.cases (by decide) (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

end SpectreFinite.HexSearch.ForwardSubstitution
