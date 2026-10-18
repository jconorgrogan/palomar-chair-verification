module

public import SpectreFinite.ForwardTriplePortTriangles0
public import SpectreFinite.ForwardTriplePortTriangles1
public import SpectreFinite.ForwardTriplePortTriangles2
public import SpectreFinite.ForwardTriplePortTriangles3
public import SpectreFinite.ForwardTriplePortTriangles4
public import SpectreFinite.ForwardTriplePortTriangles5
public import SpectreFinite.ForwardTriplePortTriangles6
public import SpectreFinite.ForwardTriplePortTriangles7
public import SpectreFinite.ForwardTriplePortTriangles8

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution

theorem all_root_port_triangles : ∀ k : TileKind, ∀ s : Fin 6, RootPortTriangleCertificate k s := by
  exact (Fin.cases (Fin.cases all_root_port_triangles_0_0 (Fin.cases all_root_port_triangles_0_1 (Fin.cases all_root_port_triangles_0_2 (Fin.cases all_root_port_triangles_0_3 (Fin.cases all_root_port_triangles_0_4 (Fin.cases all_root_port_triangles_0_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_1_0 (Fin.cases all_root_port_triangles_1_1 (Fin.cases all_root_port_triangles_1_2 (Fin.cases all_root_port_triangles_1_3 (Fin.cases all_root_port_triangles_1_4 (Fin.cases all_root_port_triangles_1_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_2_0 (Fin.cases all_root_port_triangles_2_1 (Fin.cases all_root_port_triangles_2_2 (Fin.cases all_root_port_triangles_2_3 (Fin.cases all_root_port_triangles_2_4 (Fin.cases all_root_port_triangles_2_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_3_0 (Fin.cases all_root_port_triangles_3_1 (Fin.cases all_root_port_triangles_3_2 (Fin.cases all_root_port_triangles_3_3 (Fin.cases all_root_port_triangles_3_4 (Fin.cases all_root_port_triangles_3_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_4_0 (Fin.cases all_root_port_triangles_4_1 (Fin.cases all_root_port_triangles_4_2 (Fin.cases all_root_port_triangles_4_3 (Fin.cases all_root_port_triangles_4_4 (Fin.cases all_root_port_triangles_4_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_5_0 (Fin.cases all_root_port_triangles_5_1 (Fin.cases all_root_port_triangles_5_2 (Fin.cases all_root_port_triangles_5_3 (Fin.cases all_root_port_triangles_5_4 (Fin.cases all_root_port_triangles_5_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_6_0 (Fin.cases all_root_port_triangles_6_1 (Fin.cases all_root_port_triangles_6_2 (Fin.cases all_root_port_triangles_6_3 (Fin.cases all_root_port_triangles_6_4 (Fin.cases all_root_port_triangles_6_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_7_0 (Fin.cases all_root_port_triangles_7_1 (Fin.cases all_root_port_triangles_7_2 (Fin.cases all_root_port_triangles_7_3 (Fin.cases all_root_port_triangles_7_4 (Fin.cases all_root_port_triangles_7_5 (fun i => Fin.elim0 i))))))) (Fin.cases (Fin.cases all_root_port_triangles_8_0 (Fin.cases all_root_port_triangles_8_1 (Fin.cases all_root_port_triangles_8_2 (Fin.cases all_root_port_triangles_8_3 (Fin.cases all_root_port_triangles_8_4 (Fin.cases all_root_port_triangles_8_5 (fun i => Fin.elim0 i))))))) (fun i => Fin.elim0 i))))))))))

end SpectreFinite.HexSearch.ForwardSubstitution
