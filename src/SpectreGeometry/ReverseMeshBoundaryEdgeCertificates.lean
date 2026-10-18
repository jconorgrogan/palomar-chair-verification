module

public import SpectreGeometry.ReverseMeshBoundaryEdges0
public import SpectreGeometry.ReverseMeshBoundaryEdges1
public import SpectreGeometry.ReverseMeshBoundaryEdges2
public import SpectreGeometry.ReverseMeshBoundaryEdges3
public import SpectreGeometry.ReverseMeshBoundaryEdges4
public import SpectreGeometry.ReverseMeshBoundaryEdges5
public import SpectreGeometry.ReverseMeshBoundaryEdges6
public import SpectreGeometry.ReverseMeshBoundaryEdges7
public import SpectreGeometry.ReverseMeshBoundaryEdges8

@[expose] public section

namespace SpectreGeometry.ReverseMeshEdgeIncidence
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem boundary_edge_certificates_block_0_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 0 (0+i.val) := by
  exact Fin.cases boundary_edge_0_0 (Fin.cases boundary_edge_0_1 (Fin.cases boundary_edge_0_2 (Fin.cases boundary_edge_0_3 (Fin.cases boundary_edge_0_4 (Fin.cases boundary_edge_0_5 (Fin.cases boundary_edge_0_6 (Fin.cases boundary_edge_0_7 (Fin.cases boundary_edge_0_8 (Fin.cases boundary_edge_0_9 (Fin.cases boundary_edge_0_10 (Fin.cases boundary_edge_0_11 (Fin.cases boundary_edge_0_12 (Fin.cases boundary_edge_0_13 (Fin.cases boundary_edge_0_14 (Fin.cases boundary_edge_0_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_0_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 0 (16+i.val) := by
  exact Fin.cases boundary_edge_0_16 (Fin.cases boundary_edge_0_17 (Fin.cases boundary_edge_0_18 (Fin.cases boundary_edge_0_19 (Fin.cases boundary_edge_0_20 (Fin.cases boundary_edge_0_21 (Fin.cases boundary_edge_0_22 (Fin.cases boundary_edge_0_23 (Fin.cases boundary_edge_0_24 (Fin.cases boundary_edge_0_25 (Fin.cases boundary_edge_0_26 (Fin.cases boundary_edge_0_27 (Fin.cases boundary_edge_0_28 (Fin.cases boundary_edge_0_29 (Fin.cases boundary_edge_0_30 (Fin.cases boundary_edge_0_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_0_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 0 (32+i.val) := by
  exact Fin.cases boundary_edge_0_32 (Fin.cases boundary_edge_0_33 (Fin.cases boundary_edge_0_34 (Fin.cases boundary_edge_0_35 (Fin.cases boundary_edge_0_36 (Fin.cases boundary_edge_0_37 (Fin.cases boundary_edge_0_38 (Fin.cases boundary_edge_0_39 (Fin.cases boundary_edge_0_40 (Fin.cases boundary_edge_0_41 (Fin.cases boundary_edge_0_42 (Fin.cases boundary_edge_0_43 (Fin.cases boundary_edge_0_44 (Fin.cases boundary_edge_0_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_0 : ∀ i : Fin 46, BoundaryEdgeCertificate 0 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_0_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_0_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_0_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_1_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 1 (0+i.val) := by
  exact Fin.cases boundary_edge_1_0 (Fin.cases boundary_edge_1_1 (Fin.cases boundary_edge_1_2 (Fin.cases boundary_edge_1_3 (Fin.cases boundary_edge_1_4 (Fin.cases boundary_edge_1_5 (Fin.cases boundary_edge_1_6 (Fin.cases boundary_edge_1_7 (Fin.cases boundary_edge_1_8 (Fin.cases boundary_edge_1_9 (Fin.cases boundary_edge_1_10 (Fin.cases boundary_edge_1_11 (Fin.cases boundary_edge_1_12 (Fin.cases boundary_edge_1_13 (Fin.cases boundary_edge_1_14 (Fin.cases boundary_edge_1_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_1_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 1 (16+i.val) := by
  exact Fin.cases boundary_edge_1_16 (Fin.cases boundary_edge_1_17 (Fin.cases boundary_edge_1_18 (Fin.cases boundary_edge_1_19 (Fin.cases boundary_edge_1_20 (Fin.cases boundary_edge_1_21 (Fin.cases boundary_edge_1_22 (Fin.cases boundary_edge_1_23 (Fin.cases boundary_edge_1_24 (Fin.cases boundary_edge_1_25 (Fin.cases boundary_edge_1_26 (Fin.cases boundary_edge_1_27 (Fin.cases boundary_edge_1_28 (Fin.cases boundary_edge_1_29 (Fin.cases boundary_edge_1_30 (Fin.cases boundary_edge_1_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_1_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 1 (32+i.val) := by
  exact Fin.cases boundary_edge_1_32 (Fin.cases boundary_edge_1_33 (Fin.cases boundary_edge_1_34 (Fin.cases boundary_edge_1_35 (Fin.cases boundary_edge_1_36 (Fin.cases boundary_edge_1_37 (Fin.cases boundary_edge_1_38 (Fin.cases boundary_edge_1_39 (Fin.cases boundary_edge_1_40 (Fin.cases boundary_edge_1_41 (Fin.cases boundary_edge_1_42 (Fin.cases boundary_edge_1_43 (Fin.cases boundary_edge_1_44 (Fin.cases boundary_edge_1_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_1 : ∀ i : Fin 46, BoundaryEdgeCertificate 1 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_1_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_1_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_1_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_2_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 2 (0+i.val) := by
  exact Fin.cases boundary_edge_2_0 (Fin.cases boundary_edge_2_1 (Fin.cases boundary_edge_2_2 (Fin.cases boundary_edge_2_3 (Fin.cases boundary_edge_2_4 (Fin.cases boundary_edge_2_5 (Fin.cases boundary_edge_2_6 (Fin.cases boundary_edge_2_7 (Fin.cases boundary_edge_2_8 (Fin.cases boundary_edge_2_9 (Fin.cases boundary_edge_2_10 (Fin.cases boundary_edge_2_11 (Fin.cases boundary_edge_2_12 (Fin.cases boundary_edge_2_13 (Fin.cases boundary_edge_2_14 (Fin.cases boundary_edge_2_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_2_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 2 (16+i.val) := by
  exact Fin.cases boundary_edge_2_16 (Fin.cases boundary_edge_2_17 (Fin.cases boundary_edge_2_18 (Fin.cases boundary_edge_2_19 (Fin.cases boundary_edge_2_20 (Fin.cases boundary_edge_2_21 (Fin.cases boundary_edge_2_22 (Fin.cases boundary_edge_2_23 (Fin.cases boundary_edge_2_24 (Fin.cases boundary_edge_2_25 (Fin.cases boundary_edge_2_26 (Fin.cases boundary_edge_2_27 (Fin.cases boundary_edge_2_28 (Fin.cases boundary_edge_2_29 (Fin.cases boundary_edge_2_30 (Fin.cases boundary_edge_2_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_2_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 2 (32+i.val) := by
  exact Fin.cases boundary_edge_2_32 (Fin.cases boundary_edge_2_33 (Fin.cases boundary_edge_2_34 (Fin.cases boundary_edge_2_35 (Fin.cases boundary_edge_2_36 (Fin.cases boundary_edge_2_37 (Fin.cases boundary_edge_2_38 (Fin.cases boundary_edge_2_39 (Fin.cases boundary_edge_2_40 (Fin.cases boundary_edge_2_41 (Fin.cases boundary_edge_2_42 (Fin.cases boundary_edge_2_43 (Fin.cases boundary_edge_2_44 (Fin.cases boundary_edge_2_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_2 : ∀ i : Fin 46, BoundaryEdgeCertificate 2 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_2_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_2_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_2_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_3_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 3 (0+i.val) := by
  exact Fin.cases boundary_edge_3_0 (Fin.cases boundary_edge_3_1 (Fin.cases boundary_edge_3_2 (Fin.cases boundary_edge_3_3 (Fin.cases boundary_edge_3_4 (Fin.cases boundary_edge_3_5 (Fin.cases boundary_edge_3_6 (Fin.cases boundary_edge_3_7 (Fin.cases boundary_edge_3_8 (Fin.cases boundary_edge_3_9 (Fin.cases boundary_edge_3_10 (Fin.cases boundary_edge_3_11 (Fin.cases boundary_edge_3_12 (Fin.cases boundary_edge_3_13 (Fin.cases boundary_edge_3_14 (Fin.cases boundary_edge_3_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_3_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 3 (16+i.val) := by
  exact Fin.cases boundary_edge_3_16 (Fin.cases boundary_edge_3_17 (Fin.cases boundary_edge_3_18 (Fin.cases boundary_edge_3_19 (Fin.cases boundary_edge_3_20 (Fin.cases boundary_edge_3_21 (Fin.cases boundary_edge_3_22 (Fin.cases boundary_edge_3_23 (Fin.cases boundary_edge_3_24 (Fin.cases boundary_edge_3_25 (Fin.cases boundary_edge_3_26 (Fin.cases boundary_edge_3_27 (Fin.cases boundary_edge_3_28 (Fin.cases boundary_edge_3_29 (Fin.cases boundary_edge_3_30 (Fin.cases boundary_edge_3_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_3_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 3 (32+i.val) := by
  exact Fin.cases boundary_edge_3_32 (Fin.cases boundary_edge_3_33 (Fin.cases boundary_edge_3_34 (Fin.cases boundary_edge_3_35 (Fin.cases boundary_edge_3_36 (Fin.cases boundary_edge_3_37 (Fin.cases boundary_edge_3_38 (Fin.cases boundary_edge_3_39 (Fin.cases boundary_edge_3_40 (Fin.cases boundary_edge_3_41 (Fin.cases boundary_edge_3_42 (Fin.cases boundary_edge_3_43 (Fin.cases boundary_edge_3_44 (Fin.cases boundary_edge_3_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_3 : ∀ i : Fin 46, BoundaryEdgeCertificate 3 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_3_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_3_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_3_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_4_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 4 (0+i.val) := by
  exact Fin.cases boundary_edge_4_0 (Fin.cases boundary_edge_4_1 (Fin.cases boundary_edge_4_2 (Fin.cases boundary_edge_4_3 (Fin.cases boundary_edge_4_4 (Fin.cases boundary_edge_4_5 (Fin.cases boundary_edge_4_6 (Fin.cases boundary_edge_4_7 (Fin.cases boundary_edge_4_8 (Fin.cases boundary_edge_4_9 (Fin.cases boundary_edge_4_10 (Fin.cases boundary_edge_4_11 (Fin.cases boundary_edge_4_12 (Fin.cases boundary_edge_4_13 (Fin.cases boundary_edge_4_14 (Fin.cases boundary_edge_4_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_4_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 4 (16+i.val) := by
  exact Fin.cases boundary_edge_4_16 (Fin.cases boundary_edge_4_17 (Fin.cases boundary_edge_4_18 (Fin.cases boundary_edge_4_19 (Fin.cases boundary_edge_4_20 (Fin.cases boundary_edge_4_21 (Fin.cases boundary_edge_4_22 (Fin.cases boundary_edge_4_23 (Fin.cases boundary_edge_4_24 (Fin.cases boundary_edge_4_25 (Fin.cases boundary_edge_4_26 (Fin.cases boundary_edge_4_27 (Fin.cases boundary_edge_4_28 (Fin.cases boundary_edge_4_29 (Fin.cases boundary_edge_4_30 (Fin.cases boundary_edge_4_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_4_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 4 (32+i.val) := by
  exact Fin.cases boundary_edge_4_32 (Fin.cases boundary_edge_4_33 (Fin.cases boundary_edge_4_34 (Fin.cases boundary_edge_4_35 (Fin.cases boundary_edge_4_36 (Fin.cases boundary_edge_4_37 (Fin.cases boundary_edge_4_38 (Fin.cases boundary_edge_4_39 (Fin.cases boundary_edge_4_40 (Fin.cases boundary_edge_4_41 (Fin.cases boundary_edge_4_42 (Fin.cases boundary_edge_4_43 (Fin.cases boundary_edge_4_44 (Fin.cases boundary_edge_4_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_4 : ∀ i : Fin 46, BoundaryEdgeCertificate 4 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_4_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_4_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_4_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_5_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 5 (0+i.val) := by
  exact Fin.cases boundary_edge_5_0 (Fin.cases boundary_edge_5_1 (Fin.cases boundary_edge_5_2 (Fin.cases boundary_edge_5_3 (Fin.cases boundary_edge_5_4 (Fin.cases boundary_edge_5_5 (Fin.cases boundary_edge_5_6 (Fin.cases boundary_edge_5_7 (Fin.cases boundary_edge_5_8 (Fin.cases boundary_edge_5_9 (Fin.cases boundary_edge_5_10 (Fin.cases boundary_edge_5_11 (Fin.cases boundary_edge_5_12 (Fin.cases boundary_edge_5_13 (Fin.cases boundary_edge_5_14 (Fin.cases boundary_edge_5_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_5_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 5 (16+i.val) := by
  exact Fin.cases boundary_edge_5_16 (Fin.cases boundary_edge_5_17 (Fin.cases boundary_edge_5_18 (Fin.cases boundary_edge_5_19 (Fin.cases boundary_edge_5_20 (Fin.cases boundary_edge_5_21 (Fin.cases boundary_edge_5_22 (Fin.cases boundary_edge_5_23 (Fin.cases boundary_edge_5_24 (Fin.cases boundary_edge_5_25 (Fin.cases boundary_edge_5_26 (Fin.cases boundary_edge_5_27 (Fin.cases boundary_edge_5_28 (Fin.cases boundary_edge_5_29 (Fin.cases boundary_edge_5_30 (Fin.cases boundary_edge_5_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_5_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 5 (32+i.val) := by
  exact Fin.cases boundary_edge_5_32 (Fin.cases boundary_edge_5_33 (Fin.cases boundary_edge_5_34 (Fin.cases boundary_edge_5_35 (Fin.cases boundary_edge_5_36 (Fin.cases boundary_edge_5_37 (Fin.cases boundary_edge_5_38 (Fin.cases boundary_edge_5_39 (Fin.cases boundary_edge_5_40 (Fin.cases boundary_edge_5_41 (Fin.cases boundary_edge_5_42 (Fin.cases boundary_edge_5_43 (Fin.cases boundary_edge_5_44 (Fin.cases boundary_edge_5_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_5 : ∀ i : Fin 46, BoundaryEdgeCertificate 5 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_5_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_5_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_5_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_6_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 6 (0+i.val) := by
  exact Fin.cases boundary_edge_6_0 (Fin.cases boundary_edge_6_1 (Fin.cases boundary_edge_6_2 (Fin.cases boundary_edge_6_3 (Fin.cases boundary_edge_6_4 (Fin.cases boundary_edge_6_5 (Fin.cases boundary_edge_6_6 (Fin.cases boundary_edge_6_7 (Fin.cases boundary_edge_6_8 (Fin.cases boundary_edge_6_9 (Fin.cases boundary_edge_6_10 (Fin.cases boundary_edge_6_11 (Fin.cases boundary_edge_6_12 (Fin.cases boundary_edge_6_13 (Fin.cases boundary_edge_6_14 (Fin.cases boundary_edge_6_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_6_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 6 (16+i.val) := by
  exact Fin.cases boundary_edge_6_16 (Fin.cases boundary_edge_6_17 (Fin.cases boundary_edge_6_18 (Fin.cases boundary_edge_6_19 (Fin.cases boundary_edge_6_20 (Fin.cases boundary_edge_6_21 (Fin.cases boundary_edge_6_22 (Fin.cases boundary_edge_6_23 (Fin.cases boundary_edge_6_24 (Fin.cases boundary_edge_6_25 (Fin.cases boundary_edge_6_26 (Fin.cases boundary_edge_6_27 (Fin.cases boundary_edge_6_28 (Fin.cases boundary_edge_6_29 (Fin.cases boundary_edge_6_30 (Fin.cases boundary_edge_6_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_6_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 6 (32+i.val) := by
  exact Fin.cases boundary_edge_6_32 (Fin.cases boundary_edge_6_33 (Fin.cases boundary_edge_6_34 (Fin.cases boundary_edge_6_35 (Fin.cases boundary_edge_6_36 (Fin.cases boundary_edge_6_37 (Fin.cases boundary_edge_6_38 (Fin.cases boundary_edge_6_39 (Fin.cases boundary_edge_6_40 (Fin.cases boundary_edge_6_41 (Fin.cases boundary_edge_6_42 (Fin.cases boundary_edge_6_43 (Fin.cases boundary_edge_6_44 (Fin.cases boundary_edge_6_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_6 : ∀ i : Fin 46, BoundaryEdgeCertificate 6 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_6_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_6_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_6_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_7_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 7 (0+i.val) := by
  exact Fin.cases boundary_edge_7_0 (Fin.cases boundary_edge_7_1 (Fin.cases boundary_edge_7_2 (Fin.cases boundary_edge_7_3 (Fin.cases boundary_edge_7_4 (Fin.cases boundary_edge_7_5 (Fin.cases boundary_edge_7_6 (Fin.cases boundary_edge_7_7 (Fin.cases boundary_edge_7_8 (Fin.cases boundary_edge_7_9 (Fin.cases boundary_edge_7_10 (Fin.cases boundary_edge_7_11 (Fin.cases boundary_edge_7_12 (Fin.cases boundary_edge_7_13 (Fin.cases boundary_edge_7_14 (Fin.cases boundary_edge_7_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_7_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 7 (16+i.val) := by
  exact Fin.cases boundary_edge_7_16 (Fin.cases boundary_edge_7_17 (Fin.cases boundary_edge_7_18 (Fin.cases boundary_edge_7_19 (Fin.cases boundary_edge_7_20 (Fin.cases boundary_edge_7_21 (Fin.cases boundary_edge_7_22 (Fin.cases boundary_edge_7_23 (Fin.cases boundary_edge_7_24 (Fin.cases boundary_edge_7_25 (Fin.cases boundary_edge_7_26 (Fin.cases boundary_edge_7_27 (Fin.cases boundary_edge_7_28 (Fin.cases boundary_edge_7_29 (Fin.cases boundary_edge_7_30 (Fin.cases boundary_edge_7_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_7_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 7 (32+i.val) := by
  exact Fin.cases boundary_edge_7_32 (Fin.cases boundary_edge_7_33 (Fin.cases boundary_edge_7_34 (Fin.cases boundary_edge_7_35 (Fin.cases boundary_edge_7_36 (Fin.cases boundary_edge_7_37 (Fin.cases boundary_edge_7_38 (Fin.cases boundary_edge_7_39 (Fin.cases boundary_edge_7_40 (Fin.cases boundary_edge_7_41 (Fin.cases boundary_edge_7_42 (Fin.cases boundary_edge_7_43 (Fin.cases boundary_edge_7_44 (Fin.cases boundary_edge_7_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_7 : ∀ i : Fin 46, BoundaryEdgeCertificate 7 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_7_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_7_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_7_2 ⟨i.val-32,by omega⟩

theorem boundary_edge_certificates_block_8_0 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 8 (0+i.val) := by
  exact Fin.cases boundary_edge_8_0 (Fin.cases boundary_edge_8_1 (Fin.cases boundary_edge_8_2 (Fin.cases boundary_edge_8_3 (Fin.cases boundary_edge_8_4 (Fin.cases boundary_edge_8_5 (Fin.cases boundary_edge_8_6 (Fin.cases boundary_edge_8_7 (Fin.cases boundary_edge_8_8 (Fin.cases boundary_edge_8_9 (Fin.cases boundary_edge_8_10 (Fin.cases boundary_edge_8_11 (Fin.cases boundary_edge_8_12 (Fin.cases boundary_edge_8_13 (Fin.cases boundary_edge_8_14 (Fin.cases boundary_edge_8_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_8_1 : ∀ i : Fin 16,
    BoundaryEdgeCertificate 8 (16+i.val) := by
  exact Fin.cases boundary_edge_8_16 (Fin.cases boundary_edge_8_17 (Fin.cases boundary_edge_8_18 (Fin.cases boundary_edge_8_19 (Fin.cases boundary_edge_8_20 (Fin.cases boundary_edge_8_21 (Fin.cases boundary_edge_8_22 (Fin.cases boundary_edge_8_23 (Fin.cases boundary_edge_8_24 (Fin.cases boundary_edge_8_25 (Fin.cases boundary_edge_8_26 (Fin.cases boundary_edge_8_27 (Fin.cases boundary_edge_8_28 (Fin.cases boundary_edge_8_29 (Fin.cases boundary_edge_8_30 (Fin.cases boundary_edge_8_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem boundary_edge_certificates_block_8_2 : ∀ i : Fin 14,
    BoundaryEdgeCertificate 8 (32+i.val) := by
  exact Fin.cases boundary_edge_8_32 (Fin.cases boundary_edge_8_33 (Fin.cases boundary_edge_8_34 (Fin.cases boundary_edge_8_35 (Fin.cases boundary_edge_8_36 (Fin.cases boundary_edge_8_37 (Fin.cases boundary_edge_8_38 (Fin.cases boundary_edge_8_39 (Fin.cases boundary_edge_8_40 (Fin.cases boundary_edge_8_41 (Fin.cases boundary_edge_8_42 (Fin.cases boundary_edge_8_43 (Fin.cases boundary_edge_8_44 (Fin.cases boundary_edge_8_45 ((fun i => Fin.elim0 i)))))))))))))))

theorem boundary_edge_certificates_bounded_8 : ∀ i : Fin 46, BoundaryEdgeCertificate 8 i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using boundary_edge_certificates_block_8_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_8_1 ⟨i.val-16,by omega⟩
  have hs : 32 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using boundary_edge_certificates_block_8_2 ⟨i.val-32,by omega⟩

theorem all_boundary_edge_certificates_bounded : ∀ (k : Fin 9) (i : Fin 46), BoundaryEdgeCertificate k i.val := by
  exact Fin.cases boundary_edge_certificates_bounded_0 (Fin.cases boundary_edge_certificates_bounded_1 (Fin.cases boundary_edge_certificates_bounded_2 (Fin.cases boundary_edge_certificates_bounded_3 (Fin.cases boundary_edge_certificates_bounded_4 (Fin.cases boundary_edge_certificates_bounded_5 (Fin.cases boundary_edge_certificates_bounded_6 (Fin.cases boundary_edge_certificates_bounded_7 (Fin.cases boundary_edge_certificates_bounded_8 ((fun i => Fin.elim0 i))))))))))

theorem all_boundary_edge_certificates : ∀ (k : Fin 9) (i : Nat), BoundaryEdgeCertificate k i := by
  intro k i hi
  have hn : boundarySize (k.val != 0) ≤ 46 := by
    unfold boundarySize
    split <;> decide
  have hb : i < 46 := by omega
  exact all_boundary_edge_certificates_bounded k ⟨i,hb⟩ hi

end SpectreGeometry.ReverseMeshEdgeIncidence
