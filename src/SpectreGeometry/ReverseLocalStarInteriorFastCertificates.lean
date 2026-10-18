module

public import SpectreGeometry.ReverseLocalStarInteriorFast00
public import SpectreGeometry.ReverseLocalStarInteriorFast01
public import SpectreGeometry.ReverseLocalStarInteriorFast02
public import SpectreGeometry.ReverseLocalStarInteriorFast03
public import SpectreGeometry.ReverseLocalStarInteriorFast04
public import SpectreGeometry.ReverseLocalStarInteriorFast05
public import SpectreGeometry.ReverseLocalStarInteriorFast06
public import SpectreGeometry.ReverseLocalStarInteriorFast07
public import SpectreGeometry.ReverseLocalStarInteriorFast08
public import SpectreGeometry.ReverseLocalStarInteriorFast10
public import SpectreGeometry.ReverseLocalStarInteriorFast11
public import SpectreGeometry.ReverseLocalStarInteriorFast12
public import SpectreGeometry.ReverseLocalStarInteriorFast13
public import SpectreGeometry.ReverseLocalStarInteriorFast14
public import SpectreGeometry.ReverseLocalStarInteriorFast15
public import SpectreGeometry.ReverseLocalStarInteriorFast16
public import SpectreGeometry.ReverseLocalStarInteriorFast17
public import SpectreGeometry.ReverseLocalStarInteriorFast18

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem interior_fast_certificate_block_0_0 : ∀ i : Fin 16,
    InteriorFastCertificate false (0+i.val) := by
  exact Fin.cases interior_fast_certificate_0_0 (Fin.cases interior_fast_certificate_0_1 (Fin.cases interior_fast_certificate_0_2 (Fin.cases interior_fast_certificate_0_3 (Fin.cases interior_fast_certificate_0_4 (Fin.cases interior_fast_certificate_0_5 (Fin.cases interior_fast_certificate_0_6 (Fin.cases interior_fast_certificate_0_7 (Fin.cases interior_fast_certificate_0_8 (Fin.cases interior_fast_certificate_0_9 (Fin.cases interior_fast_certificate_0_10 (Fin.cases interior_fast_certificate_0_11 (Fin.cases interior_fast_certificate_0_12 (Fin.cases interior_fast_certificate_0_13 (Fin.cases interior_fast_certificate_0_14 (Fin.cases interior_fast_certificate_0_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_1 : ∀ i : Fin 16,
    InteriorFastCertificate false (16+i.val) := by
  exact Fin.cases interior_fast_certificate_0_16 (Fin.cases interior_fast_certificate_0_17 (Fin.cases interior_fast_certificate_0_18 (Fin.cases interior_fast_certificate_0_19 (Fin.cases interior_fast_certificate_0_20 (Fin.cases interior_fast_certificate_0_21 (Fin.cases interior_fast_certificate_0_22 (Fin.cases interior_fast_certificate_0_23 (Fin.cases interior_fast_certificate_0_24 (Fin.cases interior_fast_certificate_0_25 (Fin.cases interior_fast_certificate_0_26 (Fin.cases interior_fast_certificate_0_27 (Fin.cases interior_fast_certificate_0_28 (Fin.cases interior_fast_certificate_0_29 (Fin.cases interior_fast_certificate_0_30 (Fin.cases interior_fast_certificate_0_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_2 : ∀ i : Fin 16,
    InteriorFastCertificate false (32+i.val) := by
  exact Fin.cases interior_fast_certificate_0_32 (Fin.cases interior_fast_certificate_0_33 (Fin.cases interior_fast_certificate_0_34 (Fin.cases interior_fast_certificate_0_35 (Fin.cases interior_fast_certificate_0_36 (Fin.cases interior_fast_certificate_0_37 (Fin.cases interior_fast_certificate_0_38 (Fin.cases interior_fast_certificate_0_39 (Fin.cases interior_fast_certificate_0_40 (Fin.cases interior_fast_certificate_0_41 (Fin.cases interior_fast_certificate_0_42 (Fin.cases interior_fast_certificate_0_43 (Fin.cases interior_fast_certificate_0_44 (Fin.cases interior_fast_certificate_0_45 (Fin.cases interior_fast_certificate_0_46 (Fin.cases interior_fast_certificate_0_47 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_3 : ∀ i : Fin 16,
    InteriorFastCertificate false (48+i.val) := by
  exact Fin.cases interior_fast_certificate_0_48 (Fin.cases interior_fast_certificate_0_49 (Fin.cases interior_fast_certificate_0_50 (Fin.cases interior_fast_certificate_0_51 (Fin.cases interior_fast_certificate_0_52 (Fin.cases interior_fast_certificate_0_53 (Fin.cases interior_fast_certificate_0_54 (Fin.cases interior_fast_certificate_0_55 (Fin.cases interior_fast_certificate_0_56 (Fin.cases interior_fast_certificate_0_57 (Fin.cases interior_fast_certificate_0_58 (Fin.cases interior_fast_certificate_0_59 (Fin.cases interior_fast_certificate_0_60 (Fin.cases interior_fast_certificate_0_61 (Fin.cases interior_fast_certificate_0_62 (Fin.cases interior_fast_certificate_0_63 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_4 : ∀ i : Fin 16,
    InteriorFastCertificate false (64+i.val) := by
  exact Fin.cases interior_fast_certificate_0_64 (Fin.cases interior_fast_certificate_0_65 (Fin.cases interior_fast_certificate_0_66 (Fin.cases interior_fast_certificate_0_67 (Fin.cases interior_fast_certificate_0_68 (Fin.cases interior_fast_certificate_0_69 (Fin.cases interior_fast_certificate_0_70 (Fin.cases interior_fast_certificate_0_71 (Fin.cases interior_fast_certificate_0_72 (Fin.cases interior_fast_certificate_0_73 (Fin.cases interior_fast_certificate_0_74 (Fin.cases interior_fast_certificate_0_75 (Fin.cases interior_fast_certificate_0_76 (Fin.cases interior_fast_certificate_0_77 (Fin.cases interior_fast_certificate_0_78 (Fin.cases interior_fast_certificate_0_79 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_5 : ∀ i : Fin 16,
    InteriorFastCertificate false (80+i.val) := by
  exact Fin.cases interior_fast_certificate_0_80 (Fin.cases interior_fast_certificate_0_81 (Fin.cases interior_fast_certificate_0_82 (Fin.cases interior_fast_certificate_0_83 (Fin.cases interior_fast_certificate_0_84 (Fin.cases interior_fast_certificate_0_85 (Fin.cases interior_fast_certificate_0_86 (Fin.cases interior_fast_certificate_0_87 (Fin.cases interior_fast_certificate_0_88 (Fin.cases interior_fast_certificate_0_89 (Fin.cases interior_fast_certificate_0_90 (Fin.cases interior_fast_certificate_0_91 (Fin.cases interior_fast_certificate_0_92 (Fin.cases interior_fast_certificate_0_93 (Fin.cases interior_fast_certificate_0_94 (Fin.cases interior_fast_certificate_0_95 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_6 : ∀ i : Fin 16,
    InteriorFastCertificate false (96+i.val) := by
  exact Fin.cases interior_fast_certificate_0_96 (Fin.cases interior_fast_certificate_0_97 (Fin.cases interior_fast_certificate_0_98 (Fin.cases interior_fast_certificate_0_99 (Fin.cases interior_fast_certificate_0_100 (Fin.cases interior_fast_certificate_0_101 (Fin.cases interior_fast_certificate_0_102 (Fin.cases interior_fast_certificate_0_103 (Fin.cases interior_fast_certificate_0_104 (Fin.cases interior_fast_certificate_0_105 (Fin.cases interior_fast_certificate_0_106 (Fin.cases interior_fast_certificate_0_107 (Fin.cases interior_fast_certificate_0_108 (Fin.cases interior_fast_certificate_0_109 (Fin.cases interior_fast_certificate_0_110 (Fin.cases interior_fast_certificate_0_111 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_7 : ∀ i : Fin 16,
    InteriorFastCertificate false (112+i.val) := by
  exact Fin.cases interior_fast_certificate_0_112 (Fin.cases interior_fast_certificate_0_113 (Fin.cases interior_fast_certificate_0_114 (Fin.cases interior_fast_certificate_0_115 (Fin.cases interior_fast_certificate_0_116 (Fin.cases interior_fast_certificate_0_117 (Fin.cases interior_fast_certificate_0_118 (Fin.cases interior_fast_certificate_0_119 (Fin.cases interior_fast_certificate_0_120 (Fin.cases interior_fast_certificate_0_121 (Fin.cases interior_fast_certificate_0_122 (Fin.cases interior_fast_certificate_0_123 (Fin.cases interior_fast_certificate_0_124 (Fin.cases interior_fast_certificate_0_125 (Fin.cases interior_fast_certificate_0_126 (Fin.cases interior_fast_certificate_0_127 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_0_8 : ∀ i : Fin 5,
    InteriorFastCertificate false (128+i.val) := by
  exact Fin.cases interior_fast_certificate_0_128 (Fin.cases interior_fast_certificate_0_129 (Fin.cases interior_fast_certificate_0_130 (Fin.cases interior_fast_certificate_0_131 (Fin.cases interior_fast_certificate_0_132 ((fun i => Fin.elim0 i))))))

theorem all_interior_fast_certificates_bounded_false : ∀ i : Fin 133, InteriorFastCertificate false i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using interior_fast_certificate_block_0_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_1 ⟨i.val-16,by omega⟩
  by_cases h2 : i.val < 48
  · have hs : 32 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_2 ⟨i.val-32,by omega⟩
  by_cases h3 : i.val < 64
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_3 ⟨i.val-48,by omega⟩
  by_cases h4 : i.val < 80
  · have hs : 64 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_4 ⟨i.val-64,by omega⟩
  by_cases h5 : i.val < 96
  · have hs : 80 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_5 ⟨i.val-80,by omega⟩
  by_cases h6 : i.val < 112
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_6 ⟨i.val-96,by omega⟩
  by_cases h7 : i.val < 128
  · have hs : 112 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_7 ⟨i.val-112,by omega⟩
  have hs : 128 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_0_8 ⟨i.val-128,by omega⟩

theorem interior_fast_certificate_block_1_0 : ∀ i : Fin 16,
    InteriorFastCertificate true (0+i.val) := by
  exact Fin.cases interior_fast_certificate_1_0 (Fin.cases interior_fast_certificate_1_1 (Fin.cases interior_fast_certificate_1_2 (Fin.cases interior_fast_certificate_1_3 (Fin.cases interior_fast_certificate_1_4 (Fin.cases interior_fast_certificate_1_5 (Fin.cases interior_fast_certificate_1_6 (Fin.cases interior_fast_certificate_1_7 (Fin.cases interior_fast_certificate_1_8 (Fin.cases interior_fast_certificate_1_9 (Fin.cases interior_fast_certificate_1_10 (Fin.cases interior_fast_certificate_1_11 (Fin.cases interior_fast_certificate_1_12 (Fin.cases interior_fast_certificate_1_13 (Fin.cases interior_fast_certificate_1_14 (Fin.cases interior_fast_certificate_1_15 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_1 : ∀ i : Fin 16,
    InteriorFastCertificate true (16+i.val) := by
  exact Fin.cases interior_fast_certificate_1_16 (Fin.cases interior_fast_certificate_1_17 (Fin.cases interior_fast_certificate_1_18 (Fin.cases interior_fast_certificate_1_19 (Fin.cases interior_fast_certificate_1_20 (Fin.cases interior_fast_certificate_1_21 (Fin.cases interior_fast_certificate_1_22 (Fin.cases interior_fast_certificate_1_23 (Fin.cases interior_fast_certificate_1_24 (Fin.cases interior_fast_certificate_1_25 (Fin.cases interior_fast_certificate_1_26 (Fin.cases interior_fast_certificate_1_27 (Fin.cases interior_fast_certificate_1_28 (Fin.cases interior_fast_certificate_1_29 (Fin.cases interior_fast_certificate_1_30 (Fin.cases interior_fast_certificate_1_31 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_2 : ∀ i : Fin 16,
    InteriorFastCertificate true (32+i.val) := by
  exact Fin.cases interior_fast_certificate_1_32 (Fin.cases interior_fast_certificate_1_33 (Fin.cases interior_fast_certificate_1_34 (Fin.cases interior_fast_certificate_1_35 (Fin.cases interior_fast_certificate_1_36 (Fin.cases interior_fast_certificate_1_37 (Fin.cases interior_fast_certificate_1_38 (Fin.cases interior_fast_certificate_1_39 (Fin.cases interior_fast_certificate_1_40 (Fin.cases interior_fast_certificate_1_41 (Fin.cases interior_fast_certificate_1_42 (Fin.cases interior_fast_certificate_1_43 (Fin.cases interior_fast_certificate_1_44 (Fin.cases interior_fast_certificate_1_45 (Fin.cases interior_fast_certificate_1_46 (Fin.cases interior_fast_certificate_1_47 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_3 : ∀ i : Fin 16,
    InteriorFastCertificate true (48+i.val) := by
  exact Fin.cases interior_fast_certificate_1_48 (Fin.cases interior_fast_certificate_1_49 (Fin.cases interior_fast_certificate_1_50 (Fin.cases interior_fast_certificate_1_51 (Fin.cases interior_fast_certificate_1_52 (Fin.cases interior_fast_certificate_1_53 (Fin.cases interior_fast_certificate_1_54 (Fin.cases interior_fast_certificate_1_55 (Fin.cases interior_fast_certificate_1_56 (Fin.cases interior_fast_certificate_1_57 (Fin.cases interior_fast_certificate_1_58 (Fin.cases interior_fast_certificate_1_59 (Fin.cases interior_fast_certificate_1_60 (Fin.cases interior_fast_certificate_1_61 (Fin.cases interior_fast_certificate_1_62 (Fin.cases interior_fast_certificate_1_63 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_4 : ∀ i : Fin 16,
    InteriorFastCertificate true (64+i.val) := by
  exact Fin.cases interior_fast_certificate_1_64 (Fin.cases interior_fast_certificate_1_65 (Fin.cases interior_fast_certificate_1_66 (Fin.cases interior_fast_certificate_1_67 (Fin.cases interior_fast_certificate_1_68 (Fin.cases interior_fast_certificate_1_69 (Fin.cases interior_fast_certificate_1_70 (Fin.cases interior_fast_certificate_1_71 (Fin.cases interior_fast_certificate_1_72 (Fin.cases interior_fast_certificate_1_73 (Fin.cases interior_fast_certificate_1_74 (Fin.cases interior_fast_certificate_1_75 (Fin.cases interior_fast_certificate_1_76 (Fin.cases interior_fast_certificate_1_77 (Fin.cases interior_fast_certificate_1_78 (Fin.cases interior_fast_certificate_1_79 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_5 : ∀ i : Fin 16,
    InteriorFastCertificate true (80+i.val) := by
  exact Fin.cases interior_fast_certificate_1_80 (Fin.cases interior_fast_certificate_1_81 (Fin.cases interior_fast_certificate_1_82 (Fin.cases interior_fast_certificate_1_83 (Fin.cases interior_fast_certificate_1_84 (Fin.cases interior_fast_certificate_1_85 (Fin.cases interior_fast_certificate_1_86 (Fin.cases interior_fast_certificate_1_87 (Fin.cases interior_fast_certificate_1_88 (Fin.cases interior_fast_certificate_1_89 (Fin.cases interior_fast_certificate_1_90 (Fin.cases interior_fast_certificate_1_91 (Fin.cases interior_fast_certificate_1_92 (Fin.cases interior_fast_certificate_1_93 (Fin.cases interior_fast_certificate_1_94 (Fin.cases interior_fast_certificate_1_95 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_6 : ∀ i : Fin 16,
    InteriorFastCertificate true (96+i.val) := by
  exact Fin.cases interior_fast_certificate_1_96 (Fin.cases interior_fast_certificate_1_97 (Fin.cases interior_fast_certificate_1_98 (Fin.cases interior_fast_certificate_1_99 (Fin.cases interior_fast_certificate_1_100 (Fin.cases interior_fast_certificate_1_101 (Fin.cases interior_fast_certificate_1_102 (Fin.cases interior_fast_certificate_1_103 (Fin.cases interior_fast_certificate_1_104 (Fin.cases interior_fast_certificate_1_105 (Fin.cases interior_fast_certificate_1_106 (Fin.cases interior_fast_certificate_1_107 (Fin.cases interior_fast_certificate_1_108 (Fin.cases interior_fast_certificate_1_109 (Fin.cases interior_fast_certificate_1_110 (Fin.cases interior_fast_certificate_1_111 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_7 : ∀ i : Fin 16,
    InteriorFastCertificate true (112+i.val) := by
  exact Fin.cases interior_fast_certificate_1_112 (Fin.cases interior_fast_certificate_1_113 (Fin.cases interior_fast_certificate_1_114 (Fin.cases interior_fast_certificate_1_115 (Fin.cases interior_fast_certificate_1_116 (Fin.cases interior_fast_certificate_1_117 (Fin.cases interior_fast_certificate_1_118 (Fin.cases interior_fast_certificate_1_119 (Fin.cases interior_fast_certificate_1_120 (Fin.cases interior_fast_certificate_1_121 (Fin.cases interior_fast_certificate_1_122 (Fin.cases interior_fast_certificate_1_123 (Fin.cases interior_fast_certificate_1_124 (Fin.cases interior_fast_certificate_1_125 (Fin.cases interior_fast_certificate_1_126 (Fin.cases interior_fast_certificate_1_127 ((fun i => Fin.elim0 i)))))))))))))))))

theorem interior_fast_certificate_block_1_8 : ∀ i : Fin 5,
    InteriorFastCertificate true (128+i.val) := by
  exact Fin.cases interior_fast_certificate_1_128 (Fin.cases interior_fast_certificate_1_129 (Fin.cases interior_fast_certificate_1_130 (Fin.cases interior_fast_certificate_1_131 (Fin.cases interior_fast_certificate_1_132 ((fun i => Fin.elim0 i))))))

theorem all_interior_fast_certificates_bounded_true : ∀ i : Fin 133, InteriorFastCertificate true i.val := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using interior_fast_certificate_block_1_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_1 ⟨i.val-16,by omega⟩
  by_cases h2 : i.val < 48
  · have hs : 32 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_2 ⟨i.val-32,by omega⟩
  by_cases h3 : i.val < 64
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_3 ⟨i.val-48,by omega⟩
  by_cases h4 : i.val < 80
  · have hs : 64 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_4 ⟨i.val-64,by omega⟩
  by_cases h5 : i.val < 96
  · have hs : 80 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_5 ⟨i.val-80,by omega⟩
  by_cases h6 : i.val < 112
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_6 ⟨i.val-96,by omega⟩
  by_cases h7 : i.val < 128
  · have hs : 112 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_7 ⟨i.val-112,by omega⟩
  have hs : 128 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using interior_fast_certificate_block_1_8 ⟨i.val-128,by omega⟩

theorem all_interior_fast_certificates : ∀ (big : Bool) (v : Nat), InteriorFastCertificate big v := by
  intro big v
  cases big with
  | false =>
    intro hv
    have h : v < 133 := by
      change v < 127 at hv
      omega
    exact all_interior_fast_certificates_bounded_false ⟨v,h⟩ hv
  | true =>
    intro hv
    have h : v < 133 := by
      change v < 133 at hv
      omega
    exact all_interior_fast_certificates_bounded_true ⟨v,h⟩ hv

end SpectreGeometry.ReverseLocalStarOccurrences
