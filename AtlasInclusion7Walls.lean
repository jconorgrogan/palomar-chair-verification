module
public import AtlasInclusion7Base
@[expose] public section
namespace CompactT7Preparation
open RegisteredPrime
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem pose5_atlas : ArithmeticAtlasContact P7 pose5 := by
  apply atlas_of_even_wall pose5 pose5_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose6_atlas : ArithmeticAtlasContact P7 pose6 := by
  apply atlas_of_even_wall pose6 pose6_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose7_atlas : ArithmeticAtlasContact P7 pose7 := by
  apply atlas_of_even_wall pose7 pose7_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose8_atlas : ArithmeticAtlasContact P7 pose8 := by
  apply atlas_of_even_wall pose8 pose8_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose9_atlas : ArithmeticAtlasContact P7 pose9 := by
  apply atlas_of_even_wall pose9 pose9_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose10_atlas : ArithmeticAtlasContact P7 pose10 := by
  apply atlas_of_even_wall pose10 pose10_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose11_atlas : ArithmeticAtlasContact P7 pose11 := by
  apply atlas_of_even_wall pose11 pose11_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose12_atlas : ArithmeticAtlasContact P7 pose12 := by
  apply atlas_of_even_wall pose12 pose12_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose14_atlas : ArithmeticAtlasContact P7 pose14 := by
  apply atlas_of_even_wall pose14 pose14_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose15_atlas : ArithmeticAtlasContact P7 pose15 := by
  apply atlas_of_even_wall pose15 pose15_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose17_atlas : ArithmeticAtlasContact P7 pose17 := by
  apply atlas_of_even_wall pose17 pose17_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose18_atlas : ArithmeticAtlasContact P7 pose18 := by
  apply atlas_of_even_wall pose18 pose18_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose30_atlas : ArithmeticAtlasContact P7 pose30 := by
  apply atlas_of_even_wall pose30 pose30_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose31_atlas : ArithmeticAtlasContact P7 pose31 := by
  apply atlas_of_even_wall pose31 pose31_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose32_atlas : ArithmeticAtlasContact P7 pose32 := by
  apply atlas_of_even_wall pose32 pose32_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose33_atlas : ArithmeticAtlasContact P7 pose33 := by
  apply atlas_of_even_wall pose33 pose33_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose34_atlas : ArithmeticAtlasContact P7 pose34 := by
  apply atlas_of_even_wall pose34 pose34_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose35_atlas : ArithmeticAtlasContact P7 pose35 := by
  apply atlas_of_even_wall pose35 pose35_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose36_atlas : ArithmeticAtlasContact P7 pose36 := by
  apply atlas_of_even_wall pose36 pose36_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose37_atlas : ArithmeticAtlasContact P7 pose37 := by
  apply atlas_of_even_wall pose37 pose37_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose38_atlas : ArithmeticAtlasContact P7 pose38 := by
  apply atlas_of_even_wall pose38 pose38_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose41_atlas : ArithmeticAtlasContact P7 pose41 := by
  apply atlas_of_even_wall pose41 pose41_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose42_atlas : ArithmeticAtlasContact P7 pose42 := by
  apply atlas_of_even_wall pose42 pose42_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose56_atlas : ArithmeticAtlasContact P7 pose56 := by
  apply atlas_of_even_wall pose56 pose56_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose57_atlas : ArithmeticAtlasContact P7 pose57 := by
  apply atlas_of_even_wall pose57 pose57_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose58_atlas : ArithmeticAtlasContact P7 pose58 := by
  apply atlas_of_even_wall pose58 pose58_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose62_atlas : ArithmeticAtlasContact P7 pose62 := by
  apply atlas_of_even_wall pose62 pose62_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose63_atlas : ArithmeticAtlasContact P7 pose63 := by
  apply atlas_of_even_wall pose63 pose63_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose64_atlas : ArithmeticAtlasContact P7 pose64 := by
  apply atlas_of_even_wall pose64 pose64_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose65_atlas : ArithmeticAtlasContact P7 pose65 := by
  apply atlas_of_even_wall pose65 pose65_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose66_atlas : ArithmeticAtlasContact P7 pose66 := by
  apply atlas_of_even_wall pose66 pose66_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose67_atlas : ArithmeticAtlasContact P7 pose67 := by
  apply atlas_of_even_wall pose67 pose67_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose68_atlas : ArithmeticAtlasContact P7 pose68 := by
  apply atlas_of_even_wall pose68 pose68_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose69_atlas : ArithmeticAtlasContact P7 pose69 := by
  apply atlas_of_even_wall pose69 pose69_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose72_atlas : ArithmeticAtlasContact P7 pose72 := by
  apply atlas_of_even_wall pose72 pose72_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose73_atlas : ArithmeticAtlasContact P7 pose73 := by
  apply atlas_of_even_wall pose73 pose73_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose86_atlas : ArithmeticAtlasContact P7 pose86 := by
  apply atlas_of_even_wall pose86 pose86_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose87_atlas : ArithmeticAtlasContact P7 pose87 := by
  apply atlas_of_even_wall pose87 pose87_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose88_atlas : ArithmeticAtlasContact P7 pose88 := by
  apply atlas_of_even_wall pose88 pose88_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose93_atlas : ArithmeticAtlasContact P7 pose93 := by
  apply atlas_of_even_wall pose93 pose93_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose94_atlas : ArithmeticAtlasContact P7 pose94 := by
  apply atlas_of_even_wall pose94 pose94_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose95_atlas : ArithmeticAtlasContact P7 pose95 := by
  apply atlas_of_even_wall pose95 pose95_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose96_atlas : ArithmeticAtlasContact P7 pose96 := by
  apply atlas_of_even_wall pose96 pose96_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose97_atlas : ArithmeticAtlasContact P7 pose97 := by
  apply atlas_of_even_wall pose97 pose97_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose98_atlas : ArithmeticAtlasContact P7 pose98 := by
  apply atlas_of_even_wall pose98 pose98_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose100_atlas : ArithmeticAtlasContact P7 pose100 := by
  apply atlas_of_even_wall pose100 pose100_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose101_atlas : ArithmeticAtlasContact P7 pose101 := by
  apply atlas_of_even_wall pose101 pose101_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose104_atlas : ArithmeticAtlasContact P7 pose104 := by
  apply atlas_of_even_wall pose104 pose104_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose105_atlas : ArithmeticAtlasContact P7 pose105 := by
  apply atlas_of_even_wall pose105 pose105_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose119_atlas : ArithmeticAtlasContact P7 pose119 := by
  apply atlas_of_even_wall pose119 pose119_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose120_atlas : ArithmeticAtlasContact P7 pose120 := by
  apply atlas_of_even_wall pose120 pose120_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose121_atlas : ArithmeticAtlasContact P7 pose121 := by
  apply atlas_of_even_wall pose121 pose121_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose124_atlas : ArithmeticAtlasContact P7 pose124 := by
  apply atlas_of_even_wall pose124 pose124_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose125_atlas : ArithmeticAtlasContact P7 pose125 := by
  apply atlas_of_even_wall pose125 pose125_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose126_atlas : ArithmeticAtlasContact P7 pose126 := by
  apply atlas_of_even_wall pose126 pose126_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose127_atlas : ArithmeticAtlasContact P7 pose127 := by
  apply atlas_of_even_wall pose127 pose127_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose129_atlas : ArithmeticAtlasContact P7 pose129 := by
  apply atlas_of_even_wall pose129 pose129_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose130_atlas : ArithmeticAtlasContact P7 pose130 := by
  apply atlas_of_even_wall pose130 pose130_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose132_atlas : ArithmeticAtlasContact P7 pose132 := by
  apply atlas_of_even_wall pose132 pose132_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose133_atlas : ArithmeticAtlasContact P7 pose133 := by
  apply atlas_of_even_wall pose133 pose133_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose135_atlas : ArithmeticAtlasContact P7 pose135 := by
  apply atlas_of_even_wall pose135 pose135_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose136_atlas : ArithmeticAtlasContact P7 pose136 := by
  apply atlas_of_even_wall pose136 pose136_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose148_atlas : ArithmeticAtlasContact P7 pose148 := by
  apply atlas_of_even_wall pose148 pose148_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose149_atlas : ArithmeticAtlasContact P7 pose149 := by
  apply atlas_of_even_wall pose149 pose149_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose150_atlas : ArithmeticAtlasContact P7 pose150 := by
  apply atlas_of_even_wall pose150 pose150_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose155_atlas : ArithmeticAtlasContact P7 pose155 := by
  apply atlas_of_even_wall pose155 pose155_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose156_atlas : ArithmeticAtlasContact P7 pose156 := by
  apply atlas_of_even_wall pose156 pose156_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose158_atlas : ArithmeticAtlasContact P7 pose158 := by
  apply atlas_of_even_wall pose158 pose158_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose159_atlas : ArithmeticAtlasContact P7 pose159 := by
  apply atlas_of_even_wall pose159 pose159_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose160_atlas : ArithmeticAtlasContact P7 pose160 := by
  apply atlas_of_even_wall pose160 pose160_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose161_atlas : ArithmeticAtlasContact P7 pose161 := by
  apply atlas_of_even_wall pose161 pose161_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose162_atlas : ArithmeticAtlasContact P7 pose162 := by
  apply atlas_of_even_wall pose162 pose162_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose163_atlas : ArithmeticAtlasContact P7 pose163 := by
  apply atlas_of_even_wall pose163 pose163_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose165_atlas : ArithmeticAtlasContact P7 pose165 := by
  apply atlas_of_even_wall pose165 pose165_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose166_atlas : ArithmeticAtlasContact P7 pose166 := by
  apply atlas_of_even_wall pose166 pose166_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose180_atlas : ArithmeticAtlasContact P7 pose180 := by
  apply atlas_of_even_wall pose180 pose180_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose181_atlas : ArithmeticAtlasContact P7 pose181 := by
  apply atlas_of_even_wall pose181 pose181_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose182_atlas : ArithmeticAtlasContact P7 pose182 := by
  apply atlas_of_even_wall pose182 pose182_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose192_atlas : ArithmeticAtlasContact P7 pose192 := by
  apply atlas_of_even_wall pose192 pose192_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose193_atlas : ArithmeticAtlasContact P7 pose193 := by
  apply atlas_of_even_wall pose193 pose193_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose194_atlas : ArithmeticAtlasContact P7 pose194 := by
  apply atlas_of_even_wall pose194 pose194_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose195_atlas : ArithmeticAtlasContact P7 pose195 := by
  apply atlas_of_even_wall pose195 pose195_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose196_atlas : ArithmeticAtlasContact P7 pose196 := by
  apply atlas_of_even_wall pose196 pose196_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose197_atlas : ArithmeticAtlasContact P7 pose197 := by
  apply atlas_of_even_wall pose197 pose197_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose198_atlas : ArithmeticAtlasContact P7 pose198 := by
  apply atlas_of_even_wall pose198 pose198_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose199_atlas : ArithmeticAtlasContact P7 pose199 := by
  apply atlas_of_even_wall pose199 pose199_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose202_atlas : ArithmeticAtlasContact P7 pose202 := by
  apply atlas_of_even_wall pose202 pose202_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose203_atlas : ArithmeticAtlasContact P7 pose203 := by
  apply atlas_of_even_wall pose203 pose203_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose204_atlas : ArithmeticAtlasContact P7 pose204 := by
  apply atlas_of_even_wall pose204 pose204_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose205_atlas : ArithmeticAtlasContact P7 pose205 := by
  apply atlas_of_even_wall pose205 pose205_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose214_atlas : ArithmeticAtlasContact P7 pose214 := by
  apply atlas_of_even_wall pose214 pose214_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose217_atlas : ArithmeticAtlasContact P7 pose217 := by
  apply atlas_of_even_wall pose217 pose217_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose220_atlas : ArithmeticAtlasContact P7 pose220 := by
  apply atlas_of_even_wall pose220 pose220_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inr ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose221_atlas : ArithmeticAtlasContact P7 pose221 := by
  apply atlas_of_even_wall pose221 pose221_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose222_atlas : ArithmeticAtlasContact P7 pose222 := by
  apply atlas_of_even_wall pose222 pose222_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose225_atlas : ArithmeticAtlasContact P7 pose225 := by
  apply atlas_of_even_wall pose225 pose225_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose240_atlas : ArithmeticAtlasContact P7 pose240 := by
  apply atlas_of_even_wall pose240 pose240_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inr ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose241_atlas : ArithmeticAtlasContact P7 pose241 := by
  apply atlas_of_even_wall pose241 pose241_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose244_atlas : ArithmeticAtlasContact P7 pose244 := by
  apply atlas_of_even_wall pose244 pose244_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inr ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose245_atlas : ArithmeticAtlasContact P7 pose245 := by
  apply atlas_of_even_wall pose245 pose245_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose246_atlas : ArithmeticAtlasContact P7 pose246 := by
  apply atlas_of_even_wall pose246 pose246_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inr ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose247_atlas : ArithmeticAtlasContact P7 pose247 := by
  apply atlas_of_even_wall pose247 pose247_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose248_atlas : ArithmeticAtlasContact P7 pose248 := by
  apply atlas_of_even_wall pose248 pose248_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inr ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose249_atlas : ArithmeticAtlasContact P7 pose249 := by
  apply atlas_of_even_wall pose249 pose249_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose250_atlas : ArithmeticAtlasContact P7 pose250 := by
  apply atlas_of_even_wall pose250 pose250_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inr ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose251_atlas : ArithmeticAtlasContact P7 pose251 := by
  apply atlas_of_even_wall pose251 pose251_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose252_atlas : ArithmeticAtlasContact P7 pose252 := by
  apply atlas_of_even_wall pose252 pose252_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose254_atlas : ArithmeticAtlasContact P7 pose254 := by
  apply atlas_of_even_wall pose254 pose254_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose265_atlas : ArithmeticAtlasContact P7 pose265 := by
  apply atlas_of_even_wall pose265 pose265_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose267_atlas : ArithmeticAtlasContact P7 pose267 := by
  apply atlas_of_even_wall pose267 pose267_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose269_atlas : ArithmeticAtlasContact P7 pose269 := by
  apply atlas_of_even_wall pose269 pose269_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose270_atlas : ArithmeticAtlasContact P7 pose270 := by
  apply atlas_of_even_wall pose270 pose270_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose271_atlas : ArithmeticAtlasContact P7 pose271 := by
  apply atlas_of_even_wall pose271 pose271_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose272_atlas : ArithmeticAtlasContact P7 pose272 := by
  apply atlas_of_even_wall pose272 pose272_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose278_atlas : ArithmeticAtlasContact P7 pose278 := by
  apply atlas_of_even_wall pose278 pose278_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose280_atlas : ArithmeticAtlasContact P7 pose280 := by
  apply atlas_of_even_wall pose280 pose280_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose290_atlas : ArithmeticAtlasContact P7 pose290 := by
  apply atlas_of_even_wall pose290 pose290_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose293_atlas : ArithmeticAtlasContact P7 pose293 := by
  apply atlas_of_even_wall pose293 pose293_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose296_atlas : ArithmeticAtlasContact P7 pose296 := by
  apply atlas_of_even_wall pose296 pose296_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose297_atlas : ArithmeticAtlasContact P7 pose297 := by
  apply atlas_of_even_wall pose297 pose297_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose298_atlas : ArithmeticAtlasContact P7 pose298 := by
  apply atlas_of_even_wall pose298 pose298_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose299_atlas : ArithmeticAtlasContact P7 pose299 := by
  apply atlas_of_even_wall pose299 pose299_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose304_atlas : ArithmeticAtlasContact P7 pose304 := by
  apply atlas_of_even_wall pose304 pose304_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose306_atlas : ArithmeticAtlasContact P7 pose306 := by
  apply atlas_of_even_wall pose306 pose306_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose315_atlas : ArithmeticAtlasContact P7 pose315 := by
  apply atlas_of_even_wall pose315 pose315_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose317_atlas : ArithmeticAtlasContact P7 pose317 := by
  apply atlas_of_even_wall pose317 pose317_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose320_atlas : ArithmeticAtlasContact P7 pose320 := by
  apply atlas_of_even_wall pose320 pose320_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose321_atlas : ArithmeticAtlasContact P7 pose321 := by
  apply atlas_of_even_wall pose321 pose321_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose322_atlas : ArithmeticAtlasContact P7 pose322 := by
  apply atlas_of_even_wall pose322 pose322_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose323_atlas : ArithmeticAtlasContact P7 pose323 := by
  apply atlas_of_even_wall pose323 pose323_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose330_atlas : ArithmeticAtlasContact P7 pose330 := by
  apply atlas_of_even_wall pose330 pose330_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose332_atlas : ArithmeticAtlasContact P7 pose332 := by
  apply atlas_of_even_wall pose332 pose332_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose341_atlas : ArithmeticAtlasContact P7 pose341 := by
  apply atlas_of_even_wall pose341 pose341_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose344_atlas : ArithmeticAtlasContact P7 pose344 := by
  apply atlas_of_even_wall pose344 pose344_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose347_atlas : ArithmeticAtlasContact P7 pose347 := by
  apply atlas_of_even_wall pose347 pose347_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose349_atlas : ArithmeticAtlasContact P7 pose349 := by
  apply atlas_of_even_wall pose349 pose349_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose350_atlas : ArithmeticAtlasContact P7 pose350 := by
  apply atlas_of_even_wall pose350 pose350_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose351_atlas : ArithmeticAtlasContact P7 pose351 := by
  apply atlas_of_even_wall pose351 pose351_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose356_atlas : ArithmeticAtlasContact P7 pose356 := by
  apply atlas_of_even_wall pose356 pose356_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose358_atlas : ArithmeticAtlasContact P7 pose358 := by
  apply atlas_of_even_wall pose358 pose358_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose368_atlas : ArithmeticAtlasContact P7 pose368 := by
  apply atlas_of_even_wall pose368 pose368_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose369_atlas : ArithmeticAtlasContact P7 pose369 := by
  apply atlas_of_even_wall pose369 pose369_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose371_atlas : ArithmeticAtlasContact P7 pose371 := by
  apply atlas_of_even_wall pose371 pose371_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose373_atlas : ArithmeticAtlasContact P7 pose373 := by
  apply atlas_of_even_wall pose373 pose373_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose375_atlas : ArithmeticAtlasContact P7 pose375 := by
  apply atlas_of_even_wall pose375 pose375_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose376_atlas : ArithmeticAtlasContact P7 pose376 := by
  apply atlas_of_even_wall pose376 pose376_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose385_atlas : ArithmeticAtlasContact P7 pose385 := by
  apply atlas_of_even_wall pose385 pose385_screen (by decide)
  · refine ⟨⟨1, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose386_atlas : ArithmeticAtlasContact P7 pose386 := by
  apply atlas_of_even_wall pose386 pose386_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inr ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose388_atlas : ArithmeticAtlasContact P7 pose388 := by
  apply atlas_of_even_wall pose388 pose388_screen (by decide)
  · refine ⟨⟨0, by decide⟩, Or.inl ⟨?_, Or.inr ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose401_atlas : ArithmeticAtlasContact P7 pose401 := by
  apply atlas_of_even_wall pose401 pose401_screen (by decide)
  · refine ⟨⟨2, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose403_atlas : ArithmeticAtlasContact P7 pose403 := by
  apply atlas_of_even_wall pose403 pose403_screen (by decide)
  · refine ⟨⟨3, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose404_atlas : ArithmeticAtlasContact P7 pose404 := by
  apply atlas_of_even_wall pose404 pose404_screen (by decide)
  · refine ⟨⟨4, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose405_atlas : ArithmeticAtlasContact P7 pose405 := by
  apply atlas_of_even_wall pose405 pose405_screen (by decide)
  · refine ⟨⟨5, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

theorem pose407_atlas : ArithmeticAtlasContact P7 pose407 := by
  apply atlas_of_even_wall pose407 pose407_screen (by decide)
  · refine ⟨⟨6, by decide⟩, Or.inl ⟨?_, Or.inl ?_⟩⟩
    · apply funext; decide
    · apply funext; decide
  · unfold UnitChairCell
    decide

#print axioms pose5_atlas
end CompactT7Preparation
