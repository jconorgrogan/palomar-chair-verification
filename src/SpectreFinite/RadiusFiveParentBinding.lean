module

public import SpectreFinite.RadiusFivePruningLiteral
public import SpectreFinite.RadiusFiveParentBindingPart000
public import SpectreFinite.RadiusFiveParentBindingPart001
public import SpectreFinite.RadiusFiveParentBindingPart002
public import SpectreFinite.RadiusFiveParentBindingPart003
public import SpectreFinite.RadiusFiveParentBindingPart004
public import SpectreFinite.RadiusFiveParentBindingPart005
public import SpectreFinite.RadiusFiveParentBindingPart006
public import SpectreFinite.RadiusFiveParentBindingPart007
public import SpectreFinite.RadiusFiveParentBindingPart008
public import SpectreFinite.RadiusFiveParentBindingPart009
public import SpectreFinite.RadiusFiveParentBindingPart010
public import SpectreFinite.RadiusFiveParentBindingPart011
public import SpectreFinite.RadiusFiveParentBindingPart012
public import SpectreFinite.RadiusFiveParentBindingPart013
public import SpectreFinite.RadiusFiveParentBindingPart014
public import SpectreFinite.RadiusFiveParentBindingPart015
public import SpectreFinite.RadiusFiveParentBindingPart016
public import SpectreFinite.RadiusFiveParentBindingPart017
public import SpectreFinite.RadiusFiveParentBindingPart018
public import SpectreFinite.RadiusFiveParentBindingPart019
public import SpectreFinite.RadiusFiveParentBindingPart020
public import SpectreFinite.RadiusFiveParentBindingPart021
public import SpectreFinite.RadiusFiveParentBindingPart022
public import SpectreFinite.RadiusFiveParentBindingPart023
public import SpectreFinite.RadiusFiveParentBindingPart024
public import SpectreFinite.RadiusFiveParentBindingPart025
public import SpectreFinite.RadiusFiveParentBindingPart026
public import SpectreFinite.RadiusFiveParentBindingPart027
public import SpectreFinite.RadiusFiveParentBindingPart028
public import SpectreFinite.RadiusFiveParentBindingPart029
public import SpectreFinite.RadiusFiveParentBindingPart030
public import SpectreFinite.RadiusFiveParentBindingPart031
public import SpectreFinite.RadiusFiveParentBindingPart032
public import SpectreFinite.RadiusFiveParentBindingPart033
public import SpectreFinite.RadiusFiveParentBindingPart034
public import SpectreFinite.RadiusFiveParentBindingPart035
public import SpectreFinite.RadiusFiveParentBindingPart036
public import SpectreFinite.RadiusFiveParentBindingPart037
public import SpectreFinite.RadiusFiveParentBindingPart038
public import SpectreFinite.RadiusFiveParentBindingPart039
public import SpectreFinite.RadiusFiveParentBindingPart040
public import SpectreFinite.RadiusFiveParentBindingPart041
public import SpectreFinite.RadiusFiveParentBindingPart042
public import SpectreFinite.RadiusFiveParentBindingPart043
public import SpectreFinite.RadiusFiveParentBindingPart044
public import SpectreFinite.RadiusFiveParentBindingPart045
public import SpectreFinite.RadiusFiveParentBindingPart046
public import SpectreFinite.RadiusFiveParentBindingPart047
public import SpectreFinite.RadiusFiveParentBindingPart048
public import SpectreFinite.RadiusFiveParentBindingPart049
public import SpectreFinite.RadiusFiveParentBindingPart050
public import SpectreFinite.RadiusFiveParentBindingPart051
public import SpectreFinite.RadiusFiveParentBindingPart052
public import SpectreFinite.RadiusFiveParentBindingPart053
public import SpectreFinite.RadiusFiveParentBindingPart054
public import SpectreFinite.RadiusFiveParentBindingPart055
public import SpectreFinite.RadiusFiveParentBindingPart056
public import SpectreFinite.RadiusFiveParentBindingPart057
public import SpectreFinite.RadiusFiveParentBindingPart058
public import SpectreFinite.RadiusFiveParentBindingPart059

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def sourceChunks : List (List Patch) := [RadiusFivePruning.final0_0_0, RadiusFivePruning.final0_0_1, RadiusFivePruning.final0_0_2, RadiusFivePruning.final0_0_3, RadiusFivePruning.final0_0_4, RadiusFivePruning.final0_1_0, RadiusFivePruning.final0_1_1, RadiusFivePruning.final0_1_2, RadiusFivePruning.final0_1_3, RadiusFivePruning.final0_1_4, RadiusFivePruning.final0_2_0, RadiusFivePruning.final0_2_1, RadiusFivePruning.final0_2_2, RadiusFivePruning.final0_2_3, RadiusFivePruning.final0_2_4, RadiusFivePruning.final0_3_0, RadiusFivePruning.final0_3_1, RadiusFivePruning.final0_3_2, RadiusFivePruning.final0_3_3, RadiusFivePruning.final0_3_4, RadiusFivePruning.final0_4_0, RadiusFivePruning.final0_4_1, RadiusFivePruning.final0_4_2, RadiusFivePruning.final0_4_3, RadiusFivePruning.final0_4_4, RadiusFivePruning.final0_5_0, RadiusFivePruning.final0_5_1, RadiusFivePruning.final0_5_2, RadiusFivePruning.final0_5_3, RadiusFivePruning.final0_5_4, RadiusFivePruning.final1_0_0, RadiusFivePruning.final1_0_1, RadiusFivePruning.final1_0_2, RadiusFivePruning.final1_0_3, RadiusFivePruning.final1_0_4, RadiusFivePruning.final1_1_0, RadiusFivePruning.final1_1_1, RadiusFivePruning.final1_1_2, RadiusFivePruning.final1_1_3, RadiusFivePruning.final1_1_4, RadiusFivePruning.final1_2_0, RadiusFivePruning.final1_2_1, RadiusFivePruning.final1_2_2, RadiusFivePruning.final1_2_3, RadiusFivePruning.final1_2_4, RadiusFivePruning.final1_3_0, RadiusFivePruning.final1_3_1, RadiusFivePruning.final1_3_2, RadiusFivePruning.final1_3_3, RadiusFivePruning.final1_3_4, RadiusFivePruning.final1_4_0, RadiusFivePruning.final1_4_1, RadiusFivePruning.final1_4_2, RadiusFivePruning.final1_4_3, RadiusFivePruning.final1_4_4, RadiusFivePruning.final1_5_0, RadiusFivePruning.final1_5_1, RadiusFivePruning.final1_5_2, RadiusFivePruning.final1_5_3, RadiusFivePruning.final1_5_4, RadiusFivePruning.final2_0_0, RadiusFivePruning.final2_1_0, RadiusFivePruning.final2_2_0, RadiusFivePruning.final2_3_0, RadiusFivePruning.final2_4_0, RadiusFivePruning.final2_5_0, RadiusFivePruning.final3_0_0, RadiusFivePruning.final3_1_0, RadiusFivePruning.final3_2_0, RadiusFivePruning.final3_3_0, RadiusFivePruning.final3_4_0, RadiusFivePruning.final3_5_0, RadiusFivePruning.final4_0_0, RadiusFivePruning.final4_0_1, RadiusFivePruning.final4_0_2, RadiusFivePruning.final4_0_3, RadiusFivePruning.final4_1_0, RadiusFivePruning.final4_1_1, RadiusFivePruning.final4_1_2, RadiusFivePruning.final4_1_3, RadiusFivePruning.final4_2_0, RadiusFivePruning.final4_2_1, RadiusFivePruning.final4_2_2, RadiusFivePruning.final4_2_3, RadiusFivePruning.final4_3_0, RadiusFivePruning.final4_3_1, RadiusFivePruning.final4_3_2, RadiusFivePruning.final4_3_3, RadiusFivePruning.final4_4_0, RadiusFivePruning.final4_4_1, RadiusFivePruning.final4_4_2, RadiusFivePruning.final4_4_3, RadiusFivePruning.final4_5_0, RadiusFivePruning.final4_5_1, RadiusFivePruning.final4_5_2, RadiusFivePruning.final4_5_3, RadiusFivePruning.final5_0_0, RadiusFivePruning.final5_0_1, RadiusFivePruning.final5_0_2, RadiusFivePruning.final5_1_0, RadiusFivePruning.final5_1_1, RadiusFivePruning.final5_1_2, RadiusFivePruning.final5_2_0, RadiusFivePruning.final5_2_1, RadiusFivePruning.final5_2_2, RadiusFivePruning.final5_3_0, RadiusFivePruning.final5_3_1, RadiusFivePruning.final5_3_2, RadiusFivePruning.final5_4_0, RadiusFivePruning.final5_4_1, RadiusFivePruning.final5_4_2, RadiusFivePruning.final5_5_0, RadiusFivePruning.final5_5_1, RadiusFivePruning.final5_5_2, RadiusFivePruning.final6_0_0, RadiusFivePruning.final6_0_1, RadiusFivePruning.final6_0_2, RadiusFivePruning.final6_0_3, RadiusFivePruning.final6_0_4, RadiusFivePruning.final6_0_5, RadiusFivePruning.final6_1_0, RadiusFivePruning.final6_1_1, RadiusFivePruning.final6_1_2, RadiusFivePruning.final6_1_3, RadiusFivePruning.final6_1_4, RadiusFivePruning.final6_1_5, RadiusFivePruning.final6_2_0, RadiusFivePruning.final6_2_1, RadiusFivePruning.final6_2_2, RadiusFivePruning.final6_2_3, RadiusFivePruning.final6_2_4, RadiusFivePruning.final6_2_5, RadiusFivePruning.final6_3_0, RadiusFivePruning.final6_3_1, RadiusFivePruning.final6_3_2, RadiusFivePruning.final6_3_3, RadiusFivePruning.final6_3_4, RadiusFivePruning.final6_3_5, RadiusFivePruning.final6_4_0, RadiusFivePruning.final6_4_1, RadiusFivePruning.final6_4_2, RadiusFivePruning.final6_4_3, RadiusFivePruning.final6_4_4, RadiusFivePruning.final6_4_5, RadiusFivePruning.final6_5_0, RadiusFivePruning.final6_5_1, RadiusFivePruning.final6_5_2, RadiusFivePruning.final6_5_3, RadiusFivePruning.final6_5_4, RadiusFivePruning.final6_5_5, RadiusFivePruning.final7_0_0, RadiusFivePruning.final7_0_1, RadiusFivePruning.final7_0_2, RadiusFivePruning.final7_0_3, RadiusFivePruning.final7_0_4, RadiusFivePruning.final7_0_5, RadiusFivePruning.final7_0_6, RadiusFivePruning.final7_0_7, RadiusFivePruning.final7_0_8, RadiusFivePruning.final7_1_0, RadiusFivePruning.final7_1_1, RadiusFivePruning.final7_1_2, RadiusFivePruning.final7_1_3, RadiusFivePruning.final7_1_4, RadiusFivePruning.final7_1_5, RadiusFivePruning.final7_1_6, RadiusFivePruning.final7_1_7, RadiusFivePruning.final7_1_8, RadiusFivePruning.final7_2_0, RadiusFivePruning.final7_2_1, RadiusFivePruning.final7_2_2, RadiusFivePruning.final7_2_3, RadiusFivePruning.final7_2_4, RadiusFivePruning.final7_2_5, RadiusFivePruning.final7_2_6, RadiusFivePruning.final7_2_7, RadiusFivePruning.final7_2_8, RadiusFivePruning.final7_3_0, RadiusFivePruning.final7_3_1, RadiusFivePruning.final7_3_2, RadiusFivePruning.final7_3_3, RadiusFivePruning.final7_3_4, RadiusFivePruning.final7_3_5, RadiusFivePruning.final7_3_6, RadiusFivePruning.final7_3_7, RadiusFivePruning.final7_3_8, RadiusFivePruning.final7_4_0, RadiusFivePruning.final7_4_1, RadiusFivePruning.final7_4_2, RadiusFivePruning.final7_4_3, RadiusFivePruning.final7_4_4, RadiusFivePruning.final7_4_5, RadiusFivePruning.final7_4_6, RadiusFivePruning.final7_4_7, RadiusFivePruning.final7_4_8, RadiusFivePruning.final7_5_0, RadiusFivePruning.final7_5_1, RadiusFivePruning.final7_5_2, RadiusFivePruning.final7_5_3, RadiusFivePruning.final7_5_4, RadiusFivePruning.final7_5_5, RadiusFivePruning.final7_5_6, RadiusFivePruning.final7_5_7, RadiusFivePruning.final7_5_8, RadiusFivePruning.final8_0_0, RadiusFivePruning.final8_0_1, RadiusFivePruning.final8_0_2, RadiusFivePruning.final8_0_3, RadiusFivePruning.final8_0_4, RadiusFivePruning.final8_0_5, RadiusFivePruning.final8_1_0, RadiusFivePruning.final8_1_1, RadiusFivePruning.final8_1_2, RadiusFivePruning.final8_1_3, RadiusFivePruning.final8_1_4, RadiusFivePruning.final8_1_5, RadiusFivePruning.final8_2_0, RadiusFivePruning.final8_2_1, RadiusFivePruning.final8_2_2, RadiusFivePruning.final8_2_3, RadiusFivePruning.final8_2_4, RadiusFivePruning.final8_2_5, RadiusFivePruning.final8_3_0, RadiusFivePruning.final8_3_1, RadiusFivePruning.final8_3_2, RadiusFivePruning.final8_3_3, RadiusFivePruning.final8_3_4, RadiusFivePruning.final8_3_5, RadiusFivePruning.final8_4_0, RadiusFivePruning.final8_4_1, RadiusFivePruning.final8_4_2, RadiusFivePruning.final8_4_3, RadiusFivePruning.final8_4_4, RadiusFivePruning.final8_4_5, RadiusFivePruning.final8_5_0, RadiusFivePruning.final8_5_1, RadiusFivePruning.final8_5_2, RadiusFivePruning.final8_5_3, RadiusFivePruning.final8_5_4, RadiusFivePruning.final8_5_5]
theorem sourceFamily_eq_flatten : RadiusFivePruning.certifiedFamily = sourceChunks.flatten := by rfl
theorem sourceChunks_covered : ∀ chunk ∈ sourceChunks, ∀ p ∈ chunk, p ∈ ParentOwnership.certifiedParentFamily := by
  simp only [sourceChunks, List.forall_mem_cons]
  exact ⟨chunk_mem0_0_0,⟨chunk_mem0_0_1,⟨chunk_mem0_0_2,⟨chunk_mem0_0_3,⟨chunk_mem0_0_4,⟨chunk_mem0_1_0,⟨chunk_mem0_1_1,⟨chunk_mem0_1_2,⟨chunk_mem0_1_3,⟨chunk_mem0_1_4,⟨chunk_mem0_2_0,⟨chunk_mem0_2_1,⟨chunk_mem0_2_2,⟨chunk_mem0_2_3,⟨chunk_mem0_2_4,⟨chunk_mem0_3_0,⟨chunk_mem0_3_1,⟨chunk_mem0_3_2,⟨chunk_mem0_3_3,⟨chunk_mem0_3_4,⟨chunk_mem0_4_0,⟨chunk_mem0_4_1,⟨chunk_mem0_4_2,⟨chunk_mem0_4_3,⟨chunk_mem0_4_4,⟨chunk_mem0_5_0,⟨chunk_mem0_5_1,⟨chunk_mem0_5_2,⟨chunk_mem0_5_3,⟨chunk_mem0_5_4,⟨chunk_mem1_0_0,⟨chunk_mem1_0_1,⟨chunk_mem1_0_2,⟨chunk_mem1_0_3,⟨chunk_mem1_0_4,⟨chunk_mem1_1_0,⟨chunk_mem1_1_1,⟨chunk_mem1_1_2,⟨chunk_mem1_1_3,⟨chunk_mem1_1_4,⟨chunk_mem1_2_0,⟨chunk_mem1_2_1,⟨chunk_mem1_2_2,⟨chunk_mem1_2_3,⟨chunk_mem1_2_4,⟨chunk_mem1_3_0,⟨chunk_mem1_3_1,⟨chunk_mem1_3_2,⟨chunk_mem1_3_3,⟨chunk_mem1_3_4,⟨chunk_mem1_4_0,⟨chunk_mem1_4_1,⟨chunk_mem1_4_2,⟨chunk_mem1_4_3,⟨chunk_mem1_4_4,⟨chunk_mem1_5_0,⟨chunk_mem1_5_1,⟨chunk_mem1_5_2,⟨chunk_mem1_5_3,⟨chunk_mem1_5_4,⟨chunk_mem2_0_0,⟨chunk_mem2_1_0,⟨chunk_mem2_2_0,⟨chunk_mem2_3_0,⟨chunk_mem2_4_0,⟨chunk_mem2_5_0,⟨chunk_mem3_0_0,⟨chunk_mem3_1_0,⟨chunk_mem3_2_0,⟨chunk_mem3_3_0,⟨chunk_mem3_4_0,⟨chunk_mem3_5_0,⟨chunk_mem4_0_0,⟨chunk_mem4_0_1,⟨chunk_mem4_0_2,⟨chunk_mem4_0_3,⟨chunk_mem4_1_0,⟨chunk_mem4_1_1,⟨chunk_mem4_1_2,⟨chunk_mem4_1_3,⟨chunk_mem4_2_0,⟨chunk_mem4_2_1,⟨chunk_mem4_2_2,⟨chunk_mem4_2_3,⟨chunk_mem4_3_0,⟨chunk_mem4_3_1,⟨chunk_mem4_3_2,⟨chunk_mem4_3_3,⟨chunk_mem4_4_0,⟨chunk_mem4_4_1,⟨chunk_mem4_4_2,⟨chunk_mem4_4_3,⟨chunk_mem4_5_0,⟨chunk_mem4_5_1,⟨chunk_mem4_5_2,⟨chunk_mem4_5_3,⟨chunk_mem5_0_0,⟨chunk_mem5_0_1,⟨chunk_mem5_0_2,⟨chunk_mem5_1_0,⟨chunk_mem5_1_1,⟨chunk_mem5_1_2,⟨chunk_mem5_2_0,⟨chunk_mem5_2_1,⟨chunk_mem5_2_2,⟨chunk_mem5_3_0,⟨chunk_mem5_3_1,⟨chunk_mem5_3_2,⟨chunk_mem5_4_0,⟨chunk_mem5_4_1,⟨chunk_mem5_4_2,⟨chunk_mem5_5_0,⟨chunk_mem5_5_1,⟨chunk_mem5_5_2,⟨chunk_mem6_0_0,⟨chunk_mem6_0_1,⟨chunk_mem6_0_2,⟨chunk_mem6_0_3,⟨chunk_mem6_0_4,⟨chunk_mem6_0_5,⟨chunk_mem6_1_0,⟨chunk_mem6_1_1,⟨chunk_mem6_1_2,⟨chunk_mem6_1_3,⟨chunk_mem6_1_4,⟨chunk_mem6_1_5,⟨chunk_mem6_2_0,⟨chunk_mem6_2_1,⟨chunk_mem6_2_2,⟨chunk_mem6_2_3,⟨chunk_mem6_2_4,⟨chunk_mem6_2_5,⟨chunk_mem6_3_0,⟨chunk_mem6_3_1,⟨chunk_mem6_3_2,⟨chunk_mem6_3_3,⟨chunk_mem6_3_4,⟨chunk_mem6_3_5,⟨chunk_mem6_4_0,⟨chunk_mem6_4_1,⟨chunk_mem6_4_2,⟨chunk_mem6_4_3,⟨chunk_mem6_4_4,⟨chunk_mem6_4_5,⟨chunk_mem6_5_0,⟨chunk_mem6_5_1,⟨chunk_mem6_5_2,⟨chunk_mem6_5_3,⟨chunk_mem6_5_4,⟨chunk_mem6_5_5,⟨chunk_mem7_0_0,⟨chunk_mem7_0_1,⟨chunk_mem7_0_2,⟨chunk_mem7_0_3,⟨chunk_mem7_0_4,⟨chunk_mem7_0_5,⟨chunk_mem7_0_6,⟨chunk_mem7_0_7,⟨chunk_mem7_0_8,⟨chunk_mem7_1_0,⟨chunk_mem7_1_1,⟨chunk_mem7_1_2,⟨chunk_mem7_1_3,⟨chunk_mem7_1_4,⟨chunk_mem7_1_5,⟨chunk_mem7_1_6,⟨chunk_mem7_1_7,⟨chunk_mem7_1_8,⟨chunk_mem7_2_0,⟨chunk_mem7_2_1,⟨chunk_mem7_2_2,⟨chunk_mem7_2_3,⟨chunk_mem7_2_4,⟨chunk_mem7_2_5,⟨chunk_mem7_2_6,⟨chunk_mem7_2_7,⟨chunk_mem7_2_8,⟨chunk_mem7_3_0,⟨chunk_mem7_3_1,⟨chunk_mem7_3_2,⟨chunk_mem7_3_3,⟨chunk_mem7_3_4,⟨chunk_mem7_3_5,⟨chunk_mem7_3_6,⟨chunk_mem7_3_7,⟨chunk_mem7_3_8,⟨chunk_mem7_4_0,⟨chunk_mem7_4_1,⟨chunk_mem7_4_2,⟨chunk_mem7_4_3,⟨chunk_mem7_4_4,⟨chunk_mem7_4_5,⟨chunk_mem7_4_6,⟨chunk_mem7_4_7,⟨chunk_mem7_4_8,⟨chunk_mem7_5_0,⟨chunk_mem7_5_1,⟨chunk_mem7_5_2,⟨chunk_mem7_5_3,⟨chunk_mem7_5_4,⟨chunk_mem7_5_5,⟨chunk_mem7_5_6,⟨chunk_mem7_5_7,⟨chunk_mem7_5_8,⟨chunk_mem8_0_0,⟨chunk_mem8_0_1,⟨chunk_mem8_0_2,⟨chunk_mem8_0_3,⟨chunk_mem8_0_4,⟨chunk_mem8_0_5,⟨chunk_mem8_1_0,⟨chunk_mem8_1_1,⟨chunk_mem8_1_2,⟨chunk_mem8_1_3,⟨chunk_mem8_1_4,⟨chunk_mem8_1_5,⟨chunk_mem8_2_0,⟨chunk_mem8_2_1,⟨chunk_mem8_2_2,⟨chunk_mem8_2_3,⟨chunk_mem8_2_4,⟨chunk_mem8_2_5,⟨chunk_mem8_3_0,⟨chunk_mem8_3_1,⟨chunk_mem8_3_2,⟨chunk_mem8_3_3,⟨chunk_mem8_3_4,⟨chunk_mem8_3_5,⟨chunk_mem8_4_0,⟨chunk_mem8_4_1,⟨chunk_mem8_4_2,⟨chunk_mem8_4_3,⟨chunk_mem8_4_4,⟨chunk_mem8_4_5,⟨chunk_mem8_5_0,⟨chunk_mem8_5_1,⟨chunk_mem8_5_2,⟨chunk_mem8_5_3,⟨chunk_mem8_5_4,⟨chunk_mem8_5_5,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem family_subset_parentFamily : ∀ p ∈ RadiusFivePruning.certifiedFamily, p ∈ ParentOwnership.certifiedParentFamily := by
  intro p hp
  rw [sourceFamily_eq_flatten] at hp
  obtain ⟨chunk,hc,hp⟩ := List.mem_flatten.mp hp
  exact sourceChunks_covered chunk hc p hp
theorem occurrenceComplete_transfer (f : Position → State) (hf : OccurrenceComplete f (hexRegion 5) RadiusFivePruning.certifiedFamily) : OccurrenceComplete f (hexRegion 5) ParentOwnership.certifiedParentFamily := fun center => family_subset_parentFamily _ (hf center)
#print axioms family_subset_parentFamily
#print axioms occurrenceComplete_transfer

end SpectreFinite.HexSearch.RadiusFiveParentBinding
