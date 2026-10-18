module

public import SpectreClusters.StageDReductionLiteralReplay

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem row_ids_128 : compactIDs .t7h 128 = [8,10,13,4,2,12] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_128 : packedCertificateAt 0 .t7h 128 = ⟨2,11106,47639567715045335993324530008148641087488,27⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_128 : literalCertificateCheckB tables 0 .t7h [8,10,13,4,2,12] ⟨2,11106,47639567715045335993324530008148641087488,27⟩ = true := by rfl
private theorem row_step_128 : stepCheckB tables 0 .t7h 128 = true :=
  stepCheckB_of_literal 0 .t7h 128 [8,10,13,4,2,12] ⟨2,11106,47639567715045335993324530008148641087488,27⟩ row_ids_128 row_pack_128 row_literal_128
set_option maxRecDepth 100000 in
private theorem row_ids_129 : compactIDs .t7h 129 = [8,10,13,4,6,0] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_129 : packedCertificateAt 0 .t7h 129 = ⟨4,14961,87198767530233588624242134771339242766402,34⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_129 : literalCertificateCheckB tables 0 .t7h [8,10,13,4,6,0] ⟨4,14961,87198767530233588624242134771339242766402,34⟩ = true := by rfl
private theorem row_step_129 : stepCheckB tables 0 .t7h 129 = true :=
  stepCheckB_of_literal 0 .t7h 129 [8,10,13,4,6,0] ⟨4,14961,87198767530233588624242134771339242766402,34⟩ row_ids_129 row_pack_129 row_literal_129
set_option maxRecDepth 100000 in
private theorem row_ids_130 : compactIDs .t7h 130 = [8,10,13,4,6,7] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_130 : packedCertificateAt 0 .t7h 130 = ⟨4,14961,87198767530233588624242134771339242766402,34⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_130 : literalCertificateCheckB tables 0 .t7h [8,10,13,4,6,7] ⟨4,14961,87198767530233588624242134771339242766402,34⟩ = true := by rfl
private theorem row_step_130 : stepCheckB tables 0 .t7h 130 = true :=
  stepCheckB_of_literal 0 .t7h 130 [8,10,13,4,6,7] ⟨4,14961,87198767530233588624242134771339242766402,34⟩ row_ids_130 row_pack_130 row_literal_130
set_option maxRecDepth 100000 in
private theorem row_ids_131 : compactIDs .t7h 131 = [8,10,13,4,6,12] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_131 : packedCertificateAt 0 .t7h 131 = ⟨4,14961,87198767530233588624242134771339242766402,34⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_131 : literalCertificateCheckB tables 0 .t7h [8,10,13,4,6,12] ⟨4,14961,87198767530233588624242134771339242766402,34⟩ = true := by rfl
private theorem row_step_131 : stepCheckB tables 0 .t7h 131 = true :=
  stepCheckB_of_literal 0 .t7h 131 [8,10,13,4,6,12] ⟨4,14961,87198767530233588624242134771339242766402,34⟩ row_ids_131 row_pack_131 row_literal_131
set_option maxRecDepth 100000 in
private theorem row_ids_132 : compactIDs .t7h 132 = [8,10,13,4,9,0] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_132 : packedCertificateAt 0 .t7h 132 = ⟨9,1509651509093,299541269060337061517647943921329362835773207324625676197703814835672633782025842053780598670030742152757464758834270568565,77⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_132 : literalCertificateCheckB tables 0 .t7h [8,10,13,4,9,0] ⟨9,1509651509093,299541269060337061517647943921329362835773207324625676197703814835672633782025842053780598670030742152757464758834270568565,77⟩ = true := by rfl
private theorem row_step_132 : stepCheckB tables 0 .t7h 132 = true :=
  stepCheckB_of_literal 0 .t7h 132 [8,10,13,4,9,0] ⟨9,1509651509093,299541269060337061517647943921329362835773207324625676197703814835672633782025842053780598670030742152757464758834270568565,77⟩ row_ids_132 row_pack_132 row_literal_132
set_option maxRecDepth 100000 in
private theorem row_ids_133 : compactIDs .t7h 133 = [8,10,13,4,9,7] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_133 : packedCertificateAt 0 .t7h 133 = ⟨9,1509651509093,299541269060337095920127215812207605651132057395592680927415926080466998925062582865376358687296488645337981495486456004740,77⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_133 : literalCertificateCheckB tables 0 .t7h [8,10,13,4,9,7] ⟨9,1509651509093,299541269060337095920127215812207605651132057395592680927415926080466998925062582865376358687296488645337981495486456004740,77⟩ = true := by rfl
private theorem row_step_133 : stepCheckB tables 0 .t7h 133 = true :=
  stepCheckB_of_literal 0 .t7h 133 [8,10,13,4,9,7] ⟨9,1509651509093,299541269060337095920127215812207605651132057395592680927415926080466998925062582865376358687296488645337981495486456004740,77⟩ row_ids_133 row_pack_133 row_literal_133
private theorem row_step_134 : stepCheckB tables 0 .t7h 134 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
set_option maxRecDepth 100000 in
private theorem row_ids_135 : compactIDs .t7h 135 = [8,10,13,11,2,0] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_135 : packedCertificateAt 0 .t7h 135 = ⟨0,11126,4083390999205892618441615864546212193280,29⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_135 : literalCertificateCheckB tables 0 .t7h [8,10,13,11,2,0] ⟨0,11126,4083390999205892618441615864546212193280,29⟩ = true := by rfl
private theorem row_step_135 : stepCheckB tables 0 .t7h 135 = true :=
  stepCheckB_of_literal 0 .t7h 135 [8,10,13,11,2,0] ⟨0,11126,4083390999205892618441615864546212193280,29⟩ row_ids_135 row_pack_135 row_literal_135
private theorem row_step_136 : stepCheckB tables 0 .t7h 136 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
set_option maxRecDepth 100000 in
private theorem row_ids_137 : compactIDs .t7h 137 = [8,10,13,11,2,12] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_137 : packedCertificateAt 0 .t7h 137 = ⟨2,10598,47639567715009435732185253980176598990848,20⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_137 : literalCertificateCheckB tables 0 .t7h [8,10,13,11,2,12] ⟨2,10598,47639567715009435732185253980176598990848,20⟩ = true := by rfl
private theorem row_step_137 : stepCheckB tables 0 .t7h 137 = true :=
  stepCheckB_of_literal 0 .t7h 137 [8,10,13,11,2,12] ⟨2,10598,47639567715009435732185253980176598990848,20⟩ row_ids_137 row_pack_137 row_literal_137
set_option maxRecDepth 100000 in
private theorem row_ids_138 : compactIDs .t7h 138 = [8,10,13,11,6,0] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_138 : packedCertificateAt 0 .t7h 138 = ⟨0,11126,4083390999209606438559472005370912711680,29⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_138 : literalCertificateCheckB tables 0 .t7h [8,10,13,11,6,0] ⟨0,11126,4083390999209606438559472005370912711680,29⟩ = true := by rfl
private theorem row_step_138 : stepCheckB tables 0 .t7h 138 = true :=
  stepCheckB_of_literal 0 .t7h 138 [8,10,13,11,6,0] ⟨0,11126,4083390999209606438559472005370912711680,29⟩ row_ids_138 row_pack_138 row_literal_138
private theorem row_step_139 : stepCheckB tables 0 .t7h 139 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_140 : stepCheckB tables 0 .t7h 140 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
set_option maxRecDepth 100000 in
private theorem row_ids_141 : compactIDs .t7h 141 = [8,10,13,11,9,0] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_141 : packedCertificateAt 0 .t7h 141 = ⟨9,1509517291493,299541269060337061517647943921329362835526614638712459830870651288862371874482110348278309136428757659495305458479183954037,76⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_141 : literalCertificateCheckB tables 0 .t7h [8,10,13,11,9,0] ⟨9,1509517291493,299541269060337061517647943921329362835526614638712459830870651288862371874482110348278309136428757659495305458479183954037,76⟩ = true := by rfl
private theorem row_step_141 : stepCheckB tables 0 .t7h 141 = true :=
  stepCheckB_of_literal 0 .t7h 141 [8,10,13,11,9,0] ⟨9,1509517291493,299541269060337061517647943921329362835526614638712459830870651288862371874482110348278309136428757659495305458479183954037,76⟩ row_ids_141 row_pack_141 row_literal_141
set_option maxRecDepth 100000 in
private theorem row_ids_142 : compactIDs .t7h 142 = [8,10,13,11,9,7] := by rfl
set_option maxRecDepth 100000 in
private theorem row_pack_142 : packedCertificateAt 0 .t7h 142 = ⟨9,1509517291493,299541269060337095920127215812207605650885464709679464560582762533656737017518851159874069153694504152075822195131369390212,76⟩ := by rfl
set_option maxRecDepth 100000 in
private theorem row_literal_142 : literalCertificateCheckB tables 0 .t7h [8,10,13,11,9,7] ⟨9,1509517291493,299541269060337095920127215812207605650885464709679464560582762533656737017518851159874069153694504152075822195131369390212,76⟩ = true := by rfl
private theorem row_step_142 : stepCheckB tables 0 .t7h 142 = true :=
  stepCheckB_of_literal 0 .t7h 142 [8,10,13,11,9,7] ⟨9,1509517291493,299541269060337095920127215812207605650885464709679464560582762533656737017518851159874069153694504152075822195131369390212,76⟩ row_ids_142 row_pack_142 row_literal_142
private theorem row_step_143 : stepCheckB tables 0 .t7h 143 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
theorem rowPart0T7H2_checked : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143].all (stepCheckB tables 0 .t7h) = true := by
  simp only [List.all_cons,List.all_nil,row_step_128,row_step_129,row_step_130,row_step_131,row_step_132,row_step_133,row_step_134,row_step_135,row_step_136,row_step_137,row_step_138,row_step_139,row_step_140,row_step_141,row_step_142,row_step_143,Bool.true_and]
end SpectreClusters.StageD.Reduction
