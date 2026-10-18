module

public import SpectreFinite.ParentBoundaryCensus
public import SpectreFinite.ParentBoundaryFrameRow0064
public import SpectreFinite.ParentBoundaryFrameRow0065
public import SpectreFinite.ParentBoundaryFrameRow0070
public import SpectreFinite.ParentBoundaryFrameRow0071
public import SpectreFinite.ParentBoundaryFrameRow0072
public import SpectreFinite.ParentBoundaryFrameRow0080
public import SpectreFinite.ParentBoundaryFrameRow0102
public import SpectreFinite.ParentBoundaryFrameRow0103
public import SpectreFinite.ParentBoundaryFrameRow0104
public import SpectreFinite.ParentBoundaryFrameRow0105
public import SpectreFinite.ParentBoundaryFrameRow0106
public import SpectreFinite.ParentBoundaryFrameRow0107
public import SpectreFinite.ParentBoundaryFrameRow0108
public import SpectreFinite.ParentBoundaryFrameRow0109
public import SpectreFinite.ParentBoundaryFrameRow0110
public import SpectreFinite.ParentBoundaryFrameRow0111
public import SpectreFinite.ParentBoundaryFrameRow0112
public import SpectreFinite.ParentBoundaryFrameRow0308
public import SpectreFinite.ParentBoundaryFrameRow0309
public import SpectreFinite.ParentBoundaryFrameRow0514
public import SpectreFinite.ParentBoundaryFrameRow1074
public import SpectreFinite.ParentBoundaryFrameRow1075
public import SpectreFinite.ParentBoundaryFrameRow1262
public import SpectreFinite.ParentBoundaryFrameRow1263
public import SpectreFinite.ParentBoundaryFrameRow1264
public import SpectreFinite.ParentBoundaryFrameRow1265
public import SpectreFinite.ParentBoundaryFrameRow1266
public import SpectreFinite.ParentBoundaryFrameRow1273
public import SpectreFinite.ParentBoundaryFrameRow1274
public import SpectreFinite.ParentBoundaryFrameRow1275
public import SpectreFinite.ParentBoundaryFrameRow1276
public import SpectreFinite.ParentBoundaryFrameRow1277
public import SpectreFinite.ParentBoundaryFrameRow1278
public import SpectreFinite.ParentBoundaryFrameRow1279
public import SpectreFinite.ParentBoundaryFrameRow1280
public import SpectreFinite.ParentBoundaryFrameRow1281
public import SpectreFinite.ParentBoundaryFrameRow1282
public import SpectreFinite.ParentBoundaryFrameRow1283
public import SpectreFinite.ParentBoundaryFrameRow1284
public import SpectreFinite.ParentBoundaryFrameRow1285
public import SpectreFinite.ParentBoundaryFrameRow1287
public import SpectreFinite.ParentBoundaryFrameRow1288
public import SpectreFinite.ParentBoundaryFrameRow1289
public import SpectreFinite.ParentBoundaryFrameRow1290
public import SpectreFinite.ParentBoundaryFrameRow1291

@[expose] public section


/-! All Gamma-zero cases of the literal2112-row family, with exact adjacent
frames, opposite paired directions and full three-parent triangle interfaces.
Occurrence completeness and global nine-shape binding remain explicit premises. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

theorem gammaBoundaryRows_framed : ∀ row ∈ gammaBoundaryRows,
    FramedRootStructure (indexedField row) := by
  simp only [gammaBoundaryRows, List.forall_mem_cons]
  exact ⟨boundaryFrameRow0064_structure,⟨boundaryFrameRow0065_structure,⟨boundaryFrameRow0070_structure,⟨boundaryFrameRow0071_structure,⟨boundaryFrameRow0072_structure,⟨boundaryFrameRow0080_structure,⟨boundaryFrameRow0102_structure,⟨boundaryFrameRow0103_structure,⟨boundaryFrameRow0104_structure,⟨boundaryFrameRow0105_structure,⟨boundaryFrameRow0106_structure,⟨boundaryFrameRow0107_structure,⟨boundaryFrameRow0108_structure,⟨boundaryFrameRow0109_structure,⟨boundaryFrameRow0110_structure,⟨boundaryFrameRow0111_structure,⟨boundaryFrameRow0112_structure,⟨boundaryFrameRow0308_structure,⟨boundaryFrameRow0309_structure,⟨boundaryFrameRow0514_structure,⟨boundaryFrameRow1074_structure,⟨boundaryFrameRow1075_structure,⟨boundaryFrameRow1262_structure,⟨boundaryFrameRow1263_structure,⟨boundaryFrameRow1264_structure,⟨boundaryFrameRow1265_structure,⟨boundaryFrameRow1266_structure,⟨boundaryFrameRow1273_structure,⟨boundaryFrameRow1274_structure,⟨boundaryFrameRow1275_structure,⟨boundaryFrameRow1276_structure,⟨boundaryFrameRow1277_structure,⟨boundaryFrameRow1278_structure,⟨boundaryFrameRow1279_structure,⟨boundaryFrameRow1280_structure,⟨boundaryFrameRow1281_structure,⟨boundaryFrameRow1282_structure,⟨boundaryFrameRow1283_structure,⟨boundaryFrameRow1284_structure,⟨boundaryFrameRow1285_structure,⟨boundaryFrameRow1287_structure,⟨boundaryFrameRow1288_structure,⟨boundaryFrameRow1289_structure,⟨boundaryFrameRow1290_structure,⟨boundaryFrameRow1291_structure,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem certifiedParentRows_frames : ∀ row ∈ certifiedParentRows,
    indexedField row (0,0) = (0,0) → FramedRootStructure (indexedField row) := by
  intro row hr hg
  have hm : row ∈ certifiedParentRows.filter gammaRoot :=
    List.mem_filter.mpr ⟨hr,decide_eq_true hg⟩
  rw [gammaBoundaryRows_exact] at hm
  exact gammaBoundaryRows_framed row hm

theorem certifiedParentFamily_frames : ∀ p ∈ certifiedParentFamily,
    patchState p (0,0) = (0,0) → FramedRootStructure (patchState p) := by
  intro p hp hg
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hp
  rw [encodedPatch_root] at hg
  exact framedRootStructure_encodedPatch row (certifiedParentRows_frames row hr hg)

theorem frames_of_certifiedParentFamily (f : Position → State)
    (hocc : OccurrenceComplete f (hexRegion 5) certifiedParentFamily)
    (center : Position) (hg : f center = (0,0)) :
    FramedRootStructure (shiftedField f center) :=
  frames_of_radiusFive_certificate certifiedParentFamily
    certifiedParentFamily_frames f hocc center hg

#print axioms gammaBoundaryRows_framed
#print axioms certifiedParentRows_frames
#print axioms certifiedParentFamily_frames
#print axioms frames_of_certifiedParentFamily
end SpectreFinite.HexSearch.ParentBoundary
