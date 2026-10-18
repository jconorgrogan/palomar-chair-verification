module

public import SpectreGeometry.ReverseInverseTileFacesData
public import SpectreGeometry.ReverseClusterTriangulationFacesAssemblyReal

@[expose] public section


namespace SpectreGeometry.ReverseInverseTile
noncomputable section
open SpectreClusters SpectreClusters.BodyBSP ReverseClusterTriangulation

@[simp] theorem canonicalPackets_getD (kind : HTKind) (i : Fin 12) :
    (canonicalPackets kind).getD i.val default = canonicalPacket kind i := by
  simp [canonicalPackets,List.getD_eq_getElem?_getD,i.isLt]

theorem canonicalPackets_have_faces (kind : HTKind) :
    FamilyHasFaces (canonicalPackets kind) := by
  apply familyHasFaces_of_rows _ (fun n => (canonicalFaceRows kind).getD n [])
  intro i
  let j : Fin 12 := ⟨i.val,by simpa only [canonicalPackets_length] using i.isLt⟩
  have h := canonical_face_rows kind j
  simpa only [←canonicalPackets_getD,j] using h

end
end SpectreGeometry.ReverseInverseTile
