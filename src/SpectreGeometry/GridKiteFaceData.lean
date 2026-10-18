module

public import SpectreGeometry.ReverseClusterTriangulationFacesData
public import SpectreClusters.KiteContactData

@[expose] public section


/-! Exact supporting-face checks on the already classified ten-cell contact
stencil. The six identical-cell cases are excluded; 54 distinct contacts remain. -/
namespace SpectreGeometry.GridKiteFace
open SpectreClusters SpectreClusters.BodyBSP ReverseClusterTriangulation

def kitePacket (c : Cell) : PolygonPacket :=
  ⟨cellVertices c,polygonFacets (cellVertices c),[]⟩

def kiteFaceB (a b : Cell) : Bool :=
  supportsPacketFaceB (kitePacket a) (kitePacket b)
    (summedPacketSeparator (kitePacket a) (kitePacket b))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem local_faces_0 : ∀ b ∈ localContacts 0,
    (⟨(0,0),0⟩ : Cell) ≠ b → kiteFaceB ⟨(0,0),0⟩ b = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem local_faces_1 : ∀ b ∈ localContacts 1,
    (⟨(0,0),1⟩ : Cell) ≠ b → kiteFaceB ⟨(0,0),1⟩ b = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem local_faces_2 : ∀ b ∈ localContacts 2,
    (⟨(0,0),2⟩ : Cell) ≠ b → kiteFaceB ⟨(0,0),2⟩ b = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem local_faces_3 : ∀ b ∈ localContacts 3,
    (⟨(0,0),3⟩ : Cell) ≠ b → kiteFaceB ⟨(0,0),3⟩ b = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem local_faces_4 : ∀ b ∈ localContacts 4,
    (⟨(0,0),4⟩ : Cell) ≠ b → kiteFaceB ⟨(0,0),4⟩ b = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem local_faces_5 : ∀ b ∈ localContacts 5,
    (⟨(0,0),5⟩ : Cell) ≠ b → kiteFaceB ⟨(0,0),5⟩ b = true := by decide

theorem local_contact_faces : ∀ s : Turn, ∀ b ∈ localContacts s,
    (⟨(0,0),s⟩ : Cell) ≠ b → kiteFaceB ⟨(0,0),s⟩ b = true := by
  exact Fin.cases local_faces_0 (Fin.cases local_faces_1 (Fin.cases local_faces_2
    (Fin.cases local_faces_3 (Fin.cases local_faces_4 (Fin.cases local_faces_5
      (fun i => Fin.elim0 i))))))
#print axioms local_contact_faces
end SpectreGeometry.GridKiteFace
