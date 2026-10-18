module

public import SpectreGeometry.ReversePhysicalPlacedPieceImage
public import SpectreGeometry.ReverseMarkedAtlasFiniteCertificates
public import SpectreGeometry.ReversePhysicalClusterChartCertificates
public import SpectreGeometry.ReversePhysicalClusterPathCertificates

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence Deformation ReverseExistence
open ReversePhysicalCluster SpectreFinite SpectreFinite.HexSearch

/-- An actual legal marked field yields a locally finite whole-plane tiling by
proper Euclidean images of the original P carrier. Every finite premise is
instantiated by its literal certificate theorem. -/
theorem exists_homochiral_P_tiling_of_marked_field
    (f : Position → State) (hf : GloballyLegal f) :
    ∃ p : MarkedPieceIndex f → EPlane ≃ᵢ EPlane,
      (∀ i, DirectPlacement (p i)) ∧
      (∀ x : EPlane, ∃ i, x ∈ p i '' euclideanBody) ∧
      Pairwise (fun i j => Disjoint (interior (p i '' euclideanBody))
        (interior (p j '' euclideanBody))) ∧
      LocallyFinite (fun i => p i '' euclideanBody) := by
  let C := markedAtlasFiniteCertificates
  obtain ⟨B,hzero,hstep,hB⟩ := exists_physical_translation_field
    all_physical_boundary_certificates f hf
  let G := physicalFieldHomeomorph C all_chart_packet_bindings all_chart_face_rows f hf B hB
  let H : RealPoint ≃ₜ EPlane := rawEuclideanFrame.trans G
  have himage (i : MarkedPieceIndex f) :
      H '' markedPieceCarrier f hf i = markedPiecePose f B i '' euclideanBody := by
    change (fun x => G (rawEuclideanFrame x)) '' markedPieceCarrier f hf i = _
    rw [←image_image]
    exact physicalFieldHomeomorph_image_piece C all_chart_packet_bindings
      all_chart_face_rows f hf B hB i
  refine ⟨markedPiecePose f B,markedPiecePose_direct f B,?_,?_,?_⟩
  · intro x
    obtain ⟨y,rfl⟩ := H.surjective x
    obtain ⟨i,hi⟩ := C.marked_pieces_cover f hf y
    refine ⟨i,?_⟩
    rw [←himage i]
    exact ⟨y,hi,rfl⟩
  · have hd := homeomorph_images_interiors_disjoint H (markedPieceCarrier f hf)
      (C.marked_pieces_interiors_disjoint f hf)
    simpa only [himage] using hd
  · have hl := homeomorph_images_locallyFinite H (markedPieceCarrier f hf)
      (C.marked_pieces_locallyFinite f hf)
    simpa only [himage] using hl

/-- Genuine homochiral original-P existence: the index set and all proper
placements exist, cover the entire Euclidean plane, have pairwise disjoint
ambient interiors, and form a locally finite family. No tiling premise or
unproved global geometric callback is assumed. -/
theorem exists_homochiral_P_tiling :
    ∃ (I : Type) (p : I → EPlane ≃ᵢ EPlane),
      (∀ i, DirectPlacement (p i)) ∧
      (∀ x : EPlane, ∃ i, x ∈ p i '' euclideanBody) ∧
      Pairwise (fun i j => Disjoint (interior (p i '' euclideanBody))
        (interior (p j '' euclideanBody))) ∧
      LocallyFinite (fun i => p i '' euclideanBody) := by
  obtain ⟨f,hf⟩ := PartialMarkedHexSystem.exists_globallyLegal_from_literal_substitution
  obtain ⟨p,hd,hcover,hdisjoint,hlocal⟩ := exists_homochiral_P_tiling_of_marked_field f hf
  exact ⟨MarkedPieceIndex f,p,hd,hcover,hdisjoint,hlocal⟩

end
end SpectreGeometry.ReversePhysicalClusterCharts
