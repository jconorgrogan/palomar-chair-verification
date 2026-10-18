module

public import SpectreClusters.AssignedClusterField
public import SpectreClusters.ClusterGridTranslations

@[expose] public section


/-! Source-correct extraction of the actual assigned cluster field.
The field remains on fine-grid cells, with genuine moved cluster shapes. -/
namespace SpectreClusters.StageA

noncomputable def assignedClusterPlacement (f : Cell → HTPlacement) (r : HTPlacement) : ClusterPlacement :=
  ⟨assignedKind f r,r.turn,r.center⟩

theorem assignedKind_legal (f : Cell → HTPlacement) (r : HTPlacement) :
    LegalClusterKind (assignedKind f r) := by
  classical
  unfold assignedKind LegalClusterKind
  split <;> simp

theorem assignedClusterPlacement_cells (f : Cell → HTPlacement) (r : HTPlacement) :
    clusterPlacementCells (assignedClusterPlacement f r) = assignedCells f r := by
  simp only [clusterPlacementCells,assignedClusterPlacement,assignedCells,assignedPieces,
    clusterPiecesAt,clusterCells,List.map_flatMap,List.flatMap_map]
  exact congrArg (fun h : HTPlacement → List Cell => (clusterPieces (assignedKind f r)).flatMap h)
    (funext (fun p => (placementCells_moved r.turn r.center p).symm))

noncomputable def extractedClusterField (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (c : Cell) : ClusterPlacement :=
  assignedClusterPlacement f (assignedRoot hcaptures f hf hsparse c)

theorem extractedClusterField_valid (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f) :
    ValidClusterGridField (extractedClusterField hcaptures f hf hsparse) := by
  intro c
  have hs := assignedRoot_spec hcaptures f hf hsparse c
  refine ⟨assignedKind_legal f _,?_,?_⟩
  · rw [extractedClusterField,assignedClusterPlacement_cells]
    exact hs.2.2
  · intro d hd
    rw [extractedClusterField,assignedClusterPlacement_cells] at hd
    unfold extractedClusterField
    rw [assignedRoot_coherent hcaptures f hf hsparse c d hd]

/-- Each actually owned turtle produces exactly its assigned cluster in the
extracted partition, so no original occurrence is lost through selection. -/
theorem extractedClusterField_owns (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (r : HTPlacement) (hr : RootOwned f r) (hk : r.kind = .turtle) :
    ClusterRootOwned (extractedClusterField hcaptures f hf hsparse) (assignedClusterPlacement f r) := by
  intro c hc
  rw [assignedClusterPlacement_cells] at hc
  unfold extractedClusterField
  rw [assignedRoot_unique hcaptures f hf hsparse c r hr hk hc]

theorem assignedClusterPlacement_translate_period (f : Cell → HTPlacement) (u : Point)
    (hperiod : GridFieldTranslationPeriod f u) (r : HTPlacement) :
    assignedClusterPlacement f (movePlacement 0 u r) =
      moveClusterPlacement 0 u (assignedClusterPlacement f r) := by
  have hk := assignedKind_moved 0 u f r
  rw [moveField_eq_of_period f u hperiod] at hk
  simp only [assignedClusterPlacement,movePlacement,moveClusterPlacement] at *
  rw [hk]

/-- The same nonzero integer period passes to the actual cluster grid field.
This does not identify it with SpectreFinite.FieldPeriod on a coarse chart. -/
theorem extractedClusterField_translate_period (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (u : Point) (hperiod : GridFieldTranslationPeriod f u) :
    ClusterGridFieldTranslationPeriod (extractedClusterField hcaptures f hf hsparse) u := by
  intro c
  unfold extractedClusterField
  rw [assignedRoot_translate_period hcaptures f hf hsparse u hperiod c,
    assignedClusterPlacement_translate_period f u hperiod]

end SpectreClusters.StageA
