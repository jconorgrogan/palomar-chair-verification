module

public import SpectreClusters.StageDRowTransport
public import SpectreClusters.StageDLocalCertificates
public import SpectreClusters.StageDDirectionAlgebra

@[expose] public section


/-! Intrinsic final rows and six neighbors of genuine owned cluster occurrences.
The exhaustive capture obligation is explicit until its separate replay closes. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch

abbrev ActualCluster (f : Cell → ClusterPlacement) := {p // ClusterRootOwned f p}

noncomputable def chosenRow (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f) : Row :=
  Classical.choose (hc f hf p.val p.property (cluster_owned_kind f hf p.val p.property))

theorem chosenRow_spec (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f) :
    rowKind (chosenRow hc hf p) = p.val.kind ∧
      ClusterPatchOwned f (movedPatch (chosenRow hc hf p) p.val) :=
  Classical.choose_spec (hc f hf p.val p.property (cluster_owned_kind f hf p.val p.property))

theorem row_neighbors_length (checks : FinalRowChecks) (i : Row) : (rowNeighbors i).length = 6 := by
  have h := checks.basics i
  simp only [rowBasicsB,Bool.and_eq_true,beq_iff_eq] at h
  exact h.1.1.2

theorem row_port_mem (checks : FinalRowChecks) (i : Row) (d : Fin 6) : rowPort i d ∈ rowNeighbors i := by
  have hd : d.val < (rowNeighbors i).length := by rw [row_neighbors_length checks]; exact d.isLt
  unfold rowPort
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hd,Option.getD_some]
    using List.getElem_mem hd

def neighborPlacement (i : Row) (p : ClusterPlacement) (d : Fin 6) : ClusterPlacement :=
  moveClusterPlacement p.turn p.center (rowPort i (turnDiff d p.turn))

theorem neighborPlacement_owned (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f) (d : Fin 6) :
    ClusterRootOwned f (neighborPlacement (chosenRow hc hf p) p.val d) := by
  apply (chosenRow_spec hc hf p).2
  apply List.mem_map.mpr
  exact ⟨_,List.mem_cons_of_mem _ (row_port_mem checks _ _),rfl⟩

noncomputable def clusterStep (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (d : Fin 6)
    (p : ActualCluster f) : ActualCluster f :=
  ⟨neighborPlacement (chosenRow hc hf p) p.val d,neighborPlacement_owned checks hc hf p d⟩

theorem chosenRow_eq_of_patch (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f)
    (i : Row) (hi : rowKind i = p.val.kind) (hpi : ClusterPatchOwned f (movedPatch i p.val)) :
    chosenRow hc hf p = i :=
  actual_row_unique checks.unique f p.val _ i (chosenRow_spec hc hf p).1 hi
    (chosenRow_spec hc hf p).2 hpi

theorem actual_pair_laws (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f) (d : Fin 6) :
    pairLawsB (chosenRow hc hf p) (turnDiff d p.val.turn)
      (chosenRow hc hf (clusterStep checks hc hf d p)) = true := by
  apply pairLaws_of_checked _ _ _ (checks.pairs _ _ _)
    (chosenRow_spec hc hf (clusterStep checks hc hf d p)).1
    (moveClusterField (turnNeg p.val.turn) (inverseTranslation p.val.turn p.val.center) f)
    (movedPatch_owned_normalized f _ p.val (chosenRow_spec hc hf p).2)
  have h := movedPatch_owned_moved f _ (clusterStep checks hc hf d p).val
    (chosenRow_spec hc hf (clusterStep checks hc hf d p)).2
    (turnNeg p.val.turn) (inverseTranslation p.val.turn p.val.center)
  simpa only [clusterStep,neighborPlacement,moveClusterPlacement_inverse] using h

noncomputable def clusterLabel (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (p : ActualCluster f) : State :=
  (rowMark (chosenRow hc hf p),p.val.turn)

def clusterTranslation {f : Cell → ClusterPlacement} (u : Point)
    (hu : ClusterGridFieldTranslationPeriod f u) (p : ActualCluster f) : ActualCluster f :=
  ⟨moveClusterPlacement 0 u p.val,ClusterGridFieldTranslationPeriod.rootOwned f u hu p.val p.property⟩

theorem chosenRow_translation (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f)
    (u : Point) (hu : ClusterGridFieldTranslationPeriod f u) (p : ActualCluster f) :
    chosenRow hc hf (clusterTranslation u hu p) = chosenRow hc hf p := by
  apply chosenRow_eq_of_patch checks hc hf (clusterTranslation u hu p)
    (chosenRow hc hf p) (chosenRow_spec hc hf p).1
  exact movedPatch_owned_period f u hu _ p.val (chosenRow_spec hc hf p).2

theorem clusterLabel_translation (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f)
    (u : Point) (hu : ClusterGridFieldTranslationPeriod f u) (p : ActualCluster f) :
    clusterLabel hc hf (clusterTranslation u hu p) = clusterLabel hc hf p := by
  unfold clusterLabel
  rw [chosenRow_translation checks]
  simp only [clusterTranslation,moveClusterPlacement,turnAdd_zero]

theorem clusterStep_translation (checks : FinalRowChecks) (hc : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f)
    (u : Point) (hu : ClusterGridFieldTranslationPeriod f u) (d : Fin 6) (p : ActualCluster f) :
    clusterTranslation u hu (clusterStep checks hc hf d p) =
      clusterStep checks hc hf d (clusterTranslation u hu p) := by
  apply Subtype.ext
  change moveClusterPlacement 0 u (neighborPlacement (chosenRow hc hf p) p.val d) =
    neighborPlacement (chosenRow hc hf (clusterTranslation u hu p))
      (moveClusterPlacement 0 u p.val) d
  rw [chosenRow_translation checks]
  unfold neighborPlacement
  rw [moveClusterPlacement_compose]
  simp only [moveClusterPlacement,turnAdd_zero]

end SpectreClusters.StageD
