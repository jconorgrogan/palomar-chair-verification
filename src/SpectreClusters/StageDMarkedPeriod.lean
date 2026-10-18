module

public import SpectreClusters.StageDContactInterpretation

@[expose] public section


/-! The fine-grid cluster translation produces a nonzero period of the same
literal globally legal marked field constructed from actual cluster labels.
Only the named finite capture and halo-binding obligations remain explicit. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch SpectreFinite.HexSearch.ParentOwnership

theorem clusterTranslation_moves {f : Cell → ClusterPlacement}
    (u : Point) (hu : ClusterGridFieldTranslationPeriod f u) (hne : u ≠ (0,0))
    (p : ActualCluster f) : clusterTranslation u hu p ≠ p := by
  intro he
  have hc := congrArg (fun q : ActualCluster f => q.val.center) he
  change add u p.val.center = p.val.center at hc
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  apply hne
  apply Prod.ext <;> simp only [add] at hx hy ⊢ <;> omega

theorem clusterTranslation_represented {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (u : Point) (hu : ClusterGridFieldTranslationPeriod f u)
    (base : Cell) :
    clusterCellOwner hf (moveCell 0 u base) = clusterTranslation u hu (clusterCellOwner hf base) :=
  Subtype.ext (hu base)

/-- Explicit actual-field endpoint. Neither a chosen marked field nor an
injective geometric-to-axial chart is a premise. -/
theorem cluster_period_gives_marked_period (checks : FinalRowChecks) (hc : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (u : Point) (hne : u ≠ (0,0)) (hu : ClusterGridFieldTranslationPeriod f u) (base : Cell) :
    GloballyLegal (actualMarkedField checks hc hf (clusterCellOwner hf base)) ∧
      ∃ v : Position, v ≠ (0,0) ∧
        FieldPeriod (actualMarkedField checks hc hf (clusterCellOwner hf base)) v := by
  exact ClusterOrbit.actual_symmetry_gives_periodic_marked_field
    (actualHexSystem checks hc hf) (clusterLabel hc hf) (clusterStep_match checks hc hf)
    (clusterCellOwner hf) (actual_contact_steps checks hc hh hf) base
    (clusterTranslation u hu) (clusterStep_translation checks hc hf u hu)
    (clusterLabel_translation checks hc hf u hu)
    ⟨moveCell 0 u base,clusterTranslation_represented hf u hu base⟩
    (clusterTranslation_moves u hu hne (clusterCellOwner hf base))

theorem periodic_cluster_field_gives_periodic_marked_field (checks : FinalRowChecks)
    (hc : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (u : Point) (hne : u ≠ (0,0)) (hu : ClusterGridFieldTranslationPeriod f u) :
    ∃ F : Position → State, GloballyLegal F ∧
      ∃ v : Position, v ≠ (0,0) ∧ FieldPeriod F v :=
  ⟨actualMarkedField checks hc hf (clusterCellOwner hf ⟨(0,0),0⟩),
    cluster_period_gives_marked_period checks hc hh f hf u hne hu ⟨(0,0),0⟩⟩

end SpectreClusters.StageD
