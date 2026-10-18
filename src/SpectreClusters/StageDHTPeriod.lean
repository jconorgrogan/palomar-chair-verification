module

public import SpectreClusters.StageDMarkedPeriod
public import SpectreClusters.ExtractedClusterField
public import SpectreClusters.SwappedSparsePhase

@[expose] public section


/-! Composition from genuine H/T owner fields through the intrinsic assigned
cluster partition to the literal marked field. Both finite capture obligations
are explicit until their separate exhaustive replay packets are accepted. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch SpectreFinite.HexSearch.ParentOwnership

theorem sparse_ht_period_gives_marked_period (checks : FinalRowChecks)
    (hA : StageA.FinalCaptures) (hD : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : StageA.SparseTurtles f)
    (u : Point) (hne : u ≠ (0,0)) (hu : GridFieldTranslationPeriod f u) :
    ∃ F : Position → State, GloballyLegal F ∧
      ∃ v : Position, v ≠ (0,0) ∧ FieldPeriod F v :=
  periodic_cluster_field_gives_periodic_marked_field checks hD hh
    (StageA.extractedClusterField hA f hf hs)
    (StageA.extractedClusterField_valid hA f hf hs) u hne
    (StageA.extractedClusterField_translate_period hA f hf hs u hu)

/-- An actual kind-swapping, contact-preserving occurrence correspondence
resolves the two sparse phases. Grid motions alone do not provide this premise.
The two fields may have different nonzero fine-grid period vectors. -/
theorem swapped_ht_periods_give_marked_period (checks : FinalRowChecks)
    (hA : StageA.FinalCaptures) (hD : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f g : Cell → HTPlacement) (hf : ValidGridField f) (hg : ValidGridField g)
    (E : SwappedFieldCorrespondence f g)
    (u v : Point) (hu0 : u ≠ (0,0)) (hv0 : v ≠ (0,0))
    (hu : GridFieldTranslationPeriod f u) (hv : GridFieldTranslationPeriod g v) :
    ∃ F : Position → State, GloballyLegal F ∧
      ∃ w : Position, w ≠ (0,0) ∧ FieldPeriod F w := by
  rcases StageA.one_of_swapped_fields_sparse hA f g hf E with hs | hs
  · exact sparse_ht_period_gives_marked_period checks hA hD hh f hf hs u hu0 hu
  · exact sparse_ht_period_gives_marked_period checks hA hD hh g hg hs v hv0 hv

end SpectreClusters.StageD
