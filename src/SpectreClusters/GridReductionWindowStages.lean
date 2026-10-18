module

public import SpectreClusters.GridReductionWindowBinding

@[expose] public section


/-! Finite-stage consequences of the exact window binding. The initial
completeness premise concerns genuine indexed fields, not an assumed
support relation. Every later deletion needs its checked rejection bit. -/
namespace SpectreClusters.GridReductionWindowBinding

open GridReductionWindows

def EnumerationComplete : Prop :=
  ∀ f, ValidGridField f → ∀ kind, RootOwned f (originRoot kind) →
    encode f kind ∈ StageA.rawWords kind

set_option maxRecDepth 100000 in
theorem kept_zero_range (kind : HTKind) :
    StageA.keptIds 0 kind = List.range (StageA.rawWords kind).length := by
  cases kind <;> rfl

theorem captures_zero (hcomplete : EnumerationComplete) :
    Captures StageA.rawWordAt (StageA.keptIds 0) encode := by
  intro f hf kind hr
  have hw := hcomplete f hf kind hr
  have hi := List.idxOf_lt_length_of_mem hw
  refine ⟨(StageA.rawWords kind).idxOf (encode f kind),?_,?_⟩
  · rw [kept_zero_range]
    exact List.mem_range.mpr hi
  · simp [StageA.rawWordAt,hi]

def ChecksStage (stage : Nat) : Prop :=
  ∀ kind, ∀ i ∈ StageA.keptIds stage kind,
    i ∉ StageA.keptIds (stage+1) kind → StageA.rejectionCheckB stage kind i = true

theorem captures_stages (hcandidates : CandidateComplete) (hwords : EnumerationComplete)
    (hchecks : ∀ n, ChecksStage n) (n : Nat) :
    Captures StageA.rawWordAt (StageA.keptIds n) encode :=
  captures_all_stages data StageA.rawWordAt encode StageA.keptIds
    (encoding_sound hcandidates) (captures_zero hwords)
    (fun stage => rejection_certificate stage (hchecks stage)) n

/-- The original actual row ID survives every checked stage, even when
multiple IDs happen to encode the same row. -/
theorem actual_id_stages (hcandidates : CandidateComplete) (hwords : EnumerationComplete)
    (hchecks : ∀ n, ChecksStage n) (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (originRoot kind)) (i : Nat)
    (hi : i ∈ StageA.keptIds 0 kind) (hword : StageA.rawWordAt kind i = encode f kind) :
    ∀ n, i ∈ StageA.keptIds n kind := by
  intro n
  induction n with
  | zero => exact hi
  | succ n ih =>
    exact retains_actual_id n hcandidates (captures_stages hcandidates hwords hchecks n)
      (hchecks n) f hf kind hr i ih hword

theorem captures_two (hcandidates : CandidateComplete) (hwords : EnumerationComplete)
    (hzero : ChecksStage 0) (hone : ChecksStage 1) :
    Captures StageA.rawWordAt (StageA.keptIds 2) encode :=
  captures_next 1 hcandidates
    (captures_next 0 hcandidates (captures_zero hwords) hzero) hone

/-- A genuine occurrence at any pose normalizes to a literal surviving row.
This theorem assumes a coherent grid field, not physical registration. -/
theorem normalized_mem_two (hcandidates : CandidateComplete) (hwords : EnumerationComplete)
    (hzero : ChecksStage 0) (hone : ChecksStage 1)
    (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root) :
    ∃ i ∈ StageA.keptIds 2 root.kind,
      StageA.rawWordAt root.kind i = encode (normalizeField f root) root.kind :=
  captures_two hcandidates hwords hzero hone (normalizeField f root)
    (normalizeField_valid f hf root) root.kind (normalizeField_rootOwned f root hr)

end SpectreClusters.GridReductionWindowBinding
