module

public import SpectreClusters.GridReductionWindows
public import SpectreClusters.GridReductionWords
public import SpectreClusters.StageAWindowModel

@[expose] public section


/-! Bind the literal fixed-window Boolean tests to genuine cell-owner fields.
Candidate completeness and the finite per-rejected-ID tests are separate
inputs, each supplied by independently checked literal-table modules. -/
namespace SpectreClusters.GridReductionWindowBinding

open GridReductionWindows

abbrev data : WindowData where
  domain := StageA.domain
  ownerAt := StageA.ownerAt
  candidate := StageA.candidateAt
  neighborIds := fun _ word => word
  alignmentPairs := StageA.alignmentPairs

def encode (f : Cell → HTPlacement) (kind : HTKind) : Word :=
  GridReductionWords.indexWord (StageA.candidateList kind) (StageA.haloOrder kind) f

def CandidateComplete : Prop :=
  ∀ f, ValidGridField f → ∀ kind, RootOwned f (originRoot kind) →
    ∀ c ∈ StageA.haloOrder kind, f c ∈ StageA.candidateList kind

theorem root_cells (kind : HTKind) :
    placementCells (originRoot kind) = htCells kind := by
  cases kind <;> rfl

theorem candidateAt_index (kind : HTKind) (p : HTPlacement)
    (hp : p ∈ StageA.candidateList kind) :
    StageA.candidateAt kind ((StageA.candidateList kind).idxOf p) = p :=
  GridReductionWords.candidateAt_idxOf _ _ _ hp

theorem encodes (f : Cell → HTPlacement) (kind : HTKind)
    (hr : RootOwned f (originRoot kind))
    (hmem : ∀ c ∈ StageA.haloOrder kind, f c ∈ StageA.candidateList kind) :
    Encodes data f kind (encode f kind) := by
  intro i hi
  change StageA.ownerAt kind (encode f kind) i = f ((StageA.domain kind)[i]'hi)
  unfold StageA.ownerAt
  by_cases hroot : i < (htCells kind).length
  · rw [ite_eq_left hroot]
    have hc : (StageA.domain kind)[i]'hi ∈ placementCells (originRoot kind) := by
      rw [root_cells]
      simp only [StageA.domain,List.getElem_append_left hroot]
      exact List.getElem_mem hroot
    exact (hr _ hc).symm
  · rw [ite_eq_right hroot]
    have hge : (htCells kind).length ≤ i := Nat.le_of_not_gt hroot
    have hhalo : i - (htCells kind).length < (StageA.haloOrder kind).length := by
      simp only [StageA.domain,List.length_append] at hi
      omega
    have hget : (encode f kind).getD (i - (htCells kind).length) 0 =
        (StageA.candidateList kind).idxOf
          (f ((StageA.haloOrder kind)[i - (htCells kind).length]'hhalo)) := by
      simp [encode,GridReductionWords.indexWord,hhalo]
    rw [hget,candidateAt_index kind _ (hmem _ (List.getElem_mem hhalo))]
    simp only [StageA.domain,List.getElem_append_right hge]

theorem represented_neighbor_owned (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind)
    (hmem : ∀ c ∈ StageA.haloOrder kind, f c ∈ StageA.candidateList kind)
    (n : Nat) (hn : n ∈ encode f kind) :
    RootOwned f (StageA.candidateAt kind n) := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hn
  rw [candidateAt_index kind _ (hmem c hc)]
  exact GridReduction.field_rootOwned f hf c

theorem encoding_sound (hcomplete : CandidateComplete) : EncodingSound data encode := by
  intro f hf kind hr
  exact ⟨encodes f kind hr (hcomplete f hf kind hr),
    represented_neighbor_owned f hf kind (hcomplete f hf kind hr)⟩

theorem alignment_sound (kind : HTKind) (n : Nat)
    (h : StageA.alignmentValidB kind n = true) : AlignmentSound data kind n := by
  intro ij hij
  have hpair := List.all_eq_true.mp h ij hij
  simp only [Bool.and_eq_true,decide_eq_true_eq,cellEqB_iff] at hpair
  obtain ⟨⟨hi,hj⟩,hcell⟩ := hpair
  refine ⟨hi,hj,?_⟩
  simpa [List.getD_eq_getElem?_getD,hi,hj] using hcell

theorem support_eq (kind : HTKind) (word : Word) (n : Nat) (support : Word) :
    GridReductionWindows.supportB data kind word n support =
      StageA.supportB kind word n support := rfl

/-- Every rejected ID is checked against the entire previous kept table at
the represented neighbor's kind. No completeness of overlap pairs is used. -/
theorem rejection_certificate (stage : Nat)
    (hcheck : ∀ kind, ∀ i ∈ StageA.keptIds stage kind,
      i ∉ StageA.keptIds (stage+1) kind → StageA.rejectionCheckB stage kind i = true) :
    RejectionCertificate data StageA.rawWordAt (StageA.keptIds stage)
      (StageA.keptIds (stage+1)) := by
  intro kind i hi hout
  have h := hcheck kind i hi hout
  simp only [StageA.rejectionCheckB,Bool.and_eq_true,List.contains_iff_mem] at h
  obtain ⟨⟨hn,ha⟩,hs⟩ := h
  refine ⟨StageA.rejectionNeighbor stage kind i,hn,alignment_sound kind _ ha,?_⟩
  intro j hj
  have hnone := List.all_eq_true.mp hs j hj
  simpa only [support_eq,Bool.not_eq_true'] using hnone

theorem retains_actual_id (stage : Nat) (hcomplete : CandidateComplete)
    (hbefore : Captures StageA.rawWordAt (StageA.keptIds stage) encode)
    (hcheck : ∀ kind, ∀ i ∈ StageA.keptIds stage kind,
      i ∉ StageA.keptIds (stage+1) kind → StageA.rejectionCheckB stage kind i = true)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (kind : HTKind)
    (hr : RootOwned f (originRoot kind)) (i : Nat)
    (hi : i ∈ StageA.keptIds stage kind) (hword : StageA.rawWordAt kind i = encode f kind) :
    i ∈ StageA.keptIds (stage+1) kind :=
  actual_id_survives data StageA.rawWordAt encode _ _ (encoding_sound hcomplete)
    hbefore (rejection_certificate stage hcheck) f hf kind hr i hi hword

theorem captures_next (stage : Nat) (hcomplete : CandidateComplete)
    (hbefore : Captures StageA.rawWordAt (StageA.keptIds stage) encode)
    (hcheck : ∀ kind, ∀ i ∈ StageA.keptIds stage kind,
      i ∉ StageA.keptIds (stage+1) kind → StageA.rejectionCheckB stage kind i = true) :
    Captures StageA.rawWordAt (StageA.keptIds (stage+1)) encode :=
  captures_of_rejections data StageA.rawWordAt encode _ _ (encoding_sound hcomplete)
    hbefore (rejection_certificate stage hcheck)

end SpectreClusters.GridReductionWindowBinding
