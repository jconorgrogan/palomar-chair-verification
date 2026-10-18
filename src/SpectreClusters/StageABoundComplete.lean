module

public import SpectreClusters.StageACandidatesA
public import SpectreClusters.StageACandidatesB
public import SpectreClusters.StageACompatibilityA
public import SpectreClusters.StageACompatibilityB
public import SpectreClusters.StageAHaloChoices
public import SpectreClusters.StageACoverComplete
public import SpectreClusters.GridReductionWords

@[expose] public section


/-! The literal 251-row search is now tied to actual coherent coverings of
all kite cells. This remains a discrete statement; physical registration
and polygon/kite realization must be supplied independently. -/
namespace SpectreClusters.StageA

set_option maxRecDepth 100000

theorem candidateList_complete (kind : HTKind) (p : HTPlacement)
    (hp : ShapeContact (htCells kind) (placementCells p))
    (hd : DisjointCells (htCells kind) (placementCells p)) : p ∈ candidateList kind := by
  cases kind
  · exact candidateA_complete p hp hd
  · exact candidateB_complete p hp hd

theorem compatibility_bound (kind : HTKind) (i j : Nat)
    (hi : i < (candidateList kind).length) (hj : j < (candidateList kind).length) :
    idCompatible kind i j = compatibleB (candidateAt kind i) (candidateAt kind j) := by
  cases kind
  · exact compatibilityA_bound i j hi hj
  · exact compatibilityB_bound i j hi hj

theorem placementCells_canonicalRoot (kind : HTKind) :
    placementCells (canonicalRoot kind) = htCells kind := by
  cases kind <;> rfl

theorem field_mem_candidates (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (canonicalRoot kind)) (c : Cell)
    (hc : c ∈ haloOrder kind) : f c ∈ candidateList kind := by
  have hhalo := (haloOrder_mem_iff kind c).mp hc
  obtain ⟨hout,a,ha,hcontact⟩ := (mem_halo_iff _ _).mp hhalo
  apply candidateList_complete kind (f c) ⟨a,ha,c,(hf c).1,hcontact⟩
  intro d hd hdf
  have hdroot : d ∈ placementCells (canonicalRoot kind) := by
    simpa only [placementCells_canonicalRoot] using hd
  have hsame : f c = canonicalRoot kind := ((hf c).2 d hdf).symm.trans (hr d hdroot)
  have hcroot : c ∈ placementCells (canonicalRoot kind) := hsame ▸ (hf c).1
  exact hout (by simpa only [placementCells_canonicalRoot] using hcroot)

theorem any_cellEqB (cells : List Cell) (c : Cell) :
    cells.any (cellEqB c) = cells.contains c := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,cellEqB_iff,List.contains_iff_mem]
  constructor
  · rintro ⟨d,hd,rfl⟩
    exact hd
  · intro h
    exact ⟨c,h,rfl⟩

theorem indexedChoices_eq (kind : HTKind) (c : Cell) :
    indexedChoices kind c =
      GridReductionWords.indexedChoices (candidateList kind) (canonicalRoot kind) c := by
  simp only [indexedChoices,GridReductionWords.indexedChoices,
    GridReductionWords.candidateAt,candidateAt,any_cellEqB]

def wordOf (f : Cell → HTPlacement) (kind : HTKind) : List Nat :=
  GridReductionWords.indexWord (candidateList kind) (haloOrder kind) f

theorem wordOf_bounded (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (canonicalRoot kind)) (i : Nat)
    (hi : i ∈ wordOf f kind) : i < (candidateList kind).length := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hi
  exact List.idxOf_lt_length_of_mem (field_mem_candidates f hf kind hr c hc)

/-- Every genuine normalized grid partition has one of the literal 251 words.
No externally supplied enumeration-completeness hypothesis is present. -/
theorem grid_word_mem_rawWords (f : Cell → HTPlacement) (hf : ValidGridField f)
    (kind : HTKind) (hr : RootOwned f (canonicalRoot kind)) :
    wordOf f kind ∈ rawWords kind := by
  apply (mem_rawWords_iff kind (wordOf f kind)).mpr
  have hmem := field_mem_candidates f hf kind hr
  constructor
  · rw [choicesTable_bound]
    have he : indexedChoices kind =
        GridReductionWords.indexedChoices (candidateList kind) (canonicalRoot kind) :=
      funext (indexedChoices_eq kind)
    rw [he]
    exact GridReductionWords.indexWord_overChoices _ _ _ f hf hmem
  · have hp := GridReductionWords.indexWord_pairwise (candidateList kind)
      (canonicalRoot kind) (haloOrder kind) f hf hmem
    apply List.Pairwise.imp_of_mem ?_ hp
    intro i j hi hj hij
    rw [compatibility_bound kind i j (wordOf_bounded f hf kind hr i hi)
      (wordOf_bounded f hf kind hr j hj)]
    exact hij

end SpectreClusters.StageA
