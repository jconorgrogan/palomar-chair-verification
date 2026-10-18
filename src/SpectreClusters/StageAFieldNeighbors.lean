module

public import SpectreClusters.StageABoundComplete
public import SpectreClusters.StageALocalClaims
public import SpectreClusters.GridReduction

@[expose] public section


/-! Literal row neighbors are exactly the actual distinct owned placements
meeting the root in the kite-contact model. No enumeration callback appears. -/
namespace SpectreClusters.StageA

def FieldNeighbor (f : Cell → HTPlacement) (root p : HTPlacement) : Prop :=
  RootOwned f p ∧ p ≠ root ∧ ShapeContact (placementCells root) (placementCells p)

theorem fieldNeighbor_iff_halo (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root) (p : HTPlacement) :
    FieldNeighbor f root p ↔ ∃ c ∈ halo (placementCells root), f c = p := by
  constructor
  · rintro ⟨hp,hne,a,ha,c,hc,hcontact⟩
    refine ⟨c,(mem_halo_iff _ _).mpr ⟨?_,a,ha,hcontact⟩,hp c hc⟩
    intro hcroot
    exact hne ((hp c hc).symm.trans (hr c hcroot))
  · rintro ⟨c,hc,he⟩
    obtain ⟨hout,a,ha,hcontact⟩ := (mem_halo_iff _ _).mp hc
    have hcp : c ∈ placementCells p := he ▸ (hf c).1
    refine ⟨?_,?_,a,ha,c,hcp,hcontact⟩
    · rw [← he]
      exact GridReduction.field_rootOwned f hf c
    · intro hsame
      exact hout (hsame ▸ hcp)

theorem row_neighbors_iff_fieldNeighbor (f : Cell → HTPlacement)
    (hf : ValidGridField f) (kind : HTKind)
    (hr : RootOwned f (canonicalRoot kind)) (i : Nat)
    (hword : rawWordAt kind i = wordOf f kind) (p : HTPlacement) :
    p ∈ neighbors kind i ↔ FieldNeighbor f (canonicalRoot kind) p := by
  rw [fieldNeighbor_iff_halo f hf _ hr p]
  simp only [placementCells_canonicalRoot]
  constructor
  · intro hp
    obtain ⟨n,hn,hnp⟩ := List.mem_map.mp hp
    have hnword : n ∈ wordOf f kind := hword ▸ List.mem_eraseDups.mp hn
    obtain ⟨c,hc,hcn⟩ := List.mem_map.mp hnword
    have hindex : candidateAt kind ((candidateList kind).idxOf (f c)) = f c :=
      GridReductionWords.candidateAt_idxOf _ _ _ (field_mem_candidates f hf kind hr c hc)
    refine ⟨c,(haloOrder_mem_iff kind c).mp hc,?_⟩
    exact hindex.symm.trans ((congrArg (candidateAt kind) hcn).trans hnp)
  · rintro ⟨c,hc,hcp⟩
    have hcorder := (haloOrder_mem_iff kind c).mpr hc
    apply List.mem_map.mpr
    refine ⟨(candidateList kind).idxOf (f c),List.mem_eraseDups.mpr ?_,?_⟩
    · rw [hword]
      exact List.mem_map.mpr ⟨c,hcorder,rfl⟩
    · exact (GridReductionWords.candidateAt_idxOf _ _ _
        (field_mem_candidates f hf kind hr c hcorder)).trans hcp

theorem eq_of_mem_length_le_one {α : Type} (xs : List α) (h : xs.length ≤ 1)
    (p q : α) (hp : p ∈ xs) (hq : q ∈ xs) : p = q := by
  cases xs with
  | nil => simp at hp
  | cons a tail =>
    cases tail with
    | nil =>
      have hp' : p = a := by simpa only [List.mem_singleton] using hp
      have hq' : q = a := by simpa only [List.mem_singleton] using hq
      exact hp'.trans hq'.symm
    | cons b tail => simp at h

theorem row_opposite_unique (kind : HTKind) (i : Nat)
    (hcount : oppositeCount kind i ≤ 1) (p q : HTPlacement)
    (hp : p ∈ neighbors kind i) (hq : q ∈ neighbors kind i)
    (hpk : p.kind ≠ kind) (hqk : q.kind ≠ kind) : p = q := by
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hp
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hq
  have hnfilter : n ∈ ((rawWordAt kind i).eraseDups).filter
      (fun n => !((candidateAt kind n).kind == kind)) := by
    exact List.mem_filter.mpr ⟨hn,by simpa using hpk⟩
  have hmfilter : m ∈ ((rawWordAt kind i).eraseDups).filter
      (fun n => !((candidateAt kind n).kind == kind)) := by
    exact List.mem_filter.mpr ⟨hm,by simpa using hqk⟩
  exact congrArg (candidateAt kind) (eq_of_mem_length_le_one _ hcount n m hnfilter hmfilter)

end SpectreClusters.StageA
