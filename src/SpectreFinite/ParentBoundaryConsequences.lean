module

public import SpectreFinite.ParentBoundaryTransfer

@[expose] public section


/-! Explicit six-neighbor and boundary-partition consequences. These statements
use actual owner queries; they do not construct a flat global coarse grid. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

theorem mem_trace_iff_segment (k : TileKind) (e : SideRef) :
    e ∈ trace k ↔ ∃ s : Fin 6, e ∈ segment k s := by
  rw [← (nine_marker_partitions k).2.2.2.2.1]
  simp only [List.mem_flatten, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨l,⟨s,rfl⟩,h⟩
    exact ⟨s,h⟩
  · rintro ⟨s,h⟩
    exact ⟨segment k s,⟨s,rfl⟩,h⟩

/-- The partition into six neighboring parents depends only on the displayed
parent shape, even where the neighboring Gamma anchor positions vary. -/
theorem same_owner_iff_same_segment (own : Position → List Position)
    (k : TileKind) (ns : List Position) (h : Structure own k ns)
    (s t : Fin 6) (e e' : SideRef) (he : e ∈ segment k s) (he' : e' ∈ segment k t) :
    own (outsideCell k e) = own (outsideCell k e') ↔ s = t := by
  rw [h.2.2.2.1 s e he, h.2.2.2.1 t e' he']
  have hs : s.val < ns.length := by rw [h.1]; exact s.isLt
  have ht : t.val < ns.length := by rw [h.1]; exact t.isLt
  simp only [List.singleton_inj, List.Nodup.getD_inj hs ht h.2.1, Fin.val_inj]

def outsideParents (own : Position → List Position) (k : TileKind) : List Position :=
  ((trace k).flatMap (fun e => own (outsideCell k e))).eraseDups

theorem outsideParents_membership (own : Position → List Position)
    (k : TileKind) (ns : List Position) (h : Structure own k ns) (a : Position) :
    a ∈ outsideParents own k ↔ a ∈ ns := by
  simp only [outsideParents, List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨e,he,ha⟩
    obtain ⟨s,hs⟩ := (mem_trace_iff_segment k e).mp he
    rw [h.2.2.2.1 s e hs] at ha
    have hai : a = ns.getD s.val (0,0) := by simpa using ha
    rw [hai]
    have hb : s.val < ns.length := by rw [h.1]; exact s.isLt
    apply List.mem_iff_getElem.mpr
    exact ⟨s.val,hb,by simp [List.getD_eq_getElem?_getD,hb]⟩
  · intro ha
    obtain ⟨i,hi,ha⟩ := List.mem_iff_getElem.mp ha
    let s : Fin 6 := ⟨i,by rw [h.1] at hi; exact hi⟩
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil (segment k s)
      ((nine_marker_partitions k).2.2.2.2.2 s).1
    refine ⟨e,(mem_trace_iff_segment k e).mpr ⟨s,he⟩,?_⟩
    rw [h.2.2.2.1 s e he]
    simp only [List.mem_singleton]
    rw [← ha]
    simp [s,List.getD_eq_getElem?_getD,hi]

private theorem eraseDups_nodup (xs : List Position) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a :: as =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp [List.mem_eraseDups, List.mem_filter]
    · exact eraseDups_nodup _
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The set of actual neighboring parent anchors has exactly six elements. -/
theorem outsideParents_six (own : Position → List Position)
    (k : TileKind) (ns : List Position) (h : Structure own k ns) :
    (outsideParents own k).length = 6 := by
  have hp : (outsideParents own k).Perm ns :=
    (List.perm_ext_iff_of_nodup (by exact eraseDups_nodup _) h.2.1).mpr
      (outsideParents_membership own k ns h)
  exact hp.length_eq.trans h.1

/-- This is a finite dictionary converse, not an assertion that any proposed
pair of macro-sides actually occurs or mates geometrically. -/
theorem canonicalSignature_injective : ∀ m ∈ labelAlphabet, ∀ n ∈ labelAlphabet,
    canonicalSignature m = canonicalSignature n → m = n := by decide

theorem labelAlphabet_neg : ∀ m ∈ labelAlphabet, -m ∈ labelAlphabet := by decide

theorem matching_signatures_iff_matching_labels (k l : TileKind) (s t : Fin 6) :
    actualSignature k s = reverseComplement (actualSignature l t) ↔
      macroLabel k s = -macroLabel l t := by
  constructor
  · intro h
    rw [nine_signatures, nine_signatures,
      ← canonical_complements _ (nine_labels_in_alphabet l t)] at h
    exact canonicalSignature_injective _ (nine_labels_in_alphabet k s) _
      (labelAlphabet_neg _ (nine_labels_in_alphabet l t)) h
  · exact matching_labels_matching_signatures k l s t

#print axioms same_owner_iff_same_segment
#print axioms outsideParents_six
#print axioms matching_signatures_iff_matching_labels
end SpectreFinite.HexSearch.ParentBoundary
