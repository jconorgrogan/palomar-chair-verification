module

public import SpectreFinite.PartialMarkedHexSystem
public import SpectreFinite.BoundaryGrowth

@[expose] public section


/-! Actual finite child tags and their canonical Fin encoding. No placement,
embedding, or proof of substitution preservation is included in the data. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem

structure ChildTag (S : PartialMarkedHexSystem) where
  parent : S.Cell
  child : Fin (children (S.label parent).1).length
  deriving DecidableEq

def childTags (S : PartialMarkedHexSystem) : List (ChildTag S) :=
  S.cells.flatMap fun p =>
    (List.finRange (children (S.label p).1).length).map fun i => ⟨p,i⟩

@[simp] theorem mem_childTags (S : PartialMarkedHexSystem) (t : ChildTag S) :
    t ∈ S.childTags := by
  rcases t with ⟨p,i⟩
  simp [childTags]

theorem childTags_nodup (S : PartialMarkedHexSystem) : S.childTags.Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p _
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange _).imp
    intro i j h hij
    exact h (by cases hij; rfl)
  · apply (List.nodup_finRange S.cellCount).imp
    intro p q hpq a ha b hb hab
    obtain ⟨i,_,hia⟩ := List.mem_map.mp ha
    obtain ⟨j,_,hjb⟩ := List.mem_map.mp hb
    exact hpq (by have h := congrArg ChildTag.parent hab; simpa [← hia, ← hjb] using h)

def encodeChild (S : PartialMarkedHexSystem) (t : ChildTag S) : Fin S.childTags.length :=
  ⟨S.childTags.idxOf t, List.idxOf_lt_length_of_mem (S.mem_childTags t)⟩

def decodeChild (S : PartialMarkedHexSystem) (i : Fin S.childTags.length) : ChildTag S :=
  S.childTags[i.val]

@[simp] theorem decode_encodeChild (S : PartialMarkedHexSystem) (t : ChildTag S) :
    S.decodeChild (S.encodeChild t) = t := by
  apply List.getElem_idxOf

@[simp] theorem encode_decodeChild (S : PartialMarkedHexSystem) (i : Fin S.childTags.length) :
    S.encodeChild (S.decodeChild i) = i := by
  apply Fin.ext
  exact S.childTags_nodup.idxOf_getElem i.val i.isLt

theorem encodeChild_injective (S : PartialMarkedHexSystem) {a b : ChildTag S}
    (h : S.encodeChild a = S.encodeChild b) : a = b := by
  have := congrArg S.decodeChild h
  simpa using this

def childHex (S : PartialMarkedHexSystem) (t : ChildTag S) : PlacedHex :=
  (children (S.label t.parent).1)[t.child.val]

/-- The common coordinate convention is reflected at every substitution:
listed children are rotated by the inverse of the parent's marked turn. -/
def childLabel (S : PartialMarkedHexSystem) (t : ChildTag S) : State :=
  let c := S.childHex t
  (c.kind, rotateTurn (inverseTurn (S.label t.parent).2) c.turn)

theorem childTags_length (S : PartialMarkedHexSystem) :
    S.childTags.length =
      (S.cells.map fun p => (children (S.label p).1).length).sum := by
  simp [childTags, List.length_flatMap]

private theorem sum_map_bounds {α : Type} (l : List α) (f : α → Nat) (a b : Nat)
    (h : ∀ x ∈ l, a ≤ f x ∧ f x ≤ b) :
    a*l.length ≤ (l.map f).sum ∧ (l.map f).sum ≤ b*l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem childTags_growth (S : PartialMarkedHexSystem) :
    7*S.cellCount ≤ S.childTags.length ∧ S.childTags.length ≤ 8*S.cellCount := by
  rw [childTags_length]
  simpa using sum_map_bounds S.cells (fun p => (children (S.label p).1).length) 7 8
    (fun p _ => Boundary.supertile_area_bounds (S.label p).1)

end SpectreFinite.HexSearch.PartialMarkedHexSystem
