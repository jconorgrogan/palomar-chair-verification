module

public import SpectreClusters.KiteContacts
public import SpectreClusters.LiteralData

@[expose] public section


namespace SpectreClusters

def turnDiff (a b : Turn) : Turn :=
  ⟨(a.val+6-b.val)%6,Nat.mod_lt _ (by decide)⟩

theorem turnDiff_add : ∀ a b : Turn, turnDiff (turnAdd a b) b = a := by decide

def alignPlacement (kind : HTKind) (b c : Cell) : HTPlacement :=
  let k := turnDiff c.sector b.sector
  ⟨kind,k,sub c.center (rotate k b.center)⟩

/-- A cell plus its sector determines its orientation-preserving grid motion. -/
theorem align_moved_cell (p : HTPlacement) (b : Cell) :
    alignPlacement p.kind b (moveCell p.turn p.center b) = p := by
  unfold alignPlacement moveCell translateCell rotateCell
  simp only [turnDiff_add]
  cases p with
  | mk kind turn center =>
    congr 1
    apply Prod.ext <;> simp [sub,add]

/-- Pure grid-cell disjointness, not a substitute for a real-interior theorem. -/
def DisjointCells (A B : List Cell) : Prop := ∀ c ∈ A, c ∉ B
instance (A B : List Cell) : Decidable (DisjointCells A B) :=
  inferInstanceAs (Decidable (∀ c ∈ A, c ∉ B))

def ShapeContact (A B : List Cell) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, CellContact a b

def rawNeighborPlacements (root : List Cell) : List HTPlacement :=
  root.flatMap fun a => (contacts a).flatMap fun c =>
    [HTKind.hat,HTKind.turtle].flatMap fun kind =>
      (htCells kind).map fun b => alignPlacement kind b c

/-- Complete finite overapproximation of homochiral grid neighbors. No
simple-connectivity or pair-hole pruning appears in this constructor. -/
def neighborPlacements (root : List Cell) : List HTPlacement :=
  (rawNeighborPlacements root).eraseDups.filter
    (fun p => decide (DisjointCells root (placementCells p)))

theorem rawNeighborPlacements_complete (root : List Cell) (p : HTPlacement)
    (h : ShapeContact root (placementCells p)) : p ∈ rawNeighborPlacements root := by
  obtain ⟨a,ha,c,hc,hcontact⟩ := h
  obtain ⟨b,hb,hbc⟩ := List.mem_map.mp hc
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨c,(mem_contacts_iff a c).mpr hcontact,?_⟩⟩
  apply List.mem_flatMap.mpr
  have hk : p.kind ∈ [HTKind.hat,HTKind.turtle] := by cases p.kind <;> simp
  refine ⟨p.kind,hk,List.mem_map.mpr ⟨b,hb,?_⟩⟩
  rw [← hbc]
  exact align_moved_cell p b

theorem neighborPlacements_complete (root : List Cell) (p : HTPlacement)
    (h : ShapeContact root (placementCells p))
    (hd : DisjointCells root (placementCells p)) : p ∈ neighborPlacements root := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_eraseDups.mpr (rawNeighborPlacements_complete root p h),by simp [hd]⟩

theorem neighborPlacements_disjoint (root : List Cell) (p : HTPlacement)
    (h : p ∈ neighborPlacements root) : DisjointCells root (placementCells p) := by
  have := (List.mem_filter.mp h).2
  simpa using this

end SpectreClusters
