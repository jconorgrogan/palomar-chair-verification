module

public import SpectreClusters.GridCoverModel

@[expose] public section


/-! Occurrence-preserving local-consistency reduction for genuine grid
partitions. The initial family is the proved complete corona enumeration.
No physical registration, body realization, or externally supplied
successful-corona completeness assumption is hidden in this reduction. -/
namespace SpectreClusters.GridReduction

abbrev Corona := List (Cell × HTPlacement)
abbrev CoronaFamily := HTPlacement → List Corona

def restriction (f : Cell → HTPlacement) (root : HTPlacement) : Corona :=
  (halo (placementCells root)).map (fun c => (c,f c))

/-- Include the root occurrence itself in every overlap test. -/
def placements (root : HTPlacement) (patch : Corona) : List HTPlacement :=
  root :: patch.map Prod.snd

/-- Equality-or-disjointness means both patches assign the same owner to
all cells represented in their overlap, including their root placements. -/
def Compatible (root : HTPlacement) (patch : Corona)
    (other : HTPlacement) (support : Corona) : Prop :=
  ∀ p ∈ placements root patch, ∀ q ∈ placements other support,
    p = q ∨ DisjointCells (placementCells p) (placementCells q)

instance (root : HTPlacement) (patch : Corona)
    (other : HTPlacement) (support : Corona) :
    Decidable (Compatible root patch other support) :=
  inferInstanceAs (Decidable (∀ p ∈ placements root patch,
    ∀ q ∈ placements other support,
      p = q ∨ DisjointCells (placementCells p) (placementCells q)))

def Supported (family : CoronaFamily) (root : HTPlacement) (patch : Corona) : Prop :=
  ∀ x ∈ patch, ∃ support ∈ family x.2, Compatible root patch x.2 support

instance (family : CoronaFamily) (root : HTPlacement) (patch : Corona) :
    Decidable (Supported family root patch) :=
  inferInstanceAs (Decidable (∀ x ∈ patch,
    ∃ support ∈ family x.2, Compatible root patch x.2 support))

/-- Delete exactly the coronas lacking a mutually compatible support at
one of their represented neighbor occurrences. -/
def reduce (family : CoronaFamily) : CoronaFamily := fun root =>
  (family root).filter (fun patch => decide (Supported family root patch))

def iterate (family : CoronaFamily) : Nat → CoronaFamily
  | 0 => family
  | n+1 => reduce (iterate family n)

/-- This family has no supplied completeness hypothesis. -/
def allRounds : Nat → CoronaFamily := iterate coronaAssignments

theorem field_rootOwned (f : Cell → HTPlacement) (hf : ValidGridField f) (c : Cell) :
    RootOwned f (f c) := (hf c).2

theorem owned_compatible (f : Cell → HTPlacement) (p q : HTPlacement)
    (hp : RootOwned f p) (hq : RootOwned f q) :
    p = q ∨ DisjointCells (placementCells p) (placementCells q) := by
  by_cases he : p = q
  · exact Or.inl he
  · right
    intro c hc hd
    exact he ((hp c hc).symm.trans (hq c hd))

theorem restriction_member_owned (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (x : Cell × HTPlacement) (hx : x ∈ restriction f root) :
    RootOwned f x.2 := by
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hx
  exact field_rootOwned f hf c

theorem restriction_placements_owned (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root)
    (p : HTPlacement) (hp : p ∈ placements root (restriction f root)) :
    RootOwned f p := by
  rcases List.mem_cons.mp hp with he | hp
  · exact he ▸ hr
  · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hp
    exact restriction_member_owned f hf root x hx

theorem restrictions_compatible (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root other : HTPlacement) (hr : RootOwned f root) (ho : RootOwned f other) :
    Compatible root (restriction f root) other (restriction f other) := by
  intro p hp q hq
  exact owned_compatible f p q (restriction_placements_owned f hf root hr p hp)
    (restriction_placements_owned f hf other ho q hq)

theorem mem_reduce_iff (family : CoronaFamily) (root : HTPlacement) (patch : Corona) :
    patch ∈ reduce family root ↔ patch ∈ family root ∧ Supported family root patch := by
  simp [reduce]

theorem reduce_subset (family : CoronaFamily) (root : HTPlacement) :
    ∀ patch ∈ reduce family root, patch ∈ family root := by
  intro patch hp
  exact ((mem_reduce_iff family root patch).mp hp).1

/-- Any family already containing every genuine occurrence continues to
contain every genuine occurrence after one local-consistency reduction. -/
theorem restriction_mem_reduce (f : Cell → HTPlacement) (hf : ValidGridField f)
    (family : CoronaFamily)
    (hfamily : ∀ root, RootOwned f root → restriction f root ∈ family root)
    (root : HTPlacement) (hr : RootOwned f root) :
    restriction f root ∈ reduce family root := by
  apply (mem_reduce_iff family root (restriction f root)).mpr
  refine ⟨hfamily root hr,?_⟩
  intro x hx
  have ho := restriction_member_owned f hf root x hx
  exact ⟨restriction f x.2,hfamily x.2 ho,restrictions_compatible f hf root x.2 hr ho⟩

theorem restriction_mem_iterate (f : Cell → HTPlacement) (hf : ValidGridField f)
    (family : CoronaFamily)
    (hfamily : ∀ root, RootOwned f root → restriction f root ∈ family root)
    (n : Nat) (root : HTPlacement) (hr : RootOwned f root) :
    restriction f root ∈ iterate family n root := by
  induction n generalizing root with
  | zero => exact hfamily root hr
  | succ n ih => exact restriction_mem_reduce f hf (iterate family n) ih root hr

/-- Unconditional discrete occurrence preservation in every reduction round:
the only input is an actual coherent covering of all grid cells and its root.
Physical-to-grid transfer remains a separate obligation. -/
theorem restriction_mem_allRounds (f : Cell → HTPlacement) (hf : ValidGridField f)
    (n : Nat) (root : HTPlacement) (hr : RootOwned f root) :
    restriction f root ∈ allRounds n root := by
  apply restriction_mem_iterate f hf coronaAssignments ?_ n root hr
  intro other ho
  exact gridRestriction_mem_coronaAssignments f hf other ho

end SpectreClusters.GridReduction
