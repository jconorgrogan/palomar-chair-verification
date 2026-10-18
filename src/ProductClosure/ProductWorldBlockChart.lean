module

public import ProductClosure.ProductWorldPlaced
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Common block chart from local relative-pose contacts

No absolute block-frame assumption is made about the tiling states. Complete
lattice coverage implies cell-contact connectivity; a block-coset relation
propagates over that connectivity. Normalization at any one actual tile
then puts every ambient signed-permutation pose in the same product blocks.
-/
namespace ProductClosure.World

open Set
noncomputable section
universe u

namespace CompleteTiling
variable {d : ℕ} {State : Type u} {cells : State → Set (Lattice d)}

/-- Every tile belongs to the same equivalence class when each distinct
neighboring cell-owner pair does. This is the exact finite-cell connectivity
argument, with coverage and owner uniqueness inherited from the tiling. -/
theorem all_tiles_equivalent (W : CompleteTiling cells) (R : Setoid State)
    (hlocal : W.IsLegal LatticeAdjacent R.r)
    {q r : State} (hq : q ∈ W.tiles) (hr : r ∈ W.tiles) : R.r q r := by
  obtain ⟨x, hx⟩ := W.nonempty q hq
  obtain ⟨y, hy⟩ := W.nonempty r hr
  have hstep (z : Lattice d) (i : Fin d) (b : Bool) :
      Quotient.mk R (W.owner (latticeStep z i b)) = Quotient.mk R (W.owner z) := by
    apply Quotient.sound
    by_cases h : W.owner z = W.owner (latticeStep z i b)
    · rw [← h]
    · exact R.symm (hlocal z (latticeStep z i b) ⟨i, b, rfl⟩ h)
  have heq := eq_of_latticeStep_invariant (fun z => Quotient.mk R (W.owner z)) hstep x y
  rw [W.owner_eq_of_mem hq hx, W.owner_eq_of_mem hr hy] at heq
  exact Quotient.exact heq

/-- The actual cell-face contact graph of a complete finite-cell tiling is
connected, expressed as equivalence closure of literal owner contacts. -/
theorem cell_contact_connected (W : CompleteTiling cells)
    {q r : State} (hq : q ∈ W.tiles) (hr : r ∈ W.tiles) :
    Relation.EqvGen (fun a b => ∃ x y, LatticeAdjacent x y ∧
      W.owner x = a ∧ W.owner y = b) q r := by
  apply W.all_tiles_equivalent (Relation.EqvGen.setoid _)
  · intro x y hadj _
    exact Relation.EqvGen.rel _ _ ⟨x, y, hadj, rfl, rfl⟩
  · exact hq
  · exact hr

end CompleteTiling

/-- A signed row frame preserves the two native coordinate blocks. Signs and
translations are unrestricted; mixing active and passive axes is excluded. -/
def PreservesBlocks {m n : ℕ} (q : RegisteredPrime.Pose (m + n)) : Prop :=
  ∀ i, (q.frame.perm i).val < m ↔ i.val < m

/-- Two arbitrary ambient poses induce the same assignment of global axes
to native blocks. This equivalence is invariant under all translations. -/
def SameBlockChart {m n : ℕ} (q r : RegisteredPrime.Pose (m + n)) : Prop :=
  ∀ i, (q.frame.perm i).val < m ↔ (r.frame.perm i).val < m

def blockChartSetoid (m n : ℕ) : Setoid (RegisteredPrime.Pose (m + n)) where
  r := SameBlockChart
  iseqv := ⟨fun _ _ => Iff.rfl, fun h i => (h i).symm,
    fun h h' i => (h i).trans (h' i)⟩

/-- Relative-pose block preservation is exactly equality of the two ambient
block charts, with the original signed-row composition convention. -/
theorem relative_preservesBlocks_iff {m n : ℕ}
    (q r : RegisteredPrime.Pose (m + n)) :
    PreservesBlocks (q.relative r) ↔ SameBlockChart q r := by
  constructor
  · intro h i
    have hi := h (q.frame.perm i)
    change (r.frame.perm (q.frame.inverse (q.frame.perm i))).val < m ↔
      (q.frame.perm i).val < m at hi
    rw [q.frame.left_inverse] at hi
    exact hi.symm
  · intro h i
    have hi := h (q.frame.inverse i)
    rw [q.frame.right_inverse] at hi
    exact hi.symm

/-- Local block-preserving relative contacts force one common global block
chart for every tile. No block-chart hypothesis appears on absolute poses. -/
theorem common_block_chart {m n : ℕ}
    {cells : RegisteredPrime.Pose (m + n) → Set (Lattice (m + n))}
    (W : CompleteTiling cells)
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => PreservesBlocks (q.relative r)))
    {root : RegisteredPrime.Pose (m + n)} (hroot : root ∈ W.tiles) :
    ∀ q ∈ W.tiles, PreservesBlocks (root.relative q) := by
  intro q hq
  apply (relative_preservesBlocks_iff root q).mpr
  apply W.all_tiles_equivalent (blockChartSetoid m n) ?_ hroot hq
  intro a b hadj hne
  exact (relative_preservesBlocks_iff _ _).mp (hlocal a b hadj hne)

/-- A canonical root can be obtained from full lattice coverage, rather
than assuming a preexisting marked or specially oriented tile. -/
theorem exists_common_block_chart {m n : ℕ}
    {cells : RegisteredPrime.Pose (m + n) → Set (Lattice (m + n))}
    (W : CompleteTiling cells)
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => PreservesBlocks (q.relative r))) :
    ∃ root ∈ W.tiles, ∀ q ∈ W.tiles, PreservesBlocks (root.relative q) :=
  ⟨W.owner 0, W.owner_mem 0, common_block_chart W hlocal (W.owner_mem 0)⟩

#print axioms CompleteTiling.cell_contact_connected
#print axioms common_block_chart
#print axioms exists_common_block_chart

end
end ProductClosure.World
