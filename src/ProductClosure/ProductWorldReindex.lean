module

public import ProductClosure.ProductWorldPoseBlocks
public import RegisteredPrime.WorldNormalization

@[expose] public section

/-! Exact cell and pose reindexing by a common actual registered pose. -/
namespace ProductClosure.World

open Set
noncomputable section

@[simp] theorem poseCellIndex_eq_cell {d : ℕ} (q : RegisteredPrime.Pose d)
    (z : Lattice d) : poseCellIndex q z = q.cell z := by
  funext i
  cases hn : q.frame.negative i <;>
    simp [poseCellIndex, RegisteredPrime.Pose.cell, RegisteredPrime.RegisteredFrame.linear,
      RegisteredPrime.RegisteredFrame.sign, RegisteredPrime.bit, hn] <;> omega

/-- The cell action is a genuine bijection of the full integer lattice. -/
def poseCellEquiv {d : ℕ} (q : RegisteredPrime.Pose d) : Lattice d ≃ Lattice d where
  toFun := poseCellIndex q
  invFun := poseCellIndex q.inv
  left_inv z := by simp only [poseCellIndex_eq_cell, RegisteredPrime.Pose.inv_cell_cell]
  right_inv z := by simp only [poseCellIndex_eq_cell, RegisteredPrime.Pose.cell_inv_cell]

@[simp] theorem poseCellIndex_comp {d : ℕ} (q r : RegisteredPrime.Pose d) (z : Lattice d) :
    poseCellIndex (q.comp r) z = poseCellIndex q (poseCellIndex r z) := by
  simp only [poseCellIndex_eq_cell, RegisteredPrime.Pose.comp_cell]

theorem latticeAdjacent_iff_registered {d : ℕ} (x y : Lattice d) :
    LatticeAdjacent x y ↔ RegisteredPrime.Adjacent x y := by
  constructor
  · rintro ⟨i, b, rfl⟩
    refine ⟨i, ?_, ?_⟩
    · cases b <;> simp [latticeStep]
    · intro j hji
      simp [latticeStep, hji]
  · rintro ⟨i, hi, hother⟩
    obtain hi | hi := hi
    · refine ⟨i, false, ?_⟩
      funext j
      by_cases hj : j = i
      · subst j; simp [latticeStep]; omega
      · simp [latticeStep, hj, ← hother j hj]
    · refine ⟨i, true, ?_⟩
      funext j
      by_cases hj : j = i
      · subst j; simp [latticeStep]; omega
      · simp [latticeStep, hj, ← hother j hj]

/-- Actual pose-cell reindexing preserves literal unit-neighbor contacts. -/
theorem poseCellIndex_adjacent {d : ℕ} (q : RegisteredPrime.Pose d)
    {x y : Lattice d} (h : LatticeAdjacent x y) :
    LatticeAdjacent (poseCellIndex q x) (poseCellIndex q y) := by
  rw [latticeAdjacent_iff_registered]
  simp only [poseCellIndex_eq_cell]
  exact q.adjacent_cells x y ((latticeAdjacent_iff_registered x y).mp h)

/-- Occupancy commutes with a common pose action, for any finite polycube. -/
theorem placedCells_comp_cell_iff {d : ℕ} (S : Finset (Lattice d))
    (g q : RegisteredPrime.Pose d) (x : Lattice d) :
    poseCellIndex g x ∈ placedCells S (g.comp q) ↔ x ∈ placedCells S q := by
  constructor
  · rintro ⟨z, hz, he⟩
    rw [poseCellIndex_comp] at he
    exact ⟨z, hz, (poseCellEquiv g).injective he⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, poseCellIndex_comp g q z⟩

namespace CompleteTiling
variable {d : ℕ} {S : Finset (Lattice d)}

/-- Reframe every placed finite-polycube tile in one common actual pose
chart. Coverage and nonoverlap are proved, not added as hypotheses. -/
def reframe (W : CompleteTiling (placedCells S)) (g : RegisteredPrime.Pose d) :
    CompleteTiling (placedCells S) where
  tiles q := g.comp q ∈ W.tiles
  cover x := by
    obtain ⟨q, hq, hx⟩ := W.cover (poseCellIndex g x)
    refine ⟨g.relative q, ?_, ?_⟩
    · change g.comp (g.relative q) ∈ W.tiles
      simpa only [RegisteredPrime.Pose.comp_relative] using hq
    · apply (placedCells_comp_cell_iff S g (g.relative q) x).mp
      simpa only [RegisteredPrime.Pose.comp_relative] using hx
  disjoint q hq r hr hne := Set.disjoint_left.mpr (by
    intro x hx hx'
    have hne' : g.comp q ≠ g.comp r := fun he => hne (g.comp_left_cancel q r he)
    exact Set.disjoint_left.mp (W.disjoint _ hq _ hr hne')
      ((placedCells_comp_cell_iff S g q x).mpr hx)
      ((placedCells_comp_cell_iff S g r x).mpr hx'))
  nonempty q hq := by
    obtain ⟨x, hx⟩ := W.nonempty (g.comp q) hq
    refine ⟨(poseCellEquiv g).symm x, ?_⟩
    apply (placedCells_comp_cell_iff S g q _).mp
    change poseCellIndex g (poseCellIndex g.inv x) ∈ placedCells S (g.comp q)
    simpa only [poseCellIndex_eq_cell, RegisteredPrime.Pose.cell_inv_cell] using hx

/-- Exact owner equivariance under common frame normalization. -/
theorem reframe_owner (W : CompleteTiling (placedCells S)) (g : RegisteredPrime.Pose d)
    (x : Lattice d) :
    (W.reframe g).owner x = g.relative (W.owner (poseCellIndex g x)) := by
  apply (W.reframe g).owner_eq_of_mem
  · change g.comp (g.relative _) ∈ W.tiles
    rw [RegisteredPrime.Pose.comp_relative]
    exact W.owner_mem _
  · apply (placedCells_comp_cell_iff S g _ x).mp
    rw [RegisteredPrime.Pose.comp_relative]
    exact W.mem_owner _

/-- A relative-pose language is unchanged by common actual reindexing. -/
theorem reframe_legal (W : CompleteTiling (placedCells S)) (g : RegisteredPrime.Pose d)
    {M : RegisteredPrime.Pose d → Prop}
    (hlegal : W.IsLegal LatticeAdjacent (fun q r => M (q.relative r))) :
    (W.reframe g).IsLegal LatticeAdjacent (fun q r => M (q.relative r)) := by
  intro x y hadj hne
  rw [reframe_owner, reframe_owner]
  have hne' : W.owner (poseCellIndex g x) ≠ W.owner (poseCellIndex g y) := by
    intro h
    apply hne
    rw [reframe_owner, reframe_owner, h]
  have h := hlegal _ _ (poseCellIndex_adjacent g hadj) hne'
  change M ((g.inv.comp (W.owner (poseCellIndex g x))).relative
    (g.inv.comp (W.owner (poseCellIndex g y))))
  rw [RegisteredPrime.Pose.relative_left_cancel]
  exact h

/-- Every actual tile of the normalized world preserves blocks, as a
conclusion of local relative block contacts and whole-lattice connectivity. -/
theorem reframe_preservesBlocks {m n : ℕ} {S : Finset (Lattice (m + n))}
    (W : CompleteTiling (placedCells S))
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => PreservesBlocks (q.relative r)))
    {root : RegisteredPrime.Pose (m + n)} (hroot : root ∈ W.tiles) :
    ∀ q ∈ (W.reframe root).tiles, PreservesBlocks q := by
  intro q hq
  have h := common_block_chart W hlocal hroot (root.comp q) hq
  simpa only [RegisteredPrime.Pose.relative, ← RegisteredPrime.Pose.comp_assoc,
    RegisteredPrime.Pose.inv_comp, RegisteredPrime.Pose.identity_comp] using h

#print axioms reframe
#print axioms reframe_owner
#print axioms reframe_legal
#print axioms reframe_preservesBlocks

end CompleteTiling
end
end ProductClosure.World
