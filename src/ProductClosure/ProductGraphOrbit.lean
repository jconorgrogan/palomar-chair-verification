module

public import PhysicalRegistration.NativeTubeSeparation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Native full tangent orbits and rank relabeling

The full frame is first encoded by its actual coordinate magnitudes and signs.
A passive label is an ordered signed injection of passive coordinates into the
full magnitude labels. Its complement is enumerated in increasing order. Thus
active frames with interleaved full labels are included, not discarded.
-/
namespace ProductClosure.ProductGraphOrbit
noncomputable section
open PhysicalRegistration.NativeChair
attribute [local instance] Classical.propDecidable

/-- Coordinate-to-magnitude labels and coordinate signs, with the active and
passive coordinate blocks distinguished only in the domain. -/
abbrev BlockOrbit (a b : ℕ) :=
  ((Fin a ⊕ Fin b) ≃ Fin (a+b)) × ((Fin a ⊕ Fin b) → Bool)

/-- Ordered signed passive coordinates. The magnitude labels may interleave
arbitrarily with the active labels. -/
abbrev Passive (a b : ℕ) :=
  (Fin b ↪ Fin (a+b)) × (Fin b → Bool)

def passive {a b : ℕ} (o : BlockOrbit a b) : Passive a b :=
  (⟨fun j => o.1 (.inr j), fun _ _ h => Sum.inr_injective (o.1.injective h)⟩,
    fun j => o.2 (.inr j))

/-- The actual coordinate-side encoding of a native full frame. -/
def frameToBlock {a b : ℕ} (F : Frame (a+b)) : BlockOrbit a b :=
  (finSumFinEquiv.trans F.1.symm,
    fun i => F.2 (F.1.symm (finSumFinEquiv i)))

def blockToFrame {a b : ℕ} (o : BlockOrbit a b) : Frame (a+b) :=
  ((finSumFinEquiv.symm.trans o.1).symm, fun j => o.2 (o.1.symm j))

theorem blockToFrame_frameToBlock {a b : ℕ} (F : Frame (a+b)) :
    blockToFrame (frameToBlock F : BlockOrbit a b) = F := by
  apply Prod.ext
  · ext j
    simp [blockToFrame, frameToBlock]
  · funext j
    simp [blockToFrame, frameToBlock]

theorem frameToBlock_blockToFrame {a b : ℕ} (o : BlockOrbit a b) :
    frameToBlock (blockToFrame o) = o := by
  apply Prod.ext
  · ext j
    simp [blockToFrame, frameToBlock]
  · funext j
    simp [blockToFrame, frameToBlock]

def fullFrameBlockEquiv (a b : ℕ) : Frame (a+b) ≃ BlockOrbit a b where
  toFun := frameToBlock
  invFun := blockToFrame
  left_inv := blockToFrame_frameToBlock
  right_inv := frameToBlock_blockToFrame

/-- Complement of the passive magnitude labels. -/
def remaining {a b : ℕ} (p : Passive a b) : Finset (Fin (a+b)) :=
  Finset.univ \ Finset.univ.map p.1

theorem mem_remaining {a b : ℕ} (p : Passive a b) (i : Fin (a+b)) :
    i ∈ remaining p ↔ ∀ j, p.1 j ≠ i := by
  simp [remaining]

theorem card_remaining {a b : ℕ} (p : Passive a b) : (remaining p).card = a := by
  rw [remaining, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- Canonical increasing relabeling of active magnitudes to 1,...,a
(the stored labels are zero based, as in the native frame convention). -/
def rankLabels {a b : ℕ} (p : Passive a b) : Fin a ≃o remaining p :=
  (remaining p).orderIsoOfFin (card_remaining p)

theorem active_mem_remaining {a b : ℕ} (o : BlockOrbit a b) (i : Fin a) :
    o.1 (.inl i) ∈ remaining (passive o) := by
  rw [mem_remaining]
  intro j he
  have := o.1.injective he
  cases this

/-- Restrict a full native orbit to its active coordinates. -/
def activeLabels {a b : ℕ} (o : BlockOrbit a b) : Fin a ≃ remaining (passive o) :=
  Equiv.ofBijective (fun i => ⟨o.1 (.inl i), active_mem_remaining o i⟩) (by
    constructor
    · intro i j he
      exact Sum.inl_injective (o.1.injective (congrArg Subtype.val he))
    · intro z
      obtain ⟨i, hi⟩ := o.1.surjective z.val
      cases i with
      | inl i => exact ⟨i, Subtype.ext hi⟩
      | inr j =>
        have hn := (mem_remaining (passive o) z.val).mp z.property j
        exact (hn hi).elim)

/-- Coordinate-to-rank permutation of all active labels. -/
def activeRank {a b : ℕ} (o : BlockOrbit a b) : Equiv.Perm (Fin a) :=
  (activeLabels o).trans (rankLabels (passive o)).toEquiv.symm

/-- The literal smaller native frame after increasing magnitude relabeling. -/
def activeFrame {a b : ℕ} (o : BlockOrbit a b) : Frame a :=
  ((activeRank o).symm, fun j => o.2 (.inl ((activeRank o).symm j)))

@[simp] theorem rankLabels_activeRank {a b : ℕ} (o : BlockOrbit a b) (i : Fin a) :
    ((rankLabels (passive o) (activeRank o i) : remaining (passive o)) : Fin (a+b)) =
      o.1 (.inl i) := by
  simp [activeRank]
  rfl

/-- Rank relabeling retains the sign and replaces only the positive magnitude. -/
theorem activeFrame_numerator {a b : ℕ} (o : BlockOrbit a b) (i : Fin a) :
    orbitNumerator (activeFrame o) i =
      if o.2 (.inl i) then ((activeRank o i).val : ℤ) + 1
      else -(((activeRank o i).val : ℤ) + 1) := by
  simp [orbitNumerator, activeFrame]

/-- Full native numerators contain exactly the coordinate labels and signs;
this includes full frames which mix active/passive label orderings. -/
theorem fullFrame_numerator {a b : ℕ} (o : BlockOrbit a b) (i : Fin a ⊕ Fin b) :
    orbitNumerator (blockToFrame o) (finSumFinEquiv i) =
      if o.2 i then ((o.1 i).val : ℤ) + 1 else -(((o.1 i).val : ℤ) + 1) := by
  simp [orbitNumerator, blockToFrame]

/-- Reassemble arbitrary passive signed labels with any active native frame. -/
def assembledLabels {a b : ℕ} (p : Passive a b) (F : Frame a) :
    (Fin a ⊕ Fin b) ≃ Fin (a+b) :=
  Equiv.ofBijective
    (Sum.elim (fun i => (rankLabels p (F.1.symm i)).val) p.1)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j he
      cases i with
      | inl i =>
        cases j with
        | inl j =>
          exact congrArg Sum.inl (F.1.symm.injective
            ((rankLabels p).injective (Subtype.ext he)))
        | inr j =>
          have hmem := (rankLabels p (F.1.symm i)).property
          exact ((mem_remaining p _).mp hmem j he.symm).elim
      | inr i =>
        cases j with
        | inl j =>
          have hmem := (rankLabels p (F.1.symm j)).property
          exact ((mem_remaining p _).mp hmem i he).elim
        | inr j => exact congrArg Sum.inr (p.1.injective he), by simp⟩)

def assemble {a b : ℕ} (p : Passive a b) (F : Frame a) : BlockOrbit a b :=
  (assembledLabels p F, Sum.elim (fun i => F.2 (F.1.symm i)) p.2)

@[simp] theorem assembledLabels_inl {a b : ℕ} (p : Passive a b) (F : Frame a) (i : Fin a) :
    assembledLabels p F (.inl i) = (rankLabels p (F.1.symm i)).val := rfl

@[simp] theorem assembledLabels_inr {a b : ℕ} (p : Passive a b) (F : Frame a) (i : Fin b) :
    assembledLabels p F (.inr i) = p.1 i := rfl

@[simp] theorem passive_assemble {a b : ℕ} (p : Passive a b) (F : Frame a) :
    passive (assemble p F) = p := by
  apply Prod.ext
  · ext j
    rfl
  · rfl

@[simp] theorem activeRank_assemble {a b : ℕ} (p : Passive a b) (F : Frame a) :
    activeRank (assemble p F) = F.1.symm := by
  apply Equiv.ext
  intro i
  apply (rankLabels p).injective
  apply Subtype.ext
  have h := rankLabels_activeRank (assemble p F) i
  rw [passive_assemble] at h
  exact h

@[simp] theorem activeFrame_assemble {a b : ℕ} (p : Passive a b) (F : Frame a) :
    activeFrame (assemble p F) = F := by
  apply Prod.ext
  · simp [activeFrame]
  · funext j
    simp only [activeFrame, activeRank_assemble, Equiv.symm_symm]
    change F.2 (F.1.symm (F.1 j)) = F.2 j
    simp

@[simp] theorem assemble_passive_activeFrame {a b : ℕ} (o : BlockOrbit a b) :
    assemble (passive o) (activeFrame o) = o := by
  apply Prod.ext
  · apply Equiv.ext
    intro i
    cases i with
    | inl i =>
      simp only [assemble, assembledLabels_inl, activeFrame, Equiv.symm_symm]
      change (rankLabels (passive o) (activeRank o i)).val = o.1 (.inl i)
      exact rankLabels_activeRank o i
    | inr j => rfl
  · funext i
    cases i with
    | inl i => simp [assemble, activeFrame]
    | inr j => rfl

/-- Every full tangent orbit coset is exactly one full factor orbit, with
increasing rank relabeling. This is a global bijection, so no frames with
mixed active/passive label order are omitted. -/
def blockOrbitCosetEquiv (a b : ℕ) : BlockOrbit a b ≃ Passive a b × Frame a where
  toFun o := (passive o, activeFrame o)
  invFun z := assemble z.1 z.2
  left_inv := assemble_passive_activeFrame
  right_inv := by rintro ⟨p,F⟩; simp

def nativeFullOrbitCosetEquiv (a b : ℕ) : Frame (a+b) ≃ Passive a b × Frame a :=
  (fullFrameBlockEquiv a b).trans (blockOrbitCosetEquiv a b)

/-- An arbitrary signed active coordinate change, extended by the identity
on every passive coordinate. `e` sends output coordinates to input coordinates. -/
def reindexBlock {a b : ℕ} (e : Equiv.Perm (Fin a)) (τ : Fin a → Bool)
    (o : BlockOrbit a b) : BlockOrbit a b :=
  ((e.sumCongr (Equiv.refl (Fin b))).trans o.1,
    Sum.elim (fun i => τ i == o.2 (.inl (e i))) (fun j => o.2 (.inr j)))

/-- The corresponding literal signed-permutation action on factor frames. -/
def reindexFrame {a : ℕ} (e : Equiv.Perm (Fin a)) (τ : Fin a → Bool)
    (F : Frame a) : Frame a :=
  ((e.trans F.1.symm).symm,
    fun j => τ ((e.trans F.1.symm).symm j) == F.2 j)

@[simp] theorem passive_reindexBlock {a b : ℕ} (e : Equiv.Perm (Fin a))
    (τ : Fin a → Bool) (o : BlockOrbit a b) :
    passive (reindexBlock e τ o) = passive o := by
  apply Prod.ext
  · ext j
    rfl
  · rfl

@[simp] theorem activeRank_reindexBlock {a b : ℕ} (e : Equiv.Perm (Fin a))
    (τ : Fin a → Bool) (o : BlockOrbit a b) :
    activeRank (reindexBlock e τ o) = e.trans (activeRank o) := by
  apply Equiv.ext
  intro i
  apply (rankLabels (passive o)).injective
  apply Subtype.ext
  have h := rankLabels_activeRank (reindexBlock e τ o) i
  rw [passive_reindexBlock] at h
  rw [h]
  exact (rankLabels_activeRank o (e i)).symm

/-- The increasing rank relabeling commutes with every signed permutation
of active coordinates. Passive signs and labels remain literally fixed. -/
theorem activeFrame_reindexBlock {a b : ℕ} (e : Equiv.Perm (Fin a))
    (τ : Fin a → Bool) (o : BlockOrbit a b) :
    activeFrame (reindexBlock e τ o) = reindexFrame e τ (activeFrame o) := by
  apply Prod.ext
  · simp [activeFrame, reindexFrame]
  · funext j
    simp only [activeFrame, activeRank_reindexBlock, reindexFrame, Equiv.symm_symm]
    simp [reindexBlock]

/-- Equivariance of the entire coset bijection, including all interleaved
native full-orbit labels. -/
theorem blockOrbitCosetEquiv_reindex {a b : ℕ} (e : Equiv.Perm (Fin a))
    (τ : Fin a → Bool) (o : BlockOrbit a b) :
    blockOrbitCosetEquiv a b (reindexBlock e τ o) =
      ((blockOrbitCosetEquiv a b o).1,
        reindexFrame e τ (blockOrbitCosetEquiv a b o).2) := by
  exact Prod.ext (passive_reindexBlock e τ o) (activeFrame_reindexBlock e τ o)

#print axioms blockOrbitCosetEquiv_reindex
#print axioms nativeFullOrbitCosetEquiv
#print axioms assemble_passive_activeFrame
#print axioms fullFrameBlockEquiv
#print axioms rankLabels
#print axioms activeFrame_numerator
end
end ProductClosure.ProductGraphOrbit
