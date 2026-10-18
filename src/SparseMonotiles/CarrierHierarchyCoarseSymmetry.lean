module

public import SparseMonotiles.CarrierHierarchyCoarseTransfer

@[expose] public section

/-!
Simultaneous coordinate conjugation of the finite coarse problem. This is not
an additional physical right gauge or a claimed symmetry of the keyed body.
The finite child/language invariance premises must be checked for each action.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def conjugatePose {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) : Pose d :=
  compose (unsignedPose r) (rightGauge r.symm p)

def reindexCell {d : ℕ} (r : Equiv.Perm (Fin d)) (c : Cell d) : Cell d := fun i => c (r i)

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

@[simp] theorem conjugatePose_perm {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) (i : Fin d) :
    (conjugatePose r p).perm i = r.symm (p.perm (r i)) := rfl

@[simp] theorem conjugatePose_negative {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) (i : Fin d) :
    (conjugatePose r p).negative i = p.negative (r i) := by
  simp [conjugatePose, compose, unsignedPose, rightGauge]

@[simp] theorem conjugatePose_shift {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) (i : Fin d) :
    (conjugatePose r p).shift i = p.shift (r i) := by
  simp [conjugatePose, compose, unsignedPose, rightGauge, Pose.sign]

@[simp] theorem conjugatePose_root {d : ℕ} (r : Equiv.Perm (Fin d)) :
    conjugatePose r (rootPose d) = rootPose d := by
  apply pose_ext
  · ext i
    simp [rootPose]
  · funext i
    simp [rootPose]
  · funext i
    simp [rootPose]

theorem conjugatePose_symm_cancel {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) :
    conjugatePose r.symm (conjugatePose r p) = p := by
  apply pose_ext
  · ext i
    simp
  · funext i
    simp
  · funext i
    simp

theorem conjugatePose_compose {d : ℕ} (r : Equiv.Perm (Fin d)) (p q : Pose d) :
    conjugatePose r (compose p q) = compose (conjugatePose r p) (conjugatePose r q) := by
  apply pose_ext
  · ext i
    simp [compose]
  · funext i
    simp [compose]
  · funext i
    simp [compose, Pose.sign]

theorem conjugatePose_inverse {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) :
    conjugatePose r (inversePose p) = inversePose (conjugatePose r p) := by
  apply compose_left_injective (conjugatePose r p)
  rw [← conjugatePose_compose, compose_inversePose, conjugatePose_root, compose_inversePose]

theorem conjugatePose_normalize {d : ℕ} (r : Equiv.Perm (Fin d)) (p q : Pose d) :
    conjugatePose r (normalize p q) = normalize (conjugatePose r p) (conjugatePose r q) := by
  simp only [normalize, conjugatePose_compose, conjugatePose_inverse]

theorem conjugatePose_candidate {d : ℕ} (r : Equiv.Perm (Fin d)) (a b k : Pose d) :
    conjugatePose r (parentCandidate a b k) =
      parentCandidate (conjugatePose r a) (conjugatePose r b) (conjugatePose r k) := by
  simp only [parentCandidate, conjugatePose_compose, conjugatePose_inverse]

theorem conjugatePose_even_iff {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) :
    (∀ i, (conjugatePose r p).shift i % 2 = 0) ↔ ∀ i, p.shift i % 2 = 0 := by
  constructor
  · intro h i
    simpa using h (r.symm i)
  · intro h i
    simpa using h (r i)

theorem coarsePose_conjugate {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) :
    coarsePose (fun _ => 0) (conjugatePose r p) = conjugatePose r (coarsePose (fun _ => 0) p) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    simp [coarsePose]

theorem conjugatePose_cell {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) (c : Cell d) :
    (conjugatePose r p).cell (reindexCell r c) = reindexCell r (p.cell c) := by
  funext i
  simp [Pose.cell, Pose.sign, reindexCell]

private theorem conjugatePose_inverseCell {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) (c : Cell d) :
    (conjugatePose r p).inverseCell (reindexCell r c) = reindexCell r (p.inverseCell c) := by
  apply cell_injective (conjugatePose r p)
  rw [Pose.cell_inverseCell, conjugatePose_cell, Pose.cell_inverseCell]

theorem conjugatePose_occupies {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) (c : Cell d) :
    Occupies (conjugatePose r p) (reindexCell r c) ↔ Occupies p c := by
  rw [Occupies, conjugatePose_inverseCell]
  change IsChairCell (fun i => p.inverseCell c (r i)) ↔ IsChairCell (p.inverseCell c)
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => by simpa using h (r.symm j), r i, hi⟩
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => h (r j), r.symm i, by simpa using hi⟩

theorem conjugatePose_parentOccupies {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) (c : Cell d) :
    ParentOccupies (conjugatePose r p) (reindexCell r c) ↔ ParentOccupies p c := by
  rw [ParentOccupies, conjugatePose_inverseCell]
  change DoubleCell (fun i => p.inverseCell c (r i)) ↔ DoubleCell (p.inverseCell c)
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => by simpa using h (r.symm j), r i, hi⟩
  · rintro ⟨h, i, hi⟩
    exact ⟨fun j => h (r j), r.symm i, by simpa using hi⟩

theorem reindexCell_adjacent {d : ℕ} (r : Equiv.Perm (Fin d)) {c b : Cell d}
    (h : AdjacentCells c b) : AdjacentCells (reindexCell r c) (reindexCell r b) := by
  have hc : (unsignedPose r).cell c = reindexCell r c := by
    funext i
    simp [Pose.cell, unsignedPose, Pose.sign, reindexCell]
  have hb : (unsignedPose r).cell b = reindexCell r b := by
    funext i
    simp [Pose.cell, unsignedPose, Pose.sign, reindexCell]
  rw [← hc, ← hb]
  exact adjacent_cell_image (unsignedPose r) h

/-- Forward closure for both a symmetry and its inverse proves exact membership
invariance; no finite-set cardinality or code-injectivity shortcut is needed. -/
theorem conjugate_membership_iff {d : ℕ} (r : Equiv.Perm (Fin d)) (L : Set (Pose d))
    (hforward : ∀ p ∈ L, conjugatePose r p ∈ L)
    (hbackward : ∀ p ∈ L, conjugatePose r.symm p ∈ L) (p : Pose d) :
    conjugatePose r p ∈ L ↔ p ∈ L := by
  constructor
  · intro h
    simpa only [conjugatePose_symm_cancel] using hbackward _ h
  · exact hforward p

def CoarseWitness.conjugate {d : ℕ} (r : Equiv.Perm (Fin d)) : CoarseWitness d → CoarseWitness d
  | .member => .member
  | .overlap c => .overlap (reindexCell r c)
  | .illegalChild a b c e => .illegalChild (conjugatePose r a) (conjugatePose r b)
      (reindexCell r c) (reindexCell r e)

def CoarseRow.conjugate {d : ℕ} (r : Equiv.Perm (Fin d)) (row : CoarseRow d) : CoarseRow d :=
  ⟨conjugatePose r row.pose, row.witness.conjugate r⟩

theorem CoarseWitness.conjugate_validBetween {d : ℕ} (r : Equiv.Perm (Fin d))
    (C : Finset (Pose d)) (Lf Lc : Set (Pose d))
    (hC : ∀ p ∈ C, conjugatePose r p ∈ C)
    (hLf : ∀ p, conjugatePose r p ∈ Lf ↔ p ∈ Lf)
    (hLc : ∀ p, conjugatePose r p ∈ Lc ↔ p ∈ Lc)
    {F : Pose d} {w : CoarseWitness d} (hw : w.ValidBetween C Lf Lc F) :
    (w.conjugate r).ValidBetween C Lf Lc (conjugatePose r F) := by
  cases w with
  | member =>
      change coarsePose (fun _ => 0) (conjugatePose r F) ∈ Lc
      rw [coarsePose_conjugate]
      exact (hLc _).mpr hw
  | overlap c =>
      obtain ⟨hroot, hF⟩ := hw
      constructor
      · simpa only [conjugatePose_root] using
          (conjugatePose_parentOccupies r (rootPose d) c).mpr hroot
      · exact (conjugatePose_parentOccupies r F c).mpr hF
  | illegalChild a b c e =>
      obtain ⟨ha, hb, hac, hbe, hadj, hbad⟩ := hw
      refine ⟨hC a ha, hC b hb, (conjugatePose_occupies r a c).mpr hac, ?_,
        reindexCell_adjacent r hadj, ?_⟩
      · rw [← conjugatePose_compose]
        exact (conjugatePose_occupies r (compose F b) e).mpr hbe
      · rw [← conjugatePose_compose, ← conjugatePose_normalize]
        exact fun h => hbad ((hLf _).mp h)

theorem CoarseWitness.conjugate_valid {d : ℕ} (r : Equiv.Perm (Fin d))
    (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : ∀ p ∈ C, conjugatePose r p ∈ C)
    (hL : ∀ p, conjugatePose r p ∈ L ↔ p ∈ L)
    {F : Pose d} {w : CoarseWitness d} (hw : w.Valid C L F) :
    (w.conjugate r).Valid C L (conjugatePose r F) := by
  apply (CoarseWitness.validBetween_same C L _ _).mp
  exact w.conjugate_validBetween r C L L hC hL hL ((CoarseWitness.validBetween_same C L F w).mpr hw)

#print axioms conjugatePose_candidate
#print axioms conjugatePose_even_iff
#print axioms CoarseWitness.conjugate_validBetween
#print axioms CoarseWitness.conjugate_valid
end SparseMonotiles.CarrierHierarchy
