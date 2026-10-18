module

public import SparseMonotiles.CoarseContactCertificates
public import SparseMonotiles.CarrierHierarchyCoarseChecker

@[expose] public section

/-!
Indexed refinement of the ordinary coarse-row witness API. Rejection uses a
conservative integer signature test: every supplied registry pose is checked to
pass the test, so a failed test proves nonmembership. No signature injectivity
is required; collisions can only prevent a rejection, never prove a false one.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def coarsePoseCode {d : ℕ} (p : Pose d) : ℤ :=
  (List.finRange d).foldl (fun n i => 4096 * n + (p.perm i).val +
    d * (if p.negative i then 1 else 0) + 2 * d * (p.shift i + 64)) 0

inductive IndexedCoarseWitness (d c m : ℕ) where
  | member (index : Fin m)
  | overlap (cell : Cell d)
  | illegalChild (left right : Fin c) (leftCell rightCell : Cell d)

structure IndexedCoarseRow (d c m : ℕ) where
  pose : Pose d
  witness : IndexedCoarseWitness d c m

def IndexedCoarseRow.toRow {d c m : ℕ} (child : Fin c → Pose d)
    (row : IndexedCoarseRow d c m) : CoarseRow d :=
  ⟨row.pose, match row.witness with
    | .member _ => .member
    | .overlap x => .overlap x
    | .illegalChild a b x y => .illegalChild (child a) (child b) x y⟩

def IndexedCoarseRow.check {d c m : ℕ} (child : Fin c → Pose d)
    (registry : Fin m → Pose d) (allowed : ℤ → Bool)
    (row : IndexedCoarseRow d c m) : Bool :=
  match row.witness with
  | .member i => coarsePoseMatchB (coarsePose (fun _ => 0) row.pose) (registry i)
  | .overlap x => decide (ParentOccupies (rootPose d) x ∧ ParentOccupies row.pose x)
  | .illegalChild a b x y =>
      decide (Occupies (child a) x ∧ Occupies (compose row.pose (child b)) y ∧
        AdjacentCells x y) &&
      !(allowed (coarsePoseCode (normalize (child a) (compose row.pose (child b)))))

theorem IndexedCoarseRow.check_sound {d c m : ℕ} (child : Fin c → Pose d)
    (registry : Fin m → Pose d) (allowed : ℤ → Bool)
    (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : ∀ i, child i ∈ C) (hM : ∀ i, registry i ∈ L)
    (hAllowed : ∀ p ∈ L, allowed (coarsePoseCode p) = true)
    (row : IndexedCoarseRow d c m) (h : row.check child registry allowed = true) :
    (row.toRow child).witness.Valid C L (row.toRow child).pose := by
  rcases row with ⟨F, w⟩
  cases w with
  | member i =>
      change coarsePose (fun _ => 0) F ∈ L
      have he := coarsePoseMatchB_sound h
      rw [he]
      exact hM i
  | overlap x =>
      change ParentOccupies (rootPose d) x ∧ ParentOccupies F x
      exact of_decide_eq_true h
  | illegalChild a b x y =>
      have hh : (Occupies (child a) x ∧ Occupies (compose F (child b)) y ∧
          AdjacentCells x y) ∧
          allowed (coarsePoseCode (normalize (child a) (compose F (child b)))) = false := by
        change (decide (Occupies (child a) x ∧ Occupies (compose F (child b)) y ∧
          AdjacentCells x y) && !(allowed (coarsePoseCode
            (normalize (child a) (compose F (child b)))))) = true at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with ⟨hg, hn⟩
        refine ⟨hg, ?_⟩
        cases ha : allowed (coarsePoseCode (normalize (child a) (compose F (child b)))) <;>
          simp_all
      exact ⟨hC a, hC b, hh.1.1, hh.1.2.1, hh.1.2.2,
        fun hk => Bool.false_ne_true (hh.2.symm.trans (hAllowed _ hk))⟩

#print axioms IndexedCoarseRow.check_sound
end SparseMonotiles.CarrierHierarchy
