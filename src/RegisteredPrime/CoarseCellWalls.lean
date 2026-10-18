module
public import RegisteredPrime.WallMasks
public import WeakRecognition.CoarseWorld
@[expose] public section
namespace RegisteredPrime

def roleAtCell {p : Nat} (q : Pose p) (c : Cell p) : Mask p :=
  fun i => decide (q.inv.cell c i = 1)

theorem roleAtCell_bits {p : Nat} (q : Pose p) (c : Cell p) (hc : Occupies q c) :
    (fun i => bit (roleAtCell q c i)) = q.inv.cell c := by
  funext i
  rcases ((occupies_inverse_iff q c).mp hc).1 i with hi | hi <;>
    simp [roleAtCell, bit, hi]

theorem roleAtCell_proper {p : Nat} (q : Pose p) (c : Cell p) (hc : Occupies q c) :
    Proper (roleAtCell q c) := by
  obtain ⟨i, hi⟩ := ((occupies_inverse_iff q c).mp hc).2
  exact ⟨i, by simp [roleAtCell, hi]⟩

theorem roleAtCell_cell {p : Nat} (q : Pose p) (c : Cell p) (hc : Occupies q c) :
    q.cell (fun i => bit (roleAtCell q c i)) = c := by
  rw [roleAtCell_bits q c hc, Pose.cell_inv_cell]

def cellDigit {p : Nat} (q : Pose p) (c : Cell p) : Mask p :=
  fun i => decide (c i = boxLower q i + 1)

theorem cellDigit_bit {p : Nat} (q : Pose p) (c : Cell p) (hc : Occupies q c) (i : Fin p) :
    bit (cellDigit q c i) = c i - boxLower q i := by
  rcases ((occupies_box_iff q c).mp hc).1 i with hi | hi <;>
    simp [cellDigit, bit, hi] <;> omega

theorem refined_roleAtCell_negative (P : Parameters) (q : Pose P.p) (c : Cell P.p)
    (hc : Occupies q c) :
    (refine P q (.outer (roleAtCell q c) (roleAtCell_proper q c hc))).frame.negative = cellDigit q c := by
  funext i
  have h1 := refine_outer_lower P q (roleAtCell q c) (roleAtCell_proper q c hc) i
  have h2 := refine_outer_macrocell P q (roleAtCell q c) (roleAtCell_proper q c hc) i
  rw [roleAtCell_cell q c hc] at h2
  have h3 := cellDigit_bit q c hc i
  cases hn : (refine P q (.outer (roleAtCell q c) (roleAtCell_proper q c hc))).frame.negative i <;>
    cases hd : cellDigit q c i <;> simp [hn, hd, bit] at h1 h3 ⊢ <;> omega

/-- Every actual coarse cell face inherits the singleton/complement mask test
from a real fine outer interface. The fine test is an explicit contact clause. -/
theorem child_recognition_coarse_cell_wall_test (P : Parameters) (q r : Pose P.p)
    (hl : WeakRecognition.ChildRecognition P (doubleAnchor q) (doubleAnchor r))
    (x y : Cell P.p) (hx : Occupies q x) (hy : Occupies r y) (j : Fin P.p)
    (hj : x j = y j + 1 ∨ y j = x j + 1) (ht : ∀ i, i ≠ j → x i = y i) :
    WallMaskAt (fun i => xor (cellDigit q x i) (cellDigit r y i)) j := by
  let A := roleAtCell q x
  let B := roleAtCell r y
  let hA := roleAtCell_proper q x hx
  let hB := roleAtCell_proper r y hy
  let Q := refine P q (.outer A hA)
  let R := refine P r (.outer B hB)
  have hcell : Adjacent (q.cell (fun i => bit (A i))) (r.cell (fun i => bit (B i))) := by
    rw [roleAtCell_cell q x hx, roleAtCell_cell r y hy]
    exact ⟨j, hj, ht⟩
  have hc : FaceContact Q R := refined_outer_contact_of_adjacent_cells P q r A B hA hB hcell
  have hrec : RecognitionContact P (Q.relative R) := hl (.outer A hA) (.outer B hB) hc
  have he : ∀ i, (Q.relative R).anchor i % 2 = 0 := by
    apply same_anchor_parity_relative_even Q R
    intro i
    exact (refine_anchor_parity P q (.outer A hA) i).trans
      (refine_anchor_parity P r (.outer B hB) i).symm
  have hw := hrec.walls he
  have hQ : ∀ i, boxLower Q i = 2 * x i := by
    intro i
    rw [refine_outer_macrocell, roleAtCell_cell q x hx]
  have hR : ∀ i, boxLower R i = 2 * y i := by
    intro i
    rw [refine_outer_macrocell, roleAtCell_cell r y hy]
  have haxis : boxLower R j = boxLower Q j + 2 ∨ boxLower Q j = boxLower R j + 2 := by
    rw [hQ, hR]
    omega
  have htrans : ∀ i, i ≠ j → boxLower Q i = boxLower R i := by
    intro i hij
    rw [hQ, hR, ht i hij]
  have hm := relative_wall_mask_at Q R j haxis htrans hw
  have hnQ : Q.frame.negative = cellDigit q x := refined_roleAtCell_negative P q x hx
  have hnR : R.frame.negative = cellDigit r y := refined_roleAtCell_negative P r y hy
  simpa only [hnQ, hnR] using hm

end RegisteredPrime
