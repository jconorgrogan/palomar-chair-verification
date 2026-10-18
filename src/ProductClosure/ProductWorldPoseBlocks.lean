module

public import ProductClosure.ProductWorldBlockChart
public import ProductClosure.ProductPolycube

@[expose] public section

/-! Exact restriction of a block-preserving ambient registered pose to its
two complete factor poses, and literal occupied-cell product transport. -/
namespace ProductClosure.World

open Set
noncomputable section

variable {m n : ℕ}

theorem inverse_preservesBlocks (q : RegisteredPrime.Pose (m + n))
    (h : PreservesBlocks q) (i : Fin (m + n)) :
    (q.frame.inverse i).val < m ↔ i.val < m := by
  have hi := h (q.frame.inverse i)
  rw [q.frame.right_inverse] at hi
  exact hi.symm

def leftPerm (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) (i : Fin m) : Fin m :=
  ⟨(q.frame.perm (Fin.castAdd n i)).val, (h _).mpr i.isLt⟩

def leftInverse (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) (i : Fin m) : Fin m :=
  ⟨(q.frame.inverse (Fin.castAdd n i)).val, (inverse_preservesBlocks q h _).mpr i.isLt⟩

@[simp] theorem castAdd_leftPerm (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q)
    (i : Fin m) : Fin.castAdd n (leftPerm q h i) = q.frame.perm (Fin.castAdd n i) :=
  Fin.ext rfl

@[simp] theorem castAdd_leftInverse (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q)
    (i : Fin m) : Fin.castAdd n (leftInverse q h i) = q.frame.inverse (Fin.castAdd n i) :=
  Fin.ext rfl

def leftFrame (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) :
    RegisteredPrime.RegisteredFrame m where
  perm := leftPerm q h
  inverse := leftInverse q h
  left_inverse i := by
    apply Fin.ext
    have he := congrArg Fin.val (show Fin.castAdd n (leftInverse q h (leftPerm q h i)) =
      Fin.castAdd n i by rw [castAdd_leftInverse, castAdd_leftPerm, q.frame.left_inverse])
    exact he
  right_inverse i := by
    apply Fin.ext
    have he := congrArg Fin.val (show Fin.castAdd n (leftPerm q h (leftInverse q h i)) =
      Fin.castAdd n i by rw [castAdd_leftPerm, castAdd_leftInverse, q.frame.right_inverse])
    exact he
  negative i := q.frame.negative (Fin.castAdd n i)

def rightPerm (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) (i : Fin n) : Fin n :=
  ⟨(q.frame.perm (Fin.natAdd m i)).val - m, by
    have hh := h (Fin.natAdd m i)
    have hn : ¬(Fin.natAdd m i).val < m := by simp
    have hlo := mt hh.mp hn
    have hup := (q.frame.perm (Fin.natAdd m i)).isLt
    omega⟩

def rightInverse (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) (i : Fin n) : Fin n :=
  ⟨(q.frame.inverse (Fin.natAdd m i)).val - m, by
    have hh := inverse_preservesBlocks q h (Fin.natAdd m i)
    have hn : ¬(Fin.natAdd m i).val < m := by simp
    have hlo := mt hh.mp hn
    have hup := (q.frame.inverse (Fin.natAdd m i)).isLt
    omega⟩

@[simp] theorem natAdd_rightPerm (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q)
    (i : Fin n) : Fin.natAdd m (rightPerm q h i) = q.frame.perm (Fin.natAdd m i) := by
  apply Fin.ext
  have hh := h (Fin.natAdd m i)
  have hn : ¬(Fin.natAdd m i).val < m := by simp
  have hlo := mt hh.mp hn
  simp only [Fin.val_natAdd, rightPerm]
  omega

@[simp] theorem natAdd_rightInverse (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q)
    (i : Fin n) : Fin.natAdd m (rightInverse q h i) = q.frame.inverse (Fin.natAdd m i) := by
  apply Fin.ext
  have hh := inverse_preservesBlocks q h (Fin.natAdd m i)
  have hn : ¬(Fin.natAdd m i).val < m := by simp
  have hlo := mt hh.mp hn
  simp only [Fin.val_natAdd, rightInverse]
  omega

def rightFrame (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) :
    RegisteredPrime.RegisteredFrame n where
  perm := rightPerm q h
  inverse := rightInverse q h
  left_inverse i := by
    apply Fin.ext
    have he := congrArg Fin.val (show Fin.natAdd m (rightInverse q h (rightPerm q h i)) =
      Fin.natAdd m i by rw [natAdd_rightInverse, natAdd_rightPerm, q.frame.left_inverse])
    simp only [Fin.val_natAdd] at he
    omega
  right_inverse i := by
    apply Fin.ext
    have he := congrArg Fin.val (show Fin.natAdd m (rightPerm q h (rightInverse q h i)) =
      Fin.natAdd m i by rw [natAdd_rightPerm, natAdd_rightInverse, q.frame.right_inverse])
    simp only [Fin.val_natAdd] at he
    omega
  negative i := q.frame.negative (Fin.natAdd m i)

/-- Full active placed pose, including translation and all signed-frame data. -/
def leftPose (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) :
    RegisteredPrime.Pose m where
  frame := leftFrame q h
  anchor i := q.anchor (Fin.castAdd n i)

/-- Full passive placed pose, including translation and all signed-frame data. -/
def rightPose (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) :
    RegisteredPrime.Pose n where
  frame := rightFrame q h
  anchor i := q.anchor (Fin.natAdd m i)

theorem leftIndex_poseCellIndex (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q)
    (x : Lattice m) (y : Lattice n) :
    Polycube.leftIndex (poseCellIndex q (Fin.append x y)) = poseCellIndex (leftPose q h) x := by
  funext i
  change q.anchor (Fin.castAdd n i) +
    (if q.frame.negative (Fin.castAdd n i) then
      -(Fin.append x y) (q.frame.perm (Fin.castAdd n i)) - 1
      else (Fin.append x y) (q.frame.perm (Fin.castAdd n i))) = _
  rw [← castAdd_leftPerm q h i]
  simp only [Fin.append_left, poseCellIndex, leftPose, leftFrame]
  rfl

theorem rightIndex_poseCellIndex (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q)
    (x : Lattice m) (y : Lattice n) :
    Polycube.rightIndex (poseCellIndex q (Fin.append x y)) = poseCellIndex (rightPose q h) y := by
  funext i
  change q.anchor (Fin.natAdd m i) +
    (if q.frame.negative (Fin.natAdd m i) then
      -(Fin.append x y) (q.frame.perm (Fin.natAdd m i)) - 1
      else (Fin.append x y) (q.frame.perm (Fin.natAdd m i))) = _
  rw [← natAdd_rightPerm q h i]
  simp only [Fin.append_right, poseCellIndex, rightPose, rightFrame]
  rfl

theorem poseCellIndex_append (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q)
    (x : Lattice m) (y : Lattice n) :
    poseCellIndex q (Fin.append x y) =
      Fin.append (poseCellIndex (leftPose q h) x) (poseCellIndex (rightPose q h) y) := by
  rw [← leftIndex_poseCellIndex q h x y, ← rightIndex_poseCellIndex q h x y]
  exact (Polycube.append_leftIndex_rightIndex _).symm

/-- The complete occupied set of a normalized block-preserving product tile
is exactly the product of the two actual factor-pose footprints. -/
theorem placedCells_product_iff (S : Finset (Lattice m)) (T : Finset (Lattice n))
    (q : RegisteredPrime.Pose (m + n)) (h : PreservesBlocks q) (z : Lattice (m + n)) :
    z ∈ placedCells (Polycube.productCells S T) q ↔
      Polycube.leftIndex z ∈ placedCells S (leftPose q h) ∧
      Polycube.rightIndex z ∈ placedCells T (rightPose q h) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := (Polycube.mem_productCells S T w).mp hw
    have he : w = Fin.append (Polycube.leftIndex w) (Polycube.rightIndex w) :=
      (Polycube.append_leftIndex_rightIndex w).symm
    constructor
    · refine ⟨Polycube.leftIndex w, hw'.1, ?_⟩
      conv_rhs => rw [he]
      exact (leftIndex_poseCellIndex q h _ _).symm
    · refine ⟨Polycube.rightIndex w, hw'.2, ?_⟩
      conv_rhs => rw [he]
      exact (rightIndex_poseCellIndex q h _ _).symm
  · rintro ⟨⟨x, hx, hzx⟩, ⟨y, hy, hzy⟩⟩
    refine ⟨Fin.append x y, (Polycube.append_mem_productCells S T x y).mpr ⟨hx, hy⟩, ?_⟩
    rw [poseCellIndex_append q h, hzx, hzy]
    exact Polycube.append_leftIndex_rightIndex z

/-- Equality of both restricted complete poses implies equality of the
ambient pose. In particular the splitting forgets no placed-frame phase. -/
theorem splitPose_injective (q r : RegisteredPrime.Pose (m + n))
    (hq : PreservesBlocks q) (hr : PreservesBlocks r)
    (hleft : leftPose q hq = leftPose r hr)
    (hright : rightPose q hq = rightPose r hr) : q = r := by
  apply RegisteredPrime.Pose.Same.eq
  constructor
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      have he := congrArg (fun p : RegisteredPrime.Pose m => p.frame.perm j) hleft
      have he' := congrArg (Fin.castAdd n) he
      simpa only [leftPose, leftFrame, castAdd_leftPerm] using he'
    · intro j
      have he := congrArg (fun p : RegisteredPrime.Pose n => p.frame.perm j) hright
      have he' := congrArg (Fin.natAdd m) he
      simpa only [rightPose, rightFrame, natAdd_rightPerm] using he'
  constructor
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact congrArg (fun p : RegisteredPrime.Pose m => p.frame.negative j) hleft
    · intro j
      exact congrArg (fun p : RegisteredPrime.Pose n => p.frame.negative j) hright
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact congrArg (fun p : RegisteredPrime.Pose m => p.anchor j) hleft
    · intro j
      exact congrArg (fun p : RegisteredPrime.Pose n => p.anchor j) hright

#print axioms poseCellIndex_append
#print axioms placedCells_product_iff
#print axioms splitPose_injective

end
end ProductClosure.World
