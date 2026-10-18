module

public import ProductClosure.ProductWorldRelative

@[expose] public section

/-! Actual full registered block poses, inverse to exact factor-pose splitting. -/
namespace ProductClosure.World

noncomputable section
variable {m n : ℕ}

/-- Direct sum of the original signed row frames. -/
def blockFrame (F : RegisteredPrime.RegisteredFrame m) (G : RegisteredPrime.RegisteredFrame n) :
    RegisteredPrime.RegisteredFrame (m + n) where
  perm := Fin.addCases (fun i => Fin.castAdd n (F.perm i)) (fun i => Fin.natAdd m (G.perm i))
  inverse := Fin.addCases (fun i => Fin.castAdd n (F.inverse i)) (fun i => Fin.natAdd m (G.inverse i))
  left_inverse i := by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [F.left_inverse, G.left_inverse]
  right_inverse i := by
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [F.right_inverse, G.right_inverse]
  negative := Fin.append F.negative G.negative

/-- Direct product of two entire placed factor poses. -/
def blockPose (q : RegisteredPrime.Pose m) (r : RegisteredPrime.Pose n) :
    RegisteredPrime.Pose (m + n) where
  frame := blockFrame q.frame r.frame
  anchor := Fin.append q.anchor r.anchor

theorem blockPose_preservesBlocks (q : RegisteredPrime.Pose m) (r : RegisteredPrime.Pose n) :
    PreservesBlocks (blockPose q r) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [blockPose, blockFrame]
  · intro j
    simp [blockPose, blockFrame]

@[simp] theorem leftPose_blockPose (q : RegisteredPrime.Pose m) (r : RegisteredPrime.Pose n) :
    leftPose (blockPose q r) (blockPose_preservesBlocks q r) = q := by
  apply RegisteredPrime.Pose.Same.eq
  constructor
  · intro i; apply Fin.ext
    simp [leftPose, leftFrame, leftPerm, blockPose, blockFrame]
  constructor <;> intro i <;> simp [leftPose, leftFrame, blockPose, blockFrame]

@[simp] theorem rightPose_blockPose (q : RegisteredPrime.Pose m) (r : RegisteredPrime.Pose n) :
    rightPose (blockPose q r) (blockPose_preservesBlocks q r) = r := by
  apply RegisteredPrime.Pose.Same.eq
  constructor
  · intro i; apply Fin.ext
    simp [rightPose, rightFrame, rightPerm, blockPose, blockFrame]
  constructor <;> intro i <;> simp [rightPose, rightFrame, blockPose, blockFrame]

/-- Reassembly equals the complete original ambient pose, including signs
and anchors, rather than only its action on the unmarked carrier. -/
theorem blockPose_left_right (q : RegisteredPrime.Pose (m + n)) (hq : PreservesBlocks q) :
    blockPose (leftPose q hq) (rightPose q hq) = q := by
  apply splitPose_injective _ _ (blockPose_preservesBlocks _ _) hq
  · exact leftPose_blockPose _ _
  · exact rightPose_blockPose _ _

theorem blockPose_injective : Function.Injective
    (fun p : RegisteredPrime.Pose m × RegisteredPrime.Pose n => blockPose p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · have h := congrArg (fun e : {e : RegisteredPrime.Pose (m + n) // PreservesBlocks e} =>
      leftPose e.val e.property)
      (show (⟨blockPose p.1 p.2, blockPose_preservesBlocks _ _⟩ : {e // PreservesBlocks e}) =
        ⟨blockPose q.1 q.2, blockPose_preservesBlocks _ _⟩ from Subtype.ext hpq)
    simpa using h
  · have h := congrArg (fun e : {e : RegisteredPrime.Pose (m + n) // PreservesBlocks e} =>
      rightPose e.val e.property)
      (show (⟨blockPose p.1 p.2, blockPose_preservesBlocks _ _⟩ : {e // PreservesBlocks e}) =
        ⟨blockPose q.1 q.2, blockPose_preservesBlocks _ _⟩ from Subtype.ext hpq)
    simpa using h

/-- Explicit exact equivalence between block-preserving complete ambient
poses and pairs of complete factor poses. -/
def blockPoseEquiv : (RegisteredPrime.Pose m × RegisteredPrime.Pose n) ≃
    {q : RegisteredPrime.Pose (m + n) // PreservesBlocks q} where
  toFun p := ⟨blockPose p.1 p.2, blockPose_preservesBlocks _ _⟩
  invFun q := (leftPose q.val q.property, rightPose q.val q.property)
  left_inv p := by cases p; simp
  right_inv q := Subtype.ext (blockPose_left_right q.val q.property)

@[simp] theorem poseCellIndex_blockPose (q : RegisteredPrime.Pose m) (r : RegisteredPrime.Pose n)
    (x : Lattice m) (y : Lattice n) :
    poseCellIndex (blockPose q r) (Fin.append x y) =
      Fin.append (poseCellIndex q x) (poseCellIndex r y) := by
  simpa only [leftPose_blockPose, rightPose_blockPose] using
    poseCellIndex_append (blockPose q r) (blockPose_preservesBlocks q r) x y

/-- Canonical dimension cast on full pose data. -/
def castPose {d e : ℕ} (h : d = e) (q : RegisteredPrime.Pose d) : RegisteredPrime.Pose e := h ▸ q

@[simp] theorem castPose_perm {d e : ℕ} (h : d = e) (q : RegisteredPrime.Pose d) (i : Fin d) :
    (castPose h q).frame.perm (Fin.cast h i) = Fin.cast h (q.frame.perm i) := by subst e; rfl
@[simp] theorem castPose_negative {d e : ℕ} (h : d = e) (q : RegisteredPrime.Pose d) (i : Fin d) :
    (castPose h q).frame.negative (Fin.cast h i) = q.frame.negative i := by subst e; rfl
@[simp] theorem castPose_anchor {d e : ℕ} (h : d = e) (q : RegisteredPrime.Pose d) (i : Fin d) :
    (castPose h q).anchor (Fin.cast h i) = q.anchor i := by subst e; rfl

/-- Exact Euclidean action of the combined pose in canonical product
coordinates. This is an equality of genuine isometries on every point. -/
theorem poseIsometry_blockPose_append {a b : ℕ}
    (q : RegisteredPrime.Pose (a + 1)) (r : RegisteredPrime.Pose (b + 1))
    (x : Polycube.Space (a + 1)) (y : Polycube.Space (b + 1)) :
    PhysicalRegistration.NativeChair.poseIsometry (m := a + 1 + b) (blockPose (m := a + 1) (n := b + 1) q r)
      (Polycube.appendPoint (m := a + 1) (n := b + 1) x y) =
      Polycube.appendPoint (m := a + 1) (n := b + 1) (PhysicalRegistration.NativeChair.poseIsometry q x)
        (PhysicalRegistration.NativeChair.poseIsometry r y) := by
  ext i
  refine Fin.addCases (m := a + 1) (n := b + 1) ?_ ?_ i <;> intro j <;>
    simp [PhysicalRegistration.NativeChair.poseIsometry_apply, blockPose, blockFrame,
      RegisteredPrime.RegisteredFrame.sign, Polycube.appendPoint]

#print axioms blockPoseEquiv
#print axioms poseIsometry_blockPose_append

end
end ProductClosure.World
