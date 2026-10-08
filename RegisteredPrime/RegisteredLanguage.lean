module
public import RegisteredPrime.ExactChildImages
@[expose] public section
namespace RegisteredPrime
structure RegisteredFrame (p : Nat) where
  perm : Fin p → Fin p
  inverse : Fin p → Fin p
  left_inverse : ∀ i, inverse (perm i) = i
  right_inverse : ∀ i, perm (inverse i) = i
  negative : Mask p
structure Pose (p : Nat) where
  frame : RegisteredFrame p
  anchor : Cell p
def RegisteredFrame.sign {p : Nat} (F : RegisteredFrame p) (i : Fin p) : Int :=
  if F.negative i then -1 else 1
def RegisteredFrame.linear {p : Nat} (F : RegisteredFrame p) (x : Cell p) : Cell p :=
  fun i => F.sign i * x (F.perm i)
def Pose.cell {p : Nat} (q : Pose p) (x : Cell p) : Cell p :=
  fun i => q.anchor i + q.frame.linear x i - bit (q.frame.negative i)
def RegisteredFrame.comp {p : Nat} (F G : RegisteredFrame p) : RegisteredFrame p where
  perm := fun i => G.perm (F.perm i)
  inverse := fun i => F.inverse (G.inverse i)
  left_inverse := fun i => by rw [G.left_inverse, F.left_inverse]
  right_inverse := fun i => by rw [F.right_inverse, G.right_inverse]
  negative := fun i => xor (F.negative i) (G.negative (F.perm i))
def RegisteredFrame.inv {p : Nat} (F : RegisteredFrame p) : RegisteredFrame p where
  perm := F.inverse
  inverse := F.perm
  left_inverse := F.right_inverse
  right_inverse := F.left_inverse
  negative := fun i => F.negative (F.inverse i)
def Pose.comp {p : Nat} (q r : Pose p) : Pose p where
  frame := q.frame.comp r.frame
  anchor := fun i => q.anchor i + q.frame.linear r.anchor i
def Pose.inv {p : Nat} (q : Pose p) : Pose p where
  frame := q.frame.inv
  anchor := fun i => -(q.frame.inv.linear q.anchor i)
def Pose.relative {p : Nat} (q r : Pose p) : Pose p := q.inv.comp r
def Pose.Same {p : Nat} (q r : Pose p) : Prop :=
  (∀ i, q.frame.perm i = r.frame.perm i) ∧
  (∀ i, q.frame.negative i = r.frame.negative i) ∧
  (∀ i, q.anchor i = r.anchor i)
noncomputable def arithmeticChild (P : Parameters) (r : Role P.p) : Pose P.p where
  frame := {
    perm := childIndex P r
    inverse := childIndexInverse P r
    left_inverse := childIndex_left_inverse P r
    right_inverse := childIndex_right_inverse P r
    negative := fun i => (childFrame P r).neg i.val
  }
  anchor := childShift P r
@[simp] theorem arithmeticChild_cell (P : Parameters) (r : Role P.p) (x : Cell P.p) :
    (arithmeticChild P r).cell x = childCell P r x := rfl
def Occupies {p : Nat} (q : Pose p) (c : Cell p) : Prop :=
  ∃ b, UnitChairCell b ∧ q.cell b = c
@[simp] theorem arithmeticChild_occupies (P : Parameters) (r : Role P.p) (c : Cell P.p) :
    Occupies (arithmeticChild P r) c ↔ ChildOccupies P r c := Iff.rfl
def Disjoint {p : Nat} (q r : Pose p) : Prop :=
  ∀ c, ¬ (Occupies q c ∧ Occupies r c)
def Adjacent {p : Nat} (a b : Cell p) : Prop :=
  ∃ j, (a j = b j + 1 ∨ b j = a j + 1) ∧ ∀ i, i ≠ j → a i = b i
def FaceContact {p : Nat} (q r : Pose p) : Prop :=
  Disjoint q r ∧ ∃ a b, Occupies q a ∧ Occupies r b ∧ Adjacent a b
noncomputable def refine (P : Parameters) (q : Pose P.p) (r : Role P.p) : Pose P.p :=
  ({ frame := q.frame, anchor := fun i => 2 * q.anchor i } : Pose P.p).comp
    (arithmeticChild P r)
noncomputable def Descendant (P : Parameters) : Nat → Pose P.p → Pose P.p → Prop
  | 0, q, t => q.Same t
  | n + 1, q, t => ∃ r, Descendant P n (refine P q r) t
def identityPose (p : Nat) : Pose p where
  frame := {
    perm := fun i => i
    inverse := fun i => i
    left_inverse := fun _ => rfl
    right_inverse := fun _ => rfl
    negative := fun _ => false
  }
  anchor := fun _ => 0
def GeneratedContact (P : Parameters) (e : Pose P.p) : Prop :=
  ∃ n q r, Descendant P n (identityPose P.p) q ∧
    Descendant P n (identityPose P.p) r ∧ FaceContact q r ∧ (q.relative r).Same e
structure RegisteredWorld (p : Nat) where
  tiles : Pose p → Prop
  covers : ∀ c, ∃ q, tiles q ∧ Occupies q c
  nonoverlap : ∀ q r, tiles q → tiles r → ∀ c,
    Occupies q c → Occupies r c → q.Same r
def RegisteredWorld.Legal (P : Parameters) (W : RegisteredWorld P.p) : Prop :=
  ∀ q r, W.tiles q → W.tiles r → FaceContact q r → GeneratedContact P (q.relative r)
theorem arithmetic_children_partition (P : Parameters) (c : Cell P.p)
    (hc : DoubledChairCell c) :
    ∃ r, Occupies (arithmeticChild P r) c ∧
      ∀ s, Occupies (arithmeticChild P s) c → s = r := exact_dissection P c hc
theorem Pose.comp_cell {p : Nat} (q r : Pose p) (c : Cell p) :
    (q.comp r).cell c = q.cell (r.cell c) := by
  funext i
  simp only [Pose.comp, Pose.cell, RegisteredFrame.linear, RegisteredFrame.comp,
    RegisteredFrame.sign, bit]
  by_cases hq : q.frame.negative i = true <;>
    by_cases hr : r.frame.negative (q.frame.perm i) = true <;>
    simp [hq, hr] <;> omega
end RegisteredPrime
