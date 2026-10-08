module
public import RegisteredPrime.RegisteredLanguage
@[expose] public section
namespace RegisteredPrime
open Uniform
def RegisteredFrame.toUniform {p : Nat} (F : RegisteredFrame p) : Uniform.Frame where
  perm := fun i => if h : i < p then (F.perm ⟨i, h⟩).val else i
  neg := extendMask F.negative
def RegisteredFrame.IsProper {p : Nat} (F : RegisteredFrame p) : Prop :=
  Uniform.IsRotation p F.toUniform
theorem rotation_congr_on {p : Nat} (F G : Uniform.Frame)
    (hperm : ∀ i, i < p → F.perm i = G.perm i)
    (hneg : ∀ i, i < p → F.neg i = G.neg i) :
    IsRotation p F ↔ IsRotation p G := by
  have hper : IsPermOn p F.perm ↔ IsPermOn p G.perm := by
    constructor
    · intro h
      constructor
      · intro i hi
        rw [← hperm i hi]
        exact h.1 i hi
      · intro i j hi hj hij
        apply h.2 i j hi hj
        rw [hperm i hi, hperm j hj]
        exact hij
    · intro h
      constructor
      · intro i hi
        rw [hperm i hi]
        exact h.1 i hi
      · intro i j hi hj hij
        apply h.2 i j hi hj
        rw [← hperm i hi, ← hperm j hj]
        exact hij
  have hcount : invCount p F.perm = invCount p G.perm := by
    unfold invCount
    apply List.countP_congr
    intro q hq
    have h := mem_pairs.mp hq
    rw [hperm q.1 (by omega), hperm q.2 h.2]
  have hsign : signProd p F.neg = signProd p G.neg := by
    unfold signProd
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hneg i (List.mem_range.mp hi)]
  unfold IsRotation permSign
  rw [hper, hcount, hsign]
theorem arithmeticChild_proper (P : Parameters) (r : Role P.p) :
    (arithmeticChild P r).frame.IsProper := by
  unfold RegisteredFrame.IsProper
  apply (rotation_congr_on (childFrame P r) (arithmeticChild P r).frame.toUniform
    (fun i hi => by simp [RegisteredFrame.toUniform, arithmeticChild, childIndex, hi])
    (fun i hi => by simp [RegisteredFrame.toUniform, arithmeticChild, extendMask, hi])).mp
  exact all_child_frames_rotation P r
def RegisteredWorld.Proper {p : Nat} (W : RegisteredWorld p) : Prop :=
  ∀ q, W.tiles q → q.frame.IsProper
end RegisteredPrime
