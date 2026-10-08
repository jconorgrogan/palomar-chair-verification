module
public import RegisteredPrime.ArithmeticAtlas
public import AtlasPeriods.Aperiodicity

@[expose] public section
namespace CompactT7Preparation
open RegisteredPrime
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

-- Literal finite registry source SHA-256: 26403cdb1291b173904a28adf9044738db34d837d06bb4e8115cfab257cc0fa0
-- This module proves only the named finite entry conditions and a conditional adapter.
-- It does not identify this registry with compact T7 physical contacts.

def perm0 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else if i.val = 2 then 2 else if i.val = 3 then 3 else if i.val = 4 then 4 else if i.val = 5 then 5 else 6)
def inv0 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else if i.val = 2 then 2 else if i.val = 3 then 3 else if i.val = 4 then 4 else if i.val = 5 then 5 else 6)
theorem left0 : ∀ i, inv0 (perm0 i) = i := by decide
theorem right0 : ∀ i, perm0 (inv0 i) = i := by decide

def perm1 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 0 else if i.val = 1 then 6 else if i.val = 2 then 5 else if i.val = 3 then 4 else if i.val = 4 then 3 else if i.val = 5 then 2 else 1)
def inv1 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 0 else if i.val = 1 then 6 else if i.val = 2 then 5 else if i.val = 3 then 4 else if i.val = 4 then 3 else if i.val = 5 then 2 else 1)
theorem left1 : ∀ i, inv1 (perm1 i) = i := by decide
theorem right1 : ∀ i, perm1 (inv1 i) = i := by decide

def perm2 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 1 else if i.val = 1 then 0 else if i.val = 2 then 6 else if i.val = 3 then 5 else if i.val = 4 then 4 else if i.val = 5 then 3 else 2)
def inv2 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 1 else if i.val = 1 then 0 else if i.val = 2 then 6 else if i.val = 3 then 5 else if i.val = 4 then 4 else if i.val = 5 then 3 else 2)
theorem left2 : ∀ i, inv2 (perm2 i) = i := by decide
theorem right2 : ∀ i, perm2 (inv2 i) = i := by decide

def perm3 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else if i.val = 2 then 3 else if i.val = 3 then 4 else if i.val = 4 then 5 else if i.val = 5 then 6 else 0)
def inv3 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 6 else if i.val = 1 then 0 else if i.val = 2 then 1 else if i.val = 3 then 2 else if i.val = 4 then 3 else if i.val = 5 then 4 else 5)
theorem left3 : ∀ i, inv3 (perm3 i) = i := by decide
theorem right3 : ∀ i, perm3 (inv3 i) = i := by decide

def perm4 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 2 else if i.val = 1 then 1 else if i.val = 2 then 0 else if i.val = 3 then 6 else if i.val = 4 then 5 else if i.val = 5 then 4 else 3)
def inv4 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 2 else if i.val = 1 then 1 else if i.val = 2 then 0 else if i.val = 3 then 6 else if i.val = 4 then 5 else if i.val = 5 then 4 else 3)
theorem left4 : ∀ i, inv4 (perm4 i) = i := by decide
theorem right4 : ∀ i, perm4 (inv4 i) = i := by decide

def perm5 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 2 else if i.val = 1 then 3 else if i.val = 2 then 4 else if i.val = 3 then 5 else if i.val = 4 then 6 else if i.val = 5 then 0 else 1)
def inv5 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 5 else if i.val = 1 then 6 else if i.val = 2 then 0 else if i.val = 3 then 1 else if i.val = 4 then 2 else if i.val = 5 then 3 else 4)
theorem left5 : ∀ i, inv5 (perm5 i) = i := by decide
theorem right5 : ∀ i, perm5 (inv5 i) = i := by decide

def perm6 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 3 else if i.val = 1 then 2 else if i.val = 2 then 1 else if i.val = 3 then 0 else if i.val = 4 then 6 else if i.val = 5 then 5 else 4)
def inv6 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 3 else if i.val = 1 then 2 else if i.val = 2 then 1 else if i.val = 3 then 0 else if i.val = 4 then 6 else if i.val = 5 then 5 else 4)
theorem left6 : ∀ i, inv6 (perm6 i) = i := by decide
theorem right6 : ∀ i, perm6 (inv6 i) = i := by decide

def perm7 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 3 else if i.val = 1 then 4 else if i.val = 2 then 5 else if i.val = 3 then 6 else if i.val = 4 then 0 else if i.val = 5 then 1 else 2)
def inv7 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 4 else if i.val = 1 then 5 else if i.val = 2 then 6 else if i.val = 3 then 0 else if i.val = 4 then 1 else if i.val = 5 then 2 else 3)
theorem left7 : ∀ i, inv7 (perm7 i) = i := by decide
theorem right7 : ∀ i, perm7 (inv7 i) = i := by decide

def perm8 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 4 else if i.val = 1 then 3 else if i.val = 2 then 2 else if i.val = 3 then 1 else if i.val = 4 then 0 else if i.val = 5 then 6 else 5)
def inv8 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 4 else if i.val = 1 then 3 else if i.val = 2 then 2 else if i.val = 3 then 1 else if i.val = 4 then 0 else if i.val = 5 then 6 else 5)
theorem left8 : ∀ i, inv8 (perm8 i) = i := by decide
theorem right8 : ∀ i, perm8 (inv8 i) = i := by decide

def perm9 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 4 else if i.val = 1 then 5 else if i.val = 2 then 6 else if i.val = 3 then 0 else if i.val = 4 then 1 else if i.val = 5 then 2 else 3)
def inv9 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 3 else if i.val = 1 then 4 else if i.val = 2 then 5 else if i.val = 3 then 6 else if i.val = 4 then 0 else if i.val = 5 then 1 else 2)
theorem left9 : ∀ i, inv9 (perm9 i) = i := by decide
theorem right9 : ∀ i, perm9 (inv9 i) = i := by decide

def perm10 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 5 else if i.val = 1 then 4 else if i.val = 2 then 3 else if i.val = 3 then 2 else if i.val = 4 then 1 else if i.val = 5 then 0 else 6)
def inv10 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 5 else if i.val = 1 then 4 else if i.val = 2 then 3 else if i.val = 3 then 2 else if i.val = 4 then 1 else if i.val = 5 then 0 else 6)
theorem left10 : ∀ i, inv10 (perm10 i) = i := by decide
theorem right10 : ∀ i, perm10 (inv10 i) = i := by decide

def perm11 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 5 else if i.val = 1 then 6 else if i.val = 2 then 0 else if i.val = 3 then 1 else if i.val = 4 then 2 else if i.val = 5 then 3 else 4)
def inv11 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 2 else if i.val = 1 then 3 else if i.val = 2 then 4 else if i.val = 3 then 5 else if i.val = 4 then 6 else if i.val = 5 then 0 else 1)
theorem left11 : ∀ i, inv11 (perm11 i) = i := by decide
theorem right11 : ∀ i, perm11 (inv11 i) = i := by decide

def perm12 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 6 else if i.val = 1 then 0 else if i.val = 2 then 1 else if i.val = 3 then 2 else if i.val = 4 then 3 else if i.val = 5 then 4 else 5)
def inv12 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 1 else if i.val = 1 then 2 else if i.val = 2 then 3 else if i.val = 3 then 4 else if i.val = 4 then 5 else if i.val = 5 then 6 else 0)
theorem left12 : ∀ i, inv12 (perm12 i) = i := by decide
theorem right12 : ∀ i, perm12 (inv12 i) = i := by decide

def perm13 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 6 else if i.val = 1 then 5 else if i.val = 2 then 4 else if i.val = 3 then 3 else if i.val = 4 then 2 else if i.val = 5 then 1 else 0)
def inv13 : Fin 7 → Fin 7 := (fun i => if i.val = 0 then 6 else if i.val = 1 then 5 else if i.val = 2 then 4 else if i.val = 3 then 3 else if i.val = 4 then 2 else if i.val = 5 then 1 else 0)
theorem left13 : ∀ i, inv13 (perm13 i) = i := by decide
theorem right13 : ∀ i, perm13 (inv13 i) = i := by decide

def EntryScreen (q : Pose 7) : Prop :=
  q.UniformParity ∧ q.AffineIndex ∧
    ((∀ i, q.anchor i = 0) → q.frame.perm ⟨0, by decide⟩ = ⟨0, by decide⟩)

def pose0 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose0_screen : EntryScreen pose0 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose1 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose1_screen : EntryScreen pose1 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose2 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose2_screen : EntryScreen pose2 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose3 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose3_screen : EntryScreen pose3 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose4 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose4_screen : EntryScreen pose4 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose5 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else -2)⟩
theorem pose5_screen : EntryScreen pose5 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose6 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose6_screen : EntryScreen pose6 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose7 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then -2 else 2)⟩
theorem pose7_screen : EntryScreen pose7 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose8 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose8_screen : EntryScreen pose8 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose9 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then -2 else if i.val = 5 then 2 else 2)⟩
theorem pose9_screen : EntryScreen pose9 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose10 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose10_screen : EntryScreen pose10 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose11 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then -2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose11_screen : EntryScreen pose11 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose12 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose12_screen : EntryScreen pose12 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose13 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose13_screen : EntryScreen pose13 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose14 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then -2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose14_screen : EntryScreen pose14 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose15 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose15_screen : EntryScreen pose15 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose16 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose16_screen : EntryScreen pose16 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose17 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose17_screen : EntryScreen pose17 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose18 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose18_screen : EntryScreen pose18 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose19 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose19_screen : EntryScreen pose19 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose20 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose20_screen : EntryScreen pose20 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose21 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose21_screen : EntryScreen pose21 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose22 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose22_screen : EntryScreen pose22 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose23 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose23_screen : EntryScreen pose23 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose24 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose24_screen : EntryScreen pose24 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose25 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose25_screen : EntryScreen pose25 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose26 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose26_screen : EntryScreen pose26 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose27 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose27_screen : EntryScreen pose27 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose28 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose28_screen : EntryScreen pose28 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose29 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose29_screen : EntryScreen pose29 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose30 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 4 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose30_screen : EntryScreen pose30 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose31 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else -2)⟩
theorem pose31_screen : EntryScreen pose31 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose32 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose32_screen : EntryScreen pose32 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose33 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then -2 else 2)⟩
theorem pose33_screen : EntryScreen pose33 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose34 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose34_screen : EntryScreen pose34 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose35 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then -2 else if i.val = 5 then 2 else 2)⟩
theorem pose35_screen : EntryScreen pose35 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose36 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose36_screen : EntryScreen pose36 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose37 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then -2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose37_screen : EntryScreen pose37 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose38 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose38_screen : EntryScreen pose38 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose39 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose39_screen : EntryScreen pose39 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose40 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose40_screen : EntryScreen pose40 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose41 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then -2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose41_screen : EntryScreen pose41 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose42 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose42_screen : EntryScreen pose42 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose43 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose43_screen : EntryScreen pose43 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose44 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose44_screen : EntryScreen pose44 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose45 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose45_screen : EntryScreen pose45 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose46 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose46_screen : EntryScreen pose46 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose47 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose47_screen : EntryScreen pose47 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose48 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose48_screen : EntryScreen pose48 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose49 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose49_screen : EntryScreen pose49 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose50 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose50_screen : EntryScreen pose50 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose51 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose51_screen : EntryScreen pose51 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose52 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose52_screen : EntryScreen pose52 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose53 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose53_screen : EntryScreen pose53 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose54 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose54_screen : EntryScreen pose54 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose55 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose55_screen : EntryScreen pose55 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose56 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 4 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose56_screen : EntryScreen pose56 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose57 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose57_screen : EntryScreen pose57 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose58 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose58_screen : EntryScreen pose58 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose59 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose59_screen : EntryScreen pose59 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose60 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose60_screen : EntryScreen pose60 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose61 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose61_screen : EntryScreen pose61 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose62 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else -2)⟩
theorem pose62_screen : EntryScreen pose62 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose63 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose63_screen : EntryScreen pose63 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose64 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then -2 else 2)⟩
theorem pose64_screen : EntryScreen pose64 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose65 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose65_screen : EntryScreen pose65 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose66 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then -2 else if i.val = 5 then 2 else 2)⟩
theorem pose66_screen : EntryScreen pose66 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose67 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose67_screen : EntryScreen pose67 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose68 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then -2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose68_screen : EntryScreen pose68 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose69 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose69_screen : EntryScreen pose69 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose70 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose70_screen : EntryScreen pose70 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose71 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose71_screen : EntryScreen pose71 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose72 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then -2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose72_screen : EntryScreen pose72 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose73 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose73_screen : EntryScreen pose73 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose74 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose74_screen : EntryScreen pose74 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose75 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose75_screen : EntryScreen pose75 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose76 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose76_screen : EntryScreen pose76 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose77 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose77_screen : EntryScreen pose77 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose78 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose78_screen : EntryScreen pose78 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose79 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose79_screen : EntryScreen pose79 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose80 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose80_screen : EntryScreen pose80 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose81 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose81_screen : EntryScreen pose81 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose82 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose82_screen : EntryScreen pose82 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose83 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose83_screen : EntryScreen pose83 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose84 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose84_screen : EntryScreen pose84 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose85 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose85_screen : EntryScreen pose85 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose86 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 4 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose86_screen : EntryScreen pose86 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose87 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose87_screen : EntryScreen pose87 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose88 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose88_screen : EntryScreen pose88 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose89 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose89_screen : EntryScreen pose89 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose90 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose90_screen : EntryScreen pose90 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose91 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose91_screen : EntryScreen pose91 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose92 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose92_screen : EntryScreen pose92 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose93 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else -2)⟩
theorem pose93_screen : EntryScreen pose93 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose94 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose94_screen : EntryScreen pose94 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose95 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then -2 else 2)⟩
theorem pose95_screen : EntryScreen pose95 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose96 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose96_screen : EntryScreen pose96 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose97 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then -2 else if i.val = 5 then 2 else 2)⟩
theorem pose97_screen : EntryScreen pose97 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose98 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose98_screen : EntryScreen pose98 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose99 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose99_screen : EntryScreen pose99 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose100 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then -2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose100_screen : EntryScreen pose100 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose101 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose101_screen : EntryScreen pose101 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose102 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose102_screen : EntryScreen pose102 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose103 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose103_screen : EntryScreen pose103 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose104 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then -2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose104_screen : EntryScreen pose104 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose105 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose105_screen : EntryScreen pose105 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose106 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose106_screen : EntryScreen pose106 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose107 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose107_screen : EntryScreen pose107 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose108 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose108_screen : EntryScreen pose108 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose109 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose109_screen : EntryScreen pose109 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose110 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose110_screen : EntryScreen pose110 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose111 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose111_screen : EntryScreen pose111 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose112 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose112_screen : EntryScreen pose112 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose113 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose113_screen : EntryScreen pose113 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose114 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose114_screen : EntryScreen pose114 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose115 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose115_screen : EntryScreen pose115 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose116 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose116_screen : EntryScreen pose116 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose117 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose117_screen : EntryScreen pose117 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose118 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose118_screen : EntryScreen pose118 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose119 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 4 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose119_screen : EntryScreen pose119 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose120 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose120_screen : EntryScreen pose120 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose121 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose121_screen : EntryScreen pose121 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose122 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose122_screen : EntryScreen pose122 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose123 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose123_screen : EntryScreen pose123 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose124 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else -2)⟩
theorem pose124_screen : EntryScreen pose124 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose125 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose125_screen : EntryScreen pose125 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose126 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then -2 else 2)⟩
theorem pose126_screen : EntryScreen pose126 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose127 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose127_screen : EntryScreen pose127 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose128 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose128_screen : EntryScreen pose128 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose129 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then -2 else if i.val = 5 then 2 else 2)⟩
theorem pose129_screen : EntryScreen pose129 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose130 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose130_screen : EntryScreen pose130 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose131 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose131_screen : EntryScreen pose131 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose132 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then -2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose132_screen : EntryScreen pose132 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose133 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose133_screen : EntryScreen pose133 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose134 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose134_screen : EntryScreen pose134 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose135 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then -2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose135_screen : EntryScreen pose135 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose136 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose136_screen : EntryScreen pose136 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose137 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose137_screen : EntryScreen pose137 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose138 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose138_screen : EntryScreen pose138 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose139 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose139_screen : EntryScreen pose139 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose140 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose140_screen : EntryScreen pose140 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose141 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose141_screen : EntryScreen pose141 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose142 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose142_screen : EntryScreen pose142 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose143 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose143_screen : EntryScreen pose143 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose144 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose144_screen : EntryScreen pose144 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose145 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose145_screen : EntryScreen pose145 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose146 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose146_screen : EntryScreen pose146 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose147 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose147_screen : EntryScreen pose147 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose148 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 4 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose148_screen : EntryScreen pose148 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose149 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose149_screen : EntryScreen pose149 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose150 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose150_screen : EntryScreen pose150 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose151 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose151_screen : EntryScreen pose151 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose152 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose152_screen : EntryScreen pose152 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose153 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose153_screen : EntryScreen pose153 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose154 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose154_screen : EntryScreen pose154 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose155 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else -2)⟩
theorem pose155_screen : EntryScreen pose155 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose156 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose156_screen : EntryScreen pose156 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose157 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose157_screen : EntryScreen pose157 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose158 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then -2 else 2)⟩
theorem pose158_screen : EntryScreen pose158 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose159 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose159_screen : EntryScreen pose159 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose160 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then -2 else if i.val = 5 then 2 else 2)⟩
theorem pose160_screen : EntryScreen pose160 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose161 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose161_screen : EntryScreen pose161 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose162 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then -2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose162_screen : EntryScreen pose162 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose163 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose163_screen : EntryScreen pose163 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose164 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose164_screen : EntryScreen pose164 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose165 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then -2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose165_screen : EntryScreen pose165 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose166 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose166_screen : EntryScreen pose166 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose167 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose167_screen : EntryScreen pose167 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose168 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose168_screen : EntryScreen pose168 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose169 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose169_screen : EntryScreen pose169 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose170 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose170_screen : EntryScreen pose170 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose171 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose171_screen : EntryScreen pose171 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose172 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose172_screen : EntryScreen pose172 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose173 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose173_screen : EntryScreen pose173 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose174 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose174_screen : EntryScreen pose174 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose175 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose175_screen : EntryScreen pose175 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose176 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose176_screen : EntryScreen pose176 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose177 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose177_screen : EntryScreen pose177 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose178 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose178_screen : EntryScreen pose178 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose179 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose179_screen : EntryScreen pose179 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose180 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 4 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose180_screen : EntryScreen pose180 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose181 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose181_screen : EntryScreen pose181 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose182 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose182_screen : EntryScreen pose182 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose183 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose183_screen : EntryScreen pose183 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose184 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose184_screen : EntryScreen pose184 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose185 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose185_screen : EntryScreen pose185 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose186 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose186_screen : EntryScreen pose186 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose187 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose187_screen : EntryScreen pose187 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose188 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose188_screen : EntryScreen pose188 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose189 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose189_screen : EntryScreen pose189 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose190 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose190_screen : EntryScreen pose190 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose191 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose191_screen : EntryScreen pose191 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose192 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else -2)⟩
theorem pose192_screen : EntryScreen pose192 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose193 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose193_screen : EntryScreen pose193 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose194 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then -2 else 2)⟩
theorem pose194_screen : EntryScreen pose194 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose195 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose195_screen : EntryScreen pose195 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose196 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then -2 else if i.val = 5 then 2 else 2)⟩
theorem pose196_screen : EntryScreen pose196 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose197 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose197_screen : EntryScreen pose197 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose198 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then -2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose198_screen : EntryScreen pose198 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose199 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose199_screen : EntryScreen pose199 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose200 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose200_screen : EntryScreen pose200 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose201 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose201_screen : EntryScreen pose201 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose202 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then -2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose202_screen : EntryScreen pose202 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose203 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose203_screen : EntryScreen pose203 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose204 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then -2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose204_screen : EntryScreen pose204 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose205 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose205_screen : EntryScreen pose205 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose206 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose206_screen : EntryScreen pose206 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose207 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose207_screen : EntryScreen pose207 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose208 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose208_screen : EntryScreen pose208 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose209 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose209_screen : EntryScreen pose209 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose210 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose210_screen : EntryScreen pose210 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose211 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose211_screen : EntryScreen pose211 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose212 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose212_screen : EntryScreen pose212 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose213 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose213_screen : EntryScreen pose213 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose214 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose214_screen : EntryScreen pose214 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose215 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose215_screen : EntryScreen pose215 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose216 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose216_screen : EntryScreen pose216 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose217 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then true else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 4 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose217_screen : EntryScreen pose217 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose218 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose218_screen : EntryScreen pose218 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose219 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose219_screen : EntryScreen pose219 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose220 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose220_screen : EntryScreen pose220 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose221 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose221_screen : EntryScreen pose221 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose222 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose222_screen : EntryScreen pose222 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose223 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose223_screen : EntryScreen pose223 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose224 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose224_screen : EntryScreen pose224 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose225 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose225_screen : EntryScreen pose225 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose226 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose226_screen : EntryScreen pose226 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose227 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose227_screen : EntryScreen pose227 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose228 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose228_screen : EntryScreen pose228 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose229 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose229_screen : EntryScreen pose229 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose230 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose230_screen : EntryScreen pose230 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose231 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose231_screen : EntryScreen pose231 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose232 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose232_screen : EntryScreen pose232 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose233 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose233_screen : EntryScreen pose233 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose234 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose234_screen : EntryScreen pose234 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose235 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose235_screen : EntryScreen pose235 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose236 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose236_screen : EntryScreen pose236 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose237 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose237_screen : EntryScreen pose237 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose238 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose238_screen : EntryScreen pose238 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose239 : Pose 7 :=
  ⟨⟨perm0, inv0, left0, right0, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 1)⟩
theorem pose239_screen : EntryScreen pose239 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose240 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose240_screen : EntryScreen pose240 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose241 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 4 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose241_screen : EntryScreen pose241 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose242 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose242_screen : EntryScreen pose242 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose243 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose243_screen : EntryScreen pose243 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose244 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose244_screen : EntryScreen pose244 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose245 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 4 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose245_screen : EntryScreen pose245 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose246 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose246_screen : EntryScreen pose246 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose247 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 4 else if i.val = 5 then 0 else 0)⟩
theorem pose247_screen : EntryScreen pose247 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose248 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose248_screen : EntryScreen pose248 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose249 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 4 else 0)⟩
theorem pose249_screen : EntryScreen pose249 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose250 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose250_screen : EntryScreen pose250 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose251 : Pose 7 :=
  ⟨⟨perm1, inv1, left1, right1, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 4)⟩
theorem pose251_screen : EntryScreen pose251 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 0, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose252 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose252_screen : EntryScreen pose252 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose253 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose253_screen : EntryScreen pose253 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose254 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose254_screen : EntryScreen pose254 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose255 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose255_screen : EntryScreen pose255 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose256 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose256_screen : EntryScreen pose256 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose257 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose257_screen : EntryScreen pose257 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose258 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose258_screen : EntryScreen pose258 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose259 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose259_screen : EntryScreen pose259 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose260 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose260_screen : EntryScreen pose260 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose261 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose261_screen : EntryScreen pose261 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose262 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose262_screen : EntryScreen pose262 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose263 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose263_screen : EntryScreen pose263 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose264 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose264_screen : EntryScreen pose264 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose265 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose265_screen : EntryScreen pose265 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose266 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose266_screen : EntryScreen pose266 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose267 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 4 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose267_screen : EntryScreen pose267 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose268 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose268_screen : EntryScreen pose268 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose269 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 4 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose269_screen : EntryScreen pose269 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose270 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 4 else if i.val = 5 then 0 else 0)⟩
theorem pose270_screen : EntryScreen pose270 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose271 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 4 else 0)⟩
theorem pose271_screen : EntryScreen pose271 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose272 : Pose 7 :=
  ⟨⟨perm2, inv2, left2, right2, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 4)⟩
theorem pose272_screen : EntryScreen pose272 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose273 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose273_screen : EntryScreen pose273 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose274 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose274_screen : EntryScreen pose274 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose275 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose275_screen : EntryScreen pose275 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose276 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose276_screen : EntryScreen pose276 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose277 : Pose 7 :=
  ⟨⟨perm3, inv3, left3, right3, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose277_screen : EntryScreen pose277 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 1, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose278 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose278_screen : EntryScreen pose278 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose279 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose279_screen : EntryScreen pose279 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose280 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose280_screen : EntryScreen pose280 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose281 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose281_screen : EntryScreen pose281 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose282 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose282_screen : EntryScreen pose282 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose283 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose283_screen : EntryScreen pose283 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose284 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose284_screen : EntryScreen pose284 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose285 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose285_screen : EntryScreen pose285 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose286 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose286_screen : EntryScreen pose286 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose287 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose287_screen : EntryScreen pose287 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose288 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose288_screen : EntryScreen pose288 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose289 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose289_screen : EntryScreen pose289 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose290 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose290_screen : EntryScreen pose290 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose291 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose291_screen : EntryScreen pose291 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose292 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose292_screen : EntryScreen pose292 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose293 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 4 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose293_screen : EntryScreen pose293 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose294 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose294_screen : EntryScreen pose294 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose295 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose295_screen : EntryScreen pose295 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose296 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 4 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose296_screen : EntryScreen pose296 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose297 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 4 else if i.val = 5 then 0 else 0)⟩
theorem pose297_screen : EntryScreen pose297 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose298 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 4 else 0)⟩
theorem pose298_screen : EntryScreen pose298 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose299 : Pose 7 :=
  ⟨⟨perm4, inv4, left4, right4, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 4)⟩
theorem pose299_screen : EntryScreen pose299 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose300 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose300_screen : EntryScreen pose300 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose301 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose301_screen : EntryScreen pose301 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose302 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose302_screen : EntryScreen pose302 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose303 : Pose 7 :=
  ⟨⟨perm5, inv5, left5, right5, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose303_screen : EntryScreen pose303 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 2, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose304 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose304_screen : EntryScreen pose304 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose305 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose305_screen : EntryScreen pose305 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose306 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose306_screen : EntryScreen pose306 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose307 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose307_screen : EntryScreen pose307 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose308 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose308_screen : EntryScreen pose308 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose309 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose309_screen : EntryScreen pose309 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose310 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose310_screen : EntryScreen pose310 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose311 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose311_screen : EntryScreen pose311 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose312 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose312_screen : EntryScreen pose312 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose313 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose313_screen : EntryScreen pose313 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose314 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose314_screen : EntryScreen pose314 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose315 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose315_screen : EntryScreen pose315 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose316 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose316_screen : EntryScreen pose316 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose317 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 4 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose317_screen : EntryScreen pose317 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose318 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose318_screen : EntryScreen pose318 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose319 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose319_screen : EntryScreen pose319 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose320 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 4 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose320_screen : EntryScreen pose320 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose321 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 4 else if i.val = 5 then 0 else 0)⟩
theorem pose321_screen : EntryScreen pose321 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose322 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 4 else 0)⟩
theorem pose322_screen : EntryScreen pose322 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose323 : Pose 7 :=
  ⟨⟨perm6, inv6, left6, right6, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 4)⟩
theorem pose323_screen : EntryScreen pose323 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose324 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose324_screen : EntryScreen pose324 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose325 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose325_screen : EntryScreen pose325 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose326 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose326_screen : EntryScreen pose326 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose327 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose327_screen : EntryScreen pose327 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose328 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose328_screen : EntryScreen pose328 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose329 : Pose 7 :=
  ⟨⟨perm7, inv7, left7, right7, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose329_screen : EntryScreen pose329 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 3, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose330 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose330_screen : EntryScreen pose330 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose331 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose331_screen : EntryScreen pose331 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose332 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose332_screen : EntryScreen pose332 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose333 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose333_screen : EntryScreen pose333 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose334 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose334_screen : EntryScreen pose334 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose335 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose335_screen : EntryScreen pose335 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose336 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose336_screen : EntryScreen pose336 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose337 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose337_screen : EntryScreen pose337 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose338 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose338_screen : EntryScreen pose338 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose339 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose339_screen : EntryScreen pose339 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose340 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose340_screen : EntryScreen pose340 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose341 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose341_screen : EntryScreen pose341 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose342 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose342_screen : EntryScreen pose342 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose343 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose343_screen : EntryScreen pose343 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose344 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 4 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose344_screen : EntryScreen pose344 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose345 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose345_screen : EntryScreen pose345 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose346 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose346_screen : EntryScreen pose346 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose347 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 4 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose347_screen : EntryScreen pose347 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose348 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose348_screen : EntryScreen pose348 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose349 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 4 else if i.val = 5 then 0 else 0)⟩
theorem pose349_screen : EntryScreen pose349 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose350 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 4 else 0)⟩
theorem pose350_screen : EntryScreen pose350 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose351 : Pose 7 :=
  ⟨⟨perm8, inv8, left8, right8, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 4)⟩
theorem pose351_screen : EntryScreen pose351 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose352 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose352_screen : EntryScreen pose352 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose353 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose353_screen : EntryScreen pose353 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose354 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose354_screen : EntryScreen pose354 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose355 : Pose 7 :=
  ⟨⟨perm9, inv9, left9, right9, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose355_screen : EntryScreen pose355 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 4, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose356 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose356_screen : EntryScreen pose356 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose357 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose357_screen : EntryScreen pose357 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose358 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose358_screen : EntryScreen pose358 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose359 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose359_screen : EntryScreen pose359 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose360 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose360_screen : EntryScreen pose360 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose361 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose361_screen : EntryScreen pose361 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose362 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else -1)⟩
theorem pose362_screen : EntryScreen pose362 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose363 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose363_screen : EntryScreen pose363 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose364 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose364_screen : EntryScreen pose364 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose365 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose365_screen : EntryScreen pose365 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose366 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose366_screen : EntryScreen pose366 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose367 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else -1)⟩
theorem pose367_screen : EntryScreen pose367 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose368 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose368_screen : EntryScreen pose368 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose369 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 4 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose369_screen : EntryScreen pose369 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose370 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose370_screen : EntryScreen pose370 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose371 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 4 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose371_screen : EntryScreen pose371 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose372 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose372_screen : EntryScreen pose372 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose373 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 4 else if i.val = 5 then 0 else 0)⟩
theorem pose373_screen : EntryScreen pose373 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose374 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose374_screen : EntryScreen pose374 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose375 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 4 else 0)⟩
theorem pose375_screen : EntryScreen pose375 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose376 : Pose 7 :=
  ⟨⟨perm10, inv10, left10, right10, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 4)⟩
theorem pose376_screen : EntryScreen pose376 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose377 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose377_screen : EntryScreen pose377 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose378 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose378_screen : EntryScreen pose378 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose379 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose379_screen : EntryScreen pose379 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose380 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose380_screen : EntryScreen pose380 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose381 : Pose 7 :=
  ⟨⟨perm11, inv11, left11, right11, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then 3 else 3)⟩
theorem pose381_screen : EntryScreen pose381 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 5, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose382 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose382_screen : EntryScreen pose382 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose383 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose383_screen : EntryScreen pose383 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose384 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then -1 else 3)⟩
theorem pose384_screen : EntryScreen pose384 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose385 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose385_screen : EntryScreen pose385 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose386 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose386_screen : EntryScreen pose386 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose387 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose387_screen : EntryScreen pose387 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose388 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 2 else if i.val = 1 then 2 else if i.val = 2 then 2 else if i.val = 3 then 2 else if i.val = 4 then 2 else if i.val = 5 then 2 else 2)⟩
theorem pose388_screen : EntryScreen pose388 := by
  refine ⟨⟨false, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose389 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then 3 else -1)⟩
theorem pose389_screen : EntryScreen pose389 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose390 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose390_screen : EntryScreen pose390 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose391 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 3)⟩
theorem pose391_screen : EntryScreen pose391 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose392 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then true else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 3 else if i.val = 2 then 1 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 1 else 3)⟩
theorem pose392_screen : EntryScreen pose392 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose393 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 1)⟩
theorem pose393_screen : EntryScreen pose393 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose394 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 3 else if i.val = 3 then 1 else if i.val = 4 then 1 else if i.val = 5 then 3 else 1)⟩
theorem pose394_screen : EntryScreen pose394 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose395 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 3 else 3)⟩
theorem pose395_screen : EntryScreen pose395 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose396 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 3 else if i.val = 5 then 1 else 1)⟩
theorem pose396_screen : EntryScreen pose396 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose397 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose397_screen : EntryScreen pose397 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose398 : Pose 7 :=
  ⟨⟨perm12, inv12, left12, right12, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose398_screen : EntryScreen pose398 := by
  refine ⟨⟨true, by decide⟩, ⟨1, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose399 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then 3 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose399_screen : EntryScreen pose399 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose400 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then 3 else if i.val = 3 then -1 else if i.val = 4 then 3 else if i.val = 5 then 3 else -1)⟩
theorem pose400_screen : EntryScreen pose400 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose401 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then true else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 4 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose401_screen : EntryScreen pose401 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose402 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then true else true)⟩, (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else if i.val = 3 then 3 else if i.val = 4 then 1 else if i.val = 5 then 3 else 3)⟩
theorem pose402_screen : EntryScreen pose402 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose403 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then true else if i.val = 4 then false else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 4 else if i.val = 4 then 0 else if i.val = 5 then 0 else 0)⟩
theorem pose403_screen : EntryScreen pose403 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose404 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then true else if i.val = 5 then false else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 4 else if i.val = 5 then 0 else 0)⟩
theorem pose404_screen : EntryScreen pose404 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose405 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then true else false)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 4 else 0)⟩
theorem pose405_screen : EntryScreen pose405 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose406 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then -1 else if i.val = 1 then -1 else if i.val = 2 then -1 else if i.val = 3 then -1 else if i.val = 4 then -1 else if i.val = 5 then -1 else 3)⟩
theorem pose406_screen : EntryScreen pose406 := by
  refine ⟨⟨true, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def pose407 : Pose 7 :=
  ⟨⟨perm13, inv13, left13, right13, (fun i => if i.val = 0 then false else if i.val = 1 then false else if i.val = 2 then false else if i.val = 3 then false else if i.val = 4 then false else if i.val = 5 then false else true)⟩, (fun i => if i.val = 0 then 0 else if i.val = 1 then 0 else if i.val = 2 then 0 else if i.val = 3 then 0 else if i.val = 4 then 0 else if i.val = 5 then 0 else 4)⟩
theorem pose407_screen : EntryScreen pose407 := by
  refine ⟨⟨false, by decide⟩, ⟨6, 6, by decide, by unfold Uniform.MEq; decide⟩, ?_⟩
  decide

def catalogChunk0 : List (Pose 7) := [pose0, pose1, pose2, pose3, pose4, pose5, pose6, pose7, pose8, pose9, pose10, pose11, pose12, pose13, pose14, pose15, pose16, pose17, pose18, pose19, pose20, pose21, pose22, pose23, pose24, pose25, pose26, pose27, pose28, pose29, pose30, pose31]
theorem catalogChunk0_screen : ∀ q ∈ catalogChunk0, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose0_screen, (List.forall_mem_cons.mpr ⟨pose1_screen, (List.forall_mem_cons.mpr ⟨pose2_screen, (List.forall_mem_cons.mpr ⟨pose3_screen, (List.forall_mem_cons.mpr ⟨pose4_screen, (List.forall_mem_cons.mpr ⟨pose5_screen, (List.forall_mem_cons.mpr ⟨pose6_screen, (List.forall_mem_cons.mpr ⟨pose7_screen, (List.forall_mem_cons.mpr ⟨pose8_screen, (List.forall_mem_cons.mpr ⟨pose9_screen, (List.forall_mem_cons.mpr ⟨pose10_screen, (List.forall_mem_cons.mpr ⟨pose11_screen, (List.forall_mem_cons.mpr ⟨pose12_screen, (List.forall_mem_cons.mpr ⟨pose13_screen, (List.forall_mem_cons.mpr ⟨pose14_screen, (List.forall_mem_cons.mpr ⟨pose15_screen, (List.forall_mem_cons.mpr ⟨pose16_screen, (List.forall_mem_cons.mpr ⟨pose17_screen, (List.forall_mem_cons.mpr ⟨pose18_screen, (List.forall_mem_cons.mpr ⟨pose19_screen, (List.forall_mem_cons.mpr ⟨pose20_screen, (List.forall_mem_cons.mpr ⟨pose21_screen, (List.forall_mem_cons.mpr ⟨pose22_screen, (List.forall_mem_cons.mpr ⟨pose23_screen, (List.forall_mem_cons.mpr ⟨pose24_screen, (List.forall_mem_cons.mpr ⟨pose25_screen, (List.forall_mem_cons.mpr ⟨pose26_screen, (List.forall_mem_cons.mpr ⟨pose27_screen, (List.forall_mem_cons.mpr ⟨pose28_screen, (List.forall_mem_cons.mpr ⟨pose29_screen, (List.forall_mem_cons.mpr ⟨pose30_screen, (List.forall_mem_cons.mpr ⟨pose31_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk1 : List (Pose 7) := [pose32, pose33, pose34, pose35, pose36, pose37, pose38, pose39, pose40, pose41, pose42, pose43, pose44, pose45, pose46, pose47, pose48, pose49, pose50, pose51, pose52, pose53, pose54, pose55, pose56, pose57, pose58, pose59, pose60, pose61, pose62, pose63]
theorem catalogChunk1_screen : ∀ q ∈ catalogChunk1, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose32_screen, (List.forall_mem_cons.mpr ⟨pose33_screen, (List.forall_mem_cons.mpr ⟨pose34_screen, (List.forall_mem_cons.mpr ⟨pose35_screen, (List.forall_mem_cons.mpr ⟨pose36_screen, (List.forall_mem_cons.mpr ⟨pose37_screen, (List.forall_mem_cons.mpr ⟨pose38_screen, (List.forall_mem_cons.mpr ⟨pose39_screen, (List.forall_mem_cons.mpr ⟨pose40_screen, (List.forall_mem_cons.mpr ⟨pose41_screen, (List.forall_mem_cons.mpr ⟨pose42_screen, (List.forall_mem_cons.mpr ⟨pose43_screen, (List.forall_mem_cons.mpr ⟨pose44_screen, (List.forall_mem_cons.mpr ⟨pose45_screen, (List.forall_mem_cons.mpr ⟨pose46_screen, (List.forall_mem_cons.mpr ⟨pose47_screen, (List.forall_mem_cons.mpr ⟨pose48_screen, (List.forall_mem_cons.mpr ⟨pose49_screen, (List.forall_mem_cons.mpr ⟨pose50_screen, (List.forall_mem_cons.mpr ⟨pose51_screen, (List.forall_mem_cons.mpr ⟨pose52_screen, (List.forall_mem_cons.mpr ⟨pose53_screen, (List.forall_mem_cons.mpr ⟨pose54_screen, (List.forall_mem_cons.mpr ⟨pose55_screen, (List.forall_mem_cons.mpr ⟨pose56_screen, (List.forall_mem_cons.mpr ⟨pose57_screen, (List.forall_mem_cons.mpr ⟨pose58_screen, (List.forall_mem_cons.mpr ⟨pose59_screen, (List.forall_mem_cons.mpr ⟨pose60_screen, (List.forall_mem_cons.mpr ⟨pose61_screen, (List.forall_mem_cons.mpr ⟨pose62_screen, (List.forall_mem_cons.mpr ⟨pose63_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk2 : List (Pose 7) := [pose64, pose65, pose66, pose67, pose68, pose69, pose70, pose71, pose72, pose73, pose74, pose75, pose76, pose77, pose78, pose79, pose80, pose81, pose82, pose83, pose84, pose85, pose86, pose87, pose88, pose89, pose90, pose91, pose92, pose93, pose94, pose95]
theorem catalogChunk2_screen : ∀ q ∈ catalogChunk2, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose64_screen, (List.forall_mem_cons.mpr ⟨pose65_screen, (List.forall_mem_cons.mpr ⟨pose66_screen, (List.forall_mem_cons.mpr ⟨pose67_screen, (List.forall_mem_cons.mpr ⟨pose68_screen, (List.forall_mem_cons.mpr ⟨pose69_screen, (List.forall_mem_cons.mpr ⟨pose70_screen, (List.forall_mem_cons.mpr ⟨pose71_screen, (List.forall_mem_cons.mpr ⟨pose72_screen, (List.forall_mem_cons.mpr ⟨pose73_screen, (List.forall_mem_cons.mpr ⟨pose74_screen, (List.forall_mem_cons.mpr ⟨pose75_screen, (List.forall_mem_cons.mpr ⟨pose76_screen, (List.forall_mem_cons.mpr ⟨pose77_screen, (List.forall_mem_cons.mpr ⟨pose78_screen, (List.forall_mem_cons.mpr ⟨pose79_screen, (List.forall_mem_cons.mpr ⟨pose80_screen, (List.forall_mem_cons.mpr ⟨pose81_screen, (List.forall_mem_cons.mpr ⟨pose82_screen, (List.forall_mem_cons.mpr ⟨pose83_screen, (List.forall_mem_cons.mpr ⟨pose84_screen, (List.forall_mem_cons.mpr ⟨pose85_screen, (List.forall_mem_cons.mpr ⟨pose86_screen, (List.forall_mem_cons.mpr ⟨pose87_screen, (List.forall_mem_cons.mpr ⟨pose88_screen, (List.forall_mem_cons.mpr ⟨pose89_screen, (List.forall_mem_cons.mpr ⟨pose90_screen, (List.forall_mem_cons.mpr ⟨pose91_screen, (List.forall_mem_cons.mpr ⟨pose92_screen, (List.forall_mem_cons.mpr ⟨pose93_screen, (List.forall_mem_cons.mpr ⟨pose94_screen, (List.forall_mem_cons.mpr ⟨pose95_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk3 : List (Pose 7) := [pose96, pose97, pose98, pose99, pose100, pose101, pose102, pose103, pose104, pose105, pose106, pose107, pose108, pose109, pose110, pose111, pose112, pose113, pose114, pose115, pose116, pose117, pose118, pose119, pose120, pose121, pose122, pose123, pose124, pose125, pose126, pose127]
theorem catalogChunk3_screen : ∀ q ∈ catalogChunk3, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose96_screen, (List.forall_mem_cons.mpr ⟨pose97_screen, (List.forall_mem_cons.mpr ⟨pose98_screen, (List.forall_mem_cons.mpr ⟨pose99_screen, (List.forall_mem_cons.mpr ⟨pose100_screen, (List.forall_mem_cons.mpr ⟨pose101_screen, (List.forall_mem_cons.mpr ⟨pose102_screen, (List.forall_mem_cons.mpr ⟨pose103_screen, (List.forall_mem_cons.mpr ⟨pose104_screen, (List.forall_mem_cons.mpr ⟨pose105_screen, (List.forall_mem_cons.mpr ⟨pose106_screen, (List.forall_mem_cons.mpr ⟨pose107_screen, (List.forall_mem_cons.mpr ⟨pose108_screen, (List.forall_mem_cons.mpr ⟨pose109_screen, (List.forall_mem_cons.mpr ⟨pose110_screen, (List.forall_mem_cons.mpr ⟨pose111_screen, (List.forall_mem_cons.mpr ⟨pose112_screen, (List.forall_mem_cons.mpr ⟨pose113_screen, (List.forall_mem_cons.mpr ⟨pose114_screen, (List.forall_mem_cons.mpr ⟨pose115_screen, (List.forall_mem_cons.mpr ⟨pose116_screen, (List.forall_mem_cons.mpr ⟨pose117_screen, (List.forall_mem_cons.mpr ⟨pose118_screen, (List.forall_mem_cons.mpr ⟨pose119_screen, (List.forall_mem_cons.mpr ⟨pose120_screen, (List.forall_mem_cons.mpr ⟨pose121_screen, (List.forall_mem_cons.mpr ⟨pose122_screen, (List.forall_mem_cons.mpr ⟨pose123_screen, (List.forall_mem_cons.mpr ⟨pose124_screen, (List.forall_mem_cons.mpr ⟨pose125_screen, (List.forall_mem_cons.mpr ⟨pose126_screen, (List.forall_mem_cons.mpr ⟨pose127_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk4 : List (Pose 7) := [pose128, pose129, pose130, pose131, pose132, pose133, pose134, pose135, pose136, pose137, pose138, pose139, pose140, pose141, pose142, pose143, pose144, pose145, pose146, pose147, pose148, pose149, pose150, pose151, pose152, pose153, pose154, pose155, pose156, pose157, pose158, pose159]
theorem catalogChunk4_screen : ∀ q ∈ catalogChunk4, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose128_screen, (List.forall_mem_cons.mpr ⟨pose129_screen, (List.forall_mem_cons.mpr ⟨pose130_screen, (List.forall_mem_cons.mpr ⟨pose131_screen, (List.forall_mem_cons.mpr ⟨pose132_screen, (List.forall_mem_cons.mpr ⟨pose133_screen, (List.forall_mem_cons.mpr ⟨pose134_screen, (List.forall_mem_cons.mpr ⟨pose135_screen, (List.forall_mem_cons.mpr ⟨pose136_screen, (List.forall_mem_cons.mpr ⟨pose137_screen, (List.forall_mem_cons.mpr ⟨pose138_screen, (List.forall_mem_cons.mpr ⟨pose139_screen, (List.forall_mem_cons.mpr ⟨pose140_screen, (List.forall_mem_cons.mpr ⟨pose141_screen, (List.forall_mem_cons.mpr ⟨pose142_screen, (List.forall_mem_cons.mpr ⟨pose143_screen, (List.forall_mem_cons.mpr ⟨pose144_screen, (List.forall_mem_cons.mpr ⟨pose145_screen, (List.forall_mem_cons.mpr ⟨pose146_screen, (List.forall_mem_cons.mpr ⟨pose147_screen, (List.forall_mem_cons.mpr ⟨pose148_screen, (List.forall_mem_cons.mpr ⟨pose149_screen, (List.forall_mem_cons.mpr ⟨pose150_screen, (List.forall_mem_cons.mpr ⟨pose151_screen, (List.forall_mem_cons.mpr ⟨pose152_screen, (List.forall_mem_cons.mpr ⟨pose153_screen, (List.forall_mem_cons.mpr ⟨pose154_screen, (List.forall_mem_cons.mpr ⟨pose155_screen, (List.forall_mem_cons.mpr ⟨pose156_screen, (List.forall_mem_cons.mpr ⟨pose157_screen, (List.forall_mem_cons.mpr ⟨pose158_screen, (List.forall_mem_cons.mpr ⟨pose159_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk5 : List (Pose 7) := [pose160, pose161, pose162, pose163, pose164, pose165, pose166, pose167, pose168, pose169, pose170, pose171, pose172, pose173, pose174, pose175, pose176, pose177, pose178, pose179, pose180, pose181, pose182, pose183, pose184, pose185, pose186, pose187, pose188, pose189, pose190, pose191]
theorem catalogChunk5_screen : ∀ q ∈ catalogChunk5, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose160_screen, (List.forall_mem_cons.mpr ⟨pose161_screen, (List.forall_mem_cons.mpr ⟨pose162_screen, (List.forall_mem_cons.mpr ⟨pose163_screen, (List.forall_mem_cons.mpr ⟨pose164_screen, (List.forall_mem_cons.mpr ⟨pose165_screen, (List.forall_mem_cons.mpr ⟨pose166_screen, (List.forall_mem_cons.mpr ⟨pose167_screen, (List.forall_mem_cons.mpr ⟨pose168_screen, (List.forall_mem_cons.mpr ⟨pose169_screen, (List.forall_mem_cons.mpr ⟨pose170_screen, (List.forall_mem_cons.mpr ⟨pose171_screen, (List.forall_mem_cons.mpr ⟨pose172_screen, (List.forall_mem_cons.mpr ⟨pose173_screen, (List.forall_mem_cons.mpr ⟨pose174_screen, (List.forall_mem_cons.mpr ⟨pose175_screen, (List.forall_mem_cons.mpr ⟨pose176_screen, (List.forall_mem_cons.mpr ⟨pose177_screen, (List.forall_mem_cons.mpr ⟨pose178_screen, (List.forall_mem_cons.mpr ⟨pose179_screen, (List.forall_mem_cons.mpr ⟨pose180_screen, (List.forall_mem_cons.mpr ⟨pose181_screen, (List.forall_mem_cons.mpr ⟨pose182_screen, (List.forall_mem_cons.mpr ⟨pose183_screen, (List.forall_mem_cons.mpr ⟨pose184_screen, (List.forall_mem_cons.mpr ⟨pose185_screen, (List.forall_mem_cons.mpr ⟨pose186_screen, (List.forall_mem_cons.mpr ⟨pose187_screen, (List.forall_mem_cons.mpr ⟨pose188_screen, (List.forall_mem_cons.mpr ⟨pose189_screen, (List.forall_mem_cons.mpr ⟨pose190_screen, (List.forall_mem_cons.mpr ⟨pose191_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk6 : List (Pose 7) := [pose192, pose193, pose194, pose195, pose196, pose197, pose198, pose199, pose200, pose201, pose202, pose203, pose204, pose205, pose206, pose207, pose208, pose209, pose210, pose211, pose212, pose213, pose214, pose215, pose216, pose217, pose218, pose219, pose220, pose221, pose222, pose223]
theorem catalogChunk6_screen : ∀ q ∈ catalogChunk6, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose192_screen, (List.forall_mem_cons.mpr ⟨pose193_screen, (List.forall_mem_cons.mpr ⟨pose194_screen, (List.forall_mem_cons.mpr ⟨pose195_screen, (List.forall_mem_cons.mpr ⟨pose196_screen, (List.forall_mem_cons.mpr ⟨pose197_screen, (List.forall_mem_cons.mpr ⟨pose198_screen, (List.forall_mem_cons.mpr ⟨pose199_screen, (List.forall_mem_cons.mpr ⟨pose200_screen, (List.forall_mem_cons.mpr ⟨pose201_screen, (List.forall_mem_cons.mpr ⟨pose202_screen, (List.forall_mem_cons.mpr ⟨pose203_screen, (List.forall_mem_cons.mpr ⟨pose204_screen, (List.forall_mem_cons.mpr ⟨pose205_screen, (List.forall_mem_cons.mpr ⟨pose206_screen, (List.forall_mem_cons.mpr ⟨pose207_screen, (List.forall_mem_cons.mpr ⟨pose208_screen, (List.forall_mem_cons.mpr ⟨pose209_screen, (List.forall_mem_cons.mpr ⟨pose210_screen, (List.forall_mem_cons.mpr ⟨pose211_screen, (List.forall_mem_cons.mpr ⟨pose212_screen, (List.forall_mem_cons.mpr ⟨pose213_screen, (List.forall_mem_cons.mpr ⟨pose214_screen, (List.forall_mem_cons.mpr ⟨pose215_screen, (List.forall_mem_cons.mpr ⟨pose216_screen, (List.forall_mem_cons.mpr ⟨pose217_screen, (List.forall_mem_cons.mpr ⟨pose218_screen, (List.forall_mem_cons.mpr ⟨pose219_screen, (List.forall_mem_cons.mpr ⟨pose220_screen, (List.forall_mem_cons.mpr ⟨pose221_screen, (List.forall_mem_cons.mpr ⟨pose222_screen, (List.forall_mem_cons.mpr ⟨pose223_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk7 : List (Pose 7) := [pose224, pose225, pose226, pose227, pose228, pose229, pose230, pose231, pose232, pose233, pose234, pose235, pose236, pose237, pose238, pose239, pose240, pose241, pose242, pose243, pose244, pose245, pose246, pose247, pose248, pose249, pose250, pose251, pose252, pose253, pose254, pose255]
theorem catalogChunk7_screen : ∀ q ∈ catalogChunk7, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose224_screen, (List.forall_mem_cons.mpr ⟨pose225_screen, (List.forall_mem_cons.mpr ⟨pose226_screen, (List.forall_mem_cons.mpr ⟨pose227_screen, (List.forall_mem_cons.mpr ⟨pose228_screen, (List.forall_mem_cons.mpr ⟨pose229_screen, (List.forall_mem_cons.mpr ⟨pose230_screen, (List.forall_mem_cons.mpr ⟨pose231_screen, (List.forall_mem_cons.mpr ⟨pose232_screen, (List.forall_mem_cons.mpr ⟨pose233_screen, (List.forall_mem_cons.mpr ⟨pose234_screen, (List.forall_mem_cons.mpr ⟨pose235_screen, (List.forall_mem_cons.mpr ⟨pose236_screen, (List.forall_mem_cons.mpr ⟨pose237_screen, (List.forall_mem_cons.mpr ⟨pose238_screen, (List.forall_mem_cons.mpr ⟨pose239_screen, (List.forall_mem_cons.mpr ⟨pose240_screen, (List.forall_mem_cons.mpr ⟨pose241_screen, (List.forall_mem_cons.mpr ⟨pose242_screen, (List.forall_mem_cons.mpr ⟨pose243_screen, (List.forall_mem_cons.mpr ⟨pose244_screen, (List.forall_mem_cons.mpr ⟨pose245_screen, (List.forall_mem_cons.mpr ⟨pose246_screen, (List.forall_mem_cons.mpr ⟨pose247_screen, (List.forall_mem_cons.mpr ⟨pose248_screen, (List.forall_mem_cons.mpr ⟨pose249_screen, (List.forall_mem_cons.mpr ⟨pose250_screen, (List.forall_mem_cons.mpr ⟨pose251_screen, (List.forall_mem_cons.mpr ⟨pose252_screen, (List.forall_mem_cons.mpr ⟨pose253_screen, (List.forall_mem_cons.mpr ⟨pose254_screen, (List.forall_mem_cons.mpr ⟨pose255_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk8 : List (Pose 7) := [pose256, pose257, pose258, pose259, pose260, pose261, pose262, pose263, pose264, pose265, pose266, pose267, pose268, pose269, pose270, pose271, pose272, pose273, pose274, pose275, pose276, pose277, pose278, pose279, pose280, pose281, pose282, pose283, pose284, pose285, pose286, pose287]
theorem catalogChunk8_screen : ∀ q ∈ catalogChunk8, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose256_screen, (List.forall_mem_cons.mpr ⟨pose257_screen, (List.forall_mem_cons.mpr ⟨pose258_screen, (List.forall_mem_cons.mpr ⟨pose259_screen, (List.forall_mem_cons.mpr ⟨pose260_screen, (List.forall_mem_cons.mpr ⟨pose261_screen, (List.forall_mem_cons.mpr ⟨pose262_screen, (List.forall_mem_cons.mpr ⟨pose263_screen, (List.forall_mem_cons.mpr ⟨pose264_screen, (List.forall_mem_cons.mpr ⟨pose265_screen, (List.forall_mem_cons.mpr ⟨pose266_screen, (List.forall_mem_cons.mpr ⟨pose267_screen, (List.forall_mem_cons.mpr ⟨pose268_screen, (List.forall_mem_cons.mpr ⟨pose269_screen, (List.forall_mem_cons.mpr ⟨pose270_screen, (List.forall_mem_cons.mpr ⟨pose271_screen, (List.forall_mem_cons.mpr ⟨pose272_screen, (List.forall_mem_cons.mpr ⟨pose273_screen, (List.forall_mem_cons.mpr ⟨pose274_screen, (List.forall_mem_cons.mpr ⟨pose275_screen, (List.forall_mem_cons.mpr ⟨pose276_screen, (List.forall_mem_cons.mpr ⟨pose277_screen, (List.forall_mem_cons.mpr ⟨pose278_screen, (List.forall_mem_cons.mpr ⟨pose279_screen, (List.forall_mem_cons.mpr ⟨pose280_screen, (List.forall_mem_cons.mpr ⟨pose281_screen, (List.forall_mem_cons.mpr ⟨pose282_screen, (List.forall_mem_cons.mpr ⟨pose283_screen, (List.forall_mem_cons.mpr ⟨pose284_screen, (List.forall_mem_cons.mpr ⟨pose285_screen, (List.forall_mem_cons.mpr ⟨pose286_screen, (List.forall_mem_cons.mpr ⟨pose287_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk9 : List (Pose 7) := [pose288, pose289, pose290, pose291, pose292, pose293, pose294, pose295, pose296, pose297, pose298, pose299, pose300, pose301, pose302, pose303, pose304, pose305, pose306, pose307, pose308, pose309, pose310, pose311, pose312, pose313, pose314, pose315, pose316, pose317, pose318, pose319]
theorem catalogChunk9_screen : ∀ q ∈ catalogChunk9, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose288_screen, (List.forall_mem_cons.mpr ⟨pose289_screen, (List.forall_mem_cons.mpr ⟨pose290_screen, (List.forall_mem_cons.mpr ⟨pose291_screen, (List.forall_mem_cons.mpr ⟨pose292_screen, (List.forall_mem_cons.mpr ⟨pose293_screen, (List.forall_mem_cons.mpr ⟨pose294_screen, (List.forall_mem_cons.mpr ⟨pose295_screen, (List.forall_mem_cons.mpr ⟨pose296_screen, (List.forall_mem_cons.mpr ⟨pose297_screen, (List.forall_mem_cons.mpr ⟨pose298_screen, (List.forall_mem_cons.mpr ⟨pose299_screen, (List.forall_mem_cons.mpr ⟨pose300_screen, (List.forall_mem_cons.mpr ⟨pose301_screen, (List.forall_mem_cons.mpr ⟨pose302_screen, (List.forall_mem_cons.mpr ⟨pose303_screen, (List.forall_mem_cons.mpr ⟨pose304_screen, (List.forall_mem_cons.mpr ⟨pose305_screen, (List.forall_mem_cons.mpr ⟨pose306_screen, (List.forall_mem_cons.mpr ⟨pose307_screen, (List.forall_mem_cons.mpr ⟨pose308_screen, (List.forall_mem_cons.mpr ⟨pose309_screen, (List.forall_mem_cons.mpr ⟨pose310_screen, (List.forall_mem_cons.mpr ⟨pose311_screen, (List.forall_mem_cons.mpr ⟨pose312_screen, (List.forall_mem_cons.mpr ⟨pose313_screen, (List.forall_mem_cons.mpr ⟨pose314_screen, (List.forall_mem_cons.mpr ⟨pose315_screen, (List.forall_mem_cons.mpr ⟨pose316_screen, (List.forall_mem_cons.mpr ⟨pose317_screen, (List.forall_mem_cons.mpr ⟨pose318_screen, (List.forall_mem_cons.mpr ⟨pose319_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk10 : List (Pose 7) := [pose320, pose321, pose322, pose323, pose324, pose325, pose326, pose327, pose328, pose329, pose330, pose331, pose332, pose333, pose334, pose335, pose336, pose337, pose338, pose339, pose340, pose341, pose342, pose343, pose344, pose345, pose346, pose347, pose348, pose349, pose350, pose351]
theorem catalogChunk10_screen : ∀ q ∈ catalogChunk10, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose320_screen, (List.forall_mem_cons.mpr ⟨pose321_screen, (List.forall_mem_cons.mpr ⟨pose322_screen, (List.forall_mem_cons.mpr ⟨pose323_screen, (List.forall_mem_cons.mpr ⟨pose324_screen, (List.forall_mem_cons.mpr ⟨pose325_screen, (List.forall_mem_cons.mpr ⟨pose326_screen, (List.forall_mem_cons.mpr ⟨pose327_screen, (List.forall_mem_cons.mpr ⟨pose328_screen, (List.forall_mem_cons.mpr ⟨pose329_screen, (List.forall_mem_cons.mpr ⟨pose330_screen, (List.forall_mem_cons.mpr ⟨pose331_screen, (List.forall_mem_cons.mpr ⟨pose332_screen, (List.forall_mem_cons.mpr ⟨pose333_screen, (List.forall_mem_cons.mpr ⟨pose334_screen, (List.forall_mem_cons.mpr ⟨pose335_screen, (List.forall_mem_cons.mpr ⟨pose336_screen, (List.forall_mem_cons.mpr ⟨pose337_screen, (List.forall_mem_cons.mpr ⟨pose338_screen, (List.forall_mem_cons.mpr ⟨pose339_screen, (List.forall_mem_cons.mpr ⟨pose340_screen, (List.forall_mem_cons.mpr ⟨pose341_screen, (List.forall_mem_cons.mpr ⟨pose342_screen, (List.forall_mem_cons.mpr ⟨pose343_screen, (List.forall_mem_cons.mpr ⟨pose344_screen, (List.forall_mem_cons.mpr ⟨pose345_screen, (List.forall_mem_cons.mpr ⟨pose346_screen, (List.forall_mem_cons.mpr ⟨pose347_screen, (List.forall_mem_cons.mpr ⟨pose348_screen, (List.forall_mem_cons.mpr ⟨pose349_screen, (List.forall_mem_cons.mpr ⟨pose350_screen, (List.forall_mem_cons.mpr ⟨pose351_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk11 : List (Pose 7) := [pose352, pose353, pose354, pose355, pose356, pose357, pose358, pose359, pose360, pose361, pose362, pose363, pose364, pose365, pose366, pose367, pose368, pose369, pose370, pose371, pose372, pose373, pose374, pose375, pose376, pose377, pose378, pose379, pose380, pose381, pose382, pose383]
theorem catalogChunk11_screen : ∀ q ∈ catalogChunk11, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose352_screen, (List.forall_mem_cons.mpr ⟨pose353_screen, (List.forall_mem_cons.mpr ⟨pose354_screen, (List.forall_mem_cons.mpr ⟨pose355_screen, (List.forall_mem_cons.mpr ⟨pose356_screen, (List.forall_mem_cons.mpr ⟨pose357_screen, (List.forall_mem_cons.mpr ⟨pose358_screen, (List.forall_mem_cons.mpr ⟨pose359_screen, (List.forall_mem_cons.mpr ⟨pose360_screen, (List.forall_mem_cons.mpr ⟨pose361_screen, (List.forall_mem_cons.mpr ⟨pose362_screen, (List.forall_mem_cons.mpr ⟨pose363_screen, (List.forall_mem_cons.mpr ⟨pose364_screen, (List.forall_mem_cons.mpr ⟨pose365_screen, (List.forall_mem_cons.mpr ⟨pose366_screen, (List.forall_mem_cons.mpr ⟨pose367_screen, (List.forall_mem_cons.mpr ⟨pose368_screen, (List.forall_mem_cons.mpr ⟨pose369_screen, (List.forall_mem_cons.mpr ⟨pose370_screen, (List.forall_mem_cons.mpr ⟨pose371_screen, (List.forall_mem_cons.mpr ⟨pose372_screen, (List.forall_mem_cons.mpr ⟨pose373_screen, (List.forall_mem_cons.mpr ⟨pose374_screen, (List.forall_mem_cons.mpr ⟨pose375_screen, (List.forall_mem_cons.mpr ⟨pose376_screen, (List.forall_mem_cons.mpr ⟨pose377_screen, (List.forall_mem_cons.mpr ⟨pose378_screen, (List.forall_mem_cons.mpr ⟨pose379_screen, (List.forall_mem_cons.mpr ⟨pose380_screen, (List.forall_mem_cons.mpr ⟨pose381_screen, (List.forall_mem_cons.mpr ⟨pose382_screen, (List.forall_mem_cons.mpr ⟨pose383_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def catalogChunk12 : List (Pose 7) := [pose384, pose385, pose386, pose387, pose388, pose389, pose390, pose391, pose392, pose393, pose394, pose395, pose396, pose397, pose398, pose399, pose400, pose401, pose402, pose403, pose404, pose405, pose406, pose407]
theorem catalogChunk12_screen : ∀ q ∈ catalogChunk12, EntryScreen q :=
  (List.forall_mem_cons.mpr ⟨pose384_screen, (List.forall_mem_cons.mpr ⟨pose385_screen, (List.forall_mem_cons.mpr ⟨pose386_screen, (List.forall_mem_cons.mpr ⟨pose387_screen, (List.forall_mem_cons.mpr ⟨pose388_screen, (List.forall_mem_cons.mpr ⟨pose389_screen, (List.forall_mem_cons.mpr ⟨pose390_screen, (List.forall_mem_cons.mpr ⟨pose391_screen, (List.forall_mem_cons.mpr ⟨pose392_screen, (List.forall_mem_cons.mpr ⟨pose393_screen, (List.forall_mem_cons.mpr ⟨pose394_screen, (List.forall_mem_cons.mpr ⟨pose395_screen, (List.forall_mem_cons.mpr ⟨pose396_screen, (List.forall_mem_cons.mpr ⟨pose397_screen, (List.forall_mem_cons.mpr ⟨pose398_screen, (List.forall_mem_cons.mpr ⟨pose399_screen, (List.forall_mem_cons.mpr ⟨pose400_screen, (List.forall_mem_cons.mpr ⟨pose401_screen, (List.forall_mem_cons.mpr ⟨pose402_screen, (List.forall_mem_cons.mpr ⟨pose403_screen, (List.forall_mem_cons.mpr ⟨pose404_screen, (List.forall_mem_cons.mpr ⟨pose405_screen, (List.forall_mem_cons.mpr ⟨pose406_screen, (List.forall_mem_cons.mpr ⟨pose407_screen, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

def literalCatalog : List (Pose 7) := catalogChunk0 ++ catalogChunk1 ++ catalogChunk2 ++ catalogChunk3 ++ catalogChunk4 ++ catalogChunk5 ++ catalogChunk6 ++ catalogChunk7 ++ catalogChunk8 ++ catalogChunk9 ++ catalogChunk10 ++ catalogChunk11 ++ catalogChunk12

theorem literalCatalog_entryScreen : ∀ q ∈ literalCatalog, EntryScreen q :=
  (List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨(List.forall_mem_append.mpr ⟨catalogChunk0_screen, catalogChunk1_screen⟩), catalogChunk2_screen⟩), catalogChunk3_screen⟩), catalogChunk4_screen⟩), catalogChunk5_screen⟩), catalogChunk6_screen⟩), catalogChunk7_screen⟩), catalogChunk8_screen⟩), catalogChunk9_screen⟩), catalogChunk10_screen⟩), catalogChunk11_screen⟩), catalogChunk12_screen⟩)

theorem literalCatalog_length : literalCatalog.length = 408 := by decide

/-- A catalog-to-atlas inclusion can reuse the proved registered atlas hierarchy.
This adapter leaves that inclusion and actual world legality as explicit premises. -/
theorem catalog_translation_aperiodic (P : Parameters) (L : Pose P.p → Prop)
    (atlas : ∀ q, L q → ArithmeticAtlasContact P q)
    (W : RegisteredWorld P.p)
    (legal : ∀ q r, W.tiles q → W.tiles r → FaceContact q r → L (q.relative r))
    (v : Cell P.p) (period : AtlasPeriods.TranslationPeriod W v) : v = (fun _ => 0) :=
  AtlasPeriods.arithmetic_atlas_translation_aperiodic P W
    (fun q r hq hr hc => atlas _ (legal q r hq hr hc)) v period

#print axioms literalCatalog_entryScreen
#print axioms literalCatalog_length
#print axioms catalog_translation_aperiodic
end CompactT7Preparation
