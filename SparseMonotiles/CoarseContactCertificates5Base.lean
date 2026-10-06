module

public import SparseMonotiles.CoarseContactCertificates

@[expose] public section

/-! Literal canonical children, independently bound to the already checked
Catalog5 role formula. Source registry SHA-256: b76cb81ef4325c4465e89f5459a19bcbbb036dd6c6c7c98e74f063f11c9adb87
Witness export SHA-256: 823d856b5521b4d205328cbc0870c9d8e8b554f4bb192f7938a6366c8abf61fa
-/
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def child0 : Pose 5 := ⟨Catalog5.perm0, ![false, false, false, false, false], ![0, 0, 0, 0, 0]⟩
def child1 : Pose 5 := ⟨Catalog5.perm1, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def child2 : Pose 5 := ⟨Catalog5.perm12, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def child3 : Pose 5 := ⟨Catalog5.perm14, ![true, true, false, false, false], ![4, 4, 0, 0, 0]⟩
def child4 : Pose 5 := ⟨Catalog5.perm6, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def child5 : Pose 5 := ⟨Catalog5.perm4, ![true, false, true, false, false], ![4, 0, 4, 0, 0]⟩
def child6 : Pose 5 := ⟨Catalog5.perm19, ![false, true, true, false, false], ![0, 4, 4, 0, 0]⟩
def child7 : Pose 5 := ⟨Catalog5.perm8, ![true, true, true, false, false], ![4, 4, 4, 0, 0]⟩
def child8 : Pose 5 := ⟨Catalog5.perm17, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def child9 : Pose 5 := ⟨Catalog5.perm19, ![true, false, false, true, false], ![4, 0, 0, 4, 0]⟩
def child10 : Pose 5 := ⟨Catalog5.perm9, ![false, true, false, true, false], ![0, 4, 0, 4, 0]⟩
def child11 : Pose 5 := ⟨Catalog5.perm7, ![true, true, false, true, false], ![4, 4, 0, 4, 0]⟩
def child12 : Pose 5 := ⟨Catalog5.perm3, ![false, false, true, true, false], ![0, 0, 4, 4, 0]⟩
def child13 : Pose 5 := ⟨Catalog5.perm2, ![true, false, true, true, false], ![4, 0, 4, 4, 0]⟩
def child14 : Pose 5 := ⟨Catalog5.perm18, ![false, true, true, true, false], ![0, 4, 4, 4, 0]⟩
def child15 : Pose 5 := ⟨Catalog5.perm5, ![true, true, true, true, false], ![4, 4, 4, 4, 0]⟩
def child16 : Pose 5 := ⟨Catalog5.perm11, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def child17 : Pose 5 := ⟨Catalog5.perm9, ![true, false, false, false, true], ![4, 0, 0, 0, 4]⟩
def child18 : Pose 5 := ⟨Catalog5.perm3, ![false, true, false, false, true], ![0, 4, 0, 0, 4]⟩
def child19 : Pose 5 := ⟨Catalog5.perm2, ![true, true, false, false, true], ![4, 4, 0, 0, 4]⟩
def child20 : Pose 5 := ⟨Catalog5.perm14, ![false, false, true, false, true], ![0, 0, 4, 0, 4]⟩
def child21 : Pose 5 := ⟨Catalog5.perm18, ![true, false, true, false, true], ![4, 0, 4, 0, 4]⟩
def child22 : Pose 5 := ⟨Catalog5.perm13, ![false, true, true, false, true], ![0, 4, 4, 0, 4]⟩
def child23 : Pose 5 := ⟨Catalog5.perm10, ![true, true, true, false, true], ![4, 4, 4, 0, 4]⟩
def child24 : Pose 5 := ⟨Catalog5.perm4, ![false, false, false, true, true], ![0, 0, 0, 4, 4]⟩
def child25 : Pose 5 := ⟨Catalog5.perm13, ![true, false, false, true, true], ![4, 0, 0, 4, 4]⟩
def child26 : Pose 5 := ⟨Catalog5.perm8, ![false, true, false, true, true], ![0, 4, 0, 4, 4]⟩
def child27 : Pose 5 := ⟨Catalog5.perm15, ![true, true, false, true, true], ![4, 4, 0, 4, 4]⟩
def child28 : Pose 5 := ⟨Catalog5.perm7, ![false, false, true, true, true], ![0, 0, 4, 4, 4]⟩
def child29 : Pose 5 := ⟨Catalog5.perm16, ![true, false, true, true, true], ![4, 0, 4, 4, 4]⟩
def child30 : Pose 5 := ⟨Catalog5.perm0, ![false, true, true, true, true], ![0, 4, 4, 4, 4]⟩
def child31 : Pose 5 := ⟨Catalog5.perm0, ![false, false, false, false, false], ![1, 1, 1, 1, 1]⟩

def child : Fin 32 → Pose 5 := fun i =>
  (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then child0 else child1) else (if i.val < 3 then child2 else child3)) else (if i.val < 6 then (if i.val < 5 then child4 else child5) else (if i.val < 7 then child6 else child7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then child8 else child9) else (if i.val < 11 then child10 else child11)) else (if i.val < 14 then (if i.val < 13 then child12 else child13) else (if i.val < 15 then child14 else child15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then child16 else child17) else (if i.val < 19 then child18 else child19)) else (if i.val < 22 then (if i.val < 21 then child20 else child21) else (if i.val < 23 then child22 else child23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then child24 else child25) else (if i.val < 27 then child26 else child27)) else (if i.val < 30 then (if i.val < 29 then child28 else child29) else (if i.val < 31 then child30 else child31)))))
def childList : List (Pose 5) := (List.finRange 32).map child
def C : Finset (Pose 5) := ⟨childList, by decide +kernel⟩
def L : Set (Pose 5) := {q | q ∈ Catalog5.supplied}

theorem child_table_covers : CoversCanonicalChildren Catalog5.childPerm C := by
  unfold CoversCanonicalChildren
  decide +kernel

instance (q : Pose 5) : Decidable (q ∈ children Catalog5.childPerm (rootPose 5)) :=
  inferInstanceAs (Decidable (q = centralChild (rootPose 5) ∨ ∃ a : Bits 5,
    Proper a ∧ q = compose (rootPose 5) (outerPose a (Catalog5.childPerm a))))

theorem child_table_sound : ∀ i : Fin 32, child i ∈ children Catalog5.childPerm (rootPose 5) := by decide +kernel

theorem C_sound : ∀ q ∈ C, q ∈ children Catalog5.childPerm (rootPose 5) := by
  intro q hq
  change q ∈ childList at hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact child_table_sound i

def registry0 : Pose 5 := ⟨Catalog5.perm19, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry1 : Pose 5 := ⟨Catalog5.perm19, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry2 : Pose 5 := ⟨Catalog5.perm19, ![true, true, true, true, false], ![3, 3, 3, 3, -1]⟩
def registry3 : Pose 5 := ⟨Catalog5.perm19, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry4 : Pose 5 := ⟨Catalog5.perm19, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry5 : Pose 5 := ⟨Catalog5.perm19, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry6 : Pose 5 := ⟨Catalog5.perm19, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry7 : Pose 5 := ⟨Catalog5.perm18, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry8 : Pose 5 := ⟨Catalog5.perm17, ![true, true, false, true, false], ![3, 3, -1, 3, -1]⟩
def registry9 : Pose 5 := ⟨Catalog5.perm17, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry10 : Pose 5 := ⟨Catalog5.perm16, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry11 : Pose 5 := ⟨Catalog5.perm16, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry12 : Pose 5 := ⟨Catalog5.perm16, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry13 : Pose 5 := ⟨Catalog5.perm16, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry14 : Pose 5 := ⟨Catalog5.perm16, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry15 : Pose 5 := ⟨Catalog5.perm16, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry16 : Pose 5 := ⟨Catalog5.perm16, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry17 : Pose 5 := ⟨Catalog5.perm16, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry18 : Pose 5 := ⟨Catalog5.perm16, ![true, false, true, true, true], ![3, -1, 3, 3, 3]⟩
def registry19 : Pose 5 := ⟨Catalog5.perm16, ![true, false, true, false, false], ![3, -1, 3, -1, -1]⟩
def registry20 : Pose 5 := ⟨Catalog5.perm17, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry21 : Pose 5 := ⟨Catalog5.perm17, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry22 : Pose 5 := ⟨Catalog5.perm17, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry23 : Pose 5 := ⟨Catalog5.perm18, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry24 : Pose 5 := ⟨Catalog5.perm18, ![true, false, true, false, true], ![3, -1, 3, -1, 3]⟩
def registry25 : Pose 5 := ⟨Catalog5.perm18, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry26 : Pose 5 := ⟨Catalog5.perm18, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry27 : Pose 5 := ⟨Catalog5.perm19, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry28 : Pose 5 := ⟨Catalog5.perm19, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry29 : Pose 5 := ⟨Catalog5.perm19, ![true, false, false, true, false], ![3, -1, -1, 3, -1]⟩
def registry30 : Pose 5 := ⟨Catalog5.perm15, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry31 : Pose 5 := ⟨Catalog5.perm15, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry32 : Pose 5 := ⟨Catalog5.perm15, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry33 : Pose 5 := ⟨Catalog5.perm15, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry34 : Pose 5 := ⟨Catalog5.perm15, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry35 : Pose 5 := ⟨Catalog5.perm15, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry36 : Pose 5 := ⟨Catalog5.perm15, ![true, true, false, true, true], ![3, 3, -1, 3, 3]⟩
def registry37 : Pose 5 := ⟨Catalog5.perm14, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry38 : Pose 5 := ⟨Catalog5.perm14, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry39 : Pose 5 := ⟨Catalog5.perm14, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry40 : Pose 5 := ⟨Catalog5.perm14, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry41 : Pose 5 := ⟨Catalog5.perm14, ![true, true, true, false, true], ![3, 3, 3, -1, 3]⟩
def registry42 : Pose 5 := ⟨Catalog5.perm14, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry43 : Pose 5 := ⟨Catalog5.perm14, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry44 : Pose 5 := ⟨Catalog5.perm14, ![true, true, false, false, false], ![3, 3, -1, -1, -1]⟩
def registry45 : Pose 5 := ⟨Catalog5.perm13, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry46 : Pose 5 := ⟨Catalog5.perm12, ![true, true, true, false, false], ![3, 3, 3, -1, -1]⟩
def registry47 : Pose 5 := ⟨Catalog5.perm12, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry48 : Pose 5 := ⟨Catalog5.perm12, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry49 : Pose 5 := ⟨Catalog5.perm12, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry50 : Pose 5 := ⟨Catalog5.perm12, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry51 : Pose 5 := ⟨Catalog5.perm13, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry52 : Pose 5 := ⟨Catalog5.perm13, ![true, false, false, true, true], ![3, -1, -1, 3, 3]⟩
def registry53 : Pose 5 := ⟨Catalog5.perm13, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry54 : Pose 5 := ⟨Catalog5.perm13, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry55 : Pose 5 := ⟨Catalog5.perm14, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry56 : Pose 5 := ⟨Catalog5.perm14, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry57 : Pose 5 := ⟨Catalog5.perm15, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry58 : Pose 5 := ⟨Catalog5.perm15, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry59 : Pose 5 := ⟨Catalog5.perm15, ![true, false, false, false, true], ![3, -1, -1, -1, 3]⟩
def registry60 : Pose 5 := ⟨Catalog5.perm11, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry61 : Pose 5 := ⟨Catalog5.perm10, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry62 : Pose 5 := ⟨Catalog5.perm10, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry63 : Pose 5 := ⟨Catalog5.perm10, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry64 : Pose 5 := ⟨Catalog5.perm10, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry65 : Pose 5 := ⟨Catalog5.perm10, ![true, true, true, false, true], ![3, 3, 3, -1, 3]⟩
def registry66 : Pose 5 := ⟨Catalog5.perm10, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry67 : Pose 5 := ⟨Catalog5.perm10, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry68 : Pose 5 := ⟨Catalog5.perm10, ![true, true, false, false, false], ![3, 3, -1, -1, -1]⟩
def registry69 : Pose 5 := ⟨Catalog5.perm9, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry70 : Pose 5 := ⟨Catalog5.perm9, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry71 : Pose 5 := ⟨Catalog5.perm9, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry72 : Pose 5 := ⟨Catalog5.perm9, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry73 : Pose 5 := ⟨Catalog5.perm9, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry74 : Pose 5 := ⟨Catalog5.perm9, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry75 : Pose 5 := ⟨Catalog5.perm9, ![true, true, false, true, true], ![3, 3, -1, 3, 3]⟩
def registry76 : Pose 5 := ⟨Catalog5.perm8, ![true, true, true, false, false], ![3, 3, 3, -1, -1]⟩
def registry77 : Pose 5 := ⟨Catalog5.perm8, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry78 : Pose 5 := ⟨Catalog5.perm8, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry79 : Pose 5 := ⟨Catalog5.perm8, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry80 : Pose 5 := ⟨Catalog5.perm8, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry81 : Pose 5 := ⟨Catalog5.perm9, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry82 : Pose 5 := ⟨Catalog5.perm9, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry83 : Pose 5 := ⟨Catalog5.perm9, ![true, false, false, false, true], ![3, -1, -1, -1, 3]⟩
def registry84 : Pose 5 := ⟨Catalog5.perm10, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry85 : Pose 5 := ⟨Catalog5.perm10, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry86 : Pose 5 := ⟨Catalog5.perm11, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry87 : Pose 5 := ⟨Catalog5.perm11, ![true, false, false, true, true], ![3, -1, -1, 3, 3]⟩
def registry88 : Pose 5 := ⟨Catalog5.perm11, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry89 : Pose 5 := ⟨Catalog5.perm11, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry90 : Pose 5 := ⟨Catalog5.perm7, ![true, true, false, true, false], ![3, 3, -1, 3, -1]⟩
def registry91 : Pose 5 := ⟨Catalog5.perm7, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry92 : Pose 5 := ⟨Catalog5.perm6, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry93 : Pose 5 := ⟨Catalog5.perm5, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry94 : Pose 5 := ⟨Catalog5.perm5, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry95 : Pose 5 := ⟨Catalog5.perm5, ![true, true, true, true, false], ![3, 3, 3, 3, -1]⟩
def registry96 : Pose 5 := ⟨Catalog5.perm5, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry97 : Pose 5 := ⟨Catalog5.perm5, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry98 : Pose 5 := ⟨Catalog5.perm5, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry99 : Pose 5 := ⟨Catalog5.perm5, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry100 : Pose 5 := ⟨Catalog5.perm4, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry101 : Pose 5 := ⟨Catalog5.perm4, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry102 : Pose 5 := ⟨Catalog5.perm4, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry103 : Pose 5 := ⟨Catalog5.perm4, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry104 : Pose 5 := ⟨Catalog5.perm4, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry105 : Pose 5 := ⟨Catalog5.perm4, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry106 : Pose 5 := ⟨Catalog5.perm4, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry107 : Pose 5 := ⟨Catalog5.perm4, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry108 : Pose 5 := ⟨Catalog5.perm4, ![true, false, true, true, true], ![3, -1, 3, 3, 3]⟩
def registry109 : Pose 5 := ⟨Catalog5.perm4, ![true, false, true, false, false], ![3, -1, 3, -1, -1]⟩
def registry110 : Pose 5 := ⟨Catalog5.perm5, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry111 : Pose 5 := ⟨Catalog5.perm5, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry112 : Pose 5 := ⟨Catalog5.perm5, ![true, false, false, true, false], ![3, -1, -1, 3, -1]⟩
def registry113 : Pose 5 := ⟨Catalog5.perm6, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry114 : Pose 5 := ⟨Catalog5.perm6, ![true, false, true, false, true], ![3, -1, 3, -1, 3]⟩
def registry115 : Pose 5 := ⟨Catalog5.perm6, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry116 : Pose 5 := ⟨Catalog5.perm6, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry117 : Pose 5 := ⟨Catalog5.perm7, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry118 : Pose 5 := ⟨Catalog5.perm7, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry119 : Pose 5 := ⟨Catalog5.perm7, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry120 : Pose 5 := ⟨Catalog5.perm3, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry121 : Pose 5 := ⟨Catalog5.perm3, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry122 : Pose 5 := ⟨Catalog5.perm3, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry123 : Pose 5 := ⟨Catalog5.perm3, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry124 : Pose 5 := ⟨Catalog5.perm3, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry125 : Pose 5 := ⟨Catalog5.perm3, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry126 : Pose 5 := ⟨Catalog5.perm2, ![true, true, false, false, true], ![3, 3, -1, -1, 3]⟩
def registry127 : Pose 5 := ⟨Catalog5.perm2, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry128 : Pose 5 := ⟨Catalog5.perm1, ![true, true, false, false, true], ![3, 3, -1, -1, 3]⟩
def registry129 : Pose 5 := ⟨Catalog5.perm1, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩
def registry130 : Pose 5 := ⟨Catalog5.perm0, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩
def registry131 : Pose 5 := ⟨Catalog5.perm0, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩
def registry132 : Pose 5 := ⟨Catalog5.perm0, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩
def registry133 : Pose 5 := ⟨Catalog5.perm0, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩
def registry134 : Pose 5 := ⟨Catalog5.perm0, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩
def registry135 : Pose 5 := ⟨Catalog5.perm0, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩
def registry136 : Pose 5 := ⟨Catalog5.perm0, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry137 : Pose 5 := ⟨Catalog5.perm0, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry138 : Pose 5 := ⟨Catalog5.perm1, ![true, false, true, true, false], ![3, -1, 3, 3, -1]⟩
def registry139 : Pose 5 := ⟨Catalog5.perm1, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry140 : Pose 5 := ⟨Catalog5.perm1, ![true, false, false, false, false], ![0, 0, 0, 0, 0]⟩
def registry141 : Pose 5 := ⟨Catalog5.perm1, ![true, false, false, false, false], ![3, -1, -1, -1, -1]⟩
def registry142 : Pose 5 := ⟨Catalog5.perm1, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry143 : Pose 5 := ⟨Catalog5.perm1, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry144 : Pose 5 := ⟨Catalog5.perm2, ![true, false, true, true, false], ![3, -1, 3, 3, -1]⟩
def registry145 : Pose 5 := ⟨Catalog5.perm2, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩
def registry146 : Pose 5 := ⟨Catalog5.perm2, ![true, false, false, false, false], ![0, 0, 0, 0, 0]⟩
def registry147 : Pose 5 := ⟨Catalog5.perm2, ![true, false, false, false, false], ![3, -1, -1, -1, -1]⟩
def registry148 : Pose 5 := ⟨Catalog5.perm2, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩
def registry149 : Pose 5 := ⟨Catalog5.perm2, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩
def registry150 : Pose 5 := ⟨Catalog5.perm3, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩
def registry151 : Pose 5 := ⟨Catalog5.perm3, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry152 : Pose 5 := ⟨Catalog5.perm3, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry153 : Pose 5 := ⟨Catalog5.perm3, ![false, true, true, true, true], ![-1, 3, 3, 3, 3]⟩
def registry154 : Pose 5 := ⟨Catalog5.perm3, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry155 : Pose 5 := ⟨Catalog5.perm3, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry156 : Pose 5 := ⟨Catalog5.perm3, ![false, true, false, false, true], ![-1, 3, -1, -1, 3]⟩
def registry157 : Pose 5 := ⟨Catalog5.perm3, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry158 : Pose 5 := ⟨Catalog5.perm2, ![false, true, false, false, false], ![0, 0, 0, 0, 0]⟩
def registry159 : Pose 5 := ⟨Catalog5.perm2, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry160 : Pose 5 := ⟨Catalog5.perm1, ![false, true, false, false, false], ![0, 0, 0, 0, 0]⟩
def registry161 : Pose 5 := ⟨Catalog5.perm1, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry162 : Pose 5 := ⟨Catalog5.perm0, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry163 : Pose 5 := ⟨Catalog5.perm0, ![false, true, true, true, true], ![-1, 3, 3, 3, 3]⟩
def registry164 : Pose 5 := ⟨Catalog5.perm0, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry165 : Pose 5 := ⟨Catalog5.perm0, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry166 : Pose 5 := ⟨Catalog5.perm0, ![false, true, false, false, true], ![-1, 3, -1, -1, 3]⟩
def registry167 : Pose 5 := ⟨Catalog5.perm0, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry168 : Pose 5 := ⟨Catalog5.perm0, ![false, false, true, true, false], ![-1, -1, 3, 3, -1]⟩
def registry169 : Pose 5 := ⟨Catalog5.perm0, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry170 : Pose 5 := ⟨Catalog5.perm0, ![false, false, false, false, false], ![-1, -1, -1, -1, -1]⟩
def registry171 : Pose 5 := ⟨Catalog5.perm0, ![false, false, false, false, false], ![1, 1, 1, 1, 1]⟩
def registry172 : Pose 5 := ⟨Catalog5.perm1, ![false, false, true, false, false], ![0, 0, 0, 0, 0]⟩
def registry173 : Pose 5 := ⟨Catalog5.perm1, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry174 : Pose 5 := ⟨Catalog5.perm1, ![false, false, false, true, false], ![0, 0, 0, 0, 0]⟩
def registry175 : Pose 5 := ⟨Catalog5.perm1, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry176 : Pose 5 := ⟨Catalog5.perm1, ![false, false, false, false, true], ![0, 0, 0, 0, 0]⟩
def registry177 : Pose 5 := ⟨Catalog5.perm1, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry178 : Pose 5 := ⟨Catalog5.perm2, ![false, false, true, false, false], ![0, 0, 0, 0, 0]⟩
def registry179 : Pose 5 := ⟨Catalog5.perm2, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry180 : Pose 5 := ⟨Catalog5.perm2, ![false, false, false, true, false], ![0, 0, 0, 0, 0]⟩
def registry181 : Pose 5 := ⟨Catalog5.perm2, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry182 : Pose 5 := ⟨Catalog5.perm2, ![false, false, false, false, true], ![0, 0, 0, 0, 0]⟩
def registry183 : Pose 5 := ⟨Catalog5.perm2, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry184 : Pose 5 := ⟨Catalog5.perm3, ![false, false, true, true, false], ![-1, -1, 3, 3, -1]⟩
def registry185 : Pose 5 := ⟨Catalog5.perm3, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry186 : Pose 5 := ⟨Catalog5.perm3, ![false, false, false, false, false], ![-1, -1, -1, -1, -1]⟩
def registry187 : Pose 5 := ⟨Catalog5.perm3, ![false, false, false, false, false], ![1, 1, 1, 1, 1]⟩
def registry188 : Pose 5 := ⟨Catalog5.perm7, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry189 : Pose 5 := ⟨Catalog5.perm6, ![false, true, true, true, false], ![-1, 3, 3, 3, -1]⟩
def registry190 : Pose 5 := ⟨Catalog5.perm6, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry191 : Pose 5 := ⟨Catalog5.perm5, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry192 : Pose 5 := ⟨Catalog5.perm5, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry193 : Pose 5 := ⟨Catalog5.perm5, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry194 : Pose 5 := ⟨Catalog5.perm5, ![false, true, true, false, false], ![-1, 3, 3, -1, -1]⟩
def registry195 : Pose 5 := ⟨Catalog5.perm5, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry196 : Pose 5 := ⟨Catalog5.perm4, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry197 : Pose 5 := ⟨Catalog5.perm4, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry198 : Pose 5 := ⟨Catalog5.perm4, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry199 : Pose 5 := ⟨Catalog5.perm4, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry200 : Pose 5 := ⟨Catalog5.perm4, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry201 : Pose 5 := ⟨Catalog5.perm4, ![false, false, false, true, true], ![-1, -1, -1, 3, 3]⟩
def registry202 : Pose 5 := ⟨Catalog5.perm5, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry203 : Pose 5 := ⟨Catalog5.perm6, ![false, false, true, false, false], ![-1, -1, 3, -1, -1]⟩
def registry204 : Pose 5 := ⟨Catalog5.perm6, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry205 : Pose 5 := ⟨Catalog5.perm6, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry206 : Pose 5 := ⟨Catalog5.perm6, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry207 : Pose 5 := ⟨Catalog5.perm7, ![false, false, true, true, true], ![-1, -1, 3, 3, 3]⟩
def registry208 : Pose 5 := ⟨Catalog5.perm7, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry209 : Pose 5 := ⟨Catalog5.perm7, ![false, false, false, true, false], ![-1, -1, -1, 3, -1]⟩
def registry210 : Pose 5 := ⟨Catalog5.perm7, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry211 : Pose 5 := ⟨Catalog5.perm7, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry212 : Pose 5 := ⟨Catalog5.perm11, ![false, true, true, false, true], ![-1, 3, 3, -1, 3]⟩
def registry213 : Pose 5 := ⟨Catalog5.perm11, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry214 : Pose 5 := ⟨Catalog5.perm10, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry215 : Pose 5 := ⟨Catalog5.perm10, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry216 : Pose 5 := ⟨Catalog5.perm10, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry217 : Pose 5 := ⟨Catalog5.perm10, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry218 : Pose 5 := ⟨Catalog5.perm9, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry219 : Pose 5 := ⟨Catalog5.perm9, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry220 : Pose 5 := ⟨Catalog5.perm9, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry221 : Pose 5 := ⟨Catalog5.perm9, ![false, true, false, true, false], ![-1, 3, -1, 3, -1]⟩
def registry222 : Pose 5 := ⟨Catalog5.perm9, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry223 : Pose 5 := ⟨Catalog5.perm8, ![false, true, false, true, true], ![-1, 3, -1, 3, 3]⟩
def registry224 : Pose 5 := ⟨Catalog5.perm8, ![false, true, false, false, false], ![-1, 3, -1, -1, -1]⟩
def registry225 : Pose 5 := ⟨Catalog5.perm8, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry226 : Pose 5 := ⟨Catalog5.perm8, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry227 : Pose 5 := ⟨Catalog5.perm8, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry228 : Pose 5 := ⟨Catalog5.perm8, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry229 : Pose 5 := ⟨Catalog5.perm9, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry230 : Pose 5 := ⟨Catalog5.perm10, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry231 : Pose 5 := ⟨Catalog5.perm10, ![false, false, true, false, true], ![-1, -1, 3, -1, 3]⟩
def registry232 : Pose 5 := ⟨Catalog5.perm11, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry233 : Pose 5 := ⟨Catalog5.perm11, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry234 : Pose 5 := ⟨Catalog5.perm11, ![false, false, false, false, true], ![-1, -1, -1, -1, 3]⟩
def registry235 : Pose 5 := ⟨Catalog5.perm11, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry236 : Pose 5 := ⟨Catalog5.perm15, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry237 : Pose 5 := ⟨Catalog5.perm15, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry238 : Pose 5 := ⟨Catalog5.perm15, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry239 : Pose 5 := ⟨Catalog5.perm15, ![false, true, false, true, false], ![-1, 3, -1, 3, -1]⟩
def registry240 : Pose 5 := ⟨Catalog5.perm15, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry241 : Pose 5 := ⟨Catalog5.perm14, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry242 : Pose 5 := ⟨Catalog5.perm14, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry243 : Pose 5 := ⟨Catalog5.perm14, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry244 : Pose 5 := ⟨Catalog5.perm14, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry245 : Pose 5 := ⟨Catalog5.perm13, ![false, true, true, false, true], ![-1, 3, 3, -1, 3]⟩
def registry246 : Pose 5 := ⟨Catalog5.perm13, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry247 : Pose 5 := ⟨Catalog5.perm12, ![false, true, false, true, true], ![-1, 3, -1, 3, 3]⟩
def registry248 : Pose 5 := ⟨Catalog5.perm12, ![false, true, false, false, false], ![-1, 3, -1, -1, -1]⟩
def registry249 : Pose 5 := ⟨Catalog5.perm12, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry250 : Pose 5 := ⟨Catalog5.perm12, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry251 : Pose 5 := ⟨Catalog5.perm12, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry252 : Pose 5 := ⟨Catalog5.perm12, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry253 : Pose 5 := ⟨Catalog5.perm13, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry254 : Pose 5 := ⟨Catalog5.perm13, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry255 : Pose 5 := ⟨Catalog5.perm13, ![false, false, false, false, true], ![-1, -1, -1, -1, 3]⟩
def registry256 : Pose 5 := ⟨Catalog5.perm13, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry257 : Pose 5 := ⟨Catalog5.perm14, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry258 : Pose 5 := ⟨Catalog5.perm14, ![false, false, true, false, true], ![-1, -1, 3, -1, 3]⟩
def registry259 : Pose 5 := ⟨Catalog5.perm15, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry260 : Pose 5 := ⟨Catalog5.perm19, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry261 : Pose 5 := ⟨Catalog5.perm19, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry262 : Pose 5 := ⟨Catalog5.perm19, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry263 : Pose 5 := ⟨Catalog5.perm19, ![false, true, true, false, false], ![-1, 3, 3, -1, -1]⟩
def registry264 : Pose 5 := ⟨Catalog5.perm19, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry265 : Pose 5 := ⟨Catalog5.perm18, ![false, true, true, true, false], ![-1, 3, 3, 3, -1]⟩
def registry266 : Pose 5 := ⟨Catalog5.perm18, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry267 : Pose 5 := ⟨Catalog5.perm17, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩
def registry268 : Pose 5 := ⟨Catalog5.perm16, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩
def registry269 : Pose 5 := ⟨Catalog5.perm16, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩
def registry270 : Pose 5 := ⟨Catalog5.perm16, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩
def registry271 : Pose 5 := ⟨Catalog5.perm16, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩
def registry272 : Pose 5 := ⟨Catalog5.perm16, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry273 : Pose 5 := ⟨Catalog5.perm16, ![false, false, false, true, true], ![-1, -1, -1, 3, 3]⟩
def registry274 : Pose 5 := ⟨Catalog5.perm17, ![false, false, true, true, true], ![-1, -1, 3, 3, 3]⟩
def registry275 : Pose 5 := ⟨Catalog5.perm17, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry276 : Pose 5 := ⟨Catalog5.perm17, ![false, false, false, true, false], ![-1, -1, -1, 3, -1]⟩
def registry277 : Pose 5 := ⟨Catalog5.perm17, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry278 : Pose 5 := ⟨Catalog5.perm17, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry279 : Pose 5 := ⟨Catalog5.perm18, ![false, false, true, false, false], ![-1, -1, 3, -1, -1]⟩
def registry280 : Pose 5 := ⟨Catalog5.perm18, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩
def registry281 : Pose 5 := ⟨Catalog5.perm18, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩
def registry282 : Pose 5 := ⟨Catalog5.perm18, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩
def registry283 : Pose 5 := ⟨Catalog5.perm19, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
def registry : Fin 284 → Pose 5 := fun i =>
  (if i.val < 142 then (if i.val < 71 then (if i.val < 35 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then registry0 else registry1) else (if i.val < 3 then registry2 else registry3)) else (if i.val < 6 then (if i.val < 5 then registry4 else registry5) else (if i.val < 7 then registry6 else registry7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then registry8 else registry9) else (if i.val < 11 then registry10 else registry11)) else (if i.val < 14 then (if i.val < 13 then registry12 else registry13) else (if i.val < 15 then registry14 else (if i.val < 16 then registry15 else registry16))))) else (if i.val < 26 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then registry17 else registry18) else (if i.val < 20 then registry19 else registry20)) else (if i.val < 23 then (if i.val < 22 then registry21 else registry22) else (if i.val < 24 then registry23 else (if i.val < 25 then registry24 else registry25)))) else (if i.val < 30 then (if i.val < 28 then (if i.val < 27 then registry26 else registry27) else (if i.val < 29 then registry28 else registry29)) else (if i.val < 32 then (if i.val < 31 then registry30 else registry31) else (if i.val < 33 then registry32 else (if i.val < 34 then registry33 else registry34)))))) else (if i.val < 53 then (if i.val < 44 then (if i.val < 39 then (if i.val < 37 then (if i.val < 36 then registry35 else registry36) else (if i.val < 38 then registry37 else registry38)) else (if i.val < 41 then (if i.val < 40 then registry39 else registry40) else (if i.val < 42 then registry41 else (if i.val < 43 then registry42 else registry43)))) else (if i.val < 48 then (if i.val < 46 then (if i.val < 45 then registry44 else registry45) else (if i.val < 47 then registry46 else registry47)) else (if i.val < 50 then (if i.val < 49 then registry48 else registry49) else (if i.val < 51 then registry50 else (if i.val < 52 then registry51 else registry52))))) else (if i.val < 62 then (if i.val < 57 then (if i.val < 55 then (if i.val < 54 then registry53 else registry54) else (if i.val < 56 then registry55 else registry56)) else (if i.val < 59 then (if i.val < 58 then registry57 else registry58) else (if i.val < 60 then registry59 else (if i.val < 61 then registry60 else registry61)))) else (if i.val < 66 then (if i.val < 64 then (if i.val < 63 then registry62 else registry63) else (if i.val < 65 then registry64 else registry65)) else (if i.val < 68 then (if i.val < 67 then registry66 else registry67) else (if i.val < 69 then registry68 else (if i.val < 70 then registry69 else registry70))))))) else (if i.val < 106 then (if i.val < 88 then (if i.val < 79 then (if i.val < 75 then (if i.val < 73 then (if i.val < 72 then registry71 else registry72) else (if i.val < 74 then registry73 else registry74)) else (if i.val < 77 then (if i.val < 76 then registry75 else registry76) else (if i.val < 78 then registry77 else registry78))) else (if i.val < 83 then (if i.val < 81 then (if i.val < 80 then registry79 else registry80) else (if i.val < 82 then registry81 else registry82)) else (if i.val < 85 then (if i.val < 84 then registry83 else registry84) else (if i.val < 86 then registry85 else (if i.val < 87 then registry86 else registry87))))) else (if i.val < 97 then (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then registry88 else registry89) else (if i.val < 91 then registry90 else registry91)) else (if i.val < 94 then (if i.val < 93 then registry92 else registry93) else (if i.val < 95 then registry94 else (if i.val < 96 then registry95 else registry96)))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then registry97 else registry98) else (if i.val < 100 then registry99 else registry100)) else (if i.val < 103 then (if i.val < 102 then registry101 else registry102) else (if i.val < 104 then registry103 else (if i.val < 105 then registry104 else registry105)))))) else (if i.val < 124 then (if i.val < 115 then (if i.val < 110 then (if i.val < 108 then (if i.val < 107 then registry106 else registry107) else (if i.val < 109 then registry108 else registry109)) else (if i.val < 112 then (if i.val < 111 then registry110 else registry111) else (if i.val < 113 then registry112 else (if i.val < 114 then registry113 else registry114)))) else (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then registry115 else registry116) else (if i.val < 118 then registry117 else registry118)) else (if i.val < 121 then (if i.val < 120 then registry119 else registry120) else (if i.val < 122 then registry121 else (if i.val < 123 then registry122 else registry123))))) else (if i.val < 133 then (if i.val < 128 then (if i.val < 126 then (if i.val < 125 then registry124 else registry125) else (if i.val < 127 then registry126 else registry127)) else (if i.val < 130 then (if i.val < 129 then registry128 else registry129) else (if i.val < 131 then registry130 else (if i.val < 132 then registry131 else registry132)))) else (if i.val < 137 then (if i.val < 135 then (if i.val < 134 then registry133 else registry134) else (if i.val < 136 then registry135 else registry136)) else (if i.val < 139 then (if i.val < 138 then registry137 else registry138) else (if i.val < 140 then registry139 else (if i.val < 141 then registry140 else registry141)))))))) else (if i.val < 213 then (if i.val < 177 then (if i.val < 159 then (if i.val < 150 then (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then registry142 else registry143) else (if i.val < 145 then registry144 else registry145)) else (if i.val < 148 then (if i.val < 147 then registry146 else registry147) else (if i.val < 149 then registry148 else registry149))) else (if i.val < 154 then (if i.val < 152 then (if i.val < 151 then registry150 else registry151) else (if i.val < 153 then registry152 else registry153)) else (if i.val < 156 then (if i.val < 155 then registry154 else registry155) else (if i.val < 157 then registry156 else (if i.val < 158 then registry157 else registry158))))) else (if i.val < 168 then (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then registry159 else registry160) else (if i.val < 162 then registry161 else registry162)) else (if i.val < 165 then (if i.val < 164 then registry163 else registry164) else (if i.val < 166 then registry165 else (if i.val < 167 then registry166 else registry167)))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then registry168 else registry169) else (if i.val < 171 then registry170 else registry171)) else (if i.val < 174 then (if i.val < 173 then registry172 else registry173) else (if i.val < 175 then registry174 else (if i.val < 176 then registry175 else registry176)))))) else (if i.val < 195 then (if i.val < 186 then (if i.val < 181 then (if i.val < 179 then (if i.val < 178 then registry177 else registry178) else (if i.val < 180 then registry179 else registry180)) else (if i.val < 183 then (if i.val < 182 then registry181 else registry182) else (if i.val < 184 then registry183 else (if i.val < 185 then registry184 else registry185)))) else (if i.val < 190 then (if i.val < 188 then (if i.val < 187 then registry186 else registry187) else (if i.val < 189 then registry188 else registry189)) else (if i.val < 192 then (if i.val < 191 then registry190 else registry191) else (if i.val < 193 then registry192 else (if i.val < 194 then registry193 else registry194))))) else (if i.val < 204 then (if i.val < 199 then (if i.val < 197 then (if i.val < 196 then registry195 else registry196) else (if i.val < 198 then registry197 else registry198)) else (if i.val < 201 then (if i.val < 200 then registry199 else registry200) else (if i.val < 202 then registry201 else (if i.val < 203 then registry202 else registry203)))) else (if i.val < 208 then (if i.val < 206 then (if i.val < 205 then registry204 else registry205) else (if i.val < 207 then registry206 else registry207)) else (if i.val < 210 then (if i.val < 209 then registry208 else registry209) else (if i.val < 211 then registry210 else (if i.val < 212 then registry211 else registry212))))))) else (if i.val < 248 then (if i.val < 230 then (if i.val < 221 then (if i.val < 217 then (if i.val < 215 then (if i.val < 214 then registry213 else registry214) else (if i.val < 216 then registry215 else registry216)) else (if i.val < 219 then (if i.val < 218 then registry217 else registry218) else (if i.val < 220 then registry219 else registry220))) else (if i.val < 225 then (if i.val < 223 then (if i.val < 222 then registry221 else registry222) else (if i.val < 224 then registry223 else registry224)) else (if i.val < 227 then (if i.val < 226 then registry225 else registry226) else (if i.val < 228 then registry227 else (if i.val < 229 then registry228 else registry229))))) else (if i.val < 239 then (if i.val < 234 then (if i.val < 232 then (if i.val < 231 then registry230 else registry231) else (if i.val < 233 then registry232 else registry233)) else (if i.val < 236 then (if i.val < 235 then registry234 else registry235) else (if i.val < 237 then registry236 else (if i.val < 238 then registry237 else registry238)))) else (if i.val < 243 then (if i.val < 241 then (if i.val < 240 then registry239 else registry240) else (if i.val < 242 then registry241 else registry242)) else (if i.val < 245 then (if i.val < 244 then registry243 else registry244) else (if i.val < 246 then registry245 else (if i.val < 247 then registry246 else registry247)))))) else (if i.val < 266 then (if i.val < 257 then (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then registry248 else registry249) else (if i.val < 251 then registry250 else registry251)) else (if i.val < 254 then (if i.val < 253 then registry252 else registry253) else (if i.val < 255 then registry254 else (if i.val < 256 then registry255 else registry256)))) else (if i.val < 261 then (if i.val < 259 then (if i.val < 258 then registry257 else registry258) else (if i.val < 260 then registry259 else registry260)) else (if i.val < 263 then (if i.val < 262 then registry261 else registry262) else (if i.val < 264 then registry263 else (if i.val < 265 then registry264 else registry265))))) else (if i.val < 275 then (if i.val < 270 then (if i.val < 268 then (if i.val < 267 then registry266 else registry267) else (if i.val < 269 then registry268 else registry269)) else (if i.val < 272 then (if i.val < 271 then registry270 else registry271) else (if i.val < 273 then registry272 else (if i.val < 274 then registry273 else registry274)))) else (if i.val < 279 then (if i.val < 277 then (if i.val < 276 then registry275 else registry276) else (if i.val < 278 then registry277 else registry278)) else (if i.val < 281 then (if i.val < 280 then registry279 else registry280) else (if i.val < 282 then registry281 else (if i.val < 283 then registry282 else registry283)))))))))
theorem supplied_indexed : Catalog5.supplied = (List.finRange 284).map registry := by decide +kernel
theorem registry_mem (i : Fin 284) : registry i ∈ L := by
  change registry i ∈ Catalog5.supplied
  rw [supplied_indexed]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
theorem registry_complete {q : Pose 5} (h : q ∈ L) : ∃ i, registry i = q := by
  change q ∈ Catalog5.supplied at h
  rw [supplied_indexed] at h
  obtain ⟨i, _, he⟩ := List.mem_map.mp h
  exact ⟨i, he⟩
def leftIndex : Fin 284 → Fin 284 := fun i =>
  (if i.val < 142 then (if i.val < 71 then (if i.val < 35 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 16 else 17) else (if i.val < 3 then 18 else 14)) else (if i.val < 6 then (if i.val < 5 then 15 else 12) else (if i.val < 7 then 13 else 9))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 24 else 7) else (if i.val < 11 then 27 else 28)) else (if i.val < 14 then (if i.val < 13 then 5 else 6) else (if i.val < 15 then 3 else (if i.val < 16 then 4 else 0))))) else (if i.val < 26 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then 1 else 2) else (if i.val < 20 then 29 else 23)) else (if i.val < 23 then (if i.val < 22 then 25 else 26) else (if i.val < 24 then 20 else (if i.val < 25 then 8 else 21)))) else (if i.val < 30 then (if i.val < 28 then (if i.val < 27 then 22 else 10) else (if i.val < 29 then 11 else 19)) else (if i.val < 32 then (if i.val < 31 then 55 else 56) else (if i.val < 33 then 42 else (if i.val < 34 then 43 else 39)))))) else (if i.val < 53 then (if i.val < 44 then (if i.val < 39 then (if i.val < 37 then (if i.val < 36 then 40 else 41) else (if i.val < 38 then 57 else 58)) else (if i.val < 41 then (if i.val < 40 then 34 else 35) else (if i.val < 42 then 36 else (if i.val < 43 then 32 else 33)))) else (if i.val < 48 then (if i.val < 46 then (if i.val < 45 then 59 else 47) else (if i.val < 47 then 52 else 45)) else (if i.val < 50 then (if i.val < 49 then 51 else 53) else (if i.val < 51 then 54 else (if i.val < 52 then 48 else 46))))) else (if i.val < 62 then (if i.val < 57 then (if i.val < 55 then (if i.val < 54 then 49 else 50) else (if i.val < 56 then 30 else 31)) else (if i.val < 59 then (if i.val < 58 then 37 else 38) else (if i.val < 60 then 44 else (if i.val < 61 then 77 else 81)))) else (if i.val < 66 then (if i.val < 64 then (if i.val < 63 then 82 else 73) else (if i.val < 65 then 74 else 75)) else (if i.val < 68 then (if i.val < 67 then 71 else 72) else (if i.val < 69 then 83 else (if i.val < 70 then 84 else 85))))))) else (if i.val < 106 then (if i.val < 88 then (if i.val < 79 then (if i.val < 75 then (if i.val < 73 then (if i.val < 72 then 66 else 67) else (if i.val < 74 then 63 else 64)) else (if i.val < 77 then (if i.val < 76 then 65 else 87) else (if i.val < 78 then 60 else 86))) else (if i.val < 83 then (if i.val < 81 then (if i.val < 80 then 88 else 89) else (if i.val < 82 then 61 else 62)) else (if i.val < 85 then (if i.val < 84 then 68 else 69) else (if i.val < 86 then 70 else (if i.val < 87 then 78 else 76))))) else (if i.val < 97 then (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 79 else 80) else (if i.val < 91 then 114 else 92)) else (if i.val < 94 then (if i.val < 93 then 91 else 106) else (if i.val < 95 then 107 else (if i.val < 96 then 108 else 104)))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then 105 else 102) else (if i.val < 100 then 103 else 110)) else (if i.val < 103 then (if i.val < 102 then 111 else 98) else (if i.val < 104 then 99 else (if i.val < 105 then 96 else 97)))))) else (if i.val < 124 then (if i.val < 115 then (if i.val < 110 then (if i.val < 108 then (if i.val < 107 then 93 else 94) else (if i.val < 109 then 95 else 112)) else (if i.val < 112 then (if i.val < 111 then 100 else 101) else (if i.val < 113 then 109 else (if i.val < 114 then 117 else 90)))) else (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then 118 else 119) else (if i.val < 118 then 113 else 115)) else (if i.val < 121 then (if i.val < 120 then 116 else 136) else (if i.val < 122 then 137 else (if i.val < 123 then 134 else 135))))) else (if i.val < 133 then (if i.val < 128 then (if i.val < 126 then (if i.val < 125 then 132 else 133) else (if i.val < 127 then 128 else 129)) else (if i.val < 130 then (if i.val < 129 then 126 else 127) else (if i.val < 131 then 150 else (if i.val < 132 then 151 else 124)))) else (if i.val < 137 then (if i.val < 135 then (if i.val < 134 then 125 else 122) else (if i.val < 136 then 123 else 120)) else (if i.val < 139 then (if i.val < 138 then 121 else 144) else (if i.val < 140 then 145 else (if i.val < 141 then 146 else 147)))))))) else (if i.val < 213 then (if i.val < 177 then (if i.val < 159 then (if i.val < 150 then (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then 148 else 149) else (if i.val < 145 then 138 else 139)) else (if i.val < 148 then (if i.val < 147 then 140 else 141) else (if i.val < 149 then 142 else 143))) else (if i.val < 154 then (if i.val < 152 then (if i.val < 151 then 130 else 131) else (if i.val < 153 then 162 else 163)) else (if i.val < 156 then (if i.val < 155 then 164 else 165) else (if i.val < 157 then 166 else (if i.val < 158 then 167 else 176))))) else (if i.val < 168 then (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then 177 else 182) else (if i.val < 162 then 183 else 152)) else (if i.val < 165 then (if i.val < 164 then 153 else 154) else (if i.val < 166 then 155 else (if i.val < 167 then 156 else 157)))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 184 else 185) else (if i.val < 171 then 186 else 187)) else (if i.val < 174 then (if i.val < 173 then 180 else 181) else (if i.val < 175 then 178 else (if i.val < 176 then 179 else 158)))))) else (if i.val < 195 then (if i.val < 186 then (if i.val < 181 then (if i.val < 179 then (if i.val < 178 then 159 else 174) else (if i.val < 180 then 175 else 172)) else (if i.val < 183 then (if i.val < 182 then 173 else 160) else (if i.val < 184 then 161 else (if i.val < 185 then 168 else 169)))) else (if i.val < 190 then (if i.val < 188 then (if i.val < 187 then 170 else 171) else (if i.val < 189 then 206 else 207)) else (if i.val < 192 then (if i.val < 191 then 211 else 196) else (if i.val < 193 then 197 else (if i.val < 194 then 198 else 201))))) else (if i.val < 204 then (if i.val < 199 then (if i.val < 197 then (if i.val < 196 then 199 else 191) else (if i.val < 198 then 192 else 193)) else (if i.val < 201 then (if i.val < 200 then 195 else 202) else (if i.val < 202 then 194 else (if i.val < 203 then 200 else 209)))) else (if i.val < 208 then (if i.val < 206 then (if i.val < 205 then 210 else 208) else (if i.val < 207 then 188 else 189)) else (if i.val < 210 then (if i.val < 209 then 205 else 203) else (if i.val < 211 then 204 else (if i.val < 212 then 190 else 223))))))) else (if i.val < 248 then (if i.val < 230 then (if i.val < 221 then (if i.val < 217 then (if i.val < 215 then (if i.val < 214 then 228 else 218) else (if i.val < 216 then 219 else 220)) else (if i.val < 219 then (if i.val < 218 then 222 else 214) else (if i.val < 220 then 215 else 216))) else (if i.val < 225 then (if i.val < 223 then (if i.val < 222 then 231 else 217) else (if i.val < 224 then 212 else 234)) else (if i.val < 227 then (if i.val < 226 then 235 else 233) else (if i.val < 228 then 232 else (if i.val < 229 then 213 else 230))))) else (if i.val < 239 then (if i.val < 234 then (if i.val < 232 then (if i.val < 231 then 229 else 221) else (if i.val < 233 then 227 else 226)) else (if i.val < 236 then (if i.val < 235 then 224 else 225) else (if i.val < 237 then 241 else (if i.val < 238 then 242 else 243)))) else (if i.val < 243 then (if i.val < 241 then (if i.val < 240 then 258 else 244) else (if i.val < 242 then 236 else 237)) else (if i.val < 245 then (if i.val < 244 then 238 else 240) else (if i.val < 246 then 247 else (if i.val < 247 then 252 else 245)))))) else (if i.val < 266 then (if i.val < 257 then (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 255 else 256) else (if i.val < 251 then 254 else 253)) else (if i.val < 254 then (if i.val < 253 then 246 else 251) else (if i.val < 255 then 250 else (if i.val < 256 then 248 else 249)))) else (if i.val < 261 then (if i.val < 259 then (if i.val < 258 then 259 else 239) else (if i.val < 260 then 257 else 268)) else (if i.val < 263 then (if i.val < 262 then 269 else 270) else (if i.val < 264 then 273 else (if i.val < 265 then 271 else 274))))) else (if i.val < 275 then (if i.val < 270 then (if i.val < 268 then (if i.val < 267 then 278 else 282) else (if i.val < 269 then 260 else 261)) else (if i.val < 272 then (if i.val < 271 then 262 else 264) else (if i.val < 273 then 283 else (if i.val < 274 then 263 else 265)))) else (if i.val < 279 then (if i.val < 277 then (if i.val < 276 then 281 else 279) else (if i.val < 278 then 280 else 266)) else (if i.val < 281 then (if i.val < 280 then 276 else 277) else (if i.val < 282 then 275 else (if i.val < 283 then 267 else 272)))))))))
theorem left_gauge_checked : coarseAllB (fun i =>
    coarsePoseMatchB (compose (unsignedPose Catalog5.r) (registry i)) (registry (leftIndex i))) = true := by decide +kernel
theorem left_gauge_closed : ∀ q ∈ L, compose (unsignedPose Catalog5.r) q ∈ L := by
  intro q hq
  obtain ⟨i, rfl⟩ := registry_complete hq
  rw [coarsePoseMatchB_sound (coarseAllB_sound left_gauge_checked i)]
  exact registry_mem (leftIndex i)
def rightIndex : Fin 284 → Fin 284 := fun i =>
  (if i.val < 142 then (if i.val < 71 then (if i.val < 35 then (if i.val < 17 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 93 else 94) else (if i.val < 3 then 95 else 96)) else (if i.val < 6 then (if i.val < 5 then 97 else 98) else (if i.val < 7 then 99 else 92))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 90 else 91) else (if i.val < 11 then 100 else 101)) else (if i.val < 14 then (if i.val < 13 then 102 else 103) else (if i.val < 15 then 104 else (if i.val < 16 then 105 else 106))))) else (if i.val < 26 then (if i.val < 21 then (if i.val < 19 then (if i.val < 18 then 107 else 108) else (if i.val < 20 then 109 else 117)) else (if i.val < 23 then (if i.val < 22 then 118 else 119) else (if i.val < 24 then 113 else (if i.val < 25 then 114 else 115)))) else (if i.val < 30 then (if i.val < 28 then (if i.val < 27 then 116 else 110) else (if i.val < 29 then 111 else 112)) else (if i.val < 32 then (if i.val < 31 then 69 else 70) else (if i.val < 33 then 71 else (if i.val < 34 then 72 else 73)))))) else (if i.val < 53 then (if i.val < 44 then (if i.val < 39 then (if i.val < 37 then (if i.val < 36 then 74 else 75) else (if i.val < 38 then 61 else 62)) else (if i.val < 41 then (if i.val < 40 then 63 else 64) else (if i.val < 42 then 65 else (if i.val < 43 then 66 else 67)))) else (if i.val < 48 then (if i.val < 46 then (if i.val < 45 then 68 else 60) else (if i.val < 47 then 76 else 77)) else (if i.val < 50 then (if i.val < 49 then 78 else 79) else (if i.val < 51 then 80 else (if i.val < 52 then 86 else 87))))) else (if i.val < 62 then (if i.val < 57 then (if i.val < 55 then (if i.val < 54 then 88 else 89) else (if i.val < 56 then 84 else 85)) else (if i.val < 59 then (if i.val < 58 then 81 else 82) else (if i.val < 60 then 83 else (if i.val < 61 then 45 else 37)))) else (if i.val < 66 then (if i.val < 64 then (if i.val < 63 then 38 else 39) else (if i.val < 65 then 40 else 41)) else (if i.val < 68 then (if i.val < 67 then 42 else 43) else (if i.val < 69 then 44 else (if i.val < 70 then 30 else 31))))))) else (if i.val < 106 then (if i.val < 88 then (if i.val < 79 then (if i.val < 75 then (if i.val < 73 then (if i.val < 72 then 32 else 33) else (if i.val < 74 then 34 else 35)) else (if i.val < 77 then (if i.val < 76 then 36 else 46) else (if i.val < 78 then 47 else 48))) else (if i.val < 83 then (if i.val < 81 then (if i.val < 80 then 49 else 50) else (if i.val < 82 then 57 else 58)) else (if i.val < 85 then (if i.val < 84 then 59 else 55) else (if i.val < 86 then 56 else (if i.val < 87 then 51 else 52))))) else (if i.val < 97 then (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 53 else 54) else (if i.val < 91 then 8 else 9)) else (if i.val < 94 then (if i.val < 93 then 7 else 0) else (if i.val < 95 then 1 else (if i.val < 96 then 2 else 3)))) else (if i.val < 101 then (if i.val < 99 then (if i.val < 98 then 4 else 5) else (if i.val < 100 then 6 else 10)) else (if i.val < 103 then (if i.val < 102 then 11 else 12) else (if i.val < 104 then 13 else (if i.val < 105 then 14 else 15)))))) else (if i.val < 124 then (if i.val < 115 then (if i.val < 110 then (if i.val < 108 then (if i.val < 107 then 16 else 17) else (if i.val < 109 then 18 else 19)) else (if i.val < 112 then (if i.val < 111 then 27 else 28) else (if i.val < 113 then 29 else (if i.val < 114 then 23 else 24)))) else (if i.val < 119 then (if i.val < 117 then (if i.val < 116 then 25 else 26) else (if i.val < 118 then 20 else 21)) else (if i.val < 121 then (if i.val < 120 then 22 else 130) else (if i.val < 122 then 131 else (if i.val < 123 then 132 else 133))))) else (if i.val < 133 then (if i.val < 128 then (if i.val < 126 then (if i.val < 125 then 134 else 135) else (if i.val < 127 then 128 else 129)) else (if i.val < 130 then (if i.val < 129 then 126 else 127) else (if i.val < 131 then 120 else (if i.val < 132 then 121 else 122)))) else (if i.val < 137 then (if i.val < 135 then (if i.val < 134 then 123 else 124) else (if i.val < 136 then 125 else 150)) else (if i.val < 139 then (if i.val < 138 then 151 else 144) else (if i.val < 140 then 145 else (if i.val < 141 then 146 else 147)))))))) else (if i.val < 213 then (if i.val < 177 then (if i.val < 159 then (if i.val < 150 then (if i.val < 146 then (if i.val < 144 then (if i.val < 143 then 148 else 149) else (if i.val < 145 then 138 else 139)) else (if i.val < 148 then (if i.val < 147 then 140 else 141) else (if i.val < 149 then 142 else 143))) else (if i.val < 154 then (if i.val < 152 then (if i.val < 151 then 136 else 137) else (if i.val < 153 then 162 else 163)) else (if i.val < 156 then (if i.val < 155 then 164 else 165) else (if i.val < 157 then 166 else (if i.val < 158 then 167 else 160))))) else (if i.val < 168 then (if i.val < 163 then (if i.val < 161 then (if i.val < 160 then 161 else 158) else (if i.val < 162 then 159 else 152)) else (if i.val < 165 then (if i.val < 164 then 153 else 154) else (if i.val < 166 then 155 else (if i.val < 167 then 156 else 157)))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 184 else 185) else (if i.val < 171 then 186 else 187)) else (if i.val < 174 then (if i.val < 173 then 178 else 179) else (if i.val < 175 then 180 else (if i.val < 176 then 181 else 182)))))) else (if i.val < 195 then (if i.val < 186 then (if i.val < 181 then (if i.val < 179 then (if i.val < 178 then 183 else 172) else (if i.val < 180 then 173 else 174)) else (if i.val < 183 then (if i.val < 182 then 175 else 176) else (if i.val < 184 then 177 else (if i.val < 185 then 168 else 169)))) else (if i.val < 190 then (if i.val < 188 then (if i.val < 187 then 170 else 171) else (if i.val < 189 then 267 else 265)) else (if i.val < 192 then (if i.val < 191 then 266 else 260) else (if i.val < 193 then 261 else (if i.val < 194 then 262 else 263))))) else (if i.val < 204 then (if i.val < 199 then (if i.val < 197 then (if i.val < 196 then 264 else 268) else (if i.val < 198 then 269 else 270)) else (if i.val < 201 then (if i.val < 200 then 271 else 272) else (if i.val < 202 then 273 else (if i.val < 203 then 283 else 279)))) else (if i.val < 208 then (if i.val < 206 then (if i.val < 205 then 280 else 281) else (if i.val < 207 then 282 else 274)) else (if i.val < 210 then (if i.val < 209 then 275 else 276) else (if i.val < 211 then 277 else (if i.val < 212 then 278 else 245))))))) else (if i.val < 248 then (if i.val < 230 then (if i.val < 221 then (if i.val < 217 then (if i.val < 215 then (if i.val < 214 then 246 else 241) else (if i.val < 216 then 242 else 243)) else (if i.val < 219 then (if i.val < 218 then 244 else 236) else (if i.val < 220 then 237 else 238))) else (if i.val < 225 then (if i.val < 223 then (if i.val < 222 then 239 else 240) else (if i.val < 224 then 247 else 248)) else (if i.val < 227 then (if i.val < 226 then 249 else 250) else (if i.val < 228 then 251 else (if i.val < 229 then 252 else 259))))) else (if i.val < 239 then (if i.val < 234 then (if i.val < 232 then (if i.val < 231 then 257 else 258) else (if i.val < 233 then 253 else 254)) else (if i.val < 236 then (if i.val < 235 then 255 else 256) else (if i.val < 237 then 218 else (if i.val < 238 then 219 else 220)))) else (if i.val < 243 then (if i.val < 241 then (if i.val < 240 then 221 else 222) else (if i.val < 242 then 214 else 215)) else (if i.val < 245 then (if i.val < 244 then 216 else 217) else (if i.val < 246 then 212 else (if i.val < 247 then 213 else 223)))))) else (if i.val < 266 then (if i.val < 257 then (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 224 else 225) else (if i.val < 251 then 226 else 227)) else (if i.val < 254 then (if i.val < 253 then 228 else 232) else (if i.val < 255 then 233 else (if i.val < 256 then 234 else 235)))) else (if i.val < 261 then (if i.val < 259 then (if i.val < 258 then 230 else 231) else (if i.val < 260 then 229 else 191)) else (if i.val < 263 then (if i.val < 262 then 192 else 193) else (if i.val < 264 then 194 else (if i.val < 265 then 195 else 189))))) else (if i.val < 275 then (if i.val < 270 then (if i.val < 268 then (if i.val < 267 then 190 else 188) else (if i.val < 269 then 196 else 197)) else (if i.val < 272 then (if i.val < 271 then 198 else 199) else (if i.val < 273 then 200 else (if i.val < 274 then 201 else 207)))) else (if i.val < 279 then (if i.val < 277 then (if i.val < 276 then 208 else 209) else (if i.val < 278 then 210 else 211)) else (if i.val < 281 then (if i.val < 280 then 203 else 204) else (if i.val < 282 then 205 else (if i.val < 283 then 206 else 202)))))))))
theorem right_gauge_checked : coarseAllB (fun i =>
    coarsePoseMatchB (rightGauge Catalog5.r (registry i)) (registry (rightIndex i))) = true := by decide +kernel
theorem right_gauge_closed : ∀ q ∈ L, rightGauge Catalog5.r q ∈ L := by
  intro q hq
  obtain ⟨i, rfl⟩ := registry_complete hq
  rw [coarsePoseMatchB_sound (coarseAllB_sound right_gauge_checked i)]
  exact registry_mem (rightIndex i)

#print axioms child_table_covers
#print axioms C_sound
#print axioms left_gauge_closed
#print axioms right_gauge_closed
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5
