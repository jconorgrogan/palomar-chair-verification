module

public import SparseMonotiles.CarrierHierarchyCatalog

@[expose] public section

/-! Supplied exact contact catalog, not a proved physical contact law.
Source: p5_F.json; SHA-256: b76cb81ef4325c4465e89f5459a19bcbbb036dd6c6c7c98e74f063f11c9adb87
Canonical children use μ=1, the stated g, and the zero-mean empty endpoint.
-/
namespace SparseMonotiles.CarrierHierarchy.Catalog5
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def perm0 : Equiv.Perm (Fin 5) :=
  ⟨![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], by decide, by decide⟩
def perm1 : Equiv.Perm (Fin 5) :=
  ⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide, by decide⟩
def perm2 : Equiv.Perm (Fin 5) :=
  ⟨![0, 3, 1, 4, 2], ![0, 2, 4, 1, 3], by decide, by decide⟩
def perm3 : Equiv.Perm (Fin 5) :=
  ⟨![0, 4, 3, 2, 1], ![0, 4, 3, 2, 1], by decide, by decide⟩
def perm4 : Equiv.Perm (Fin 5) :=
  ⟨![1, 0, 4, 3, 2], ![1, 0, 4, 3, 2], by decide, by decide⟩
def perm5 : Equiv.Perm (Fin 5) :=
  ⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide, by decide⟩
def perm6 : Equiv.Perm (Fin 5) :=
  ⟨![1, 3, 0, 2, 4], ![2, 0, 3, 1, 4], by decide, by decide⟩
def perm7 : Equiv.Perm (Fin 5) :=
  ⟨![1, 4, 2, 0, 3], ![3, 0, 2, 4, 1], by decide, by decide⟩
def perm8 : Equiv.Perm (Fin 5) :=
  ⟨![2, 0, 3, 1, 4], ![1, 3, 0, 2, 4], by decide, by decide⟩
def perm9 : Equiv.Perm (Fin 5) :=
  ⟨![2, 1, 0, 4, 3], ![2, 1, 0, 4, 3], by decide, by decide⟩
def perm10 : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide, by decide⟩
def perm11 : Equiv.Perm (Fin 5) :=
  ⟨![2, 4, 1, 3, 0], ![4, 2, 0, 3, 1], by decide, by decide⟩
def perm12 : Equiv.Perm (Fin 5) :=
  ⟨![3, 0, 2, 4, 1], ![1, 4, 2, 0, 3], by decide, by decide⟩
def perm13 : Equiv.Perm (Fin 5) :=
  ⟨![3, 1, 4, 2, 0], ![4, 1, 3, 0, 2], by decide, by decide⟩
def perm14 : Equiv.Perm (Fin 5) :=
  ⟨![3, 2, 1, 0, 4], ![3, 2, 1, 0, 4], by decide, by decide⟩
def perm15 : Equiv.Perm (Fin 5) :=
  ⟨![3, 4, 0, 1, 2], ![2, 3, 4, 0, 1], by decide, by decide⟩
def perm16 : Equiv.Perm (Fin 5) :=
  ⟨![4, 0, 1, 2, 3], ![1, 2, 3, 4, 0], by decide, by decide⟩
def perm17 : Equiv.Perm (Fin 5) :=
  ⟨![4, 1, 3, 0, 2], ![3, 1, 4, 2, 0], by decide, by decide⟩
def perm18 : Equiv.Perm (Fin 5) :=
  ⟨![4, 2, 0, 3, 1], ![2, 4, 1, 3, 0], by decide, by decide⟩
def perm19 : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 2, 1, 0], ![4, 3, 2, 1, 0], by decide, by decide⟩
def r : Equiv.Perm (Fin 5) := perm3
theorem r_involutive : Function.Involutive r := by unfold Function.Involutive; decide
def childPermTable : List (Equiv.Perm (Fin 5)) := [
perm0, perm1, perm12, perm14, perm6, perm4, perm19, perm8, perm17, perm19, perm9, perm7, perm3, perm2, perm18, perm5, perm11, perm9, perm3, perm2, perm14, perm18, perm13, perm10, perm4, perm13, perm8, perm15, perm7, perm16, perm0, perm1
]
def childPerm (a : Bits 5) : Equiv.Perm (Fin 5) :=
  childPermTable.getD (bitCode a) (Equiv.refl _)
def supplied : List (Pose 5) := [
  ⟨perm19, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm19, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm19, ![true, true, true, true, false], ![3, 3, 3, 3, -1]⟩,
  ⟨perm19, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm19, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm19, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm19, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm18, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm17, ![true, true, false, true, false], ![3, 3, -1, 3, -1]⟩,
  ⟨perm17, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm16, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm16, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm16, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm16, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm16, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm16, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm16, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm16, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm16, ![true, false, true, true, true], ![3, -1, 3, 3, 3]⟩,
  ⟨perm16, ![true, false, true, false, false], ![3, -1, 3, -1, -1]⟩,
  ⟨perm17, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm17, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm17, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm18, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm18, ![true, false, true, false, true], ![3, -1, 3, -1, 3]⟩,
  ⟨perm18, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm18, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm19, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm19, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm19, ![true, false, false, true, false], ![3, -1, -1, 3, -1]⟩,
  ⟨perm15, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm15, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm15, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm15, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm15, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm15, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm15, ![true, true, false, true, true], ![3, 3, -1, 3, 3]⟩,
  ⟨perm14, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm14, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm14, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm14, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm14, ![true, true, true, false, true], ![3, 3, 3, -1, 3]⟩,
  ⟨perm14, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm14, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm14, ![true, true, false, false, false], ![3, 3, -1, -1, -1]⟩,
  ⟨perm13, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm12, ![true, true, true, false, false], ![3, 3, 3, -1, -1]⟩,
  ⟨perm12, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm12, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm12, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm12, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm13, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm13, ![true, false, false, true, true], ![3, -1, -1, 3, 3]⟩,
  ⟨perm13, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm13, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm14, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm14, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm15, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm15, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm15, ![true, false, false, false, true], ![3, -1, -1, -1, 3]⟩,
  ⟨perm11, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm10, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm10, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm10, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm10, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm10, ![true, true, true, false, true], ![3, 3, 3, -1, 3]⟩,
  ⟨perm10, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm10, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm10, ![true, true, false, false, false], ![3, 3, -1, -1, -1]⟩,
  ⟨perm9, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm9, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm9, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm9, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm9, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm9, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm9, ![true, true, false, true, true], ![3, 3, -1, 3, 3]⟩,
  ⟨perm8, ![true, true, true, false, false], ![3, 3, 3, -1, -1]⟩,
  ⟨perm8, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm8, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm8, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm8, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm9, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm9, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm9, ![true, false, false, false, true], ![3, -1, -1, -1, 3]⟩,
  ⟨perm10, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm10, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm11, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm11, ![true, false, false, true, true], ![3, -1, -1, 3, 3]⟩,
  ⟨perm11, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm11, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm7, ![true, true, false, true, false], ![3, 3, -1, 3, -1]⟩,
  ⟨perm7, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm6, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm5, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm5, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm5, ![true, true, true, true, false], ![3, 3, 3, 3, -1]⟩,
  ⟨perm5, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm5, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm5, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm5, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm4, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm4, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm4, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm4, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm4, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm4, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm4, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm4, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm4, ![true, false, true, true, true], ![3, -1, 3, 3, 3]⟩,
  ⟨perm4, ![true, false, true, false, false], ![3, -1, 3, -1, -1]⟩,
  ⟨perm5, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm5, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm5, ![true, false, false, true, false], ![3, -1, -1, 3, -1]⟩,
  ⟨perm6, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm6, ![true, false, true, false, true], ![3, -1, 3, -1, 3]⟩,
  ⟨perm6, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm6, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm7, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm7, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm7, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm3, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm3, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm3, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm3, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm3, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm3, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm2, ![true, true, false, false, true], ![3, 3, -1, -1, 3]⟩,
  ⟨perm2, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm1, ![true, true, false, false, true], ![3, 3, -1, -1, 3]⟩,
  ⟨perm1, ![true, true, false, false, true], ![3, 3, 1, 1, 3]⟩,
  ⟨perm0, ![true, true, true, true, false], ![2, 2, 2, 2, -2]⟩,
  ⟨perm0, ![true, true, true, true, false], ![2, 2, 2, 2, 2]⟩,
  ⟨perm0, ![true, true, true, false, true], ![2, 2, 2, -2, 2]⟩,
  ⟨perm0, ![true, true, true, false, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm0, ![true, true, false, true, true], ![2, 2, -2, 2, 2]⟩,
  ⟨perm0, ![true, true, false, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm0, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm0, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm1, ![true, false, true, true, false], ![3, -1, 3, 3, -1]⟩,
  ⟨perm1, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm1, ![true, false, false, false, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm1, ![true, false, false, false, false], ![3, -1, -1, -1, -1]⟩,
  ⟨perm1, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm1, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm2, ![true, false, true, true, false], ![3, -1, 3, 3, -1]⟩,
  ⟨perm2, ![true, false, true, true, false], ![3, 1, 3, 3, 1]⟩,
  ⟨perm2, ![true, false, false, false, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm2, ![true, false, false, false, false], ![3, -1, -1, -1, -1]⟩,
  ⟨perm2, ![true, false, false, false, false], ![3, 1, 1, 1, 1]⟩,
  ⟨perm2, ![true, false, false, false, false], ![4, 0, 0, 0, 0]⟩,
  ⟨perm3, ![true, false, true, true, true], ![2, -2, 2, 2, 2]⟩,
  ⟨perm3, ![true, false, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm3, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm3, ![false, true, true, true, true], ![-1, 3, 3, 3, 3]⟩,
  ⟨perm3, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm3, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm3, ![false, true, false, false, true], ![-1, 3, -1, -1, 3]⟩,
  ⟨perm3, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm2, ![false, true, false, false, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm2, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm1, ![false, true, false, false, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm1, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm0, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm0, ![false, true, true, true, true], ![-1, 3, 3, 3, 3]⟩,
  ⟨perm0, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm0, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm0, ![false, true, false, false, true], ![-1, 3, -1, -1, 3]⟩,
  ⟨perm0, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm0, ![false, false, true, true, false], ![-1, -1, 3, 3, -1]⟩,
  ⟨perm0, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm0, ![false, false, false, false, false], ![-1, -1, -1, -1, -1]⟩,
  ⟨perm0, ![false, false, false, false, false], ![1, 1, 1, 1, 1]⟩,
  ⟨perm1, ![false, false, true, false, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm1, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm1, ![false, false, false, true, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm1, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm1, ![false, false, false, false, true], ![0, 0, 0, 0, 0]⟩,
  ⟨perm1, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm2, ![false, false, true, false, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm2, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm2, ![false, false, false, true, false], ![0, 0, 0, 0, 0]⟩,
  ⟨perm2, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm2, ![false, false, false, false, true], ![0, 0, 0, 0, 0]⟩,
  ⟨perm2, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm3, ![false, false, true, true, false], ![-1, -1, 3, 3, -1]⟩,
  ⟨perm3, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm3, ![false, false, false, false, false], ![-1, -1, -1, -1, -1]⟩,
  ⟨perm3, ![false, false, false, false, false], ![1, 1, 1, 1, 1]⟩,
  ⟨perm7, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm6, ![false, true, true, true, false], ![-1, 3, 3, 3, -1]⟩,
  ⟨perm6, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm5, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm5, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm5, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm5, ![false, true, true, false, false], ![-1, 3, 3, -1, -1]⟩,
  ⟨perm5, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm4, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm4, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm4, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm4, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm4, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm4, ![false, false, false, true, true], ![-1, -1, -1, 3, 3]⟩,
  ⟨perm5, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm6, ![false, false, true, false, false], ![-1, -1, 3, -1, -1]⟩,
  ⟨perm6, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm6, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm6, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm7, ![false, false, true, true, true], ![-1, -1, 3, 3, 3]⟩,
  ⟨perm7, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm7, ![false, false, false, true, false], ![-1, -1, -1, 3, -1]⟩,
  ⟨perm7, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm7, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm11, ![false, true, true, false, true], ![-1, 3, 3, -1, 3]⟩,
  ⟨perm11, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm10, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm10, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm10, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm10, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm9, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm9, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm9, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm9, ![false, true, false, true, false], ![-1, 3, -1, 3, -1]⟩,
  ⟨perm9, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm8, ![false, true, false, true, true], ![-1, 3, -1, 3, 3]⟩,
  ⟨perm8, ![false, true, false, false, false], ![-1, 3, -1, -1, -1]⟩,
  ⟨perm8, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm8, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm8, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm8, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm9, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm10, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm10, ![false, false, true, false, true], ![-1, -1, 3, -1, 3]⟩,
  ⟨perm11, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm11, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm11, ![false, false, false, false, true], ![-1, -1, -1, -1, 3]⟩,
  ⟨perm11, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm15, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm15, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm15, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm15, ![false, true, false, true, false], ![-1, 3, -1, 3, -1]⟩,
  ⟨perm15, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm14, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm14, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm14, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm14, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm13, ![false, true, true, false, true], ![-1, 3, 3, -1, 3]⟩,
  ⟨perm13, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm12, ![false, true, false, true, true], ![-1, 3, -1, 3, 3]⟩,
  ⟨perm12, ![false, true, false, false, false], ![-1, 3, -1, -1, -1]⟩,
  ⟨perm12, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm12, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm12, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm12, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm13, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm13, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm13, ![false, false, false, false, true], ![-1, -1, -1, -1, 3]⟩,
  ⟨perm13, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm14, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm14, ![false, false, true, false, true], ![-1, -1, 3, -1, 3]⟩,
  ⟨perm15, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm19, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm19, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm19, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm19, ![false, true, true, false, false], ![-1, 3, 3, -1, -1]⟩,
  ⟨perm19, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm18, ![false, true, true, true, false], ![-1, 3, 3, 3, -1]⟩,
  ⟨perm18, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm17, ![false, true, false, false, false], ![0, 4, 0, 0, 0]⟩,
  ⟨perm16, ![false, true, true, true, true], ![-2, 2, 2, 2, 2]⟩,
  ⟨perm16, ![false, true, true, true, true], ![1, 3, 3, 3, 3]⟩,
  ⟨perm16, ![false, true, true, true, true], ![2, 2, 2, 2, 2]⟩,
  ⟨perm16, ![false, true, false, false, true], ![1, 3, 1, 1, 3]⟩,
  ⟨perm16, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩,
  ⟨perm16, ![false, false, false, true, true], ![-1, -1, -1, 3, 3]⟩,
  ⟨perm17, ![false, false, true, true, true], ![-1, -1, 3, 3, 3]⟩,
  ⟨perm17, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm17, ![false, false, false, true, false], ![-1, -1, -1, 3, -1]⟩,
  ⟨perm17, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm17, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm18, ![false, false, true, false, false], ![-1, -1, 3, -1, -1]⟩,
  ⟨perm18, ![false, false, true, false, false], ![0, 0, 4, 0, 0]⟩,
  ⟨perm18, ![false, false, false, true, false], ![0, 0, 0, 4, 0]⟩,
  ⟨perm18, ![false, false, false, false, true], ![0, 0, 0, 0, 4]⟩,
  ⟨perm19, ![false, false, true, true, false], ![1, 1, 3, 3, 1]⟩
]
theorem supplied_count : supplied.length = 284 := by decide
theorem child_rule_equivariant : EquivariantChildren childPerm r := by decide
theorem checked_local_catalog : supplied.all (checkLocalCatalog childPerm r) = true := by decide
theorem local_catalog : ∀ p ∈ supplied, LocalCatalogFacts childPerm r p :=
  localCatalog_of_checked checked_local_catalog
#print axioms local_catalog
end SparseMonotiles.CarrierHierarchy.Catalog5
