module

public import SparseMonotiles.ContactChecker

@[expose] public section

namespace SparseMonotiles.Canonical

def canonicalPerm7_0 : Equiv.Perm (Fin 7) :=
  ⟨![0, 1, 2, 6, 3, 4, 5], ![0, 1, 2, 4, 5, 6, 3], by decide, by decide⟩

def canonicalPerm7_1 : Equiv.Perm (Fin 7) :=
  ⟨![0, 1, 6, 2, 3, 4, 5], ![0, 1, 3, 4, 5, 6, 2], by decide, by decide⟩

def canonicalPerm7_2 : Equiv.Perm (Fin 7) :=
  ⟨![0, 5, 4, 3, 2, 6, 1], ![0, 6, 4, 3, 2, 1, 5], by decide, by decide⟩

def canonicalPerm7_3 : Equiv.Perm (Fin 7) :=
  ⟨![0, 5, 4, 3, 6, 2, 1], ![0, 6, 5, 3, 2, 1, 4], by decide, by decide⟩

def canonicalPerm7_4 : Equiv.Perm (Fin 7) :=
  ⟨![1, 0, 5, 4, 3, 2, 6], ![1, 0, 5, 4, 3, 2, 6], by decide, by decide⟩

def canonicalPerm7_5 : Equiv.Perm (Fin 7) :=
  ⟨![1, 0, 5, 4, 3, 6, 2], ![1, 0, 6, 4, 3, 2, 5], by decide, by decide⟩

def canonicalPerm7_6 : Equiv.Perm (Fin 7) :=
  ⟨![1, 2, 6, 3, 4, 5, 0], ![6, 0, 1, 3, 4, 5, 2], by decide, by decide⟩

def canonicalPerm7_7 : Equiv.Perm (Fin 7) :=
  ⟨![1, 6, 2, 3, 4, 5, 0], ![6, 0, 2, 3, 4, 5, 1], by decide, by decide⟩

def canonicalPerm7_8 : Equiv.Perm (Fin 7) :=
  ⟨![2, 1, 0, 5, 4, 3, 6], ![2, 1, 0, 5, 4, 3, 6], by decide, by decide⟩

def canonicalPerm7_9 : Equiv.Perm (Fin 7) :=
  ⟨![2, 3, 4, 5, 0, 1, 6], ![4, 5, 0, 1, 2, 3, 6], by decide, by decide⟩

def canonicalPerm7_10 : Equiv.Perm (Fin 7) :=
  ⟨![2, 6, 1, 0, 5, 4, 3], ![3, 2, 0, 6, 5, 4, 1], by decide, by decide⟩

def canonicalPerm7_11 : Equiv.Perm (Fin 7) :=
  ⟨![2, 6, 3, 4, 5, 0, 1], ![5, 6, 0, 2, 3, 4, 1], by decide, by decide⟩

def canonicalPerm7_12 : Equiv.Perm (Fin 7) :=
  ⟨![3, 2, 6, 1, 0, 5, 4], ![4, 3, 1, 0, 6, 5, 2], by decide, by decide⟩

def canonicalPerm7_13 : Equiv.Perm (Fin 7) :=
  ⟨![3, 4, 5, 0, 1, 2, 6], ![3, 4, 5, 0, 1, 2, 6], by decide, by decide⟩

def canonicalPerm7_14 : Equiv.Perm (Fin 7) :=
  ⟨![3, 4, 5, 0, 1, 6, 2], ![3, 4, 6, 0, 1, 2, 5], by decide, by decide⟩

def canonicalPerm7_15 : Equiv.Perm (Fin 7) :=
  ⟨![3, 6, 2, 1, 0, 5, 4], ![4, 3, 2, 0, 6, 5, 1], by decide, by decide⟩

def canonicalPerm7_16 : Equiv.Perm (Fin 7) :=
  ⟨![4, 3, 2, 6, 1, 0, 5], ![5, 4, 2, 1, 0, 6, 3], by decide, by decide⟩

def canonicalPerm7_17 : Equiv.Perm (Fin 7) :=
  ⟨![4, 3, 6, 2, 1, 0, 5], ![5, 4, 3, 1, 0, 6, 2], by decide, by decide⟩

def canonicalPerm7_18 : Equiv.Perm (Fin 7) :=
  ⟨![4, 5, 0, 1, 2, 6, 3], ![2, 3, 4, 6, 0, 1, 5], by decide, by decide⟩

def canonicalPerm7_19 : Equiv.Perm (Fin 7) :=
  ⟨![4, 5, 0, 1, 6, 2, 3], ![2, 3, 5, 6, 0, 1, 4], by decide, by decide⟩

def canonicalPerm7_20 : Equiv.Perm (Fin 7) :=
  ⟨![5, 0, 1, 2, 6, 3, 4], ![1, 2, 3, 5, 6, 0, 4], by decide, by decide⟩

def canonicalPerm7_21 : Equiv.Perm (Fin 7) :=
  ⟨![5, 0, 1, 6, 2, 3, 4], ![1, 2, 4, 5, 6, 0, 3], by decide, by decide⟩

def canonicalPerm7_22 : Equiv.Perm (Fin 7) :=
  ⟨![5, 4, 3, 2, 6, 1, 0], ![6, 5, 3, 2, 1, 0, 4], by decide, by decide⟩

def canonicalPerm7_23 : Equiv.Perm (Fin 7) :=
  ⟨![5, 4, 3, 6, 2, 1, 0], ![6, 5, 4, 2, 1, 0, 3], by decide, by decide⟩

def canonicalPerm7_24 : Equiv.Perm (Fin 7) :=
  ⟨![6, 1, 0, 5, 4, 3, 2], ![2, 1, 6, 5, 4, 3, 0], by decide, by decide⟩

def canonicalPerm7_25 : Equiv.Perm (Fin 7) :=
  ⟨![6, 2, 1, 0, 5, 4, 3], ![3, 2, 1, 6, 5, 4, 0], by decide, by decide⟩

def canonicalPerm7_26 : Equiv.Perm (Fin 7) :=
  ⟨![6, 2, 3, 4, 5, 0, 1], ![5, 6, 1, 2, 3, 4, 0], by decide, by decide⟩

def canonicalPerm7_27 : Equiv.Perm (Fin 7) :=
  ⟨![6, 3, 4, 5, 0, 1, 2], ![4, 5, 6, 1, 2, 3, 0], by decide, by decide⟩

end SparseMonotiles.Canonical
