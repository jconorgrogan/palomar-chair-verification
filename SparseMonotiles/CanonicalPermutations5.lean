module

public import SparseMonotiles.ContactChecker

@[expose] public section

namespace SparseMonotiles.Canonical

def canonicalPerm5_0 : Equiv.Perm (Fin 5) :=
  ⟨![0, 1, 2, 4, 3], ![0, 1, 2, 4, 3], by decide, by decide⟩

def canonicalPerm5_1 : Equiv.Perm (Fin 5) :=
  ⟨![0, 2, 3, 1, 4], ![0, 3, 1, 2, 4], by decide, by decide⟩

def canonicalPerm5_2 : Equiv.Perm (Fin 5) :=
  ⟨![0, 3, 4, 2, 1], ![0, 4, 3, 1, 2], by decide, by decide⟩

def canonicalPerm5_3 : Equiv.Perm (Fin 5) :=
  ⟨![0, 4, 1, 3, 2], ![0, 2, 4, 3, 1], by decide, by decide⟩

def canonicalPerm5_4 : Equiv.Perm (Fin 5) :=
  ⟨![1, 0, 3, 4, 2], ![1, 0, 4, 2, 3], by decide, by decide⟩

def canonicalPerm5_5 : Equiv.Perm (Fin 5) :=
  ⟨![1, 2, 4, 3, 0], ![4, 0, 1, 3, 2], by decide, by decide⟩

def canonicalPerm5_6 : Equiv.Perm (Fin 5) :=
  ⟨![1, 3, 2, 0, 4], ![3, 0, 2, 1, 4], by decide, by decide⟩

def canonicalPerm5_7 : Equiv.Perm (Fin 5) :=
  ⟨![1, 4, 0, 2, 3], ![2, 0, 3, 4, 1], by decide, by decide⟩

def canonicalPerm5_8 : Equiv.Perm (Fin 5) :=
  ⟨![2, 0, 4, 1, 3], ![1, 3, 0, 4, 2], by decide, by decide⟩

def canonicalPerm5_9 : Equiv.Perm (Fin 5) :=
  ⟨![2, 1, 0, 3, 4], ![2, 1, 0, 3, 4], by decide, by decide⟩

def canonicalPerm5_10 : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 1, 4, 0], ![4, 2, 0, 1, 3], by decide, by decide⟩

def canonicalPerm5_11 : Equiv.Perm (Fin 5) :=
  ⟨![2, 4, 3, 0, 1], ![3, 4, 0, 2, 1], by decide, by decide⟩

def canonicalPerm5_12 : Equiv.Perm (Fin 5) :=
  ⟨![3, 0, 1, 2, 4], ![1, 2, 3, 0, 4], by decide, by decide⟩

def canonicalPerm5_13 : Equiv.Perm (Fin 5) :=
  ⟨![3, 1, 4, 0, 2], ![3, 1, 4, 0, 2], by decide, by decide⟩

def canonicalPerm5_14 : Equiv.Perm (Fin 5) :=
  ⟨![3, 2, 0, 4, 1], ![2, 4, 1, 0, 3], by decide, by decide⟩

def canonicalPerm5_15 : Equiv.Perm (Fin 5) :=
  ⟨![3, 4, 2, 1, 0], ![4, 3, 2, 0, 1], by decide, by decide⟩

def canonicalPerm5_16 : Equiv.Perm (Fin 5) :=
  ⟨![4, 0, 2, 3, 1], ![1, 4, 2, 3, 0], by decide, by decide⟩

def canonicalPerm5_17 : Equiv.Perm (Fin 5) :=
  ⟨![4, 1, 3, 2, 0], ![4, 1, 3, 2, 0], by decide, by decide⟩

def canonicalPerm5_18 : Equiv.Perm (Fin 5) :=
  ⟨![4, 2, 1, 0, 3], ![3, 2, 1, 4, 0], by decide, by decide⟩

def canonicalPerm5_19 : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 0, 1, 2], ![2, 3, 4, 1, 0], by decide, by decide⟩

end SparseMonotiles.Canonical
