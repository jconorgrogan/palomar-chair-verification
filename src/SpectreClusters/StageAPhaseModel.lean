module

public import SpectreClusters.StageAWindowModel

@[expose] public section


namespace SpectreClusters.StageA

/-- The two possible sparse-species phases, attached to literal row IDs. -/
def sparseTurtlesRow : HTKind → Nat → Bool
  | .hat, i => !(i == 210)
  | .turtle, i => i == 0

def phaseCompatibleB (kind : HTKind) (i : Nat) : Bool :=
  (rawWordAt kind i).eraseDups.all fun n =>
    alignmentValidB kind n &&
      (keptIds 2 (candidateAt kind n).kind).all fun j =>
        !(supportB kind (rawWordAt kind i) n (rawWordAt (candidateAt kind n).kind j)) ||
          (sparseTurtlesRow kind i == sparseTurtlesRow (candidateAt kind n).kind j)

theorem phaseCompatible_alignment (kind : HTKind) (i n : Nat)
    (hc : phaseCompatibleB kind i = true) (hn : n ∈ rawWordAt kind i) :
    alignmentValidB kind n = true := by
  have h := List.all_eq_true.mp hc n (List.mem_eraseDups.mpr hn)
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem phaseCompatible_sound (kind : HTKind) (i n j : Nat)
    (hc : phaseCompatibleB kind i = true) (hn : n ∈ rawWordAt kind i)
    (hj : j ∈ keptIds 2 (candidateAt kind n).kind)
    (hs : supportB kind (rawWordAt kind i) n
      (rawWordAt (candidateAt kind n).kind j) = true) :
    sparseTurtlesRow kind i = sparseTurtlesRow (candidateAt kind n).kind j := by
  have h := List.all_eq_true.mp hc n (List.mem_eraseDups.mpr hn)
  simp only [Bool.and_eq_true] at h
  have hjc := List.all_eq_true.mp h.2 j hj
  simpa [hs] using hjc

end SpectreClusters.StageA
