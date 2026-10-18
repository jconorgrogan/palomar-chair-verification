module

public import ProductClosure.ProductWorldDimensionCast

@[expose] public section

/-! Exact inverse cast for an existing native-dimension world. -/
namespace ProductClosure.World
open Set
noncomputable section
variable {d e : ℕ}

@[simp] theorem castPose_reverse {d e : ℕ} (h : d = e) (q : RegisteredPrime.Pose e) :
    castPose h (castPose h.symm q) = q := by subst e; rfl

@[simp] theorem castIndex_symm (h : d = e) (v : Lattice d) :
    Polycube.castIndex h.symm (Polycube.castIndex h v) = v := by subst e; rfl

@[simp] theorem castIndex_reverse (h : d = e) (v : Lattice e) :
    Polycube.castIndex h (Polycube.castIndex h.symm v) = v := by subst e; rfl

theorem castIndex_eq_zero_iff (h : d = e) (v : Lattice d) :
    Polycube.castIndex h v = 0 ↔ v = 0 := by subst e; rfl

namespace CompleteTiling
variable {S : Finset (Lattice d)}

/-- Undo the native-dimension cast on an actual existing complete world. -/
def uncastDimension (h : d = e)
    (W : CompleteTiling (placedCells (Polycube.castCells h S))) :
    CompleteTiling (placedCells S) := by
  subst e
  exact W

@[simp] theorem uncastDimension_tiles (h : d = e)
    (W : CompleteTiling (placedCells (Polycube.castCells h S))) :
    (uncastDimension h W).tiles = castPose h.symm '' W.tiles := by
  subst e
  ext q
  simp only [uncastDimension, castPose, Set.mem_image, exists_eq_right]

@[simp] theorem uncastDimension_owner (h : d = e)
    (W : CompleteTiling (placedCells (Polycube.castCells h S))) (z : Lattice d) :
    (uncastDimension h W).owner z = castPose h.symm (W.owner (Polycube.castIndex h z)) := by
  subst e; rfl

theorem uncastDimension_legal (h : d = e)
    (W : CompleteTiling (placedCells (Polycube.castCells h S)))
    {M : RegisteredPrime.Pose e → Prop}
    (hl : W.IsLegal LatticeAdjacent (fun q r => M (q.relative r))) :
    (uncastDimension h W).IsLegal LatticeAdjacent
      (fun q r => M (castPose h (q.relative r))) := by
  subst e
  exact hl

theorem uncastDimension_hasStatePeriod (h : d = e)
    (W : CompleteTiling (placedCells (Polycube.castCells h S)))
    (v : Lattice e) (hp : W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v)) :
    (uncastDimension h W).HasStatePeriod
      (RegisteredPrime.AtlasPeriods.translate (Polycube.castIndex h.symm v)) := by
  subst e
  exact hp

#print axioms uncastDimension_legal
#print axioms uncastDimension_hasStatePeriod
end CompleteTiling
end
end ProductClosure.World
