module

public import ProductClosure.ProductWorldBlockPose
public import ProductClosure.PolycubeDimensionCast
public import ProductClosure.ProductWorldTranslation

@[expose] public section

/-! Canonical dimension casts preserve full pose worlds, their owner laws,
relative contact languages, and genuine translation periods. -/
namespace ProductClosure.World
open Set
noncomputable section
variable {d e : ℕ}

@[simp] theorem castPose_symm (h : d = e) (q : RegisteredPrime.Pose d) :
    castPose h.symm (castPose h q) = q := by subst e; rfl

@[simp] theorem castPose_comp (h : d = e) (q r : RegisteredPrime.Pose d) :
    castPose h (q.comp r) = (castPose h q).comp (castPose h r) := by subst e; rfl

@[simp] theorem castPose_inv (h : d = e) (q : RegisteredPrime.Pose d) :
    castPose h q.inv = (castPose h q).inv := by subst e; rfl

@[simp] theorem castPose_relative (h : d = e) (q r : RegisteredPrime.Pose d) :
    castPose h (q.relative r) = (castPose h q).relative (castPose h r) := by subst e; rfl

@[simp] theorem castPose_translate (h : d = e) (v : Lattice d) (q : RegisteredPrime.Pose d) :
    castPose h (RegisteredPrime.AtlasPeriods.translate v q) =
      RegisteredPrime.AtlasPeriods.translate (Polycube.castIndex h v) (castPose h q) := by
  subst e; rfl

@[simp] theorem castIndex_mem_placedCells (h : d = e) (S : Finset (Lattice d))
    (q : RegisteredPrime.Pose d) (z : Lattice d) :
    Polycube.castIndex h z ∈ placedCells (Polycube.castCells h S) (castPose h q) ↔
      z ∈ placedCells S q := by subst e; rfl

namespace CompleteTiling
variable {S : Finset (Lattice d)}

/-- Reindex one complete world along an equality of dimensions, retaining
exact full pose data and the original finite carrier. -/
def castDimension (W : CompleteTiling (placedCells S)) (h : d = e) :
    CompleteTiling (placedCells (Polycube.castCells h S)) := by
  subst e
  exact W

@[simp] theorem castDimension_tiles (W : CompleteTiling (placedCells S)) (h : d = e) :
    (W.castDimension h).tiles = castPose h '' W.tiles := by
  subst e
  ext q
  simp only [castDimension, castPose, Set.mem_image, exists_eq_right]

@[simp] theorem castDimension_owner (W : CompleteTiling (placedCells S)) (h : d = e)
    (z : Lattice d) :
    (W.castDimension h).owner (Polycube.castIndex h z) = castPose h (W.owner z) := by
  subst e; rfl

/-- Relative language compatibility under the exact inverse pose cast. -/
theorem castDimension_legal (W : CompleteTiling (placedCells S)) (h : d = e)
    {M : RegisteredPrime.Pose d → Prop}
    (hl : W.IsLegal LatticeAdjacent (fun q r => M (q.relative r))) :
    (W.castDimension h).IsLegal LatticeAdjacent
      (fun q r => M (castPose h.symm (q.relative r))) := by
  subst e
  exact hl

/-- A proved forward comparison of relative languages can be used directly
without retaining an explicit cast in the target predicate. -/
theorem castDimension_legal_of_map (W : CompleteTiling (placedCells S)) (h : d = e)
    {M : RegisteredPrime.Pose d → Prop} {N : RegisteredPrime.Pose e → Prop}
    (hl : W.IsLegal LatticeAdjacent (fun q r => M (q.relative r)))
    (hmap : ∀ q, M q → N (castPose h q)) :
    (W.castDimension h).IsLegal LatticeAdjacent (fun q r => N (q.relative r)) := by
  subst e
  intro x y hadj hne
  exact hmap _ (hl x y hadj hne)

/-- Genuine full-pose translation periods are retained with precisely the
same dimension-cast vector. -/
theorem castDimension_hasStatePeriod (W : CompleteTiling (placedCells S)) (h : d = e)
    (v : Lattice d) (hp : W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v)) :
    (W.castDimension h).HasStatePeriod
      (RegisteredPrime.AtlasPeriods.translate (Polycube.castIndex h v)) := by
  subst e
  exact hp

/-- The period-transfer statement is reversible. -/
theorem castDimension_hasStatePeriod_iff (W : CompleteTiling (placedCells S)) (h : d = e)
    (v : Lattice d) :
    (W.castDimension h).HasStatePeriod
      (RegisteredPrime.AtlasPeriods.translate (Polycube.castIndex h v)) ↔
      W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v) := by
  subst e
  rfl

#print axioms castDimension
#print axioms castDimension_legal
#print axioms castDimension_hasStatePeriod

end CompleteTiling
end
end ProductClosure.World
