module

public import SpectreFinite.ParentFramedPatterns
public import SpectreFinite.ParentPartition

@[expose] public section


/-! Exact finite cardinality and period transport of complete parent regions.
The growth bound is for a single proved parent partition; iteration still
requires a separately proved coarse legal field. -/
namespace SpectreFinite.HexSearch.ParentOwnership

def parentPositions (f : Position → State) (a : Position) (k : TileKind) : List Position :=
  (framedChildPatch f a k).map Prod.fst

theorem child_positions_nodup : ∀ k : TileKind, ((childPatch k).map Prod.fst).Nodup := by
  decide

theorem parentPositions_nodup (f : Position → State) (a : Position) (k : TileKind) :
    (parentPositions f a k).Nodup := by
  simp only [parentPositions,framedChildPatch,List.map_map]
  change ((childPatch k).map (fun e => addPos a (rotatePosition (f a).2 e.1))).Nodup
  have hm : ((childPatch k).map (fun e => addPos a (rotatePosition (f a).2 e.1))) =
      ((childPatch k).map Prod.fst).map (fun x => addPos a (rotatePosition (f a).2 x)) := by
    rw [List.map_map]
    rfl
  rw [hm]
  exact List.Pairwise.map _ (fun x y h he => h
    (rotatePosition_injective (f a).2 x y ((addPos_left_cancel_iff a _ _).mp he)))
      (child_positions_nodup k)

theorem parentPositions_length (f : Position → State) (a : Position) (k : TileKind) :
    (parentPositions f a k).length = if k.val = 0 then 7 else 8 := by
  simpa [parentPositions,framedChildPatch,childPatch] using nineListedSupertiles_size k

theorem parentPositions_length_bounds (f : Position → State) (a : Position) (k : TileKind) :
    7 ≤ (parentPositions f a k).length ∧ (parentPositions f a k).length ≤ 8 := by
  rw [parentPositions_length]
  split <;> decide

/-- This finite list is exactly the complete parent fiber, without missing
cells outside the illustrated support. -/
theorem mem_parentPositions_iff (f : Position → State) (a : Position) (k : TileKind)
    (hk : ExactParentAt f a k) (x : Position) :
    x ∈ parentPositions f a k ↔ ParentCell f a x := by
  constructor
  · intro h
    obtain ⟨e,he,heq⟩ := List.mem_map.mp h
    have ho := (hk e.1 e.2).mpr he
    simpa only [ParentCell,heq] using ho.1
  · intro h
    exact List.mem_map.mpr ⟨(x,f x),(hk x (f x)).mp ⟨h,rfl⟩,rfl⟩

theorem framedChildPatch_period (f : Position → State) (v : Position)
    (hv : FieldPeriod f v) (a : Position) (k : TileKind) :
    framedChildPatch f (addPos v a) k =
      (framedChildPatch f a k).map (fun e => (addPos v e.1,e.2)) := by
  simp only [framedChildPatch,hv a,List.map_map]
  apply List.map_congr_left
  intro e he
  apply Prod.ext
  · exact addPos_assoc v a _
  · rfl

theorem exactParentAt_period (f : Position → State) (v : Position)
    (hv : FieldPeriod f v) (a : Position) (k : TileKind)
    (hk : ExactParentAt f a k) : ExactParentAt f (addPos v a) k := by
  intro x s
  let y := subPos x v
  have hy : addPos v y = x := by
    apply Prod.ext <;> simp only [y,addPos,subPos] <;> omega
  change (ParentCell f (addPos v a) x ∧ s = f x) ↔ _
  rw [← hy,parentCell_period_iff f v hv a y, hv y,framedChildPatch_period f v hv]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨(y,s),(hk y s).mp h,rfl⟩
  · intro h
    obtain ⟨e,he,heq⟩ := List.mem_map.mp h
    have hx := (addPos_left_cancel_iff v _ _).mp (congrArg Prod.fst heq)
    have hs := congrArg Prod.snd heq
    have he' : e = (y,s) := Prod.ext hx hs
    apply (hk y s).mpr
    simpa only [he'] using he

end SpectreFinite.HexSearch.ParentOwnership
