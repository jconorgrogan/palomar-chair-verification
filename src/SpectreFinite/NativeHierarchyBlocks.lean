module

public import SpectreFinite.NativeCoarsening

@[expose] public section


/-! Actual finite iterated parent blocks, formed by repeatedly applying the
proved coarse legal field and its exact native fibers. Growth and boundary
bounds are derived by induction, rather than stored as assumptions. -/
namespace SpectreFinite.HexSearch.NativeHierarchy
open ParentOwnership NativeBoundaryRefinement

variable (C : ParentOccurrenceTheorem)
include C

noncomputable def blocks : Nat → LegalField → Position → List Position
  | 0,_,x => [x]
  | n+1,F,x => refine C F (blocks n (next C F) x)

noncomputable def boundaryEdges : Nat → LegalField → Position → List NativeBoundaryRefinement.Edge
  | 0,_,x => (List.finRange 6).map (fun d => (x,d))
  | n+1,F,x => (boundaryEdges n (next C F) x).flatMap (expand C F)

theorem blocks_nodup (n : Nat) (F : LegalField) (x : Position) :
    (blocks C n F x).Nodup := by
  induction n generalizing F x with
  | zero => simp [blocks]
  | succ n ih => exact refine_nodup C F _ (ih (next C F) x)

theorem blocks_lower (n : Nat) (F : LegalField) (x : Position) :
    7^n ≤ (blocks C n F x).length := by
  induction n generalizing F x with
  | zero => simp [blocks]
  | succ n ih =>
    calc
      7^(n+1) = 7*(7^n) := by rw [Nat.pow_succ,Nat.mul_comm]
      _ ≤ 7*(blocks C n (next C F) x).length := Nat.mul_le_mul_left _ (ih _ _)
      _ ≤ (blocks C (n+1) F x).length := refine_lower C F _

theorem blocks_disjoint (n : Nat) (F : LegalField) (x y p : Position)
    (hx : p ∈ blocks C n F x) (hy : p ∈ blocks C n F y) : x = y := by
  induction n generalizing F x y p with
  | zero => simp only [blocks,List.mem_singleton] at hx hy; exact hx.symm.trans hy
  | succ n ih =>
    obtain ⟨a,ha,hpa⟩ := (mem_refine C F _ p).mp hx
    obtain ⟨b,hb,hpb⟩ := (mem_refine C F _ p).mp hy
    have he := cells_disjoint C F a b p hpa hpb
    subst b
    exact ih (next C F) x y a ha hb

theorem blocks_cover (n : Nat) (F : LegalField) (p : Position) :
    ∃ x, p ∈ blocks C n F x := by
  induction n generalizing F p with
  | zero => exact ⟨p,by simp [blocks]⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := cells_cover C F p
    obtain ⟨x,hx⟩ := ih (next C F) a
    exact ⟨x,(mem_refine C F _ p).mpr ⟨a,hx,ha⟩⟩

theorem boundaryEdges_bound (n : Nat) (F : LegalField) (x : Position) :
    (boundaryEdges C n F x).length ≤ 6*6^n := by
  induction n generalizing F x with
  | zero => simp [boundaryEdges]
  | succ n ih =>
    have he := FinitePartitionRefinement.expand_edges_length_le (expand C F)
      (boundaryEdges C n (next C F) x) (fun e _ => expand_bound C F e)
    calc
      _ ≤ 6*(boundaryEdges C n (next C F) x).length := he
      _ ≤ 6*(6*6^n) := Nat.mul_le_mul_left _ (ih _ _)
      _ = 6*6^(n+1) := by rw [Nat.pow_succ]; ac_rfl

theorem boundaryEdges_cover (n : Nat) (F : LegalField) (x : Position)
    (e : NativeBoundaryRefinement.Edge) (he : Exposed (blocks C n F x) e) :
    e ∈ boundaryEdges C n F x := by
  induction n generalizing F x e with
  | zero =>
    have hx : e.1 = x := List.mem_singleton.mp he.1
    exact List.mem_map.mpr ⟨e.2,List.mem_finRange _,Prod.ext hx.symm rfl⟩
  | succ n ih =>
    obtain ⟨b,hb,heb⟩ := (exposed_refine C F _ e).mp he
    exact List.mem_flatMap.mpr ⟨b,ih _ _ b hb,heb⟩

/-- Literal fine periods act as literal translations on every iterated
parent partition, without assuming a hierarchy-equivariance property. -/
theorem blocks_period (n : Nat) (F : LegalField) (v : Position)
    (hv : FieldPeriod F.val v) :
    ∃ w : Position, ∀ x, blocks C n F (addPos w x) =
      (blocks C n F x).map (addPos v) := by
  induction n generalizing F v with
  | zero => exact ⟨v,fun x => rfl⟩
  | succ n ih =>
    obtain ⟨w,hw⟩ := ih (next C F) (shift C F v hv) (shift_period C F v hv)
    refine ⟨w,?_⟩
    intro x
    change refine C F (blocks C n (next C F) (addPos w x)) = _
    rw [hw x,refine_period C F v hv]
    rfl

end SpectreFinite.HexSearch.NativeHierarchy
