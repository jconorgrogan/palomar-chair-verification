module

public import SpectreFinite.NativeHierarchyBlocks
public import SpectreFinite.HierarchyPeriodEstimate

@[expose] public section


/-! A complete discrete period obstruction conditional only on the explicit
finite radius-five occurrence theorem. Iterated partitions, global coarse
coordinates, translation covariance, and area/perimeter growth are all
constructed, not assumed. This does not assert existence of a global marked
field or its physical correspondence. -/
namespace SpectreFinite.HexSearch.NativeHierarchy
open ParentOwnership FiniteBoundaryEstimate

variable (C : ParentOccurrenceTheorem)
include C

theorem block_period_intersection (n : Nat) (F : LegalField) (v : Position)
    (hv : FieldPeriod F.val v)
    (hi : ∃ p ∈ blocks C n F (0,0), addPos p v ∈ blocks C n F (0,0)) :
    ∀ p, p ∈ blocks C n F (0,0) ↔ addPos p v ∈ blocks C n F (0,0) := by
  obtain ⟨w,hw⟩ := blocks_period C n F v hv
  have hmap : blocks C n F w = (blocks C n F (0,0)).map (addPos v) := by
    simpa only [addPos,Int.add_zero] using hw (0,0)
  obtain ⟨p,hp,hpv⟩ := hi
  have hcomm : addPos p v = addPos v p := by
    apply Prod.ext <;> simp only [addPos] <;> omega
  have hmem : addPos p v ∈ blocks C n F w := by
    rw [hmap]
    exact List.mem_map.mpr ⟨p,hp,hcomm.symm⟩
  have hwzero := blocks_disjoint C n F w (0,0) (addPos p v) hmem hpv
  subst w
  intro y
  constructor
  · intro hy
    rw [hmap]
    refine List.mem_map.mpr ⟨y,hy,?_⟩
    apply Prod.ext <;> simp only [addPos] <;> omega
  · intro hy
    rw [hmap] at hy
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hy
    have hq := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    have hzy : z = y := by
      apply Prod.ext <;> simp only [addPos] at hq hr ⊢ <;> omega
    exact hzy ▸ hz

/-- No nonzero literal translation preserves a globally matching marked
field, once the displayed finite occurrence theorem is supplied. -/
theorem fieldPeriod_eq_zero (F : LegalField) (v : Position) (hv : FieldPeriod F.val v) :
    v = (0,0) := by
  apply translation_eq_zero_of_block_bounds (fun n => blocks C n F (0,0))
    (fun n => (boundaryEdges C n F (0,0)).map Prod.fst) 6 v
  · intro n; exact blocks_nodup C n F (0,0)
  · intro n; exact blocks_lower C n F (0,0)
  · intro n
    simpa only [List.length_map] using boundaryEdges_bound C n F (0,0)
  · intro n s hs p hp
    obtain ⟨d,hd⟩ := primitiveSteps_directions s hs
    have hp' := (mem_escape (blocks C n F (0,0)) s p).mp hp
    have he : NativeBoundaryRefinement.Exposed (blocks C n F (0,0)) (p,d) := by
      exact ⟨hp'.1,by simpa only [hd] using hp'.2⟩
    exact List.mem_map.mpr ⟨(p,d),boundaryEdges_cover C n F (0,0) (p,d) he,rfl⟩
  · intro n hi
    exact block_period_intersection C n F v hv hi

theorem globallyLegal_period_zero (f : Position → State) (hf : GloballyLegal f)
    (v : Position) (hv : FieldPeriod f v) : v = (0,0) :=
  fieldPeriod_eq_zero C ⟨f,hf⟩ v hv

end SpectreFinite.HexSearch.NativeHierarchy
