module

public import SpectreFinite.ParentBoundaryGlobal
public import SpectreFinite.NativeCoarsePeriods
public import SpectreFinite.NativeBoundaryRefinement
public import SpectreFinite.FinitePartitionRefinement

@[expose] public section


/-! A repeatable actual coarsening operation, with its one remaining finite
search-completeness input displayed explicitly. Every geometry, chart,
partition, boundary expansion and period transport property is proved. -/
namespace SpectreFinite.HexSearch.NativeHierarchy
open ParentOwnership ParentBoundary NativeCoarse

abbrev LegalField := { f : Position → State // GloballyLegal f }

def ParentOccurrenceTheorem : Prop :=
  ∀ f : Position → State, GloballyLegal f →
    OccurrenceComplete f (hexRegion 5) certifiedParentFamily

variable (C : ParentOccurrenceTheorem)
include C

theorem recognition (F : LegalField) : Recognition F.val :=
  recognition_of_certifiedParentFamily C F.val F.property

theorem boundary (F : LegalField) :
    ∀ a : Anchor F.val, FramedRootStructure (normalizedAt F.val a.val) :=
  normalized_frames_of_certifiedParentFamily C F.val F.property

noncomputable def next (F : LegalField) : LegalField :=
  ⟨coarseField F.val (recognition C F) (boundary C F),
    coarseField_globallyLegal F.val (recognition C F) (boundary C F)⟩

noncomputable def cells (F : LegalField) (x : Position) : List Position :=
  coordinateFiber F.val (recognition C F) (boundary C F) x

noncomputable def refine (F : LegalField) (A : List Position) : List Position :=
  A.flatMap (cells C F)

noncomputable def expand (F : LegalField) (e : NativeBoundaryRefinement.Edge) :
    List NativeBoundaryRefinement.Edge :=
  NativeBoundaryRefinement.expansion F.val (recognition C F) (boundary C F) e

theorem cells_nodup (F : LegalField) (x : Position) : (cells C F x).Nodup :=
  fiber_nodup F.val (recognition C F) _

theorem cells_bounds (F : LegalField) (x : Position) :
    7 ≤ (cells C F x).length ∧ (cells C F x).length ≤ 8 :=
  fiber_length_bounds F.val (recognition C F) _

theorem cells_disjoint (F : LegalField) (x y p : Position)
    (hx : p ∈ cells C F x) (hy : p ∈ cells C F y) : x = y :=
  coordinateFiber_disjoint F.val (recognition C F) (boundary C F) x y p hx hy

theorem cells_cover (F : LegalField) (p : Position) : ∃ x, p ∈ cells C F x :=
  coordinateFiber_cover F.val (recognition C F) (boundary C F) p

theorem mem_refine (F : LegalField) (A : List Position) (p : Position) :
    p ∈ refine C F A ↔ ∃ x ∈ A, p ∈ cells C F x := List.mem_flatMap

theorem refine_nodup (F : LegalField) (A : List Position) (ha : A.Nodup) :
    (refine C F A).Nodup := by
  apply FinitePartitionRefinement.refine_nodup (cells C F) A ha (fun x _ => cells_nodup C F x)
  intro x _ y _ hxy p hx hy
  exact hxy (cells_disjoint C F x y p hx hy)

theorem refine_lower (F : LegalField) (A : List Position) :
    7*A.length ≤ (refine C F A).length :=
  FinitePartitionRefinement.refine_length_lower (cells C F) A 7
    (fun x _ => (cells_bounds C F x).1)

theorem expand_bound (F : LegalField) (e : NativeBoundaryRefinement.Edge) :
    (expand C F e).length ≤ 6 :=
  NativeBoundaryRefinement.expansion_length_le F.val (recognition C F) (boundary C F) e

theorem exposed_refine (F : LegalField) (A : List Position)
    (b : NativeBoundaryRefinement.Edge) :
    NativeBoundaryRefinement.Exposed (refine C F A) b ↔
      ∃ e, NativeBoundaryRefinement.Exposed A e ∧ b ∈ expand C F e :=
  NativeBoundaryRefinement.exposed_refine_iff F.val (recognition C F) (boundary C F) A b

noncomputable def shift (F : LegalField) (v : Position) (hv : FieldPeriod F.val v) : Position :=
  coarsePeriod F.val (recognition C F) (boundary C F) v hv

theorem shift_period (F : LegalField) (v : Position) (hv : FieldPeriod F.val v) :
    FieldPeriod (next C F).val (shift C F v hv) :=
  coarsePeriod_spec F.val (recognition C F) (boundary C F) v hv

theorem cells_period (F : LegalField) (v : Position) (hv : FieldPeriod F.val v) (x : Position) :
    cells C F (addPos (shift C F v hv) x) = (cells C F x).map (addPos v) :=
  coordinateFiber_period F.val (recognition C F) (boundary C F) v hv x

theorem refine_period (F : LegalField) (v : Position) (hv : FieldPeriod F.val v)
    (A : List Position) :
    refine C F (A.map (addPos (shift C F v hv))) = (refine C F A).map (addPos v) := by
  induction A with
  | nil => rfl
  | cons a as ih =>
    change cells C F (addPos (shift C F v hv) a) ++
      refine C F (as.map (addPos (shift C F v hv))) = _
    rw [cells_period,ih]
    exact List.map_append.symm

end SpectreFinite.HexSearch.NativeHierarchy
