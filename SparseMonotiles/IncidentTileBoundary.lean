module

public import SparseMonotiles.IncidentTileLocalization
public import SparseMonotiles.BoundaryInventory

@[expose] public section

/-!
# Every incident tile is a boundary tile at a regular root boundary point

Only local regularity of the specified root tile is needed. No global
regular-closed-body theorem or prior sector inventory is assumed.
-/
namespace SparseMonotiles
open Set

/-- A proved local model transfers adherence to its own interior. -/
theorem LocalSetEq.mem_closure_interior_of_model
    {X : Type*} [TopologicalSpace X] {p : X} {A M : Set X}
    (h : LocalSetEq p A M) (hp : p ∈ A)
    (hregular : M ⊆ _root_.closure (_root_.interior M)) :
    p ∈ _root_.closure (_root_.interior A) :=
  h.interior.closure.mem_iff.mpr (hregular (h.mem_iff.mp hp))

/-- Disjoint interiors prevent an interior neighbor at any adherent root
interior point. This is a purely topological fact. -/
theorem not_mem_interior_of_disjoint_root
    {X : Type*} [TopologicalSpace X] {A B : Set X} {p : X}
    (hdis : Disjoint (interior A) (interior B))
    (hp : p ∈ closure (interior B)) : p ∉ interior A := by
  intro hpA
  obtain ⟨x,hxA,hxB⟩ := mem_closure_iff.mp hp (interior A) isOpen_interior hpA
  exact Set.disjoint_left.mp hdis hxA hxB

/-- Every member of the full incident family is a boundary tile, provided
the chosen root is a boundary tile locally adherent to its interior. -/
theorem IsTiling.incident_mem_frontier_of_regular_root {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hT : IsCompact T)
    {root : Set (Point d)} (hroot : root ∈ tiles) {p : Point d}
    (hpBoundary : p ∈ frontier root) (hpRegular : p ∈ closure (interior root)) :
    ∀ A : incidentTiles tiles p, p ∈ frontier (A : Set (Point d)) := by
  intro A
  by_cases hEq : (A : Set (Point d)) = root
  · simpa only [hEq] using hpBoundary
  · have hno : p ∉ interior (A : Set (Point d)) :=
      not_mem_interior_of_disjoint_root
        (ht.2.2 A A.property.1 root hroot hEq) hpRegular
    rw [frontier, (ht.tile_isClosed hT A.property.1).closure_eq]
    exact ⟨A.property.2,hno⟩

#print axioms LocalSetEq.mem_closure_interior_of_model
#print axioms not_mem_interior_of_disjoint_root
#print axioms IsTiling.incident_mem_frontier_of_regular_root
end SparseMonotiles
