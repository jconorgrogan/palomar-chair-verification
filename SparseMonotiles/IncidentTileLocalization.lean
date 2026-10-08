module

public import SparseMonotiles.LocalFiniteness
public import SparseMonotiles.PolyhedralGerms

@[expose] public section

/-!
# Localizing an arbitrary tiling to its incident physical tiles

For a compact body containing a positive-radius ball, every tiling in
`Model.IsTiling` has only finitely many tiles incident to a point. A single
positive-radius neighborhood excludes every other tile. The incident tiles
cover that neighborhood and inherit the disjoint-interior condition.

Any independently proved local models for these incident tiles may then be
substituted simultaneously. The resulting finite family still covers a
neighborhood, with no overlap of ambient interiors there. These statements
make no registration, grid, common-frame, or face-to-face assumption. In
particular, identifying such models with planar sectors is a separate step.
-/

namespace SparseMonotiles

open Set Filter Metric
open scoped Topology

/-- Physical tiles in the collection that contain the specified point. -/
def incidentTiles {X : Type*} (tiles : Set (Set X)) (p : X) : Set (Set X) :=
  {A | A ∈ tiles ∧ p ∈ A}

@[simp] theorem mem_incidentTiles {X : Type*} {tiles : Set (Set X)} {p : X}
    {A : Set X} : A ∈ incidentTiles tiles p ↔ A ∈ tiles ∧ p ∈ A := Iff.rfl

section ClosedLocallyFinite

variable {X : Type*} [TopologicalSpace X] {tiles : Set (Set X)}

/-- Local finiteness is enough to make the set of incident physical tiles finite. -/
theorem finite_incidentTiles_of_locallyFinite
    (hlf : LocallyFinite (fun A : tiles => (A : Set X))) (p : X) :
    (incidentTiles tiles p).Finite := by
  have hfin := (hlf.point_finite p).image Subtype.val
  apply hfin.subset
  rintro A ⟨hA, hpA⟩
  exact ⟨⟨A, hA⟩, hpA, rfl⟩

/-- Closedness makes the incidence relation upper semicontinuous: near `p`,
every tile containing a nearby point already contains `p`. -/
theorem eventually_incidentTiles_subset
    (hlf : LocallyFinite (fun A : tiles => (A : Set X)))
    (hclosed : ∀ A ∈ tiles, IsClosed A) (p : X) :
    ∀ᶠ y in 𝓝 p, incidentTiles tiles y ⊆ incidentTiles tiles p := by
  apply (hlf.eventually_subset (fun A => hclosed A A.property) p).mono
  intro y hy A hA
  exact ⟨hA.1, hy (show (⟨A, hA.1⟩ : tiles) ∈ {B : tiles | y ∈ (B : Set X)}
    from hA.2)⟩

end ClosedLocallyFinite

section MetricClosedLocallyFinite

variable {X : Type*} [PseudoMetricSpace X] {tiles : Set (Set X)}

/-- A common positive-radius ball meets exactly the tiles incident to its center. -/
theorem exists_ball_meets_iff_incident_of_locallyFinite
    (hlf : LocallyFinite (fun A : tiles => (A : Set X)))
    (hclosed : ∀ A ∈ tiles, IsClosed A) (p : X) :
    ∃ ε > 0, ∀ A ∈ tiles, (A ∩ ball p ε).Nonempty ↔ p ∈ A := by
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_incidentTiles_subset hlf hclosed p)
  refine ⟨ε, hε, fun A hA => ?_⟩
  constructor
  · rintro ⟨y, hyA, hyp⟩
    exact (hlocal y hyp ⟨hA, hyA⟩).2
  · intro hpA
    exact ⟨p, hpA, mem_ball_self hε⟩

end MetricClosedLocallyFinite

namespace IsTiling

variable {d : ℕ} {T : Set (Point d)} {tiles : Set (Set (Point d))}

/-- A physical tile is compact because its placement is an arbitrary isometry. -/
theorem tile_isCompact (ht : IsTiling T tiles) (hT : IsCompact T)
    {A : Set (Point d)} (hA : A ∈ tiles) : IsCompact A := by
  obtain ⟨g, rfl⟩ := ht.1 A hA
  exact hT.image g.continuous

/-- Compact physical tiles are closed. -/
theorem tile_isClosed (ht : IsTiling T tiles) (hT : IsCompact T)
    {A : Set (Point d)} (hA : A ∈ tiles) : IsClosed A :=
  (ht.tile_isCompact hT hA).isClosed

/-- Incident tiles exist at every point by the covering axiom. -/
theorem incident_nonempty (ht : IsTiling T tiles) (p : Point d) :
    (incidentTiles tiles p).Nonempty := by
  obtain ⟨A, hA, hpA⟩ := ht.2.1 p
  exact ⟨A, hA, hpA⟩

/-- Finitely many physical tiles contain a point; no frame choices are indices. -/
theorem finite_incident (ht : IsTiling T tiles) (hT : IsCompact T)
    {c : Point d} {r : ℝ} (hr : 0 < r) (hball : ball c r ⊆ T) (p : Point d) :
    (incidentTiles tiles p).Finite :=
  finite_incidentTiles_of_locallyFinite (ht.locallyFinite hT hr hball) p

/-- A positive-radius neighborhood excludes every nonincident physical tile. -/
theorem exists_ball_meets_iff_incident (ht : IsTiling T tiles) (hT : IsCompact T)
    {c : Point d} {r : ℝ} (hr : 0 < r) (hball : ball c r ⊆ T) (p : Point d) :
    ∃ ε > 0, ∀ A ∈ tiles, (A ∩ ball p ε).Nonempty ↔ p ∈ A :=
  exists_ball_meets_iff_incident_of_locallyFinite (ht.locallyFinite hT hr hball)
    (fun _ hA => ht.tile_isClosed hT hA) p

/-- The finite incident family retains the disjoint-interior condition. -/
theorem incident_interiors_pairwise_disjoint (ht : IsTiling T tiles) (p : Point d) :
    Pairwise fun A B : incidentTiles tiles p =>
      Disjoint (interior (A : Set (Point d))) (interior (B : Set (Point d))) := by
  intro A B hAB
  exact ht.2.2 A A.property.1 B B.property.1 (fun h => hAB (Subtype.ext h))

/-- The cover and nonoverlap consequences of the localization radius, stated for
restrictions of physical tiles rather than for chosen placements. -/
theorem exists_ball_incident_partition (ht : IsTiling T tiles) (hT : IsCompact T)
    {c : Point d} {r : ℝ} (hr : 0 < r) (hball : ball c r ⊆ T) (p : Point d) :
    (incidentTiles tiles p).Finite ∧ ∃ ε > 0,
      (∀ A ∈ tiles, (A ∩ ball p ε).Nonempty ↔ p ∈ A) ∧
      (∀ y ∈ ball p ε, ∃ A : incidentTiles tiles p, y ∈ (A : Set (Point d))) ∧
      (Pairwise fun A B : incidentTiles tiles p =>
        Disjoint (interior ((A : Set (Point d)) ∩ ball p ε))
          (interior ((B : Set (Point d)) ∩ ball p ε))) := by
  obtain ⟨ε, hε, hmeet⟩ := ht.exists_ball_meets_iff_incident hT hr hball p
  refine ⟨ht.finite_incident hT hr hball p, ε, hε, hmeet, ?_, ?_⟩
  · intro y hy
    obtain ⟨A, hA, hyA⟩ := ht.2.1 y
    exact ⟨⟨A, hA, (hmeet A hA).mp ⟨y, hyA, hy⟩⟩, hyA⟩
  · intro A B hAB
    exact (ht.incident_interiors_pairwise_disjoint p hAB).mono
      (interior_mono inter_subset_left) (interior_mono inter_subset_left)

/-- The union of the finite incident family has the germ of the entire space. -/
theorem localSetEq_incident_union_univ (ht : IsTiling T tiles) (hT : IsCompact T)
    {c : Point d} {r : ℝ} (hr : 0 < r) (hball : ball c r ⊆ T) (p : Point d) :
    LocalSetEq p (⋃ A : incidentTiles tiles p, (A : Set (Point d))) univ := by
  obtain ⟨_, ε, hε, _, hcover, _⟩ := ht.exists_ball_incident_partition hT hr hball p
  apply LocalSetEq.of_ball hε
  intro y hy
  constructor
  · exact fun _ => mem_univ y
  · intro _
    obtain ⟨A, hyA⟩ := hcover y hy
    exact mem_iUnion.mpr ⟨A, hyA⟩

end IsTiling

section FiniteLocalModels

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

/-- Simultaneous replacement by finitely many proved germs preserves covering
and the absence of overlap of ambient interiors on one neighborhood. -/
theorem eventually_partition_local_models {p : X} {C M : ι → Set X}
    (hcover : ∀ᶠ y in 𝓝 p, ∃ i, y ∈ C i)
    (hdisj : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (hlocal : ∀ i, LocalSetEq p (C i) (M i)) :
    ∀ᶠ y in 𝓝 p, (∃ i, y ∈ M i) ∧
      ∀ i j, i ≠ j → ¬ (y ∈ interior (M i) ∧ y ∈ interior (M j)) := by
  have hmem : ∀ᶠ y in 𝓝 p, ∀ i, y ∈ C i ↔ y ∈ M i :=
    eventually_all.mpr hlocal
  have hint : ∀ᶠ y in 𝓝 p, ∀ i, y ∈ interior (C i) ↔ y ∈ interior (M i) := by
    apply eventually_all.mpr
    intro i
    simpa only [LocalSetEq, closure_compl, compl_compl] using (hlocal i).compl.closure.compl
  filter_upwards [hcover, hmem, hint] with y hy hm hi
  constructor
  · obtain ⟨i, hyi⟩ := hy
    exact ⟨i, (hm i).mp hyi⟩
  · intro i j hij hyij
    exact Set.disjoint_left.mp (hdisj hij) ((hi i).mpr hyij.1) ((hi j).mpr hyij.2)

end FiniteLocalModels

/-- Direct bridge from the exact unmarked tiling axioms to any proved local
models of its incident physical tiles. The finite models cover a common ball,
and distinct model interiors are disjoint inside that ball. -/
theorem IsTiling.exists_ball_local_models_partition {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hT : IsCompact T)
    {c : Point d} {r : ℝ} (hr : 0 < r) (hball : ball c r ⊆ T) (p : Point d)
    (M : incidentTiles tiles p → Set (Point d))
    (hlocal : ∀ A : incidentTiles tiles p, LocalSetEq p (A : Set (Point d)) (M A)) :
    ∃ ε > 0, ∀ y ∈ ball p ε,
      (∃ A, y ∈ M A) ∧
      ∀ A B, A ≠ B → ¬ (y ∈ interior (M A) ∧ y ∈ interior (M B)) := by
  haveI : Finite (incidentTiles tiles p) :=
    finite_coe_iff.mpr (ht.finite_incident hT hr hball p)
  have hcover : ∀ᶠ y in 𝓝 p, ∃ A : incidentTiles tiles p,
      y ∈ (A : Set (Point d)) := by
    apply (ht.localSetEq_incident_union_univ hT hr hball p).mono
    intro y hy
    exact mem_iUnion.mp (hy.mpr (mem_univ y))
  exact Metric.eventually_nhds_iff_ball.mp
    (eventually_partition_local_models hcover
      (ht.incident_interiors_pairwise_disjoint p) hlocal)

#print axioms IsTiling.finite_incident
#print axioms IsTiling.exists_ball_meets_iff_incident
#print axioms IsTiling.exists_ball_incident_partition
#print axioms IsTiling.localSetEq_incident_union_univ
#print axioms IsTiling.exists_ball_local_models_partition

end SparseMonotiles
