module

public import PhysicalRegistration.PhysicalTilingGerms
public import ProductClosure.PackingLocalFiniteness
public import ProductClosure.NativeBoundary

@[expose] public section

namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
open scoped InnerProductSpace Topology
noncomputable section
variable {m : ℕ} {C : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell C)]

/-- A physical tiling by arbitrary isometric placements of the literal native
body. These two fields are the entire tiling hypothesis. -/
structure PhysicalTiling {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m) : Prop where
  interiors_disjoint : Pairwise fun i j =>
    Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j)))
  covers : ∀ x : Space m, ∃ i, x ∈ placedBody a (f i)

/-- The actual incident index set, without a finiteness assumption. -/
def incidentTiles {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m) (x : Space m) : Set ι :=
  {i | x ∈ placedBody a (f i)}

/-- Every placed body is closed, by the proved compactness of the literal body. -/
theorem placedBody_isClosed {J : ℕ} [NeZero m]
    (a : Coefficients C J) (f : Space m ≃ᵢ Space m) :
    IsClosed (placedBody a f) :=
  ((body_isCompact a).image f.continuous).isClosed

/-- Singleton compact incidence makes every actual incident index set finite. -/
theorem finite_incidentTiles {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (x : Space m) : (incidentTiles a f x).Finite := by
  have hfinite := finite_placedBody_inter_compact a f hdisjoint {x} isCompact_singleton
  exact hfinite.subset (fun i hi => ⟨x, hi, mem_singleton x⟩)

/-- Local finiteness and closedness exclude every nonincident tile on one
actual open neighborhood. Coverage is not needed for this packing statement. -/
theorem placedBody_open_incident_neighborhood {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (x : Space m) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      ∀ i, i ∉ incidentTiles a f x → Disjoint (placedBody a (f i)) U :=
  exists_open_incident_neighborhood (fun i => placedBody a (f i))
    (placedBody_locallyFinite a f hdisjoint) (fun i => placedBody_isClosed a (f i)) x

/-- The finite incident family covers a genuine open neighborhood in a
physical tiling and inherits pairwise disjoint actual interiors. -/
theorem PhysicalTiling.finite_incident_germ {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients C J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (x : Space m) :
    (incidentTiles a f x).Finite ∧
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      (∀ i, i ∉ incidentTiles a f x → Disjoint (placedBody a (f i)) U) ∧
      (∀ y ∈ U, ∃ i ∈ incidentTiles a f x, y ∈ placedBody a (f i)) ∧
      Pairwise (fun (i j : incidentTiles a f x) =>
        Disjoint (interior (placedBody a (f i.val)))
          (interior (placedBody a (f j.val)))) := by
  obtain ⟨U, hU, hxU, havoid⟩ :=
    placedBody_open_incident_neighborhood a f T.interiors_disjoint x
  refine ⟨finite_incidentTiles a f T.interiors_disjoint x, U, hU, hxU,
    havoid, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi⟩ := T.covers y
    refine ⟨i, ?_, hi⟩
    by_contra hxi
    exact Set.disjoint_left.mp (havoid i hxi) hi hy
  · intro i j hij
    exact T.interiors_disjoint (fun h => hij (Subtype.ext h))

/-- Placed key graphs lie on the actual placed body's frontier. -/
theorem placedKeyGraph_subset_frontier_placedBody {J : ℕ} [NeZero m]
    (hm : 2 ≤ m) (a : Coefficients C J) (f : Space m ≃ᵢ Space m)
    (u : Site C) : placedKeyGraph a f u ⊆ frontier (placedBody a f) := by
  change f.toHomeomorph '' keyGraph a u ⊆ frontier (f.toHomeomorph '' body a)
  rw [← f.toHomeomorph.image_frontier]
  exact image_mono (keyGraph_subset_frontier_body hm a u)

/-- Every actual placed key-graph point is approached by actual interior
points of its own tile, using the proved local inward chart. -/
theorem placedKeyGraph_subset_closure_interior_placedBody
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients C J)
    (f : Space m ≃ᵢ Space m) (u : Site C) :
    placedKeyGraph a f u ⊆ closure (interior (placedBody a f)) := by
  intro x hx
  exact (placed_key_local_graph hm a f u x hx).mem_closure_interior

/-- A root key-graph point is in no tile interior in any actual
interior-disjoint packing. The root case uses its proved frontier; the other
cases use closure of its actual interior and openness of the other interior. -/
theorem placedKeyGraph_notMem_any_interior {J : ℕ} [NeZero m] {ι : Type*}
    (hm : 2 ≤ m) (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (root : ι) (u : Site C) (x : Space m)
    (hx : x ∈ placedKeyGraph a (f root) u) (i : ι) :
    x ∉ interior (placedBody a (f i)) := by
  by_cases hi : root = i
  · subst i
    exact (placedKeyGraph_subset_frontier_placedBody hm a (f root) u hx).2
  · exact Set.disjoint_left.mp ((hdisjoint hi).closure_left isOpen_interior)
      (placedKeyGraph_subset_closure_interior_placedBody hm a (f root) u hx)

/-- Every incident tile has actual boundary at a root placed key-graph point.
Neither coverage nor any assumed boundary fan is needed. -/
theorem placedKeyGraph_incident_mem_frontier {J : ℕ} [NeZero m] {ι : Type*}
    (hm : 2 ≤ m) (a : Coefficients C J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (root : ι) (u : Site C) (x : Space m)
    (hx : x ∈ placedKeyGraph a (f root) u) (i : ι)
    (hi : i ∈ incidentTiles a f x) : x ∈ frontier (placedBody a (f i)) :=
  ⟨subset_closure hi, placedKeyGraph_notMem_any_interior hm a f hdisjoint root u x hx i⟩

/-- At a root key-graph point a physical tiling supplies a finite actual
boundary-incident cover of an open neighborhood, with inherited disjoint
interiors. This is a concrete prerequisite for any later angle-conservation
argument, not an assumption or conclusion of such conservation. -/
theorem PhysicalTiling.finite_key_boundary_germ {J : ℕ} [NeZero m] {ι : Type*}
    (hm : 2 ≤ m) {a : Coefficients C J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site C) (x : Space m)
    (hx : x ∈ placedKeyGraph a (f root) u) :
    (incidentTiles a f x).Finite ∧
    (∀ i ∈ incidentTiles a f x, x ∈ frontier (placedBody a (f i))) ∧
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      (∀ i, i ∉ incidentTiles a f x → Disjoint (placedBody a (f i)) U) ∧
      (∀ y ∈ U, ∃ i ∈ incidentTiles a f x, y ∈ placedBody a (f i)) ∧
      Pairwise (fun (i j : incidentTiles a f x) =>
        Disjoint (interior (placedBody a (f i.val)))
          (interior (placedBody a (f j.val)))) :=
  ⟨(T.finite_incident_germ x).1,
    fun i hi => placedKeyGraph_incident_mem_frontier hm a f T.interiors_disjoint
      root u x hx i hi, (T.finite_incident_germ x).2⟩

end
end ProductClosure.NativeCompiler
