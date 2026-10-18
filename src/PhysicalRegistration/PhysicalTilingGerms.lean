module

public import PhysicalRegistration.PackingLocalFiniteness
public import PhysicalRegistration.NativeBoundary

@[expose] public section

/-!
# Finite incident germs of actual physical tilings

A physical tiling has exactly two hypotheses: pairwise disjoint actual
interiors and coverage by unrestricted isometric copies of the native body.
Finite incidence and an open neighborhood covered by the incident tiles are
consequences of the proved packing local finiteness and closedness. At an
actual placed key-graph point, every incident tile has actual boundary there.
No tangent cone, local fan, angular conservation, or local-finiteness field
is assumed.
-/

namespace PhysicalRegistration
open scoped InnerProductSpace Topology
open Set
noncomputable section

/-- Short positive inward rays in a genuine local graph chart approach the
base point through the actual interior. No sign condition on the slope is
needed for this normal-ray argument. -/
theorem LocalLipschitzGraphAt.mem_closure_interior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} {x : E} {L : ℝ} (G : LocalLipschitzGraphAt S x L) :
    x ∈ closure (interior S) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hr := G.radius_pos
  let t := min ε G.radius / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htε : t < ε := by dsimp [t]; have := min_le_left ε G.radius; linarith
  have htr : t < G.radius := by
    dsimp [t]
    have := min_le_right ε G.radius
    linarith
  refine ⟨x + t • G.inward, ?_, ?_⟩
  · simpa using G.interior_above 0 t (by simp)
      (by simpa using G.radius_pos) (by rwa [abs_of_pos ht])
      (by simpa [G.height_zero] using ht)
  · simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs, G.inward_unit,
      abs_of_pos ht, norm_sub_rev] using htε

/-- A locally finite closed family has an actual open neighborhood meeting
only members incident at its center. The proof starts with the finite local
family, then intersects the complements of its nonincident members. -/
theorem exists_open_incident_neighborhood
    {X ι : Type*} [TopologicalSpace X] (S : ι → Set X)
    (hlocal : LocallyFinite S) (hclosed : ∀ i, IsClosed (S i)) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ i, x ∉ S i → Disjoint (S i) U := by
  obtain ⟨V, hV, hfinite⟩ := hlocal x
  obtain ⟨W, hWV, hW, hxW⟩ := mem_nhds_iff.mp hV
  let B : Set ι := {i | (S i ∩ V).Nonempty ∧ x ∉ S i}
  have hB : B.Finite := hfinite.subset (fun _ hi => hi.1)
  let U := W ∩ ⋂ i ∈ B, (S i)ᶜ
  refine ⟨U, hW.inter (hB.isOpen_biInter (fun i _ => (hclosed i).isOpen_compl)),
    ⟨hxW, mem_iInter₂.mpr (fun i hi => hi.2)⟩, ?_⟩
  intro i hxi
  apply Set.disjoint_left.mpr
  intro y hy hyU
  have hiB : i ∈ B := ⟨⟨y, hy, hWV hyU.1⟩, hxi⟩
  exact (mem_iInter₂.mp hyU.2 i hiB) hy

namespace NativeChair

/-- A physical tiling by arbitrary isometric placements of the literal native
body. These two fields are the entire tiling hypothesis. -/
structure PhysicalTiling {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m) : Prop where
  interiors_disjoint : Pairwise fun i j =>
    Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j)))
  covers : ∀ x : Space m, ∃ i, x ∈ placedBody a (f i)

/-- The actual incident index set, without a finiteness assumption. -/
def incidentTiles {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m) (x : Space m) : Set ι :=
  {i | x ∈ placedBody a (f i)}

/-- Every placed body is closed, by the proved compactness of the literal body. -/
theorem placedBody_isClosed {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (f : Space m ≃ᵢ Space m) :
    IsClosed (placedBody a f) :=
  ((body_isCompact a).image f.continuous).isClosed

/-- Singleton compact incidence makes every actual incident index set finite. -/
theorem finite_incidentTiles {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (x : Space m) : (incidentTiles a f x).Finite := by
  have hfinite := finite_placedBody_inter_compact a f hdisjoint {x} isCompact_singleton
  exact hfinite.subset (fun i hi => ⟨x, hi, mem_singleton x⟩)

/-- Local finiteness and closedness exclude every nonincident tile on one
actual open neighborhood. Coverage is not needed for this packing statement. -/
theorem placedBody_open_incident_neighborhood {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (x : Space m) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      ∀ i, i ∉ incidentTiles a f x → Disjoint (placedBody a (f i)) U :=
  exists_open_incident_neighborhood (fun i => placedBody a (f i))
    (placedBody_locallyFinite a f hdisjoint) (fun i => placedBody_isClosed a (f i)) x

/-- The finite incident family covers a genuine open neighborhood in a
physical tiling and inherits pairwise disjoint actual interiors. -/
theorem PhysicalTiling.finite_incident_germ {m J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
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
theorem placedKeyGraph_subset_frontier_placedBody {m J : ℕ} [NeZero m]
    (hm : 2 ≤ m) (a : Coefficients m J) (f : Space m ≃ᵢ Space m)
    (u : Site m) : placedKeyGraph a f u ⊆ frontier (placedBody a f) := by
  change f.toHomeomorph '' keyGraph a u ⊆ frontier (f.toHomeomorph '' body a)
  rw [← f.toHomeomorph.image_frontier]
  exact image_mono (keyGraph_subset_frontier_body hm a u)

/-- Every actual placed key-graph point is approached by actual interior
points of its own tile, using the proved local inward chart. -/
theorem placedKeyGraph_subset_closure_interior_placedBody
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) :
    placedKeyGraph a f u ⊆ closure (interior (placedBody a f)) := by
  intro x hx
  exact (placed_key_local_graph hm a f u x hx).mem_closure_interior

/-- A root key-graph point is in no tile interior in any actual
interior-disjoint packing. The root case uses its proved frontier; the other
cases use closure of its actual interior and openness of the other interior. -/
theorem placedKeyGraph_notMem_any_interior {m J : ℕ} [NeZero m] {ι : Type*}
    (hm : 2 ≤ m) (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (root : ι) (u : Site m) (x : Space m)
    (hx : x ∈ placedKeyGraph a (f root) u) (i : ι) :
    x ∉ interior (placedBody a (f i)) := by
  by_cases hi : root = i
  · subst i
    exact (placedKeyGraph_subset_frontier_placedBody hm a (f root) u hx).2
  · exact Set.disjoint_left.mp ((hdisjoint hi).closure_left isOpen_interior)
      (placedKeyGraph_subset_closure_interior_placedBody hm a (f root) u hx)

/-- Every incident tile has actual boundary at a root placed key-graph point.
Neither coverage nor any assumed boundary fan is needed. -/
theorem placedKeyGraph_incident_mem_frontier {m J : ℕ} [NeZero m] {ι : Type*}
    (hm : 2 ≤ m) (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (root : ι) (u : Site m) (x : Space m)
    (hx : x ∈ placedKeyGraph a (f root) u) (i : ι)
    (hi : i ∈ incidentTiles a f x) : x ∈ frontier (placedBody a (f i)) :=
  ⟨subset_closure hi, placedKeyGraph_notMem_any_interior hm a f hdisjoint root u x hx i⟩

/-- At a root key-graph point a physical tiling supplies a finite actual
boundary-incident cover of an open neighborhood, with inherited disjoint
interiors. This is a concrete prerequisite for any later angle-conservation
argument, not an assumption or conclusion of such conservation. -/
theorem PhysicalTiling.finite_key_boundary_germ {m J : ℕ} [NeZero m] {ι : Type*}
    (hm : 2 ≤ m) {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site m) (x : Space m)
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

end NativeChair
end
end PhysicalRegistration
