module
public import SparseMonotiles.CarrierExistenceProfileRules
public import SparseMonotiles.CarrierExistenceSupportCovariance
public import SparseMonotiles.AtlasBindings7
public import SparseMonotiles.AtlasCertificates7
public import SparseMonotiles.AtlasReverse7
public import Acceptance214Certificate
@[expose] public section

/-! Exact compact T7 profile complementarity from finite key-mate laws.
No registered-world existence, forward rules, or physical tiling is assumed.
The concrete unconditional instance covers only original catalog entry 214. -/
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
open Contact Set Canonical
set_option maxRecDepth 100000

private theorem apex_mem_coordinateSupport (k : KeyData 7) :
    rationalPoint k.apex ∈ keyCoordinateSupport k := by
  intro i
  exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem exposed_support_facet (k : KeyData 7) (hk : k ∈ keys7) :
    ∃ f : Facet 7, IsChairCell f.cell ∧ ¬ IsChairCell f.neighbor ∧
      keyCoordinateSupport k ⊆ gridFacetCollar f.gridFacet := by
  obtain ⟨i, b, hb, he⟩ := everyKey7_in_atlas k hk
  refine ⟨IndexedData7.geometry.facet i, IndexedData7.owned_checked i,
    (atlas7_checked i).1, ?_⟩
  rw [← he]
  exact BoxKey.coordinateSupport_subset_collar (by decide) ((atlas7_checked i).2.1 b hb)

noncomputable def facets : KeyFacetAssignment keys7 where
  facet k hk := (exposed_support_facet k hk).choose
  owner k hk := (exposed_support_facet k hk).choose_spec.1
  exposed k hk := (exposed_support_facet k hk).choose_spec.2.1
  support k hk := (exposed_support_facet k hk).choose_spec.2.2

theorem assigned_facet_eq_indexed (A : KeyFacetAssignment keys7)
    (k : KeyData 7) (hk : k ∈ keys7) (i : Fin 896) (root : BoxKey 7)
    (hr : root ∈ IndexedData7.geometry.profile i) (he : root.toKeyData 188160 = k) :
    A.facet k hk = IndexedData7.geometry.facet i := by
  have hs : keyCoordinateSupport k ⊆
      gridFacetCollar (IndexedData7.geometry.facet i).gridFacet := by
    rw [← he]
    exact BoxKey.coordinateSupport_subset_collar (by decide) ((atlas7_checked i).2.1 root hr)
  have hp := apex_mem_coordinateSupport k
  exact Facet.eq_of_gridFacet_eq (A.exposed k hk) (IndexedData7.owned_checked i)
    (GridFacet.eq_of_mem_collars (A.support k hk hp) (hs hp))

/-- Minimal indexed input: occupied exterior neighbors have exact source keys.
Carrier disjointness and a positive contact witness are not assumed here. -/
def IndexedKeyMateLaw (L : Set (Pose 7)) : Prop :=
  ∀ p ∈ L, ∀ (i : Fin 896) (root : BoxKey 7),
    root ∈ IndexedData7.geometry.profile i →
    (IndexedData7.geometry.facet i).neighbor ∈ IndexedData7.geometry.cells.image p.cell →
    ∃ j, ∃ source ∈ IndexedData7.geometry.profile j,
      root = p.boxKey IndexedData7.geometry.denominator source

/-- Full solids, closed coordinate supports and opposite coefficients follow
from exact finite BoxKey matches and the already-proved reverse key binding. -/
theorem complementaryProfiles_of_indexed_key_mates
    (L : Set (Pose 7)) (hmates : IndexedKeyMateLaw L) (A : KeyFacetAssignment keys7) :
    ComplementaryProfiles A L := by
  intro p hp k hk hocc
  obtain ⟨i, root, hr, he⟩ := everyKey7_in_atlas k hk
  have hf := assigned_facet_eq_indexed A k hk i root hr he
  have hocc' : Occupies p (IndexedData7.geometry.facet i).neighbor := by
    simpa only [hf] using hocc
  have occupied : (IndexedData7.geometry.facet i).neighbor ∈
      IndexedData7.geometry.cells.image p.cell := by
    refine Finset.mem_image.mpr ⟨p.inverseCell (IndexedData7.geometry.facet i).neighbor, ?_,
      p.cell_inverseCell _⟩
    rw [IndexedData7.cells_eq, mem_chairCells]
    exact hocc'
  obtain ⟨j, source, hs, hm⟩ := hmates p hp i root hr occupied
  change root = p.boxKey 188160 source at hm
  refine ⟨source.toKeyData 188160, everyAtlas7Key_isLiteral j source hs, ?_, ?_, ?_⟩
  · simpa only [he] using p.boxKey_match_solid (by decide : (188160 : ℤ) ≠ 0) hm
  · simpa only [he] using p.boxKey_match_support (by decide : (188160 : ℤ) ≠ 0) hm
  · rw [← he]
    change source.bump = !root.bump
    rw [p.boxKey_match_coefficient 188160 hm]
    simp

/-- Stronger all-facet acceptance certificates are one way to provide the
minimal mate law. This implication is independent of candidate exhaustion. -/
theorem indexed_key_mates_of_fast_acceptance (L : Set (Pose 7))
    (hcert : ∀ p ∈ L, ∃ cert : MateCertificate 896,
      IndexedData7.geometry.FastAcceptanceValid p cert) : IndexedKeyMateLaw L := by
  intro p hp i root hr occupied
  obtain ⟨cert, hchecked⟩ := hcert p hp
  have ha := IndexedGeometry.fastAcceptance_valid IndexedData7.cells_eq hchecked
  obtain ⟨j, source, hs, _, hm⟩ :=
    Acceptance214Pilot7.key_mate_of_acceptance ha occupied hr
  exact ⟨j, source, hs, hm⟩

theorem complementaryProfiles_of_fast_acceptance (L : Set (Pose 7))
    (hcert : ∀ p ∈ L, ∃ cert : MateCertificate 896,
      IndexedData7.geometry.FastAcceptanceValid p cert) (A : KeyFacetAssignment keys7) :
    ComplementaryProfiles A L :=
  complementaryProfiles_of_indexed_key_mates L (indexed_key_mates_of_fast_acceptance L hcert) A

/-- The exact original catalog still needs its own finite acceptance package. -/
theorem complementaryProfiles_M7_of_fast_acceptance
    (hcert : ∀ p ∈ M7, ∃ cert : MateCertificate 896,
      IndexedData7.geometry.FastAcceptanceValid p cert) (A : KeyFacetAssignment keys7) :
    ComplementaryProfiles A M7 :=
  complementaryProfiles_of_fast_acceptance M7 hcert A

/-- Unconditional full literal profile complementarity for the one checked
original catalog pose. This is not complementarity for all of M7. -/
theorem complementaryProfiles_entry214 (A : KeyFacetAssignment keys7) :
    ComplementaryProfiles A ({Acceptance214Pilot7.pose} : Set (Pose 7)) := by
  apply complementaryProfiles_of_fast_acceptance _ _ A
  intro p hp
  have he : p = Acceptance214Pilot7.pose := Set.mem_singleton_iff.mp hp
  subst p
  exact ⟨Acceptance214Pilot7.certificate, Acceptance214Pilot7.fast_acceptance⟩

theorem concrete_entry214_profiles :
    ComplementaryProfiles facets ({Acceptance214Pilot7.pose} : Set (Pose 7)) :=
  complementaryProfiles_entry214 facets

#print axioms facets
#print axioms assigned_facet_eq_indexed
#print axioms complementaryProfiles_of_indexed_key_mates
#print axioms complementaryProfiles_M7_of_fast_acceptance
#print axioms complementaryProfiles_entry214
#print axioms concrete_entry214_profiles
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7
