module

public import SparseMonotiles.ContactPhysicalProfiles
public import SparseMonotiles.ContactKeyCodeCertificates7
public import SparseMonotiles.AtlasCertificates7
public import SparseMonotiles.AtlasBindings7
public import SparseMonotiles.ProfileCertificates7

@[expose] public section

/-!
Concrete adapters for the frozen literal T7 body and indexed profiles.
All static code, regularity, collar, cell-core, and key-asymmetry hypotheses are
kernel checked by imported certificates. Registration and physical whole-key
matches remain explicit; this module does not infer them from arbitrary contact.
-/
namespace SparseMonotiles
open Contact

attribute [local irreducible] IndexedGeometry.generatedCandidates

/-- A registered actual key-solid match recovers the full indexed key match. -/
theorem T7_indexed_solid_match {p : Pose 7} {i j : Fin 896}
    {root source : BoxKey 7}
    (hr : root ∈ IndexedData7.geometry.profile i)
    (hs : source ∈ IndexedData7.geometry.profile j)
    (disjoint : Disjoint (interior T7) (interior (p.euclidean '' T7)))
    (heq : keySolid (root.toKeyData IndexedData7.geometry.denominator) =
      p.euclidean '' keySolid (source.toKeyData IndexedData7.geometry.denominator)) :
    Shared p (IndexedData7.geometry.facet i) (IndexedData7.geometry.facet j) ∧
      root = p.boxKey IndexedData7.geometry.denominator source := by
  have shared := T7_shared_of_physical_matched_keySolids (by decide :
      0 < IndexedData7.geometry.denominator)
    (IndexedData7.owned_checked i) (IndexedData7.owned_checked j) disjoint
    ((atlas7_checked i).2.1 root hr) ((atlas7_checked j).2.1 source hs) heq
  exact ⟨shared, IndexedData7.coordinateCode.eq_boxKey_of_shared_solid_image shared
    ((keyCode7_checked i root hr).1) ((keyCode7_checked j source hs).1)
    ((keyCode7_checked i root hr).2) ((keyCode7_checked j source hs).2) heq⟩

/-- One actual matched pair from the frozen literal key list suffices to place
a registered disjoint pose in the executable all-key-pair candidate universe. -/
theorem T7_keySolidMatch_mem_generatedCandidates {p : Pose 7}
    {root source : KeyData 7} (hr : root ∈ keys7) (hs : source ∈ keys7)
    (disjoint : Disjoint (interior T7) (interior (p.euclidean '' T7)))
    (heq : keySolid root = p.euclidean '' keySolid source) :
    p ∈ IndexedData7.geometry.generatedCandidates := by
  rcases Canonical.everyKey7_in_atlas root hr with ⟨i, r, hri, hre⟩
  rcases Canonical.everyKey7_in_atlas source hs with ⟨j, s, hsj, hse⟩
  rw [← hre, ← hse] at heq
  have hm := T7_indexed_solid_match hri hsj disjoint heq
  exact IndexedGeometry.mem_generatedCandidates_of_match (by decide) hri hsj
    (((profile7_checked j).2 s hsj).2.1) hm.1 hm.2

/-- The remaining physical profile input is stated using actual solid equality.
All finite/static hypotheses of the generic contact adapter are discharged. -/
theorem T7_legalContact_of_physical_solid_profiles {p : Pose 7}
    (disjoint : Disjoint (interior T7) (interior (p.euclidean '' T7)))
    (contact : ∃ i j, ∃ root ∈ IndexedData7.geometry.profile i,
      ∃ source ∈ IndexedData7.geometry.profile j,
      keySolid (root.toKeyData IndexedData7.geometry.denominator) =
        p.euclidean '' keySolid (source.toKeyData IndexedData7.geometry.denominator))
    (hmatch : ∀ i j, Shared p (IndexedData7.geometry.facet i) (IndexedData7.geometry.facet j) →
      IndexedData7.geometry.SolidProfilesMatch p i j) :
    IndexedData7.geometry.LegalContact p := by
  apply IndexedGeometry.legalContact_of_physical_solid_matches keyCode7_codedBy
    keyCode7_regular (fun c hc => T7_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    IndexedData7.facet_owned (fun i k hk => (atlas7_checked i).2.1 k hk)
    disjoint contact hmatch

#print axioms T7_indexed_solid_match
#print axioms T7_keySolidMatch_mem_generatedCandidates
#print axioms T7_legalContact_of_physical_solid_profiles
end SparseMonotiles
