module

public import SparseMonotiles.ContactPhysicalProfiles
public import SparseMonotiles.ContactKeyCodeCertificates5
public import SparseMonotiles.AtlasCertificates5
public import SparseMonotiles.AtlasBindings5
public import SparseMonotiles.ProfileCertificates5

@[expose] public section

/-!
Concrete adapters for the frozen literal T5 body and indexed profiles.
All static code, regularity, collar, cell-core, and key-asymmetry hypotheses are
kernel checked by imported certificates. Registration and physical whole-key
matches remain explicit; this module does not infer them from arbitrary contact.
-/
namespace SparseMonotiles
open Contact

attribute [local irreducible] IndexedGeometry.generatedCandidates

/-- A registered actual key-solid match recovers the full indexed key match. -/
theorem T5_indexed_solid_match {p : Pose 5} {i j : Fin 160}
    {root source : BoxKey 5}
    (hr : root ∈ IndexedData5.geometry.profile i)
    (hs : source ∈ IndexedData5.geometry.profile j)
    (disjoint : Disjoint (interior T5) (interior (p.euclidean '' T5)))
    (heq : keySolid (root.toKeyData IndexedData5.geometry.denominator) =
      p.euclidean '' keySolid (source.toKeyData IndexedData5.geometry.denominator)) :
    Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j) ∧
      root = p.boxKey IndexedData5.geometry.denominator source := by
  have shared := T5_shared_of_physical_matched_keySolids (by decide :
      0 < IndexedData5.geometry.denominator)
    (IndexedData5.owned_checked i) (IndexedData5.owned_checked j) disjoint
    ((atlas5_checked i).2.1 root hr) ((atlas5_checked j).2.1 source hs) heq
  exact ⟨shared, IndexedData5.coordinateCode.eq_boxKey_of_shared_solid_image shared
    ((keyCode5_checked i root hr).1) ((keyCode5_checked j source hs).1)
    ((keyCode5_checked i root hr).2) ((keyCode5_checked j source hs).2) heq⟩

/-- One actual matched pair from the frozen literal key list suffices to place
a registered disjoint pose in the executable all-key-pair candidate universe. -/
theorem T5_keySolidMatch_mem_generatedCandidates {p : Pose 5}
    {root source : KeyData 5} (hr : root ∈ keys5) (hs : source ∈ keys5)
    (disjoint : Disjoint (interior T5) (interior (p.euclidean '' T5)))
    (heq : keySolid root = p.euclidean '' keySolid source) :
    p ∈ IndexedData5.geometry.generatedCandidates := by
  rcases Canonical.everyKey5_in_atlas root hr with ⟨i, r, hri, hre⟩
  rcases Canonical.everyKey5_in_atlas source hs with ⟨j, s, hsj, hse⟩
  rw [← hre, ← hse] at heq
  have hm := T5_indexed_solid_match hri hsj disjoint heq
  exact IndexedGeometry.mem_generatedCandidates_of_match (by decide) hri hsj
    (((profile5_checked j).2 s hsj).2.1) hm.1 hm.2

/-- The remaining physical profile input is stated using actual solid equality.
All finite/static hypotheses of the generic contact adapter are discharged. -/
theorem T5_legalContact_of_physical_solid_profiles {p : Pose 5}
    (disjoint : Disjoint (interior T5) (interior (p.euclidean '' T5)))
    (contact : ∃ i j, ∃ root ∈ IndexedData5.geometry.profile i,
      ∃ source ∈ IndexedData5.geometry.profile j,
      keySolid (root.toKeyData IndexedData5.geometry.denominator) =
        p.euclidean '' keySolid (source.toKeyData IndexedData5.geometry.denominator))
    (hmatch : ∀ i j, Shared p (IndexedData5.geometry.facet i) (IndexedData5.geometry.facet j) →
      IndexedData5.geometry.SolidProfilesMatch p i j) :
    IndexedData5.geometry.LegalContact p := by
  apply IndexedGeometry.legalContact_of_physical_solid_matches keyCode5_codedBy
    keyCode5_regular (fun c hc => T5_cellCentre_mem_interior ((mem_chairCells c).mp hc))
    IndexedData5.facet_owned (fun i k hk => (atlas5_checked i).2.1 k hk)
    disjoint contact hmatch

#print axioms T5_indexed_solid_match
#print axioms T5_keySolidMatch_mem_generatedCandidates
#print axioms T5_legalContact_of_physical_solid_profiles
end SparseMonotiles
