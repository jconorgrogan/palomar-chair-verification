module

public import SparseMonotiles.ContactKeySolidRecovery
public import SparseMonotiles.ContactMatchedFacet

@[expose] public section

/-!
Explicit interface from whole-key physical matches to the finite contact law.
The hypotheses describe actual convex-hull solids, not vertex-list labels.
This module does not produce those matches from arbitrary boundary contact;
that geometric obligation remains visible in `SolidProfilesMatch`.
-/
namespace SparseMonotiles.Contact

/-- Every actual root key solid has a matching posed source solid, and conversely.
No matching relation on coefficients or literal vertices is assumed. -/
def IndexedGeometry.SolidProfilesMatch {d n : ℕ} (g : IndexedGeometry d n)
    (p : Pose d) (i j : Fin n) : Prop :=
  (∀ root ∈ g.profile i, ∃ source ∈ g.profile j,
    keySolid (root.toKeyData g.denominator) =
      p.euclidean '' keySolid (source.toKeyData g.denominator)) ∧
  (∀ source ∈ g.profile j, ∃ root ∈ g.profile i,
    keySolid (root.toKeyData g.denominator) =
      p.euclidean '' keySolid (source.toKeyData g.denominator))

/-- Physical solid matches recover the full box-profile equality. -/
theorem IndexedGeometry.boxProfiles_eq_of_solid_matches {d n : ℕ}
    {g : IndexedGeometry d n} {C : KeyCoordinateCode}
    (coded : g.CodedBy C)
    (regular : ∀ i k, k ∈ g.profile i → C.RegularKey (g.facet i) k)
    {p : Pose d} {i j : Fin n} (shared : Shared p (g.facet i) (g.facet j))
    (hmatch : g.SolidProfilesMatch p i j) :
    g.profile i = (g.profile j).image (p.boxKey g.denominator) := by
  have recover {root source : BoxKey d} (hr : root ∈ g.profile i) (hs : source ∈ g.profile j)
      (he : keySolid (root.toKeyData g.denominator) =
        p.euclidean '' keySolid (source.toKeyData g.denominator)) :
      root = p.boxKey g.denominator source := by
    rw [coded.1] at he ⊢
    exact C.eq_boxKey_of_shared_solid_image shared (coded.2 i root hr)
      (coded.2 j source hs) (regular i root hr) (regular j source hs) he
  apply Finset.ext
  intro k
  constructor
  · intro hk
    rcases hmatch.1 k hk with ⟨source, hs, he⟩
    exact Finset.mem_image.mpr ⟨source, hs, (recover hk hs he).symm⟩
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨source, hs, rfl⟩
    rcases hmatch.2 source hs with ⟨root, hr, he⟩
    exact recover hr hs he ▸ hr

/-- The checked finite predicate compares literal profiles; this equality is
now a consequence of actual whole-solid matching under the static code. -/
theorem IndexedGeometry.literalProfiles_eq_of_solid_matches {d n : ℕ}
    {g : IndexedGeometry d n} {C : KeyCoordinateCode}
    (coded : g.CodedBy C)
    (regular : ∀ i k, k ∈ g.profile i → C.RegularKey (g.facet i) k)
    {p : Pose d} {i j : Fin n} (shared : Shared p (g.facet i) (g.facet j))
    (hmatch : g.SolidProfilesMatch p i j) :
    (g.profile i).image BoxKey.literal =
      ((g.profile j).image BoxKey.literal).image (p.key g.denominator) := by
  rw [boxProfiles_eq_of_solid_matches coded regular shared hmatch]
  simp only [Finset.image_image]
  congr 1
  funext k
  exact p.boxKey_literal g.denominator k

/-- All finite semantic obligations follow from the stated physical whole-key
matches plus the separately checked static collar/core/code hypotheses. -/
theorem IndexedGeometry.legalContact_of_physical_solid_matches {d n : ℕ}
    {g : IndexedGeometry d n} {C : KeyCoordinateCode} {A : Set (Point d)}
    (coded : g.CodedBy C)
    (regular : ∀ i k, k ∈ g.profile i → C.RegularKey (g.facet i) k)
    (centres : ∀ c ∈ g.cells, cellCentre c ∈ interior A)
    (owners : ∀ i, (g.facet i).cell ∈ g.cells)
    (collars : ∀ i k, k ∈ g.profile i → k.CollarValid g.denominator (g.facet i))
    {p : Pose d} (disjoint : Disjoint (interior A) (interior (p.euclidean '' A)))
    (contact : ∃ i j, ∃ root ∈ g.profile i, ∃ source ∈ g.profile j,
      keySolid (root.toKeyData g.denominator) =
        p.euclidean '' keySolid (source.toKeyData g.denominator))
    (hmatch : ∀ i j, Shared p (g.facet i) (g.facet j) → g.SolidProfilesMatch p i j) :
    g.LegalContact p := by
  refine ⟨carrier_disjoint_of_physical_interiors centres centres disjoint, ?_, ?_⟩
  · rcases contact with ⟨i, j, root, hr, source, hs, he⟩
    have hd : 0 < g.denominator := by
      rw [coded.1]
      exact (regular i root hr).1
    exact ⟨i, j, p.shared_of_physical_matched_keySolids hd centres centres
      (owners i) (owners j) disjoint (collars i root hr) (collars j source hs) he⟩
  · intro i j shared
    exact literalProfiles_eq_of_solid_matches coded regular shared (hmatch i j shared)

#print axioms IndexedGeometry.boxProfiles_eq_of_solid_matches
#print axioms IndexedGeometry.legalContact_of_physical_solid_matches
end SparseMonotiles.Contact
