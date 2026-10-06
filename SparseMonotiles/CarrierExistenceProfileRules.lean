module

public import SparseMonotiles.CarrierExistencePartners

@[expose] public section

/-! Finite-language facet-profile complementarity produces the actual key
partners needed for body realization. Relative poses and adjacent owners are
derived from the constructed registered world; no physical tiling is assumed. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact Set

theorem compose_euclidean_apply {d : ℕ} (p q : Pose d) (x : Point d) :
    (compose p q).euclidean x = p.euclidean (q.euclidean x) := by
  ext i
  simp only [Pose.euclidean_apply]
  rw [compose_sign]
  simp only [compose, Equiv.trans_apply, Int.cast_add, Int.cast_mul]
  ring

theorem compose_euclidean_image {d : ℕ} (p q : Pose d) (S : Set (Point d)) :
    (compose p q).euclidean '' S = p.euclidean '' (q.euclidean '' S) := by
  rw [Set.image_image]
  apply congrArg (fun f : Point d → Point d => f '' S)
  funext x
  exact compose_euclidean_apply p q x

theorem posed_facet_neighbor {d : ℕ} (p : Pose d) (f : Facet d) :
    (p.facet f).neighbor = p.cell f.neighbor := by
  funext i
  change p.cell f.cell i + (if i = (p.facet f).axis then (p.facet f).normal else 0) = _
  by_cases hi : i = (p.facet f).axis
  · have hp := (p.facet_axis_iff f i).mp hi
    simp only [if_pos hi, Pose.facet_normal, ← hi, Pose.cell, Facet.neighbor, if_pos hp, if_true]
    ring
  · have hp : p.perm i ≠ f.axis := fun h => hi ((p.facet_axis_iff f i).mpr h)
    simp only [if_neg hi, Pose.cell, Facet.neighbor, if_neg hp, add_zero]

theorem facet_owner_adjacent_neighbor {d : ℕ} (f : Facet d) :
    AdjacentCells f.cell f.neighbor := by
  refine ⟨f.axis, ?_, ?_⟩
  · cases hp : f.positive <;> simp [Facet.neighbor, Facet.normal, hp, sub_eq_add_neg]
  · intro i hi
    simp [Facet.neighbor, hi]

/-- A finite exact profile-complementarity obligation. For every allowed
relative pose and every literal key, if the source owns that key's exterior
cell, one literal source key has the same actual solid and coordinate support,
and the opposite material coefficient. For M5/M7 both quantified lists are
finite; no wholeworld or arbitrary-isometry matching claim occurs here. -/
def ComplementaryProfiles {d : ℕ} {ks : List (KeyData d)}
    (A : KeyFacetAssignment ks) (L : Set (Pose d)) : Prop :=
  ∀ R ∈ L, ∀ k (hk : k ∈ ks), Occupies R (A.facet k hk).neighbor →
    ∃ l ∈ ks,
      keySolid k = R.euclidean '' keySolid l ∧
      keyCoordinateSupport k = R.euclidean '' keyCoordinateSupport l ∧
      l.bump = !k.bump

/-- The exterior cell has a unique actual owner in the registered world.
Its fine contact belongs to the language, so the finite profile rule supplies
one literal mate, which is transported back to the world frame. -/
theorem keyPartner_exists_of_profiles {d : ℕ} {ks : List (KeyData d)}
    (A : KeyFacetAssignment ks) (L : Set (Pose d))
    (profiles : ComplementaryProfiles A L) (W : RegisteredWorld d) (legal : W.Legal L)
    (p : Pose d) (hp : p ∈ W.tiles) (k : KeyData d) (hk : k ∈ ks) :
    Nonempty (KeyPartner W ks p k) := by
  let f := A.facet k hk
  obtain ⟨q, hq, hqc⟩ := W.covers (p.cell f.neighbor)
  have hpq : p ≠ q := by
    intro he
    subst q
    exact A.exposed k hk ((root_occupies_cell p f.neighbor).mp hqc)
  have hpc : Occupies p (p.cell f.cell) :=
    (root_occupies_cell p f.cell).mpr (A.owner k hk)
  have hcontact : CellContact p q := ⟨p.cell f.cell, p.cell f.neighbor, hpc, hqc,
    adjacent_cell_image p (facet_owner_adjacent_neighbor f)⟩
  have hrel := legal p hp q hq hpq hcontact
  have hrelOwn : Occupies (normalize p q) f.neighbor :=
    (normalize_occupies p q f.neighbor).mpr hqc
  obtain ⟨l, hl, hsolid, hsupport, hcoeff⟩ := profiles (normalize p q) hrel k hk hrelOwn
  have hworld_solid : p.euclidean '' keySolid k = q.euclidean '' keySolid l := by
    rw [hsolid, ← compose_euclidean_image, compose_normalize]
  have hworld_support : p.euclidean '' keyCoordinateSupport k = q.euclidean '' keyCoordinateSupport l := by
    rw [hsupport, ← compose_euclidean_image, compose_normalize]
  refine ⟨⟨q, hq, hpq, l, hl, p.facet f, hpc, ?_, ?_, hworld_solid, hworld_support, hcoeff⟩⟩
  · rw [posed_facet_neighbor]
    exact hqc
  · exact (posed_support_facet A p k hk).2

/-- End-to-end generic keyed realization from a legal registered carrier
world and finite profile complementarity. The result concerns the literal
Model.body, with its final closure and actual Euclidean tile sets. -/
theorem realize_body_of_profiles {d : ℕ} (ks : List (KeyData d))
    (A : KeyFacetAssignment ks) (L : Set (Pose d))
    (profiles : ComplementaryProfiles A L)
    (hdisj : ∀ k ∈ ks, ∀ j ∈ ks, j ≠ k →
      _root_.Disjoint (keyCoordinateSupport k) (keyCoordinateSupport j))
    (hclosed : ∀ k ∈ ks, IsClosed (keySolid k))
    (W : RegisteredWorld d) (legal : W.Legal L) :
    IsTiling (body ks) ((fun p : Pose d => p.euclidean '' body ks) '' W.tiles) :=
  realize_body_of_key_partners ks A W hdisj hclosed
    (keyPartner_exists_of_profiles A L profiles W legal)

#print axioms keyPartner_exists_of_profiles
#print axioms realize_body_of_profiles
end SparseMonotiles.CarrierHierarchy.Existence
