module

public import SparseMonotiles.CarrierExistenceKeyGerms
public import SparseMonotiles.CarrierExistenceFacetOwners
public import SparseMonotiles.ContactFacetCovariance

@[expose] public section

/-! Gluing the literal body from concrete key partners, owned facet collars,
and finite within-tile support separation. No body-tiling premise is used. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact Set

/-- One native exposed facet and a genuine closed collar for each literal key. -/
structure KeyFacetAssignment {d : ℕ} (ks : List (KeyData d)) where
  facet : ∀ k, k ∈ ks → Facet d
  owner : ∀ k hk, IsChairCell (facet k hk).cell
  exposed : ∀ k hk, ¬ IsChairCell (facet k hk).neighbor
  support : ∀ k hk, keyCoordinateSupport k ⊆ gridFacetCollar (facet k hk).gridFacet

/-- Matching data are equalities of actual solids and closed coordinate
supports, plus opposite bump/dent coefficients. The poses own opposite cells
of the same actual grid facet. -/
structure KeyPartner {d : ℕ} (W : RegisteredWorld d) (ks : List (KeyData d))
    (p : Pose d) (k : KeyData d) where
  right : Pose d
  right_mem : right ∈ W.tiles
  distinct : p ≠ right
  key : KeyData d
  key_mem : key ∈ ks
  facet : Facet d
  left_owner : Occupies p facet.cell
  right_owner : Occupies right facet.neighbor
  collar : p.euclidean '' keyCoordinateSupport k ⊆ gridFacetCollar facet.gridFacet
  solid_match : p.euclidean '' keySolid k = right.euclidean '' keySolid key
  support_match : p.euclidean '' keyCoordinateSupport k = right.euclidean '' keyCoordinateSupport key
  coefficient : key.bump = !k.bump

theorem facet_cells_of_same_grid {d : ℕ} {f g : Facet d}
    (h : f.gridFacet = g.gridFacet) : g.cell = f.cell ∨ g.cell = f.neighbor := by
  have ha : f.axis = g.axis := congrArg GridFacet.axis h
  have hc (i : Fin d) := congrFun (congrArg GridFacet.anchor h) i
  by_cases hp : g.positive = f.positive
  · left
    funext i
    have hi := hc i
    change f.cell i + (if i = f.axis ∧ f.positive = true then 1 else 0) =
      g.cell i + (if i = g.axis ∧ g.positive = true then 1 else 0) at hi
    rw [← ha, hp] at hi
    omega
  · right
    funext i
    have hi := hc i
    change f.cell i + (if i = f.axis ∧ f.positive = true then 1 else 0) =
      g.cell i + (if i = g.axis ∧ g.positive = true then 1 else 0) at hi
    rw [← ha] at hi
    by_cases hai : i = f.axis <;> cases hf : f.positive <;> cases hg : g.positive <;>
      simp [Facet.neighbor, Facet.normal, hai, hf, hg] at hi hp ⊢ <;> omega

theorem posed_support_facet {d : ℕ} {ks : List (KeyData d)}
    (A : KeyFacetAssignment ks) (p : Pose d) (k : KeyData d) (hk : k ∈ ks) :
    Occupies p (p.facet (A.facet k hk)).cell ∧
      p.euclidean '' keyCoordinateSupport k ⊆ gridFacetCollar (p.facet (A.facet k hk)).gridFacet := by
  constructor
  · change IsChairCell (p.inverseCell (p.cell (A.facet k hk).cell))
    rw [Pose.inverseCell_cell]
    exact A.owner k hk
  · rintro x ⟨y, hy, rfl⟩
    exact p.mapsTo_facet_collar _ (A.support k hk hy)

/-- A third tile cannot have any key support in the chosen collar: collar
identity limits the support's owner to the same two registered cells. -/
theorem third_key_support_absent {d : ℕ} {ks : List (KeyData d)}
    (A : KeyFacetAssignment ks) (W : RegisteredWorld d) (f : Facet d)
    {p q r : Pose d} (hp : p ∈ W.tiles) (hq : q ∈ W.tiles) (hr : r ∈ W.tiles)
    (hrp : r ≠ p) (hrq : r ≠ q)
    (hpc : Occupies p f.cell) (hqn : Occupies q f.neighbor)
    {x : Point d} (hx : x ∈ gridFacetCollar f.gridFacet)
    (k : KeyData d) (hk : k ∈ ks) : x ∉ r.euclidean '' keyCoordinateSupport k := by
  intro hxr
  obtain ⟨hro, hrc⟩ := posed_support_facet A r k hk
  have he := GridFacet.eq_of_mem_collars hx (hrc hxr)
  rcases facet_cells_of_same_grid he with hc | hc
  · rw [hc] at hro
    exact hrp (W.disjoint r hr p hp _ hro hpc)
  · rw [hc] at hro
    exact hrq (W.disjoint r hr q hq _ hro hqn)

theorem posed_other_support_absent {d : ℕ} {ks : List (KeyData d)}
    (hdisj : ∀ k ∈ ks, ∀ j ∈ ks, j ≠ k →
      _root_.Disjoint (keyCoordinateSupport k) (keyCoordinateSupport j))
    (p : Pose d) {k : KeyData d} (hk : k ∈ ks) {x : Point d}
    (hx : x ∈ p.euclidean '' keyCoordinateSupport k) :
    ∀ j ∈ ks, j ≠ k → x ∉ p.euclidean '' keyCoordinateSupport j := by
  intro j hj hne hxj
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, hze⟩ := hxj
  have hzy := p.euclidean.injective hze
  subst z
  exact Set.disjoint_left.mp (hdisj k hk j hj hne) hy hz

/-- The local gluing certificate is derived from owned cells, collar bounds,
within-tile support separation, whole-key equality, and opposite signs. -/
def KeyPartner.localPair {d : ℕ} {ks : List (KeyData d)}
    (A : KeyFacetAssignment ks) (W : RegisteredWorld d)
    (hdisj : ∀ k ∈ ks, ∀ j ∈ ks, j ≠ k →
      _root_.Disjoint (keyCoordinateSupport k) (keyCoordinateSupport j))
    (hclosed : ∀ k ∈ ks, IsClosed (keySolid k))
    {p : Pose d} (hp : p ∈ W.tiles) {k : KeyData d} (hk : k ∈ ks)
    (P : KeyPartner W ks p k) {x : Point d}
    (hx : x ∈ p.euclidean '' keyCoordinateSupport k) :
    LocalKeyPair W (fun p => p.euclidean '' body ks) x := by
  have hxc := P.collar hx
  have hxn := P.facet.gridFacetCollar_subset_openCellNeighborhood hxc
  have hroot := owner_carrier_germ W P.facet hp P.right_mem P.distinct
    P.left_owner P.right_owner hxn
  have hsource := neighbor_carrier_germ W P.facet hp P.right_mem P.distinct
    P.left_owner P.right_owner hxn
  have hxq : x ∈ P.right.euclidean '' keyCoordinateSupport P.key := by
    rw [← P.support_match]
    exact hx
  have hmodels := matched_posed_key_models ks p P.right k P.key hk P.key_mem x
    (posed_other_support_absent hdisj p hk hx)
    (posed_other_support_absent hdisj P.right P.key_mem hxq)
    hroot hsource P.solid_match P.coefficient
  have hkc : IsClosed (p.euclidean '' keySolid k) := by
    have hc := p.euclidean.toHomeomorph.isClosedMap _ (hclosed k hk)
    exact hc
  refine ⟨p, P.right, hp, P.right_mem, P.distinct, P.facet.inwardHalfspace,
    outwardHalfspace P.facet, p.euclidean '' keySolid k,
    facet_regions_opposed P.facet, hkc, k.bump, hmodels.1, hmodels.2, ?_⟩
  intro r hr hrp hrq
  exact (posed_body_away_supports ks r x
      (third_key_support_absent A W P.facet hp P.right_mem hr hrp hrq
        P.left_owner P.right_owner hxc)).trans
    (third_carrier_germ_empty W P.facet hp P.right_mem hr hrp hrq
      P.left_owner P.right_owner hxn)

/-- Actual keyed-body tiling follows from geometric partners for every placed
key. All absence and carrier-germ conditions are derived, not hypotheses. -/
theorem realize_body_of_key_partners {d : ℕ} (ks : List (KeyData d))
    (A : KeyFacetAssignment ks) (W : RegisteredWorld d)
    (hdisj : ∀ k ∈ ks, ∀ j ∈ ks, j ≠ k →
      _root_.Disjoint (keyCoordinateSupport k) (keyCoordinateSupport j))
    (hclosed : ∀ k ∈ ks, IsClosed (keySolid k))
    (partners : ∀ p ∈ W.tiles, ∀ k ∈ ks, Nonempty (KeyPartner W ks p k)) :
    IsTiling (body ks) ((fun p : Pose d => p.euclidean '' body ks) '' W.tiles) := by
  apply realize_of_atlas W (body ks)
  intro x
  by_cases hx : ∃ p ∈ W.tiles, ∃ k ∈ ks, x ∈ p.euclidean '' keyCoordinateSupport k
  · obtain ⟨p, hp, k, hk, hxp⟩ := hx
    right
    exact ⟨(partners p hp k hk).some.localPair A W hdisj hclosed hp hk hxp⟩
  · left
    intro p hp
    apply posed_body_away_supports ks p x
    intro k hk hxk
    exact hx ⟨p, hp, k, hk, hxk⟩

#print axioms third_key_support_absent
#print axioms KeyPartner.localPair
#print axioms realize_body_of_key_partners
end SparseMonotiles.CarrierHierarchy.Existence
