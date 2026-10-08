module

public import SparseMonotiles.CarrierExistenceGluing
public import SparseMonotiles.KeySupportAtlas

@[expose] public section

/-! Concrete local germs of the actual finite-key body under registered poses.
Finite closed coordinate supports supply isolation; no body coverage or interior
nonoverlap is postulated. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact Set

/-- The actual posed body's germ equals its carrier when all finite closed
key supports miss the point. This needs no common neighborhood for all tiles. -/
theorem posed_body_away_supports {d : ℕ} (ks : List (KeyData d)) (p : Pose d)
    (x : Point d)
    (havoid : ∀ k ∈ ks, x ∉ p.euclidean '' keyCoordinateSupport k) :
    LocalSetEq x (p.euclidean '' body ks) (p.euclidean '' carrier d) := by
  let y := p.euclidean.symm x
  have hy : ∀ k ∈ ks, y ∉ keyCoordinateSupport k := by
    intro k hk hyk
    exact havoid k hk ⟨y, hyk, p.euclidean.apply_symm_apply x⟩
  have ha := away_keys_of_closed_supports keyCoordinateSupport
    (fun k _ => keySolid_subset_coordinateSupport k)
    (fun k _ => keyCoordinateSupport_isClosed k) hy
  have hg := (localSetEq_body_carrier_away_keys ha).image_isometry
    p.euclidean.toIsometryEquiv
  change LocalSetEq (p.euclidean y) (p.euclidean '' body ks)
    (p.euclidean '' carrier d) at hg
  simpa only [y, p.euclidean.apply_symm_apply] using hg

/-- Isometry transport preserves the exact closed signed-key operation. -/
theorem posed_closed_keyReplacement {d : ℕ} (p : Pose d)
    (C K : Set (Point d)) (b : Bool) :
    p.euclidean '' closure (keyReplacement C K b) =
      closure (keyReplacement (p.euclidean '' C) (p.euclidean '' K) b) := by
  have he := p.euclidean.toHomeomorph.image_closure (keyReplacement C K b)
  change p.euclidean '' closure (keyReplacement C K b) =
    closure (p.euclidean '' keyReplacement C K b) at he
  rw [he]
  cases b
  · rw [keyReplacement, keyReplacement]
    simp only [Bool.false_eq_true, if_false]
    rw [Set.image_diff p.euclidean.injective]
  · rw [keyReplacement, keyReplacement]
    simp only [if_true]
    rw [Set.image_union]

/-- The actual closed dent/union model at an isolated posed key. -/
theorem posed_body_isolated_key {d : ℕ} (ks : List (KeyData d)) (p : Pose d)
    (k : KeyData d) (hk : k ∈ ks) (x : Point d)
    (havoid : ∀ j ∈ ks, j ≠ k → x ∉ p.euclidean '' keyCoordinateSupport j) :
    LocalSetEq x (p.euclidean '' body ks)
      (closure (keyReplacement (p.euclidean '' carrier d)
        (p.euclidean '' keySolid k) k.bump)) := by
  let y := p.euclidean.symm x
  have hy : ∀ j ∈ ks, j ≠ k → y ∉ keyCoordinateSupport j := by
    intro j hj hne hyj
    exact havoid j hj hne ⟨y, hyj, p.euclidean.apply_symm_apply x⟩
  have hiso := key_isolation_of_closed_supports keyCoordinateSupport
    (fun j _ => keySolid_subset_coordinateSupport j)
    (fun j _ _ => keyCoordinateSupport_isClosed j) hy
  have hg := (localSetEq_body_isolated_key hk hiso).image_isometry
    p.euclidean.toIsometryEquiv
  change LocalSetEq (p.euclidean y) (p.euclidean '' body ks)
    (p.euclidean '' closure (keyReplacement (carrier d) (keySolid k) k.bump)) at hg
  simpa only [y, p.euclidean.apply_symm_apply, posed_closed_keyReplacement] using hg

/-- Pairwise support separation supplies the isolation input at every point
of the selected closed support, including its boundary. -/
theorem posed_body_isolated_of_disjoint_supports {d : ℕ} (ks : List (KeyData d))
    (hdisj : ∀ k ∈ ks, ∀ j ∈ ks, j ≠ k →
      _root_.Disjoint (keyCoordinateSupport k) (keyCoordinateSupport j))
    (p : Pose d) (k : KeyData d) (hk : k ∈ ks) {x : Point d}
    (hx : x ∈ p.euclidean '' keyCoordinateSupport k) :
    LocalSetEq x (p.euclidean '' body ks)
      (closure (keyReplacement (p.euclidean '' carrier d)
        (p.euclidean '' keySolid k) k.bump)) := by
  apply posed_body_isolated_key ks p k hk x
  intro j hj hne hxj
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, hze⟩ := hxj
  have hzy := p.euclidean.injective hze
  subst z
  exact Set.disjoint_left.mp (hdisj k hk j hj hne) hy hz

/-- Replace the actual posed carrier germ by a proved halfspace model. -/
theorem posed_body_isolated_model {d : ℕ} (ks : List (KeyData d)) (p : Pose d)
    (k : KeyData d) (hk : k ∈ ks) (x : Point d) {H : Set (Point d)}
    (havoid : ∀ j ∈ ks, j ≠ k → x ∉ p.euclidean '' keyCoordinateSupport j)
    (hH : LocalSetEq x (p.euclidean '' carrier d) H) :
    LocalSetEq x (p.euclidean '' body ks)
      (closure (keyReplacement H (p.euclidean '' keySolid k) k.bump)) :=
  (posed_body_isolated_key ks p k hk x havoid).trans
    ((hH.keyReplacement (LocalSetEq.refl x _) k.bump).closure)

/-- Whole-solid equality and opposite material coefficients give the exact
same geometric key in the two opposed local replacement models. -/
theorem matched_posed_key_models {d : ℕ} (ks : List (KeyData d))
    (p q : Pose d) (k l : KeyData d) (hk : k ∈ ks) (hl : l ∈ ks)
    (x : Point d) {H J : Set (Point d)}
    (hp : ∀ j ∈ ks, j ≠ k → x ∉ p.euclidean '' keyCoordinateSupport j)
    (hq : ∀ j ∈ ks, j ≠ l → x ∉ q.euclidean '' keyCoordinateSupport j)
    (hH : LocalSetEq x (p.euclidean '' carrier d) H)
    (hJ : LocalSetEq x (q.euclidean '' carrier d) J)
    (hmatch : p.euclidean '' keySolid k = q.euclidean '' keySolid l)
    (hb : l.bump = !k.bump) :
    LocalSetEq x (p.euclidean '' body ks)
      (closure (keyReplacement H (p.euclidean '' keySolid k) k.bump)) ∧
    LocalSetEq x (q.euclidean '' body ks)
      (closure (keyReplacement J (p.euclidean '' keySolid k) (!k.bump))) := by
  constructor
  · exact posed_body_isolated_model ks p k hk x hp hH
  · simpa only [← hmatch, hb] using posed_body_isolated_model ks q l hl x hq hJ

#print axioms posed_body_away_supports
#print axioms posed_body_isolated_key
#print axioms matched_posed_key_models
end SparseMonotiles.CarrierHierarchy.Existence
