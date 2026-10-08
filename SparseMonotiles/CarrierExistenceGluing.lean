module

public import SparseMonotiles.CarrierExistenceEuclidean
public import SparseMonotiles.BoundaryTransport

@[expose] public section

/-! Local bump/dent replacement and global realization. The dent closure is
retained. The inputs below are actual halfspace/solid germs, not HasTiling of
the keyed body, and no decorated-body substitution identity is asserted. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact Set

/-- Geometric conditions satisfied by the two closed sides of one hyperplane. -/
structure OpposedClosedRegions {X : Type*} [TopologicalSpace X]
    (H J : Set X) : Prop where
  left_closed : IsClosed H
  right_closed : IsClosed J
  covers : H ∪ J = univ
  left_interior : _root_.Disjoint (interior H) J
  right_interior : _root_.Disjoint H (interior J)

theorem OpposedClosedRegions.symm {X : Type*} [TopologicalSpace X]
    {H J : Set X} (h : OpposedClosedRegions H J) : OpposedClosedRegions J H :=
  ⟨h.right_closed, h.left_closed, by simpa [union_comm] using h.covers,
    h.right_interior.symm, h.left_interior.symm⟩

/-- Opposite closed halfspaces with one common closed key exchange material
without a gap or an open overlap, including the key's base and boundary. -/
theorem bump_dent_partition {X : Type*} [TopologicalSpace X]
    {H J K : Set X} (h : OpposedClosedRegions H J) (hK : IsClosed K) :
    closure (H ∪ K) ∪ closure (J \ K) = univ ∧
      _root_.Disjoint (interior (closure (H ∪ K))) (interior (closure (J \ K))) := by
  rw [(h.left_closed.union hK).closure_eq]
  constructor
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ H ∪ J := by rw [h.covers]; trivial
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · by_cases hk : x ∈ K
      · exact Or.inl (Or.inr hk)
      · exact Or.inr (subset_closure ⟨hx, hk⟩)
  · have hs : J \ K ⊆ (interior (H ∪ K))ᶜ := by
      intro x hx hi
      rcases hK.interior_union_right hi with hh | hk
      · exact Set.disjoint_left.mp h.left_interior hh hx.1
      · exact hx.2 hk
    have hc : closure (J \ K) ⊆ (interior (H ∪ K))ᶜ :=
      closure_minimal hs isOpen_interior.isClosed_compl
    apply Set.disjoint_left.mpr
    intro x hleft hright
    exact hc (interior_subset hright) hleft

theorem signed_key_partition {X : Type*} [TopologicalSpace X]
    {H J K : Set X} (h : OpposedClosedRegions H J) (hK : IsClosed K) (b : Bool) :
    closure (keyReplacement H K b) ∪ closure (keyReplacement J K (!b)) = univ ∧
      _root_.Disjoint (interior (closure (keyReplacement H K b)))
        (interior (closure (keyReplacement J K (!b)))) := by
  cases b
  · have hh := bump_dent_partition h.symm hK
    constructor
    · simpa only [keyReplacement, Bool.not_false, Bool.false_eq_true, if_false, if_true,
        union_comm] using hh.1
    · simpa only [keyReplacement, Bool.not_false, Bool.false_eq_true, if_false, if_true]
        using hh.2.symm
  · simpa only [keyReplacement, Bool.not_true, Bool.false_eq_true, if_false, if_true]
      using bump_dent_partition h hK

/-- Two selected tile germs are the exact complementary signed-key models.
All other tile germs vanish near this key. A later atlas adapter supplies this
from cell owners, collar separation, key isolation, and matched actual solids. -/
structure LocalKeyPair {d : ℕ} (W : RegisteredWorld d)
    (B : Pose d → Set (Point d)) (x : Point d) where
  left : Pose d
  right : Pose d
  left_mem : left ∈ W.tiles
  right_mem : right ∈ W.tiles
  distinct : left ≠ right
  H : Set (Point d)
  J : Set (Point d)
  K : Set (Point d)
  opposed : OpposedClosedRegions H J
  key_closed : IsClosed K
  bump : Bool
  left_germ : LocalSetEq x (B left) (closure (keyReplacement H K bump))
  right_germ : LocalSetEq x (B right) (closure (keyReplacement J K (!bump)))
  other_germ : ∀ p ∈ W.tiles, p ≠ left → p ≠ right → LocalSetEq x (B p) ∅

/-- Coverage is a conclusion of the opposed-region and signed-key geometry. -/
theorem LocalKeyPair.covers {d : ℕ} {W : RegisteredWorld d}
    {B : Pose d → Set (Point d)} {x : Point d} (h : LocalKeyPair W B x) :
    ∃ p ∈ W.tiles, x ∈ B p := by
  have hc := (signed_key_partition h.opposed h.key_closed h.bump).1
  have hx : x ∈ closure (keyReplacement h.H h.K h.bump) ∪
      closure (keyReplacement h.J h.K (!h.bump)) := by rw [hc]; trivial
  rcases hx with hx | hx
  · exact ⟨h.left, h.left_mem, h.left_germ.mem_iff.mpr hx⟩
  · exact ⟨h.right, h.right_mem, h.right_germ.mem_iff.mpr hx⟩

/-- Interior disjointness is a conclusion, with the dent closure handled by
the topological partition lemma rather than deleted from the local model. -/
theorem LocalKeyPair.no_overlap {d : ℕ} {W : RegisteredWorld d}
    {B : Pose d → Set (Point d)} {x : Point d} (h : LocalKeyPair W B x)
    {p q : Pose d} (hp : p ∈ W.tiles) (hq : q ∈ W.tiles) (hne : p ≠ q)
    (hpx : x ∈ interior (B p)) (hqx : x ∈ interior (B q)) : False := by
  have hp_pair : p = h.left ∨ p = h.right := by
    by_contra hn
    push_neg at hn
    have he := (h.other_germ p hp hn.1 hn.2).mem_iff.mp (interior_subset hpx)
    exact he
  have hq_pair : q = h.left ∨ q = h.right := by
    by_contra hn
    push_neg at hn
    have he := (h.other_germ q hq hn.1 hn.2).mem_iff.mp (interior_subset hqx)
    exact he
  have hd := (signed_key_partition h.opposed h.key_closed h.bump).2
  rcases hp_pair with rfl | rfl <;> rcases hq_pair with rfl | rfl
  · exact hne rfl
  · exact Set.disjoint_left.mp hd (h.left_germ.interior.mem_iff.mp hpx)
      (h.right_germ.interior.mem_iff.mp hqx)
  · exact Set.disjoint_left.mp hd (h.left_germ.interior.mem_iff.mp hqx)
      (h.right_germ.interior.mem_iff.mp hpx)
  · exact hne rfl

/-- The atlas alternatives describe actual material germs: unchanged carrier,
or one paired closed key with all other germs absent. -/
def RealizationAtlas {d : ℕ} (W : RegisteredWorld d)
    (B : Pose d → Set (Point d)) : Prop := ∀ x,
  (∀ p ∈ W.tiles, LocalSetEq x (B p) (p.euclidean '' carrier d)) ∨
    Nonempty (LocalKeyPair W B x)

/-- Global gluing from local replacement geometry. No keyed tiling, coverage,
or body interior-disjointness premise occurs in the certificate interface. -/
theorem realize_of_atlas {d : ℕ} (W : RegisteredWorld d) (T : Set (Point d))
    (atlas : RealizationAtlas W (fun p => p.euclidean '' T)) :
    IsTiling T ((fun p : Pose d => p.euclidean '' T) '' W.tiles) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro A ⟨p, hp, rfl⟩
    exact ⟨p.euclidean.toIsometryEquiv, rfl⟩
  · intro x
    have hx : ∃ p ∈ W.tiles, x ∈ p.euclidean '' T := by
      rcases (atlas x : (∀ p ∈ W.tiles, LocalSetEq x (p.euclidean '' T)
          (p.euclidean '' carrier d)) ∨ Nonempty (LocalKeyPair W (fun p => p.euclidean '' T) x)) with ha | hpair
      · obtain ⟨p, hp, hpc⟩ := carrier_covers W x
        exact ⟨p, hp, (ha p hp).mem_iff.mpr hpc⟩
      · exact hpair.some.covers
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨p.euclidean '' T, ⟨p, hp, rfl⟩, hpx⟩
  · rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun he => hne (by rw [he])
    apply Set.disjoint_left.mpr
    intro x hpx hqx
    rcases (atlas x : (∀ p ∈ W.tiles, LocalSetEq x (p.euclidean '' T)
          (p.euclidean '' carrier d)) ∨ Nonempty (LocalKeyPair W (fun p => p.euclidean '' T) x)) with ha | hpair
    · exact Set.disjoint_left.mp (carrier_interiors_disjoint W hp hq hpq)
        ((ha p hp).interior.mem_iff.mp hpx) ((ha q hq).interior.mem_iff.mp hqx)
    · exact hpair.some.no_overlap hp hq hpq hpx hqx

#print axioms bump_dent_partition
#print axioms signed_key_partition
#print axioms realize_of_atlas
end SparseMonotiles.CarrierHierarchy.Existence
