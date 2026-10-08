module

public import SparseMonotiles.ConditionalPhysicalAperiodicity7
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section
namespace SparseMonotiles
open Set Contact CarrierHierarchy

/-- An arbitrary Euclidean isometry preserving the physical tile collection. -/
def IsEuclideanSymmetry {d : ℕ} (tiles : Set (Set (Point d)))
    (f : Point d ≃ᵢ Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ f '' A ∈ tiles

/-- The full symmetry type includes arbitrary rotations, reflections and translations. -/
def EuclideanSymmetries {d : ℕ} (tiles : Set (Set (Point d))) :=
  {f : Point d ≃ᵢ Point d // IsEuclideanSymmetry tiles f}

 theorem IsEuclideanSymmetry.symm {d : ℕ} {tiles : Set (Set (Point d))}
    {f : Point d ≃ᵢ Point d} (hf : IsEuclideanSymmetry tiles f) :
    IsEuclideanSymmetry tiles f.symm := by
  intro A
  simpa only [Set.image_image, IsometryEquiv.apply_symm_apply, Set.image_id']
    using (hf (f.symm '' A)).symm

 theorem IsEuclideanSymmetry.trans {d : ℕ} {tiles : Set (Set (Point d))}
    {f g : Point d ≃ᵢ Point d} (hf : IsEuclideanSymmetry tiles f)
    (hg : IsEuclideanSymmetry tiles g) : IsEuclideanSymmetry tiles (f.trans g) := by
  intro A
  change A ∈ tiles ↔ (fun x => g (f x)) '' A ∈ tiles
  rw [← Set.image_image]
  exact (hf A).trans (hg (f '' A))

 theorem T7_exists_other_tile {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (B : tiles) : ∃ C : tiles, C ≠ B := by
  classical
  by_contra h
  have heq : ∀ C : tiles, C = B := by simpa only [not_exists, not_not] using h
  obtain ⟨g,hg⟩ := ht.1 B B.property
  have hc : IsCompact (B : Set (Point 7)) := hg ▸ T7_isCompact.image g.continuous
  apply hc.ne_univ
  apply Set.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨C,hC,hx⟩ := ht.2.1 x
  have hCB := congrArg Subtype.val (heq ⟨C,hC⟩)
  exact hCB ▸ hx

 theorem T7_relative_frames_registered {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, g A '' T7 = (A : Set (Point 7))) (A B : tiles) :
    IsRegisteredIsometry ((g B).trans (g A).symm) :=
  T7_all_frames_registered_of_exposed_extension ht g hg A
    (T7_registered_exposed_extension ht g hg) B

/-- Registration of every symmetry in one fixed root chart. The changed-frame
argument also covers symmetries fixing the root tile setwise. -/
 theorem T7_symmetry_registered_in_root {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, g A '' T7 = (A : Set (Point 7))) (A : tiles)
    {f : Point 7 ≃ᵢ Point 7} (hf : IsEuclideanSymmetry tiles f) :
    IsRegisteredIsometry (((g A).trans f).trans (g A).symm) := by
  classical
  let B : tiles := ⟨f '' (A : Set (Point 7)), (hf A).mp A.property⟩
  obtain ⟨C,hCB⟩ := T7_exists_other_tile ht B
  let g' : tiles → Point 7 ≃ᵢ Point 7 := fun D => if D = B then (g A).trans f else g D
  have hg' : ∀ D : tiles, g' D '' T7 = (D : Set (Point 7)) := by
    intro D
    by_cases hDB : D = B
    · subst D
      simp only [g', ite_eq_left rfl, IsometryEquiv.trans_apply]
      change (fun x => f (g A x)) '' T7 = f '' (A : Set (Point 7))
      rw [← Set.image_image, hg A]
    · simp only [g', ite_eq_right hDB]
      exact hg D
  have h1 := T7_relative_frames_registered ht g' hg' C B
  have h2 := T7_relative_frames_registered ht g hg A C
  have h := h1.trans h2
  have heq : ((g' B).trans (g' C).symm).trans ((g C).trans (g A).symm) =
      ((g A).trans f).trans (g A).symm := by
    simp only [g', ite_eq_left rfl, ite_eq_right hCB]
    ext x
    simp
  exact heq ▸ h



/-- A translation-free tile collection has at most one symmetry of any given
linear part. This lemma alone does not assert finitely many linear parts. -/
theorem symmetry_eq_of_equal_displacements {d : ℕ}
    {tiles : Set (Set (Point d))}
    (haper : ∀ v, IsPeriod tiles v → v = 0)
    {f h : Point d ≃ᵢ Point d}
    (hf : IsEuclideanSymmetry tiles f) (hh : IsEuclideanSymmetry tiles h)
    (hdelta : ∀ x, f x - f 0 = h x - h 0) : f = h := by
  let v := f 0 - h 0
  have hpoint : ∀ x, f x = h x + v := by
    intro x
    have hx := hdelta x
    dsimp [v]
    rw [sub_eq_sub_iff_add_eq_add] at hx
    exact (eq_sub_iff_add_eq.mpr hx).trans (by abel)
  have hv : IsPeriod tiles v := by
    intro A
    have hc := (hh.symm.trans hf) A
    have heq : (h.symm.trans f) '' A = translate v A := by
      change (fun x => f (h.symm x)) '' A = (fun x => x + v) '' A
      congr 1
      funext x
      rw [hpoint, IsometryEquiv.apply_symm_apply]
    rwa [heq] at hc
  have hzero := haper v hv
  ext x
  rw [hpoint, hzero, add_zero]

/-- Equal signed-permutation data imply equal displacements after any fixed
Euclidean change of coordinates. The integer shifts cancel. -/
theorem displacements_equal_of_conjugate_pose_orientation {d : ℕ}
    (a f h : Point d ≃ᵢ Point d) (p q : Pose d)
    (hfp : (a.trans f).trans a.symm = p.euclidean.toIsometryEquiv)
    (hhq : (a.trans h).trans a.symm = q.euclidean.toIsometryEquiv)
    (hperm : p.perm = q.perm) (hneg : p.negative = q.negative) :
    ∀ x, f x - f 0 = h x - h 0 := by
  have hdelta : ∀ z w, p.euclidean z - p.euclidean w = q.euclidean z - q.euclidean w := by
    intro z w
    ext i
    simp only [PiLp.sub_apply, Pose.euclidean_apply]
    rw [hperm]
    simp only [Pose.sign, hneg]
    ring
  intro x
  have hfpoint : ∀ z, p.euclidean z = a.symm (f (a z)) := by
    intro z
    exact (congrArg (fun k : Point d ≃ᵢ Point d => k z) hfp).symm
  have hhpoint : ∀ z, q.euclidean z = a.symm (h (a z)) := by
    intro z
    exact (congrArg (fun k : Point d ≃ᵢ Point d => k z) hhq).symm
  have hx := hdelta (a.symm x) (a.symm 0)
  simp only [hfpoint, hhpoint, IsometryEquiv.apply_symm_apply] at hx
  let e := a.symm.toRealAffineIsometryEquiv
  apply e.linearIsometryEquiv.injective
  change e.linearIsometryEquiv (f x -ᵥ f 0) = e.linearIsometryEquiv (h x -ᵥ h 0)
  rw [e.map_vsub, e.map_vsub]
  exact hx

/-- Exact T7 full symmetry injection; the unresolved contact classification is explicit. -/
theorem T7_symmetries_embed_signed_permutations_of_contact_classification
    (hclassify : ∀ p : Pose 7, IndexedData7.geometry.LegalContact p → p ∈ M7)
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles) :
    ∃ code : EuclideanSymmetries tiles → (Equiv.Perm (Fin 7) × (Fin 7 → Bool)),
      Function.Injective code := by
  classical
  choose g hg using fun A : tiles => ht.1 A A.property
  obtain ⟨R,hR,_⟩ := ht.2.1 (0 : Point 7)
  let A : tiles := ⟨R,hR⟩
  have hreg : ∀ f : EuclideanSymmetries tiles,
      ∃ p : Pose 7, ((g A).trans f.val).trans (g A).symm = p.euclidean.toIsometryEquiv := by
    intro f
    exact T7_symmetry_registered_in_root ht g (fun B => (hg B).symm) A f.property
  choose p hp using hreg
  refine ⟨fun f => ((p f).perm, (p f).negative), ?_⟩
  intro f h heq
  apply Subtype.ext
  apply symmetry_eq_of_equal_displacements
    (T7_isAperiodic_of_indexed_contact_classification hclassify tiles ht) f.property h.property
  exact displacements_equal_of_conjugate_pose_orientation (g A) f.val h.val (p f) (p h)
    (hp f) (hp h) (congrArg Prod.fst heq) (congrArg Prod.snd heq)

/-- Finite full Euclidean symmetry, conditional on the exact indexed classification. -/
theorem T7_finite_euclidean_symmetries_of_contact_classification
    (hclassify : ∀ p : Pose 7, IndexedData7.geometry.LegalContact p → p ∈ M7)
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles) :
    Finite (EuclideanSymmetries tiles) := by
  obtain ⟨code,hcode⟩ := T7_symmetries_embed_signed_permutations_of_contact_classification hclassify ht
  exact Finite.of_injective code hcode

/-- 7! axis permutations times 2^7 signs, with classification still explicit. -/
theorem T7_euclidean_symmetry_card_le_645120_of_contact_classification
    (hclassify : ∀ p : Pose 7, IndexedData7.geometry.LegalContact p → p ∈ M7)
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles) :
    Nat.card (EuclideanSymmetries tiles) ≤ 645120 := by
  obtain ⟨code,hcode⟩ := T7_symmetries_embed_signed_permutations_of_contact_classification hclassify ht
  have hb := Nat.card_le_card_of_injective code hcode
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Nat.factorial] using hb

/-- The target covers arbitrary physical placements and arbitrary Euclidean symmetries. -/
theorem T7_finite_full_symmetry_bound_of_contact_classification
    (hclassify : ∀ p : Pose 7, IndexedData7.geometry.LegalContact p → p ∈ M7) :
    ∀ tiles, IsTiling T7 tiles →
      Finite (EuclideanSymmetries tiles) ∧ Nat.card (EuclideanSymmetries tiles) ≤ 645120 := by
  intro tiles ht
  exact ⟨T7_finite_euclidean_symmetries_of_contact_classification hclassify ht,
    T7_euclidean_symmetry_card_le_645120_of_contact_classification hclassify ht⟩

#print axioms IsEuclideanSymmetry
#print axioms EuclideanSymmetries
#print axioms IsEuclideanSymmetry.symm
#print axioms IsEuclideanSymmetry.trans
#print axioms T7_exists_other_tile
#print axioms T7_relative_frames_registered
#print axioms T7_symmetry_registered_in_root
#print axioms symmetry_eq_of_equal_displacements
#print axioms displacements_equal_of_conjugate_pose_orientation
#print axioms T7_symmetries_embed_signed_permutations_of_contact_classification
#print axioms T7_finite_euclidean_symmetries_of_contact_classification
#print axioms T7_euclidean_symmetry_card_le_645120_of_contact_classification
#print axioms T7_finite_full_symmetry_bound_of_contact_classification
end SparseMonotiles
