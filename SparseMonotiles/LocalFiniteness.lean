module

public import SparseMonotiles.Model

@[expose] public section

/-!
Local finiteness is a consequence of boundedness and a positive inball, not an
extra hypothesis on a tiling. The packing argument allows arbitrary isometries,
including reflections. The auxiliary statements work in any proper metric space.
-/

namespace SparseMonotiles

open Metric Set

/-- A bounded family of uniformly separated points has only finitely many indices.
The separation is on indices, so repeated points cannot hide an infinite family. -/
theorem finite_of_isBounded_separated {X ι : Type*} [MetricSpace X] [ProperSpace X]
    {s : Set ι} {f : ι → X} {r : ℝ} (hr : 0 < r)
    (hb : Bornology.IsBounded (f '' s))
    (hsep : s.Pairwise fun i j => r ≤ dist (f i) (f j)) : s.Finite := by
  obtain ⟨t, _, ht, hcover⟩ := hb.isCompact_closure.finite_cover_balls (half_pos hr)
  have hfiber : ∀ c : X, (s ∩ f ⁻¹' ball c (r / 2)).Finite := by
    intro c
    apply Set.Subsingleton.finite
    intro i hi j hj
    by_contra hij
    have hdist := dist_triangle (f i) c (f j)
    have hi' : dist (f i) c < r / 2 := hi.2
    have hj' : dist c (f j) < r / 2 := by
      have hj'' : dist (f j) c < r / 2 := hj.2
      simpa only [dist_comm] using hj''
    have hsep' := hsep hi.1 hj.1 hij
    linarith
  apply (ht.biUnion fun c _ => hfiber c).subset
  intro i hi
  have hc := hcover (subset_closure (mem_image_of_mem f hi))
  rcases mem_iUnion.mp hc with ⟨c, hc⟩
  rcases mem_iUnion.mp hc with ⟨hct, hic⟩
  exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hct, hi, hic⟩⟩

/-- Copies of a bounded body with disjoint interiors can meet a bounded test set
only finitely often, provided the body contains an open ball of positive radius. -/
theorem finite_intersect_of_pairwise_disjoint_isometric_copies
    {X ι : Type*} [MetricSpace X] [ProperSpace X]
    {T K : Set X} {p : X} {r : ℝ}
    (hT : Bornology.IsBounded T) (hr : 0 < r) (hball : ball p r ⊆ T)
    (g : ι → X ≃ᵢ X)
    (hdisj : Pairwise fun i j => Disjoint (interior (g i '' T)) (interior (g j '' T)))
    (hK : Bornology.IsBounded K) :
    {i | ((g i '' T) ∩ K).Nonempty}.Finite := by
  have hp : p ∈ T := hball (mem_ball_self hr)
  have hballs : ∀ i, ball (g i p) r ⊆ interior (g i '' T) := by
    intro i
    apply interior_maximal ?_ isOpen_ball
    rw [← (g i).image_ball p r]
    exact image_mono hball
  have hsep : Pairwise fun i j => r ≤ dist (g i p) (g j p) := by
    intro i j hij
    by_contra h
    have hij' : g i p ∈ ball (g j p) r := lt_of_not_ge h
    exact (Set.disjoint_left.mp (hdisj hij))
      (hballs i (mem_ball_self hr)) (hballs j hij')
  obtain ⟨R, hR⟩ := hK.subset_closedBall p
  have hbound : Bornology.IsBounded
      ((fun i => g i p) '' {i | ((g i '' T) ∩ K).Nonempty}) := by
    apply (isBounded_closedBall (x := p) (r := diam T + R)).subset
    rintro _ ⟨i, ⟨x, hxT, hxK⟩, rfl⟩
    rcases hxT with ⟨y, hy, rfl⟩
    have hd : dist (g i p) (g i y) ≤ diam T := by
      rw [(g i).dist_eq]
      exact dist_le_diam_of_mem hT hp hy
    have hk : dist (g i y) p ≤ R := hR hxK
    exact (dist_triangle (g i p) (g i y) p).trans (add_le_add hd hk)
  exact finite_of_isBounded_separated hr hbound fun _ hi _ hj hij => hsep hij

/-- Finite intersection with bounded sets for the exact unmarked tiling model.
No choice of orientation, lattice registration, or local finiteness is assumed. -/
theorem IsTiling.finite_intersect_of_isBounded {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hT : IsCompact T)
    {p : Point d} {r : ℝ} (hr : 0 < r) (hball : ball p r ⊆ T)
    {K : Set (Point d)} (hK : Bornology.IsBounded K) :
    {A | A ∈ tiles ∧ (A ∩ K).Nonempty}.Finite := by
  classical
  choose g hg using (fun A : tiles => ht.1 A A.property)
  have hdisj : Pairwise fun A B : tiles =>
      Disjoint (interior (g A '' T)) (interior (g B '' T)) := by
    intro A B hAB
    rw [← hg A, ← hg B]
    exact ht.2.2 A A.property B B.property (fun h => hAB (Subtype.ext h))
  have hf := finite_intersect_of_pairwise_disjoint_isometric_copies
    hT.isBounded hr hball g hdisj hK
  have heq : {A | A ∈ tiles ∧ (A ∩ K).Nonempty} =
      Subtype.val '' {A : tiles | ((g A '' T) ∩ K).Nonempty} := by
    ext A
    constructor
    · rintro ⟨hA, hAK⟩
      refine ⟨⟨A, hA⟩, ?_, rfl⟩
      change ((g ⟨A, hA⟩ '' T) ∩ K).Nonempty
      simpa only [← hg] using hAK
    · rintro ⟨A, hA, rfl⟩
      change ((g A '' T) ∩ K).Nonempty at hA
      exact ⟨A.property, by simpa only [hg A] using hA⟩
  rw [heq]
  exact hf.image Subtype.val

/-- The usual topological local-finiteness conclusion, with physical tiles as indices. -/
theorem IsTiling.locallyFinite {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hT : IsCompact T)
    {p : Point d} {r : ℝ} (hr : 0 < r) (hball : ball p r ⊆ T) :
    LocallyFinite (fun A : tiles => (A : Set (Point d))) := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
  have hf := ht.finite_intersect_of_isBounded hT hr hball
    (isBounded_ball (x := x) (r := 1))
  exact (hf.preimage Subtype.val_injective.injOn).subset fun A hA => ⟨A.property, hA⟩

end SparseMonotiles
