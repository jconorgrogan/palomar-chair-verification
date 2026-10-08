module

public import SparseMonotiles.GenericRidgePoints
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# A thin key side face cannot contain a whole open carrier strip

All topology is intrinsic to the supporting plane of the key side face.
The side face is a finite affine-inequality intersection. Pairwise active
crease equations are removed using their codimension-two rank bounds.
An open convex strip meeting both sides must therefore meet a relative-open
crease, and the crossing can be selected generic for every neighboring plane.
No tiling companion, face-to-face property, or sector partition is assumed.
-/
namespace SparseMonotiles
open Set

section Topology
variable {X : Type*} [TopologicalSpace X]

/-- A connected set meeting the interior and exterior of a closed set must
meet its boundary. -/
theorem preconnected_exists_frontier {O F : Set X} (hO : IsPreconnected O)
    (hF : IsClosed F) (hin : (O ∩ interior F).Nonempty)
    (hout : (O ∩ Fᶜ).Nonempty) : (O ∩ frontier F).Nonempty := by
  by_contra h
  have hcover : O ⊆ interior F ∪ Fᶜ := by
    intro x hx
    by_cases hxF : x ∈ F
    · left
      by_contra hxi
      exact h ⟨x,hx,by rw [hF.frontier_eq]; exact ⟨hxF,hxi⟩⟩
    · exact Or.inr hxF
  obtain ⟨x, _, hxi, hxF⟩ := hO _ _ isOpen_interior hF.isOpen_compl hcover hin hout
  exact hxF (interior_subset hxi)
end Topology

section Crossing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Boundary crossing after deleting countably many codimension-two affine
exceptions. The interior and exterior starting points need not be generic. -/
theorem open_convex_exists_frontier_avoiding {κ : Type*} [Countable κ]
    {O F : Set E} (hO : IsOpen O) (hconv : Convex ℝ O) (hF : IsClosed F)
    (L : κ → AffineSubspace ℝ E)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 2 ≤ Module.finrank ℝ E)
    (hin : (O ∩ interior F).Nonempty) (hout : (O ∩ Fᶜ).Nonempty) :
    ∃ x ∈ O ∩ frontier F, ∀ i, x ∉ L i := by
  have hd := affineSubspaces_dense_avoid L
    (fun i => affineSubspace_ne_top_of_codim_two (L i) (hL i))
  obtain ⟨p,hp,hpL⟩ := hd.inter_open_nonempty _ (hO.inter isOpen_interior) hin
  obtain ⟨q,hq,hqL⟩ := hd.inter_open_nonempty _ (hO.inter hF.isOpen_compl) hout
  change ∀ i, p ∉ L i at hpL
  change ∀ i, q ∉ L i at hqL
  have hp' : p ∈ O \ ⋃ i, (L i : Set E) := by
    exact ⟨hp.1,by simpa only [mem_iUnion,not_exists,SetLike.mem_coe] using hpL⟩
  have hq' : q ∈ O \ ⋃ i, (L i : Set E) := by
    exact ⟨hq.1,by simpa only [mem_iUnion,not_exists,SetLike.mem_coe] using hqL⟩
  have hc := (isConnected_diff_affineSubspaces hO hconv ⟨p,hp.1⟩ L hL).isPreconnected
  obtain ⟨x,hx,hxf⟩ := preconnected_exists_frontier hc hF ⟨p,hp',hp.2⟩ ⟨q,hq',hq.2⟩
  refine ⟨x,⟨hx.1,hxf⟩,?_⟩
  simpa only [mem_iUnion,not_exists,SetLike.mem_coe] using hx.2

/-- A width-`r` unit ray from an interior point meets both the interior and
exterior of any bounded side face of diameter less than `r`. Thus the strip
crossing premises follow from the exact diameter estimate rather than being
postulated. The ray starts on the seam; the strip itself excludes its start. -/
theorem unit_ray_meets_interior_exterior {O F : Set E} {p u : E} {r : ℝ}
    (hr : 0 < r) (hp : p ∈ interior F) (hu : ‖u‖ = 1)
    (hbounded : Bornology.IsBounded F) (hdiam : Metric.diam F < r)
    (hray : ∀ t : ℝ, 0 < t → t < r → p + t • u ∈ O) :
    (O ∩ interior F).Nonempty ∧ (O ∩ Fᶜ).Nonempty := by
  have hdist (t : ℝ) (ht : 0 < t) : dist (p + t • u) p = t := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,hu,mul_one,
      Real.norm_eq_abs,abs_of_pos ht]
  constructor
  · obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
    let t := min ε r / 2
    have ht : 0 < t := half_pos (lt_min hε hr)
    have htmin : t < min ε r := half_lt_self (lt_min hε hr)
    refine ⟨p+t•u,hray t ht (htmin.trans_le (min_le_right _ _)),?_⟩
    apply hball
    rw [Metric.mem_ball,hdist t ht]
    exact htmin.trans_le (min_le_left _ _)
  · let t := (Metric.diam F+r)/2
    have ht : 0 < t := by dsimp [t]; linarith [Metric.diam_nonneg (s := F)]
    have htr : t < r := by dsimp [t]; linarith
    have hdt : Metric.diam F < t := by dsimp [t]; linarith
    refine ⟨p+t•u,hray t ht htr,?_⟩
    intro hx
    have hb := Metric.dist_le_diam_of_mem hbounded hx (interior_subset hp)
    rw [hdist t ht] at hb
    exact not_le_of_gt hdt hb

/-- Finite closed affine inequalities in the intrinsic side-face chart. -/
def closedAffineRegion {ι : Type*} (f : ι → E →ᵃ[ℝ] ℝ) : Set E :=
  {x | ∀ i, 0 ≤ f i x}

/-- Strict inequalities give an interior point; no irredundancy assumption. -/
theorem mem_interior_closedAffineRegion_of_pos {ι : Type*} [Finite ι]
    (f : ι → E →ᵃ[ℝ] ℝ) (hf : ∀ i, Continuous (f i)) {x : E}
    (hx : ∀ i, 0 < f i x) : x ∈ interior (closedAffineRegion f) := by
  have hopen : IsOpen {y : E | ∀ i, 0 < f i y} :=
    by simpa only [setOf_forall] using
      isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hf i))
  apply interior_maximal (t := {y : E | ∀ i, 0 < f i y}) (s := closedAffineRegion f) _ hopen hx
  intro y hy i
  exact (hy i).le

/-- A boundary point outside the pairwise equation intersections has exactly
one active inequality, hence lies in the relative interior of a crease. -/
theorem open_convex_crosses_single_affine_crease {ι : Type*} [Fintype ι]
    (f : ι → E →ᵃ[ℝ] ℝ) (hf : ∀ i, Continuous (f i))
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O)
    (hrank : ∀ i j, i ≠ j →
      Module.finrank ℝ ((affineFormPlane (f i) 0 ⊓ affineFormPlane (f j) 0).direction) + 2
        ≤ Module.finrank ℝ E)
    (hin : (O ∩ interior (closedAffineRegion f)).Nonempty)
    (hout : (O ∩ (closedAffineRegion f)ᶜ).Nonempty) :
    ∃ i x, x ∈ O ∧ f i x = 0 ∧ ∀ j, j ≠ i → 0 < f j x := by
  classical
  let J := {ij : ι × ι // ij.1 ≠ ij.2}
  let L : J → AffineSubspace ℝ E := fun ij =>
    affineFormPlane (f ij.1.1) 0 ⊓ affineFormPlane (f ij.1.2) 0
  have hF : IsClosed (closedAffineRegion f) :=
    by simpa only [closedAffineRegion,setOf_forall] using
      isClosed_iInter (fun i => isClosed_le (continuous_const (y := (0 : ℝ))) (hf i))
  obtain ⟨x,hx,havoid⟩ := open_convex_exists_frontier_avoiding hO hconv hF L
    (fun ij => hrank _ _ ij.2) hin hout
  have hxF : x ∈ closedAffineRegion f := hF.frontier_subset hx.2
  have hactive : ∃ i, f i x = 0 := by
    by_contra h
    apply hx.2.2
    apply mem_interior_closedAffineRegion_of_pos f hf
    intro i
    exact lt_of_le_of_ne (hxF i) (fun he => h ⟨i,he.symm⟩)
  obtain ⟨i,hi⟩ := hactive
  refine ⟨i,x,hx.1,hi,?_⟩
  intro j hji
  apply lt_of_le_of_ne (hxF j)
  intro hzero
  apply havoid ⟨(i,j),Ne.symm hji⟩
  exact ⟨(mem_affineFormPlane _ _ _).mpr hi,
    (mem_affineFormPlane _ _ _).mpr hzero.symm⟩

/-- The strip meets a crease at a point generic for every plane in an
arbitrary countable inventory. The final containment is exactly the generic
active-plane premise used by the physical normal-cone partition. -/
theorem open_convex_crosses_generic_affine_crease
    {ι κ : Type*} [Fintype ι] [Countable κ]
    (f : ι → E →ᵃ[ℝ] ℝ) (hf : ∀ i, Continuous (f i))
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O)
    (hrank : ∀ i j, i ≠ j →
      Module.finrank ℝ ((affineFormPlane (f i) 0 ⊓ affineFormPlane (f j) 0).direction) + 2
        ≤ Module.finrank ℝ E)
    (hin : (O ∩ interior (closedAffineRegion f)).Nonempty)
    (hout : (O ∩ (closedAffineRegion f)ᶜ).Nonempty)
    (H : κ → AffineSubspace ℝ E) :
    ∃ i x, x ∈ O ∧ f i x = 0 ∧ (∀ j, j ≠ i → 0 < f j x) ∧
      ∀ k, x ∈ H k → affineFormPlane (f i) 0 ≤ H k := by
  obtain ⟨i,x,hx,hi,hstrict⟩ := open_convex_crosses_single_affine_crease f hf
    hO hconv hrank hin hout
  let R := affineFormPlane (f i) 0
  have hxR : x ∈ R := (mem_affineFormPlane _ _ _).mpr hi
  let U : Set R := {y | (y : E) ∈ O ∧ ∀ j, j ≠ i → 0 < f j y}
  have hstrictOpen : IsOpen {y : R | ∀ j, j ≠ i → 0 < f j y} := by
    simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const ((hf j).comp continuous_subtype_val)
  have hU : IsOpen U := (hO.preimage continuous_subtype_val).inter hstrictOpen
  obtain ⟨y,hy,hygeneric⟩ := exists_genericRidgePoint_in_open R ⟨x,hxR⟩ H hU
    ⟨⟨x,hxR⟩,hx,hstrict⟩
  exact ⟨i,y,hy.1,(mem_affineFormPlane _ _ _).mp y.property,hy.2,hygeneric⟩

/-- Complete intrinsic strip-crossing statement with its interior/exterior
premises discharged by the exact thin-face diameter estimate. -/
theorem unit_strip_crosses_generic_affine_crease
    {ι κ : Type*} [Fintype ι] [Countable κ]
    (f : ι → E →ᵃ[ℝ] ℝ) (hf : ∀ i, Continuous (f i))
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O)
    (hrank : ∀ i j, i ≠ j →
      Module.finrank ℝ ((affineFormPlane (f i) 0 ⊓ affineFormPlane (f j) 0).direction) + 2
        ≤ Module.finrank ℝ E)
    {p u : E} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ interior (closedAffineRegion f)) (hu : ‖u‖ = 1)
    (hbounded : Bornology.IsBounded (closedAffineRegion f))
    (hdiam : Metric.diam (closedAffineRegion f) < r)
    (hray : ∀ t : ℝ, 0 < t → t < r → p + t • u ∈ O)
    (H : κ → AffineSubspace ℝ E) :
    ∃ i x, x ∈ O ∧ f i x = 0 ∧ (∀ j, j ≠ i → 0 < f j x) ∧
      ∀ k, x ∈ H k → affineFormPlane (f i) 0 ≤ H k := by
  obtain ⟨hin,hout⟩ := unit_ray_meets_interior_exterior hr hp hu hbounded hdiam hray
  exact open_convex_crosses_generic_affine_crease f hf hO hconv hrank hin hout H

end Crossing

#print axioms unit_ray_meets_interior_exterior
#print axioms unit_strip_crosses_generic_affine_crease
#print axioms preconnected_exists_frontier
#print axioms open_convex_exists_frontier_avoiding
#print axioms open_convex_crosses_single_affine_crease
#print axioms open_convex_crosses_generic_affine_crease
end SparseMonotiles
