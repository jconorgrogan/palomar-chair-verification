module

public import PhysicalRegistration.KeyHypograph

@[expose] public section

/-!
Literal finite tube replacement and local transfer for keyed chairs.
The set operation is exact. Its application to the native chair must prove
the explicit separation and carrier-halfspace hypotheses stated below.
-/

namespace PhysicalRegistration
open scoped InnerProductSpace
open Set

variable {X : Type*} [TopologicalSpace X] {κ : Type*}

def replaceTubes (carrier : Set X) (tube hypograph : κ → Set X) : Set X :=
  (carrier \ ⋃ i, interior (tube i)) ∪ ⋃ i, (tube i ∩ hypograph i)

/-- Local tube replacement is exactly the chosen hypograph wherever all
other tubes are absent and its unchanged boundary agrees with the carrier. -/
theorem replaceTubes_local_iff (carrier : Set X) (tube hypograph : κ → Set X)
    (i : κ) (U : Set X)
    (hother : ∀ j, j ≠ i → Disjoint U (tube j))
    (hboundary : ∀ x ∈ U, x ∉ interior (tube i) →
      (x ∈ carrier ↔ x ∈ hypograph i)) :
    ∀ x ∈ U, x ∈ replaceTubes carrier tube hypograph ↔ x ∈ hypograph i := by
  classical
  intro x hxU
  have hnotother : ∀ j, j ≠ i → x ∉ tube j := by
    intro j hji hxj
    exact Set.disjoint_left.mp (hother j hji) hxU hxj
  constructor
  · intro hx
    rcases hx with ⟨hxC, hxNot⟩ | hxPiece
    · have hnoti : x ∉ interior (tube i) :=
        fun hxI => hxNot (mem_iUnion.mpr ⟨i, hxI⟩)
      exact (hboundary x hxU hnoti).mp hxC
    · obtain ⟨j, hxj, hxHj⟩ := mem_iUnion.mp hxPiece
      by_cases hji : j = i
      · simpa [hji] using hxHj
      · exact (hnotother j hji hxj).elim
  · intro hxH
    by_cases hxI : x ∈ interior (tube i)
    · exact Or.inr (mem_iUnion.mpr ⟨i, interior_subset hxI, hxH⟩)
    · apply Or.inl
      refine ⟨(hboundary x hxU hxI).mpr hxH, ?_⟩
      intro hxUnion
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxUnion
      by_cases hji : j = i
      · exact hxI (hji ▸ hxj)
      · exact hnotother j hji (interior_subset hxj)

theorem replaceTubes_mem_of_untouched (carrier : Set X) (tube hypograph : κ → Set X)
    {x : X} (hx : x ∈ carrier) (h : ∀ i, x ∉ interior (tube i)) :
    x ∈ replaceTubes carrier tube hypograph :=
  Or.inl ⟨hx, fun hxU => by obtain ⟨i, hi⟩ := mem_iUnion.mp hxU; exact h i hi⟩

/-- Finite separated closed tubes provide an actual open neighborhood avoiding
every other tube, including at boundary points of the selected tube. -/
theorem exists_isolating_open_tube [Finite κ] (tube : κ → Set X)
    (hclosed : ∀ i, IsClosed (tube i))
    (hdisjoint : Pairwise fun i j => Disjoint (tube i) (tube j))
    (i : κ) {x : X} (hx : x ∈ tube i) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ j, j ≠ i → Disjoint U (tube j) := by
  classical
  let V : Set X := ⋃ j : {j : κ // j ≠ i}, tube j.val
  have hV : IsClosed V := isClosed_iUnion_of_finite fun j => hclosed j.val
  refine ⟨Vᶜ, hV.isOpen_compl, ?_, ?_⟩
  · intro hxV
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxV
    exact Set.disjoint_left.mp (hdisjoint (Ne.symm j.property)) hx hxj
  · intro j hji
    apply Set.disjoint_left.mpr
    intro y hyV hyj
    exact hyV (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)

theorem replaceTubes_isClosed [Finite κ] (carrier : Set X) (tube hypograph : κ → Set X)
    (hC : IsClosed carrier) (hT : ∀ i, IsClosed (tube i))
    (hH : ∀ i, IsClosed (hypograph i)) :
    IsClosed (replaceTubes carrier tube hypograph) := by
  apply IsClosed.union
  · exact hC.inter (isOpen_iUnion (fun i => isOpen_interior)).isClosed_compl
  · exact isClosed_iUnion_of_finite fun i => (hT i).inter (hH i)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restrict a proved local inward chart to an open neighborhood on which two
actual sets agree. The smaller radius is constructed explicitly. -/
noncomputable def LocalLipschitzGraphAt.transfer
    {S T : Set E} {x : E} {L : ℝ} (G : LocalLipschitzGraphAt S x L)
    (U : Set E) (hU : IsOpen U) (hxU : x ∈ U)
    (heq : ∀ y ∈ U, y ∈ S ↔ y ∈ T) :
    LocalLipschitzGraphAt T x L := by
  let hexists := Metric.isOpen_iff.mp hU x hxU
  let eps := Classical.choose hexists
  have heps : 0 < eps := (Classical.choose_spec hexists).1
  have hball : Metric.ball x eps ⊆ U := (Classical.choose_spec hexists).2
  let r := min G.radius (eps / 3)
  have hr : 0 < r := lt_min G.radius_pos (by positivity)
  refine {
    inward := G.inward
    inward_unit := G.inward_unit
    radius := r
    radius_pos := hr
    height := G.height
    height_zero := G.height_zero
    height_lipschitz := ?_
    interior_above := ?_
  }
  · intro v w hv hw hvr hwr
    exact G.height_lipschitz v w hv hw
      (hvr.trans_le (min_le_left _ _)) (hwr.trans_le (min_le_left _ _))
  · intro v s hv hvr hsr hs
    have hyS := G.interior_above v s hv (hvr.trans_le (min_le_left _ _))
      (hsr.trans_le (min_le_left _ _)) hs
    have hyU : x + v + s • G.inward ∈ U := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hid : x + v + s • G.inward - x = v + s • G.inward := by abel
      rw [hid]
      have htri := norm_add_le v (s • G.inward)
      rw [norm_smul, Real.norm_eq_abs, G.inward_unit, mul_one] at htri
      have hrle : r ≤ eps / 3 := min_le_right _ _
      linarith
    have hsubset : interior S ∩ U ⊆ T := by
      intro y hy
      exact (heq y hy.2).mp (interior_subset hy.1)
    exact interior_maximal hsubset (isOpen_interior.inter hU) ⟨hyS, hyU⟩

noncomputable def replaceTubes_local_graph (carrier : Set E) (tube hypograph : κ → Set E)
    (i : κ) {x : E} {L : ℝ} (G : LocalLipschitzGraphAt (hypograph i) x L)
    (U : Set E) (hU : IsOpen U) (hxU : x ∈ U)
    (hother : ∀ j, j ≠ i → Disjoint U (tube j))
    (hboundary : ∀ y ∈ U, y ∉ interior (tube i) →
      (y ∈ carrier ↔ y ∈ hypograph i)) :
    LocalLipschitzGraphAt (replaceTubes carrier tube hypograph) x L :=
  G.transfer U hU hxU
    (fun y hy => (replaceTubes_local_iff carrier tube hypograph i U hother hboundary y hy).symm)

#print axioms replaceTubes_local_iff
#print axioms exists_isolating_open_tube
#print axioms replaceTubes_isClosed
#print axioms LocalLipschitzGraphAt.transfer
#print axioms replaceTubes_local_graph
end PhysicalRegistration
