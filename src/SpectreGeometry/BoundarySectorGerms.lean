module

public import SpectreGeometry.CornerSectorReal
public import SpectreGeometry.EdgeSectorData
public import SpectreGeometry.BoundaryNonvertex

@[expose] public section


/-! Every actual boundary point has one of twenty-eight exact local sector
masks. The same mask characterizes closed-body and interior membership on
all sufficiently short rays strictly between the twelve edge directions. -/
namespace SpectreGeometry
noncomputable section
open Set

def sourceRay (x : RealPoint) (d : Fin 12) (t : ℝ) : RealPoint := x+t • realize (sectorVector d)
def BoundarySlotAt (b : BoundarySlot) (x : RealPoint) : Prop :=
  match b with
  | .inl i => x = realVertex i
  | .inr i => ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = interpolate (realVertex i) (realVertex (next i)) t

theorem frontier_has_slot (x : RealPoint) (hx : x ∈ frontier polygonBody) :
    ∃ b : BoundarySlot, BoundarySlotAt b x := by
  classical
  by_cases hv : ∃ i : Fin 14, x = realVertex i
  · obtain ⟨i,hi⟩ := hv
    exact ⟨.inl i,hi⟩
  · have hn : ∀ i : Fin 14, x ≠ realVertex i := by simpa using hv
    obtain ⟨i,t,ht,ht',he⟩ := frontier_nonvertex_strict_edge x hx hn
    exact ⟨.inr i,t,ht,ht',he⟩

theorem certified_positive_iff (q : Quad3) (hq : Quad3.signCertified q) :
    Quad3.positive q ↔ 0 < Quad3.eval q := by
  constructor
  · exact Quad3.positive_sound q
  · intro hp
    rcases hq with hz | hh | hn
    · rw [hz] at hp
      norm_num [Quad3.eval] at hp
    · exact hh
    · have he := Quad3.positive_sound _ hn
      rw [Quad3.eval_sub] at he
      have h0 : Quad3.eval (0,0) = 0 := by norm_num [Quad3.eval]
      rw [h0] at he
      linarith

theorem positive_scale_positive (q : Quad3) (hq : Quad3.signCertified q)
    (t : ℝ) (ht : 0 < t) : 0 < t*(Quad3.eval q/4) ↔ Quad3.positive q := by
  have hh : t*(Quad3.eval q/4) = (t/4)*Quad3.eval q := by ring
  rw [hh,mul_pos_iff_of_pos_left (by positivity : 0 < t/4)]
  exact (certified_positive_iff q hq).symm

theorem corner_closed_and_open_germ (i : Fin 14) (d : Fin 12) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (sourceRay (realVertex i) d t ∈ polygonBody ↔ cornerSector i d) ∧
      (sourceRay (realVertex i) d t ∈ interior polygonBody ↔ cornerSector i d) := by
  obtain ⟨U,hU,hi,hbody,hfront⟩ := vertex_local_body i
  have hc : Continuous (cornerRay i d) := by unfold cornerRay; fun_prop
  have h0 : cornerRay i d 0 ∈ U := by simpa [cornerRay] using hi
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (hU.preimage hc) 0 h0
  obtain ⟨s,hs,hI⟩ := cornerSector_actual_germ i d
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro t ht htδ
  have htr : t < r := lt_of_lt_of_le htδ (min_le_left _ _)
  have hts : t < s := lt_of_lt_of_le htδ (min_le_right _ _)
  have hmem : t ∈ Metric.ball (0 : ℝ) r := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htr
  exact ⟨(hbody _ (hball hmem)).trans (cornerRay_body_condition i d t ht),hI t ht hts⟩

theorem edge_closed_and_open_germ (i : Fin 14) (u : ℝ) (hu : 0 < u) (hu' : u < 1) (d : Fin 12) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (sourceRay (interpolate (realVertex i) (realVertex (next i)) u) d t ∈ polygonBody ↔ edgeSector i d) ∧
      (sourceRay (interpolate (realVertex i) (realVertex (next i)) u) d t ∈ interior polygonBody ↔ edgeSector i d) := by
  let x := interpolate (realVertex i) (realVertex (next i)) u
  obtain ⟨U,hU,hx,hlocal⟩ := outer_open_edge_local_halfplane i u hu hu'
  have hc : Continuous (sourceRay x d) := by unfold sourceRay; fun_prop
  have h0 : sourceRay x d 0 ∈ U := by simpa [sourceRay,x] using hx
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (hU.preimage hc) 0 h0
  have hsign := (sector_side_signs i d).2.2
  have hne := sector_vector_off_edge i d
  have hnp : Quad3.nonnegative (ExactPoint.det (edge i) (sectorVector d)) ↔ edgeSector i d := by
    constructor
    · rintro (hz | hp)
      · exact False.elim (hne hz)
      · exact hp
    · exact Or.inr
  refine ⟨r,hr,?_⟩
  intro t ht htr
  have hmem : t ∈ Metric.ball (0 : ℝ) r := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htr
  have hside : side (realVertex i) (realVertex (next i)) (sourceRay x d t) =
      t*(Quad3.eval (ExactPoint.det (edge i) (sectorVector d))/4) := by
    rw [sourceRay,side_add_ray]
    have hx0 : side (realVertex i) (realVertex (next i)) x = 0 := det_interpolate_self _ _ _
    rw [hx0,zero_add]
    change t*RealPoint.det (realEdge i) (realize (sectorVector d)) = _
    rw [←realize_edge,realize_det]
  have hbody := (hlocal _ (hball hmem)).1
  have hint := (hlocal _ (hball hmem)).2.1
  rw [hside,positive_scale_nonnegative _ hsign t ht,hnp] at hbody
  rw [hside,positive_scale_positive _ hsign t ht] at hint
  exact ⟨hbody,hint⟩

/-- Complete classification of actual boundary germs by literal sector
masks. The existence of a physical tiling is not assumed by this theorem. -/
theorem boundary_slot_actual_germ (b : BoundarySlot) (x : RealPoint) (hx : BoundarySlotAt b x)
    (d : Fin 12) : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (sourceRay x d t ∈ polygonBody ↔ slotSector b d) ∧
      (sourceRay x d t ∈ interior polygonBody ↔ slotSector b d) := by
  cases b with
  | inl i =>
      change x = realVertex i at hx
      subst x
      exact corner_closed_and_open_germ i d
  | inr i =>
      obtain ⟨u,hu,hu',rfl⟩ := hx
      exact edge_closed_and_open_germ i u hu hu' d

end
end SpectreGeometry
