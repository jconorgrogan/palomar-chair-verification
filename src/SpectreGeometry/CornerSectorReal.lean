module

public import SpectreGeometry.CornerNeighborhood
public import SpectreGeometry.CornerSignData

@[expose] public section


/-! Binding the exact twelve-sector corner catalogue to actual sufficiently
small rays in the interior of the polygon, including reflex corners. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem certified_nonnegative_iff (q : Quad3) (hq : Quad3.signCertified q) :
    Quad3.nonnegative q ↔ 0 ≤ Quad3.eval q := by
  constructor
  · rintro (hz | hp)
    · rw [hz]; norm_num [Quad3.eval]
    · exact (Quad3.positive_sound _ hp).le
  · intro he
    rcases hq with hz | hp | hn
    · exact Or.inl hz
    · exact Or.inr hp
    · have hh := Quad3.positive_sound _ hn
      rw [Quad3.eval_sub] at hh
      have h0 : Quad3.eval (0,0) = 0 := by norm_num [Quad3.eval]
      rw [h0] at hh
      linarith

theorem certified_nonpositive_iff (q : Quad3) (hq : Quad3.signCertified q) :
    Quad3.nonpositive q ↔ Quad3.eval q ≤ 0 := by
  constructor
  · exact nonpositive_real_sound q
  · intro he
    rcases hq with hz | hp | hn
    · exact Or.inl hz
    · exact False.elim ((not_lt_of_ge he) (Quad3.positive_sound _ hp))
    · exact Or.inr hn

theorem certified_eval_ne_zero (q : Quad3) (hq : Quad3.signCertified q) (hn : q ≠ (0,0)) :
    Quad3.eval q ≠ 0 := by
  intro hz
  rcases hq with he | hp | hm
  · exact hn he
  · have hp' := Quad3.positive_sound _ hp
    linarith
  · have hm' := Quad3.positive_sound _ hm
    rw [Quad3.eval_sub,hz] at hm'
    norm_num [Quad3.eval] at hm'

def cornerRay (i : Fin 14) (d : Fin 12) (t : ℝ) : RealPoint :=
  realVertex i+t • realize (sectorVector d)

theorem side_add_ray (a b x v : RealPoint) (t : ℝ) :
    side a b (x+t • v) = side a b x+t*RealPoint.det (RealPoint.sub b a) v := by
  simp only [side,RealPoint.det,RealPoint.sub,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem cornerRay_side_values (i : Fin 14) (d : Fin 12) (t : ℝ) :
    side (realVertex (previous i)) (realVertex i) (cornerRay i d t) =
      t*(Quad3.eval (ExactPoint.det (edge (previous i)) (sectorVector d))/4) ∧
    radialSide i (cornerRay i d t) =
      t*(Quad3.eval (ExactPoint.det (radialVector i) (sectorVector d))/4) ∧
    side (realVertex i) (realVertex (next i)) (cornerRay i d t) =
      t*(Quad3.eval (ExactPoint.det (edge i) (sectorVector d))/4) := by
  have hp : RealPoint.sub (realVertex i) (realVertex (previous i)) = realize (edge (previous i)) := by
    rw [realize_edge]
    unfold realEdge
    rw [next_previous]
  have hr : RealPoint.sub (realVertex i) realFanCenter = realize (radialVector i) := by
    unfold radialVector realFanCenter realVertex
    rw [realize_sub]
  have hn : RealPoint.sub (realVertex (next i)) (realVertex i) = realize (edge i) := (realize_edge i).symm
  constructor
  · rw [cornerRay,side_add_ray,side_self_right,hp,realize_det,zero_add]
  · constructor
    · unfold radialSide
      rw [cornerRay,side_add_ray,side_self_right,hr,realize_det,zero_add]
    · rw [cornerRay,side_add_ray,side_self_left,hn,realize_det,zero_add]

theorem positive_scale_nonnegative (q : Quad3) (hq : Quad3.signCertified q)
    (t : ℝ) (ht : 0 < t) : 0 ≤ t*(Quad3.eval q/4) ↔ Quad3.nonnegative q := by
  have hh : t*(Quad3.eval q/4) = (t/4)*Quad3.eval q := by ring
  rw [hh,mul_nonneg_iff_of_pos_left (by positivity : 0 < t/4)]
  exact (certified_nonnegative_iff q hq).symm

theorem positive_scale_nonpositive (q : Quad3) (hq : Quad3.signCertified q)
    (t : ℝ) (ht : 0 < t) : t*(Quad3.eval q/4) ≤ 0 ↔ Quad3.nonpositive q := by
  have hh : t*(Quad3.eval q/4) = (t/4)*Quad3.eval q := by ring
  rw [hh,certified_nonpositive_iff q hq]
  constructor
  · intro h
    exact nonpos_of_mul_nonpos_right h (by positivity)
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h

theorem cornerRay_body_condition (i : Fin 14) (d : Fin 12) (t : ℝ) (ht : 0 < t) :
    cornerBodyCondition i (cornerRay i d t) ↔ cornerSector i d := by
  obtain ⟨hp,hr,hn⟩ := cornerRay_side_values i d t
  obtain ⟨hsp,hsr,hsn⟩ := sector_side_signs i d
  unfold cornerBodyCondition cornerSector
  rw [hp,hr,hn,positive_scale_nonnegative _ hsp t ht,
    positive_scale_nonpositive _ hsr t ht,positive_scale_nonnegative _ hsr t ht,
    positive_scale_nonnegative _ hsn t ht]

theorem cornerRay_off_lines (i : Fin 14) (d : Fin 12) (t : ℝ) (ht : 0 < t) :
    side (realVertex (previous i)) (realVertex i) (cornerRay i d t) ≠ 0 ∧
    side (realVertex i) (realVertex (next i)) (cornerRay i d t) ≠ 0 := by
  obtain ⟨hp,hr,hn⟩ := cornerRay_side_values i d t
  obtain ⟨hsp,hsr,hsn⟩ := sector_side_signs i d
  rw [hp,hn]
  exact ⟨mul_ne_zero ht.ne' (div_ne_zero (certified_eval_ne_zero _ hsp (sector_vector_off_edge (previous i) d)) (by norm_num)),
    mul_ne_zero ht.ne' (div_ne_zero (certified_eval_ne_zero _ hsn (sector_vector_off_edge i d)) (by norm_num))⟩

/-- The finite sector predicate is exactly the actual interior germ along
its open sector sample, for all sufficiently small positive distances. -/
theorem cornerSector_actual_germ (i : Fin 14) (d : Fin 12) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (cornerRay i d t ∈ interior polygonBody ↔ cornerSector i d) := by
  obtain ⟨U,hU,hi,hh⟩ := vertex_local_interior_off_lines i
  have hc : Continuous (cornerRay i d) := by unfold cornerRay; fun_prop
  have h0 : cornerRay i d 0 ∈ U := by simpa [cornerRay] using hi
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hU.preimage hc) 0 h0
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ
  have hmem : t ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htδ
  have hr := cornerRay_off_lines i d t ht
  exact (hh _ (hball hmem) hr.1 hr.2).trans (cornerRay_body_condition i d t ht)

end
end SpectreGeometry
