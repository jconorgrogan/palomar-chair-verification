module

public import LiteralPlanar.WholeArcRegistration
public import SpectreGeometry.DeformationHomeomorphismRigidity

@[expose] public section


/-! Orientation is the determinant of the unrestricted physical isometry.
The edge charts are proved positive, so opposite physical handedness gives
finite contact for every pair of actual polynomial boundary arcs. -/
namespace LiteralPlanar
noncomputable section
open SpectreGeometry SpectreGeometry.Deformation

def orientationDet (f : EPlane ≃ᵢ EPlane) : ℝ :=
  RealPoint.det (frameFirst f) (frameSecond f)

theorem coordinateAction_linear_frame (f : EPlane ≃ᵢ EPlane) (x : RealPoint) :
    coordinateAction f x = x.1 • frameFirst f + x.2 • frameSecond f := by
  have hx : x = x.1 • ((1,0) : RealPoint) + x.2 • (0,1) := by
    apply Prod.ext <;> simp
  conv_lhs => rw [hx,map_add,map_smul,map_smul]
  rfl

theorem coordinateAction_det (f : EPlane ≃ᵢ EPlane) (x y : RealPoint) :
    RealPoint.det (coordinateAction f x) (coordinateAction f y) =
      orientationDet f * RealPoint.det x y := by
  rw [coordinateAction_linear_frame,coordinateAction_linear_frame]
  simp only [orientationDet,RealPoint.det,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem orientationDet_trans (f g : EPlane ≃ᵢ EPlane) :
    orientationDet (f.trans g) = orientationDet g * orientationDet f := by
  unfold orientationDet frameFirst frameSecond
  rw [coordinateAction_trans,coordinateAction_trans,coordinateAction_det]
  rfl

theorem orientationDet_sign (f : EPlane ≃ᵢ EPlane) :
    orientationDet f = 1 ∨ orientationDet f = -1 := by
  have hs := Quintic.frame_determinant_squared f
  change orientationDet f ^ 2 = 1 at hs
  have hz : (orientationDet f-1)*(orientationDet f+1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem opposite_orientation_relative (f g : EPlane ≃ᵢ EPlane)
    (hfg : orientationDet f ≠ orientationDet g) :
    orientationDet (f.trans g.symm) = -1 := by
  have hh : (f.trans g.symm).trans g = f := by ext x; simp
  have he := orientationDet_trans (f.trans g.symm) g
  rw [hh] at he
  rcases orientationDet_sign f with hf | hf <;>
    rcases orientationDet_sign g with hg | hg
  · exact (hfg (hf.trans hg.symm)).elim
  · rw [hf,hg] at he
    linarith
  · rw [hf,hg] at he
    linarith
  · exact (hfg (hf.trans hg.symm)).elim

theorem same_orientation_relative_direct (f g : EPlane ≃ᵢ EPlane)
    (hfg : orientationDet f = orientationDet g) : DirectPlacement (f.trans g.symm) := by
  have hh : (f.trans g.symm).trans g = f := by ext x; simp
  have he := orientationDet_trans (f.trans g.symm) g
  rw [hh,hfg] at he
  change 0 < orientationDet (f.trans g.symm)
  rcases orientationDet_sign g with hg | hg <;> rw [hg] at he <;> nlinarith

namespace Candidate

theorem edgeChart_coordinateAction (e : Fin 14) (x : RealPoint) :
    coordinateAction (edgeChart e) x = x.1 • realEdge e + x.2 • quarterTurn (realEdge e) := by
  have h := coordinateAction_sub (edgeChart e) 0 x
  rw [sub_zero,edgeChart_apply,edgeChart_apply,Homeomorph.symm_apply_apply,
    Homeomorph.symm_apply_apply] at h
  simp only [Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero] at h
  rw [h]
  abel

theorem orientationDet_edgeChart (e : Fin 14) : orientationDet (edgeChart e) = 1 := by
  unfold orientationDet frameFirst frameSecond
  rw [edgeChart_coordinateAction,edgeChart_coordinateAction]
  simpa only [Prod.fst,Prod.snd,one_smul,zero_smul,zero_add,add_zero,
    RealPoint.det,quarterTurn,neg_mul_neg,mul_neg,sub_neg_eq_add,RealPoint.dot] using real_edges_unit_squared e

theorem opposite_placed_edgeArcs_contact_finite (f g : EPlane ≃ᵢ EPlane)
    (hfg : orientationDet f ≠ orientationDet g) (e j : Fin 14) :
    (f '' euclideanArc e ∩ g '' euclideanArc j).Finite := by
  let F := (edgeChart e).trans f
  let G := (edgeChart j).trans g
  have hd : orientationDet F ≠ orientationDet G := by
    simpa only [F,G,orientationDet_trans,orientationDet_edgeChart,mul_one] using hfg
  have hi := Quintic.improper_standardArc_contact_finite Quintic.amplitude
    (by norm_num [Quintic.amplitude]) (F.trans G.symm) (opposite_orientation_relative F G hd)
  rw [←Quintic.inverse_image_inter] at hi
  have hfin : (F '' Quintic.standardArc Quintic.amplitude ∩
      G '' Quintic.standardArc Quintic.amplitude).Finite := by
    apply (hi.image G).subset
    intro x hx
    exact ⟨G.symm x,⟨x,hx,rfl⟩,G.apply_symm_apply x⟩
  have himage (q : EPlane ≃ᵢ EPlane) (k : Fin 14) :
      q '' euclideanArc k = (edgeChart k |>.trans q) '' Quintic.standardArc Quintic.amplitude := by
    rw [euclideanArc_eq_chart_image,Set.image_image]
    rfl
  rw [himage,himage]
  exact hfin

end Candidate
end
end LiteralPlanar
