module

public import SpectreGeometry.ReverseClusterTriangulationReal
public import SpectreGeometry.ReverseClusterTriangulationFacesData

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate
open scoped Topology

def integerVertexSet (vs : List Point) : Set RealPoint := integerPoint '' {p | p ∈ vs}

theorem constraint_nonpositive_zero_face (f : Constraint) (s face : Set RealPoint)
    (hs : ∀ x ∈ s, evalConstraint f x ≤ 0)
    (hf : ∀ x ∈ s, evalConstraint f x = 0 → x ∈ face)
    (x : RealPoint) (hx : x ∈ convexHull ℝ s) (hz : evalConstraint f x = 0) :
    x ∈ convexHull ℝ face := by
  let T : Set RealPoint := {y | evalConstraint f y ≤ 0 ∧
    (evalConstraint f y = 0 → y ∈ convexHull ℝ face)}
  have hsT : s ⊆ T := by
    intro y hy
    exact ⟨hs y hy,fun h => subset_convexHull ℝ face (hf y hy h)⟩
  have hconv : Convex ℝ T := by
    intro u hu v hv α β hα hβ hsum
    have hu' : evalConstraint f u ≤ 0 ∧ (evalConstraint f u = 0 → u ∈ convexHull ℝ face) := hu
    have hv' : evalConstraint f v ≤ 0 ∧ (evalConstraint f v = 0 → v ∈ convexHull ℝ face) := hv
    change evalConstraint f (α • u+β • v) ≤ 0 ∧ _
    rw [evalConstraint_combo f u v α β hsum]
    have hαu := mul_nonpos_of_nonneg_of_nonpos hα hu'.1
    have hβv := mul_nonpos_of_nonneg_of_nonpos hβ hv'.1
    refine ⟨add_nonpos hαu hβv,?_⟩
    intro hzero
    by_cases ha : α=0
    · have hb : β=1 := by linarith
      simpa [ha,hb] using hv'.2 (by simpa [ha,hb] using hzero)
    by_cases hb : β=0
    · have ha' : α=1 := by linarith
      simpa [ha',hb] using hu'.2 (by simpa [ha',hb] using hzero)
    have hzα : α*evalConstraint f u=0 := by linarith
    have hzβ : β*evalConstraint f v=0 := by linarith
    exact (convex_convexHull ℝ face) (hu'.2 ((mul_eq_zero.mp hzα).resolve_left ha))
      (hv'.2 ((mul_eq_zero.mp hzβ).resolve_left hb)) hα hβ hsum
  exact ((convexHull_min hsT hconv) hx).2 hz

theorem constraint_interior_pos (f : Constraint) (c : RealPoint)
    (hc : 0 < evalConstraint f c) (s : Set RealPoint)
    (hs : ∀ x ∈ s, 0 ≤ evalConstraint f x) (x : RealPoint)
    (hx : x ∈ interior s) : 0 < evalConstraint f x := by
  have hn := hs x (interior_subset hx)
  by_contra hnot
  have hz : evalConstraint f x=0 := by linarith
  let g : ℝ → RealPoint := fun t => x-t • (c-x)
  have hg : Continuous g := by unfold g; fun_prop
  have hg0 : g 0=x := by simp [g]
  have hevent : ∀ᶠ t in 𝓝 (0:ℝ), g t ∈ s := by
    have hh : g 0 ∈ interior s := hg0.symm ▸ hx
    exact hg.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.1 hh)
  obtain ⟨t,ht,hgt⟩ := hevent.exists_gt
  have h := hs (g t) hgt
  have he : evalConstraint f (g t) = (1+t)*evalConstraint f x-t*evalConstraint f c := by
    simp only [g,evalConstraint,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [he,hz] at h
  nlinarith

theorem supportsPacketFaceB_sound (p q : PolygonPacket) (f : Constraint)
    (hc : supportsPacketFaceB p q f = true) :
    integerHull p.vertices ∩ integerHull q.vertices =
        convexHull ℝ (integerVertexSet p.vertices ∩ integerVertexSet q.vertices) ∧
      Disjoint (interior (integerHull p.vertices)) (interior (integerHull q.vertices)) := by
  simp only [supportsPacketFaceB,Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨hsep,hzero⟩,hpos⟩,hneg⟩
  simp only [separatesPacketsB,Bool.and_eq_true] at hsep
  have hp (x : RealPoint) (hx : x ∈ integerHull p.vertices) : 0 ≤ evalConstraint f x :=
    verticesSatisfyB_sound _ _ hsep.1 x hx f (by simp)
  have hq (x : RealPoint) (hx : x ∈ integerHull q.vertices) : evalConstraint f x ≤ 0 := by
    have h := verticesSatisfyB_sound _ _ hsep.2 x hx (negConstraint f) (by simp)
    rw [eval_neg] at h
    linarith
  have hqv (x : RealPoint) (hx : x ∈ integerVertexSet q.vertices) : evalConstraint f x ≤ 0 :=
    hq x (subset_convexHull ℝ _ hx)
  constructor
  · apply Subset.antisymm
    · rintro x ⟨hxp,hxq⟩
      apply constraint_nonpositive_zero_face f (integerVertexSet q.vertices)
        (integerVertexSet p.vertices ∩ integerVertexSet q.vertices) hqv ?_ x hxq
        (le_antisymm (hq x hxq) (hp x hxp))
      rintro y hy hz
      obtain ⟨v,hv,rfl⟩ := hy
      have hi : edgeValue f v=0 := by rw [edgeValue_real] at hz; exact_mod_cast hz
      have hvp : v ∈ p.vertices := by
        have h := List.all_eq_true.mp hzero v hv
        simpa [hi] using h
      exact ⟨⟨v,hvp,rfl⟩,⟨v,hv,rfl⟩⟩
    · intro x hx
      exact ⟨convexHull_mono inter_subset_left hx,convexHull_mono inter_subset_right hx⟩
  · apply Set.disjoint_left.mpr
    intro x hxp hxq
    obtain ⟨v,hv,hvpos⟩ := List.any_eq_true.mp hpos
    have hvpos' : 0 < evalConstraint f (integerPoint v) := by
      rw [edgeValue_real]
      exact_mod_cast (of_decide_eq_true hvpos : 0 < edgeValue f v)
    have h := constraint_interior_pos f (integerPoint v) hvpos' _ hp x hxp
    linarith [hq x (interior_subset hxq)]

theorem pairPacketsFaceB_sound (p q : PolygonPacket) (code : Nat)
    (hc : pairPacketsFaceB p q code = true) :
    integerHull p.vertices ∩ integerHull q.vertices =
        convexHull ℝ (integerVertexSet p.vertices ∩ integerVertexSet q.vertices) ∧
      Disjoint (interior (integerHull p.vertices)) (interior (integerHull q.vertices)) := by
  unfold pairPacketsFaceB at hc
  split_ifs at hc with h0 h1 h2
  · exact supportsPacketFaceB_sound p q _ hc
  · simpa only [inter_comm,disjoint_comm] using supportsPacketFaceB_sound q p _ hc
  · exact supportsPacketFaceB_sound p q _ hc
  · simpa only [inter_comm,disjoint_comm] using supportsPacketFaceB_sound q p _ hc

theorem packetFaceRowB_at (p : PolygonPacket) (qs : List PolygonPacket) (codes : List Nat)
    (hc : packetFaceRowB p qs codes = true) (q : PolygonPacket) (hq : q ∈ qs) :
    ∃ c, pairPacketsFaceB p q c = true := by
  induction qs generalizing codes with
  | nil => simp at hq
  | cons r rs ih =>
    cases codes with
    | nil => simp [packetFaceRowB] at hc
    | cons c cs =>
      simp only [packetFaceRowB,Bool.and_eq_true] at hc
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨c,hc.1⟩
      · exact ih cs hc.2 hq

end
end SpectreGeometry.ReverseClusterTriangulation
