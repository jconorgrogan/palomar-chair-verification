module

public import SpectreGeometry.PlacedBoundaryGerms

@[expose] public section


/-! A finite local family whose actual closed-body and interior germs agree
on the sample rays has exactly one occupying member on every ray. The next
physical wrapper derives all these intermediate hypotheses from a tiling. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem finite_positive_bound {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, t < r i := by
  classical
  have haux : ∀ s : Finset ι, ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, t < r i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
        obtain ⟨t,ht,hs⟩ := ih
        refine ⟨min t (r a/2),lt_min ht (div_pos (hr a) (by norm_num)),?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with he | he
        · subst i
          exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (hr a))
        · exact lt_of_le_of_lt (min_le_left _ _) (hs i he)
  obtain ⟨t,ht,hs⟩ := haux Finset.univ
  exact ⟨t,ht,fun i => hs i (Finset.mem_univ i)⟩

theorem finite_actual_ray_partition {ι : Type*} [Fintype ι]
    (F : ι → Set EPlane) (root : EPlane ≃ᵢ EPlane) (x : EPlane)
    (mask : ι → Fin 12 → Prop)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (F i)) (interior (F j)))
    (hcover : ∃ U : Set EPlane, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∃ i, y ∈ F i)
    (hgerm : ∀ i d, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (framedRay root x d t ∈ F i ↔ mask i d) ∧
      (framedRay root x d t ∈ interior (F i) ↔ mask i d)) :
    ∀ d : Fin 12, ∃! i, mask i d := by
  classical
  intro d
  obtain ⟨U,hU,hx,hcov⟩ := hcover
  have hc : Continuous (framedRay root x d) := by unfold framedRay; fun_prop
  have h0 : framedRay root x d 0 ∈ U := by simpa [framedRay] using hx
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (hU.preimage hc) 0 h0
  choose δ hδ hg using fun i => hgerm i d
  obtain ⟨s,hs,hsδ⟩ := finite_positive_bound δ hδ
  let t := min (s/2) (r/2)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have hts : t < s := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hs)
  have htr : t < r := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hr)
  have htδ : ∀ i, t < δ i := fun i => hts.trans (hsδ i)
  have hmem : t ∈ Metric.ball (0 : ℝ) r := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htr
  obtain ⟨i,hi⟩ := hcov _ (hball hmem)
  have him := (hg i t ht (htδ i)).1.1 hi
  refine ⟨i,him,?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (hdisjoint hji)
    ((hg j t ht (htδ j)).2.2 hj) ((hg i t ht (htδ i)).2.2 him)

end
end SpectreGeometry
