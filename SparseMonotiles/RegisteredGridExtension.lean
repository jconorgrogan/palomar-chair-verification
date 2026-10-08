module

public import SparseMonotiles.RegisteredCoreExhaustion
public import SparseMonotiles.IntegerGridConnected
public import SparseMonotiles.CarrierHierarchyPartition

@[expose] public section

/-! Native exposed-facet extension closes the registered cell component under
all integer coordinate steps. The component therefore fills the whole grid,
after which the full-core clamp captures every physical tile. -/
namespace SparseMonotiles
open Set Contact CarrierHierarchy

def RegisteredExposedExtension {d : ℕ} {tiles : Set (Set (Point d))}
    (g : tiles → Point d ≃ᵢ Point d) : Prop :=
  ∀ (A : tiles) (f : Facet d), IsChairCell f.cell → ¬ IsChairCell f.neighbor →
    ∃ (B : tiles) (p : Pose d),
      (g B).trans (g A).symm = p.euclidean.toIsometryEquiv ∧
      IsChairCell (p.inverseCell f.neighbor)

private theorem grid_step_adjacent {d : ℕ} {c b : Cell d}
    (h : IntegerGridStep c b) : AdjacentCells c b := by
  obtain ⟨j,rfl | rfl⟩ := h
  · exact ⟨j,Or.inl (by simp [integerGridUnit]),fun i hi => by simp [integerGridUnit,hi]⟩
  · exact ⟨j,Or.inr (by simp [integerGridUnit]),fun i hi => by simp [integerGridUnit,hi]⟩

private theorem adjacent_is_neighbor {d : ℕ} {c b : Cell d}
    (h : AdjacentCells c b) : ∃ f : Facet d, f.cell=c ∧ f.neighbor=b := by
  obtain ⟨j,hj,hother⟩ := h
  rcases hj with hj | hj
  · refine ⟨⟨c,j,true⟩,rfl,?_⟩
    funext i
    by_cases hi : i=j
    · subst i; simpa [Facet.neighbor,Facet.normal,sub_eq_add_neg] using hj.symm
    · simpa [Facet.neighbor,hi] using (hother i hi).symm
  · refine ⟨⟨c,j,false⟩,rfl,?_⟩
    funext i
    by_cases hi : i=j
    · subst i; simpa [Facet.neighbor,Facet.normal,sub_eq_add_neg] using hj.symm
    · simpa [Facet.neighbor,hi] using (hother i hi).symm

theorem registeredCoreCells_step_closed {d : ℕ} {tiles : Set (Set (Point d))}
    (g : tiles → Point d ≃ᵢ Point d) (e : Point d ≃ᵢ Point d)
    (hext : RegisteredExposedExtension g) :
    ∀ c ∈ registeredCoreCells g e, ∀ b, IntegerGridStep c b → b ∈ registeredCoreCells g e := by
  rintro c ⟨A,q,hq,hc⟩ b hstep
  have hadj : AdjacentCells (q.inverseCell c) (q.inverseCell b) := by
    simpa only [inversePose_cell] using adjacent_cell_image (inversePose q) (grid_step_adjacent hstep)
  by_cases hb : IsChairCell (q.inverseCell b)
  · exact ⟨A,q,hq,hb⟩
  obtain ⟨f,hfc,hfb⟩ := adjacent_is_neighbor hadj
  obtain ⟨B,p,hp,hpocc⟩ := hext A f (hfc.symm ▸ hc) (hfb.symm ▸ hb)
  refine ⟨B,compose q p,?_,?_⟩
  · rw [compose_euclidean]
    change (g B).trans e = p.euclidean.toIsometryEquiv.trans q.euclidean.toIsometryEquiv
    rw [← hp,← hq]
    ext x
    simp
  · have h := (occupies_compose_cell q p f.neighbor).mpr hpocc
    have he : q.cell f.neighbor=b := by rw [hfb,Pose.cell_inverseCell]
    simpa only [he,Occupies] using h

theorem registeredCoreCells_eq_univ_of_exposed_extension {d : ℕ}
    (hd : 0<d) {tiles : Set (Set (Point d))}
    (g : tiles → Point d ≃ᵢ Point d) (A0 : tiles)
    (hext : RegisteredExposedExtension g) :
    registeredCoreCells g (g A0).symm = univ := by
  apply integerGrid_eq_univ_of_step_closed
  · refine ⟨(rootPose d).cell (fun _ => 0),A0,rootPose d,?_,?_⟩
    · rw [rootPose_euclidean]
      ext x
      simp
      rfl
    · rw [Pose.inverseCell_cell]
      exact ⟨fun _ => Or.inl rfl,⟨⟨0,hd⟩,rfl⟩⟩
  · exact registeredCoreCells_step_closed g (g A0).symm hext

theorem T5_all_frames_registered_of_exposed_extension
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5) (hg : ∀ A : tiles, g A '' T5 = (A : Set (Point 5)))
    (A0 : tiles) (hext : RegisteredExposedExtension g) :
    ∀ B : tiles, IsRegisteredIsometry ((g B).trans (g A0).symm) :=
  T5_registered_frames_of_all_core_cells ht g hg (g A0).symm
    (registeredCoreCells_eq_univ_of_exposed_extension (by norm_num) g A0 hext)

theorem T7_all_frames_registered_of_exposed_extension
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7) (hg : ∀ A : tiles, g A '' T7 = (A : Set (Point 7)))
    (A0 : tiles) (hext : RegisteredExposedExtension g) :
    ∀ B : tiles, IsRegisteredIsometry ((g B).trans (g A0).symm) :=
  T7_registered_frames_of_all_core_cells ht g hg (g A0).symm
    (registeredCoreCells_eq_univ_of_exposed_extension (by norm_num) g A0 hext)

#print axioms registeredCoreCells_eq_univ_of_exposed_extension
#print axioms T5_all_frames_registered_of_exposed_extension
#print axioms T7_all_frames_registered_of_exposed_extension
end SparseMonotiles
