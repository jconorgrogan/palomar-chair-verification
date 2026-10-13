module
public import WorldExistence.InteriorCopies
@[expose] public section
namespace RegisteredPrime
namespace WorldExistence

/-- The nested union of actual finite arithmetic supertiles, placed using
an empty-outer/central interior copy at every pair of substitution levels. -/
def world (P : Parameters) : RegisteredWorld P.p where
  tiles := fun q => ∃ k, AtStage P k q
  covers := by
    intro c
    obtain ⟨k, q, hq, hqc⟩ := stages_cover P c
    exact ⟨q, ⟨k, hq⟩, hqc⟩
  nonoverlap := by
    intro q r hq hr c hqc hrc
    obtain ⟨k, hq⟩ := hq
    obtain ⟨l, hr⟩ := hr
    obtain ⟨d, hd, rfl⟩ := stage_mono P k (k + l) (by omega) q hq
    obtain ⟨e, he, rfl⟩ := stage_mono P l (k + l) (by omega) r hr
    have hs := finite_supertile_unique_owner P (2 * (k + l)) (identityPose P.p) d e hd he
      ((stageOrigin P (k + l)).inv.cell c)
      ((occupies_comp_iff _ _ _).mp hqc) ((occupies_comp_iff _ _ _).mp hrc)
    have hde := hs.eq
    subst e
    exact Pose.Same.refl _

/-- Every actual contact of the constructed full world occurs together
inside one finite arithmetic supertile and therefore belongs to actual E. -/
theorem world_legal (P : Parameters) : (world P).Legal P := by
  intro q r hq hr hc
  obtain ⟨k, hq⟩ := hq
  obtain ⟨l, hr⟩ := hr
  obtain ⟨d, hd, rfl⟩ := stage_mono P k (k + l) (by omega) q hq
  obtain ⟨e, he, rfl⟩ := stage_mono P l (k + l) (by omega) r hr
  have hc' := (stageOrigin P (k + l)).inv.face_contact _ _ hc
  simp only [← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp] at hc'
  rw [Pose.relative_left_cancel]
  exact ⟨2 * (k + l), d, e, hd, he, hc', Pose.Same.refl _⟩

end WorldExistence

/-- Unconditional actual-E registered-world existence for every admissible
odd prime, nonzero square μ, and nonsquare g. No initial world, hierarchy,
compactness axiom, contact catalog, or scalar frame cycle is assumed. -/
theorem registered_E_world_exists (P : Parameters) :
    ∃ W : RegisteredWorld P.p, W.Legal P :=
  ⟨WorldExistence.world P, WorldExistence.world_legal P⟩

end RegisteredPrime
