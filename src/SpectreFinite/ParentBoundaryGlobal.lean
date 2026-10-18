module

public import SpectreFinite.ParentBoundaryFrameFinite
public import SpectreFinite.ParentOwnershipFiniteGlobal
public import SpectreFinite.NativeCoarseNeighbors

@[expose] public section


/-! Global consumers of the checked finite family. Universal occurrence
completeness is a visible premise, not an axiom or a hidden record field. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership NativeCoarse

theorem recognition_of_certifiedParentFamily
    (hcomplete : ∀ g : Position → State, GloballyLegal g →
      OccurrenceComplete g (hexRegion 5) certifiedParentFamily)
    (f : Position → State) (hf : GloballyLegal f) : Recognition f := by
  refine ⟨unique_ownership_of_certifiedParentFamily f (hcomplete f hf),?_⟩
  intro a ha
  obtain ⟨k,hk,_⟩ := certifiedFamily_every_Gamma_has_exact_framed_parent hcomplete f hf a ha
  exact ⟨k,hk⟩

/-- Apply genuine occurrence completeness to the rotated/translated globally
legal field. No closure of the finite row catalogue is silently assumed. -/
theorem normalized_frames_of_certifiedParentFamily
    (hcomplete : ∀ g : Position → State, GloballyLegal g →
      OccurrenceComplete g (hexRegion 5) certifiedParentFamily)
    (f : Position → State) (hf : GloballyLegal f) :
    ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val) := by
  intro a
  have hg : GloballyLegal (normalizedAt f a.val) :=
    rotatedField_globallyLegal _ _ (shiftedField_globallyLegal f hf a.val)
  have hb := frames_of_certifiedParentFamily (normalizedAt f a.val)
    (hcomplete _ hg) (0,0) (normalizedAt_root f a.val a.property)
  have hz : shiftedField (normalizedAt f a.val) (0,0) = normalizedAt f a.val := by
    funext x
    simp [shiftedField,addPos]
  rw [hz] at hb
  exact hb

#print axioms recognition_of_certifiedParentFamily
#print axioms normalized_frames_of_certifiedParentFamily
end SpectreFinite.HexSearch.ParentBoundary
