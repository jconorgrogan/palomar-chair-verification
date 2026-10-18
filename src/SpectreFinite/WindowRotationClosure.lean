module

public import SpectreFinite.RotatedWindows

@[expose] public section


/-! Uniform symmetry closure for any explicitly rotation-invariant finite
window domain. Concrete normalized cover certificates supply the sole finite
classification input; no physical correspondence is asserted. -/
namespace SpectreFinite.HexSearch

def rotationClosure (domain : List Position) (families : TileKind → List Patch) : List Patch :=
  (List.finRange 9).flatMap (fun k => (List.finRange 6).flatMap (fun t =>
    (families k).map (rotatePatch t domain)))

theorem extract_zero_eq_restriction (f : Position → State) (domain : List Position) :
    extract f (0,0) domain = restriction f domain := by
  apply List.map_congr_left
  intro x _
  simp [shiftedField, addPos]

theorem normalized_restriction_reconstruct (f : Position → State) (domain : List Position)
    (hdom : ∀ t : Fin 6, ∀ x ∈ domain, rotatePosition t x ∈ domain) :
    rotatePatch (f (0,0)).2 domain
      (restriction (rotatedField (inverseTurn (f (0,0)).2) f) domain) =
      restriction f domain := by
  rw [rotatePatch_restriction _ _ _ (hdom _)]
  unfold restriction
  apply List.map_congr_left
  intro x _
  rw [rotatedField_inverse]

/-- Nine turn-zero complete covers suffice for every kind, turn and center.
The converse is not claimed, so harmless extra certificate rows are allowed. -/
theorem rotationClosure_occurrenceComplete (domain : List Position)
    (hdom : ∀ t : Fin 6, ∀ x ∈ domain, rotatePosition t x ∈ domain)
    (families : TileKind → List Patch)
    (hcover : ∀ k (f : Position → State), GloballyLegal f → f (0,0) = (k,0) →
      restriction f domain ∈ families k)
    (f : Position → State) (hf : GloballyLegal f) :
    OccurrenceComplete f domain (rotationClosure domain families) := by
  intro center
  let g := shiftedField f center
  let h := rotatedField (inverseTurn (g (0,0)).2) g
  have hg : GloballyLegal g := shiftedField_globallyLegal f hf center
  have hh : GloballyLegal h := normalized_globallyLegal g hg
  have hp : restriction h domain ∈ families (g (0,0)).1 :=
    hcover (g (0,0)).1 h hh (normalized_root g)
  apply List.mem_flatMap.mpr
  refine ⟨(g (0,0)).1, by simp, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(g (0,0)).2, by simp, ?_⟩
  exact List.mem_map.mpr ⟨restriction h domain, hp,
    normalized_restriction_reconstruct g domain hdom⟩

/-- Exact literal closure for each of the larger domains used next. -/
theorem hexRegion_two_rotation : ∀ t : Fin 6, ∀ x ∈ hexRegion 2,
    rotatePosition t x ∈ hexRegion 2 := by
  exact Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (Fin.cases (by decide) (Fin.cases (by decide) (Fin.cases (by decide)
    (fun t => Fin.elim0 t))))))


end SpectreFinite.HexSearch
