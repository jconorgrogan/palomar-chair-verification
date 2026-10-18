module

public import SpectreGeometry.ReverseLocalStarOccurrencesData
public import SpectreGeometry.ReverseClusterTriangulationFacesReal
public import Mathlib.Data.List.Sort

@[expose] public section


/-! Geometric soundness of the finite local-star occurrence checker. Sorting
is used only to forget triangle/vertex order; its proof uses permutation,
not an unproved ordering assumption. -/
namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

def starBody (ts : List (List Point)) : Set RealPoint :=
  {x | ∃ t ∈ ts, x ∈ integerHull t}

theorem integerVertexSet_perm {a b : List Point} (h : a.Perm b) :
    integerVertexSet a = integerVertexSet b := by
  unfold integerVertexSet
  congr 1
  ext p
  exact h.mem_iff

theorem integerHull_perm {a b : List Point} (h : a.Perm b) :
    integerHull a = integerHull b := congrArg (convexHull ℝ) (integerVertexSet_perm h)

theorem starBody_perm {a b : List (List Point)} (h : a.Perm b) : starBody a = starBody b := by
  ext x
  simp only [starBody,mem_setOf_eq]
  constructor <;> rintro ⟨t,ht,hx⟩
  · exact ⟨t,h.mem_iff.mp ht,hx⟩
  · exact ⟨t,h.mem_iff.mpr ht,hx⟩

theorem starBody_normalized (ts : List (List Point)) : starBody (normalized ts) = starBody ts := by
  rw [normalized,starBody_perm (List.mergeSort_perm _ _)]
  ext x
  constructor
  · rintro ⟨t,ht,hx⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact ⟨u,hu,(integerHull_perm (List.mergeSort_perm u pointLE)) ▸ hx⟩
  · rintro ⟨t,ht,hx⟩
    exact ⟨t.mergeSort pointLE,List.mem_map.mpr ⟨t,ht,rfl⟩,
      (integerHull_perm (List.mergeSort_perm t pointLE)).symm ▸ hx⟩

def rotatedStar (ts : List (List Point)) (r : Fin 6) : List (List Point) :=
  ts.map (fun t => t.map (SpectreClusters.rotate r))

/-- An accepted row identifies the complete closed target-star carrier,
not merely its area or its exterior boundary. -/
theorem occurrenceCheckB_sound (ts : List (List Point)) (code : Nat)
    (hc : occurrenceCheckB ts code = true) :
    code<744 ∧ starBody (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩) =
      starBody (canonicalStars.getD (code/6) []) := by
  have hh : code<744 ∧
      normalized (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩) =
        normalized (canonicalStars.getD (code/6) []) := by
    simpa only [occurrenceCheckB,rotatedStar,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using hc
  refine ⟨hh.1,?_⟩
  calc
    starBody (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩) =
        starBody (normalized (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩)) :=
      (starBody_normalized _).symm
    _ = starBody (normalized (canonicalStars.getD (code/6) [])) := congrArg starBody hh.2
    _ = starBody (canonicalStars.getD (code/6) []) := starBody_normalized _

end
end SpectreGeometry.ReverseLocalStarOccurrences
