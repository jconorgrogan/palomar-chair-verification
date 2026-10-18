module

public import SpectreGeometry.EdgeMaskAlignmentCase0
public import SpectreGeometry.EdgeMaskAlignmentCase1
public import SpectreGeometry.EdgeMaskAlignmentCase2
public import SpectreGeometry.EdgeMaskAlignmentCase3
public import SpectreGeometry.EdgeMaskAlignmentCase4
public import SpectreGeometry.EdgeMaskAlignmentCase5
public import SpectreGeometry.EdgeMaskAlignmentCase6
public import SpectreGeometry.EdgeMaskAlignmentCase7
public import SpectreGeometry.EdgeMaskAlignmentCase8
public import SpectreGeometry.EdgeMaskAlignmentCase9
public import SpectreGeometry.EdgeMaskAlignmentCase10
public import SpectreGeometry.EdgeMaskAlignmentCase11
public import SpectreGeometry.EdgeMaskAlignmentCase12
public import SpectreGeometry.EdgeMaskAlignmentCase13

@[expose] public section


namespace SpectreGeometry

theorem edge_complement_end_samples_opposite : ∀ (e j : Fin 14) (k : Fin 12),
    ¬edgeSector j (directionAdd (directionInverse k) (edgeTurn e)) →
    ¬edgeSector j (directionAdd (directionInverse k) (directionAdd (edgeTurn e) 5)) →
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn e) 6 := by
  intro e
  have he := e.isLt
  have hs : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13 := by omega
  rcases hs with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13
  · subst e; exact edge_complement_end_samples_case0
  · subst e; exact edge_complement_end_samples_case1
  · subst e; exact edge_complement_end_samples_case2
  · subst e; exact edge_complement_end_samples_case3
  · subst e; exact edge_complement_end_samples_case4
  · subst e; exact edge_complement_end_samples_case5
  · subst e; exact edge_complement_end_samples_case6
  · subst e; exact edge_complement_end_samples_case7
  · subst e; exact edge_complement_end_samples_case8
  · subst e; exact edge_complement_end_samples_case9
  · subst e; exact edge_complement_end_samples_case10
  · subst e; exact edge_complement_end_samples_case11
  · subst e; exact edge_complement_end_samples_case12
  · subst e; exact edge_complement_end_samples_case13

theorem disjoint_edge_masks_opposite (e j : Fin 14) (k : Fin 12)
    (h : ∀ d : Fin 12, edgeSector e d → ¬edgeSector j (directionAdd (directionInverse k) d)) :
    directionAdd k (edgeTurn j) = directionAdd (edgeTurn e) 6 :=
  edge_complement_end_samples_opposite e j k
    (h _ (edge_sector_boundary_samples e).2.1) (h _ (edge_sector_boundary_samples e).1)

end SpectreGeometry
