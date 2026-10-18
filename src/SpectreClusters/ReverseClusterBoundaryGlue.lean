module

public import SpectreClusters.ReverseClusterBoundaryGlue0
public import SpectreClusters.ReverseClusterBoundaryGlue1
public import SpectreClusters.ReverseClusterBoundaryGlue2
public import SpectreClusters.ReverseClusterBoundaryGlue3
public import SpectreClusters.ReverseClusterBoundaryGlue4
public import SpectreClusters.ReverseClusterBoundaryGlue5
public import SpectreClusters.ReverseClusterBoundaryGlue6
public import SpectreClusters.ReverseClusterBoundaryGlue7
public import SpectreClusters.ReverseClusterBoundaryGlue8
public import SpectreClusters.ReverseClusterCocycle

@[expose] public section

namespace SpectreClusters.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch

theorem all_boundary_glue_certificates : ∀ k : Fin 9, BoundaryGlueCertificate k := by
  exact Fin.cases boundary_glue_certificate_0 (Fin.cases boundary_glue_certificate_1 (Fin.cases boundary_glue_certificate_2 (Fin.cases boundary_glue_certificate_3 (Fin.cases boundary_glue_certificate_4 (Fin.cases boundary_glue_certificate_5 (Fin.cases boundary_glue_certificate_6 (Fin.cases boundary_glue_certificate_7 (Fin.cases boundary_glue_certificate_8 (fun i => Fin.elim0 i)))))))))

/-- Matching marked sides coincide as complete ordered vertex paths, reversed
across the common edge, after the prescribed relative displacement. -/
theorem statePath_glue (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    statePath a d = ((statePath b (opposite d)).reverse).map
      (fun p => add (vertexDelta a b d) p) :=
  all_boundary_glue_certificates a.1 a.2 b.1 b.2 d h

def developedPath (f : Position → State) (hf : GloballyLegal f)
    (x : Position) (d : Fin 6) : List Point :=
  (statePath (f x) d).map (fun p => add (lattice (developedAnchor f hf x)) p)

theorem developedPath_glue (f : Position → State) (hf : GloballyLegal f)
    (x : Position) (d : Fin 6) :
    developedPath f hf x d =
      (developedPath f hf (addPos x (SpectreFinite.direction d)) (opposite d)).reverse := by
  have hs := field_sideMatch f hf x d
  have ha : lattice (developedAnchor f hf (addPos x (SpectreFinite.direction d))) =
      add (lattice (developedAnchor f hf x))
        (vertexDelta (f x) (f (addPos x (SpectreFinite.direction d))) d) := by
    rw [developedAnchor_step,lattice_add,centerDelta_lattice _ _ _ hs]
  unfold developedPath
  rw [statePath_glue _ _ _ hs,List.map_map,←List.map_reverse,ha]
  apply List.map_congr_left
  intro p hp
  ext <;> simp only [Function.comp_apply,SpectreClusters.add,Prod.fst,Prod.snd] <;> omega

end SpectreClusters.ReverseExistence
