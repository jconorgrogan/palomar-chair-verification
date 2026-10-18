module

public import SpectreClusters.ReverseClusterDeltaBounds0
public import SpectreClusters.ReverseClusterDeltaBounds1
public import SpectreClusters.ReverseClusterDeltaBounds2
public import SpectreClusters.ReverseClusterDeltaBounds3
public import SpectreClusters.ReverseClusterDeltaBounds4
public import SpectreClusters.ReverseClusterDeltaBounds5
public import SpectreClusters.ReverseClusterDeltaBounds6
public import SpectreClusters.ReverseClusterDeltaBounds7
public import SpectreClusters.ReverseClusterDeltaBounds8

@[expose] public section


namespace SpectreClusters.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch

theorem all_delta_bound_certificates : ∀ k : Fin 9, DeltaBoundCertificate k :=
  Fin.cases delta_bound_certificate_0 (Fin.cases delta_bound_certificate_1 (Fin.cases delta_bound_certificate_2 (Fin.cases delta_bound_certificate_3 (Fin.cases delta_bound_certificate_4 (Fin.cases delta_bound_certificate_5 (Fin.cases delta_bound_certificate_6 (Fin.cases delta_bound_certificate_7 (Fin.cases delta_bound_certificate_8 (fun i => Fin.elim0 i)))))))))

theorem vertexDelta_mem_options (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    vertexDelta a b d ∈ deltaOptions d :=
  all_delta_bound_certificates a.1 a.2 b.1 b.2 d h

theorem east_options_bounds : ∀ p ∈ deltaOptions 3,
    8 ≤ p.1 ∧ p.1 ≤ 18 ∧ -6 ≤ p.2 ∧ p.2 ≤ 2 := by decide

theorem north_options_bounds : ∀ p ∈ deltaOptions 4,
    -2 ≤ p.1 ∧ p.1 ≤ 6 ∧ 6 ≤ p.2 ∧ p.2 ≤ 14 := by decide

end SpectreClusters.ReverseExistence
