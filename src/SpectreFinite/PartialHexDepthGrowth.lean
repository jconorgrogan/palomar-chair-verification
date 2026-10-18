module

public import SpectreFinite.PartialMarkedHexSystem

@[expose] public section


/-! Quantitative consumers for finite partial systems. The hypotheses below
are explicitly about a supplied family; this file does not manufacture a
substitution operator or assert its growth and preservation properties. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem

theorem boundaryVertices_length_le_ports (S : PartialMarkedHexSystem) :
    S.boundaryVertices.length ≤ S.boundaryPorts.length := by
  have hnodup : S.boundaryVertices.Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange S.cellCount)
  have hsub : S.boundaryVertices ⊆ S.boundaryPorts.map Prod.fst := by
    intro v hv
    obtain ⟨d,hd⟩ := (S.mem_boundaryVertices v).mp hv
    exact List.mem_map.mpr ⟨(v,d),(S.mem_boundaryPorts v d).mpr hd,rfl⟩
  have h := hnodup.length_le_of_subset hsub
  simpa only [List.length_map] using h

/-- Explicit level at which area factor seven exceeds the boundary factor
six by enough to provide a depth-R root. The supplied family must actually
satisfy all three hypotheses. -/
theorem growing_systems_have_deep_roots
    (S : Nat → PartialMarkedHexSystem) (C R : Nat)
    (hwf : ∀ n, (S n).WellFormed)
    (harea : ∀ n, 7^n ≤ (S n).cellCount)
    (hboundary : ∀ n, (S n).boundaryPorts.length ≤ C*6^n) :
    ∃ root, (S (6*(7^R*C))).Deep R root := by
  let n := 6*(7^R*C)
  apply (S n).exists_deep_of_area_boundary (hwf n) R
  have hlo : (7^R*C)*6^n < 7^n :=
    AreaBoundaryGrowth.six_power_multiple_lt_seven (7^R*C)
  have hhi : (S n).boundaryPorts.length * 7^R ≤ (7^R*C)*6^n := by
    calc
      (S n).boundaryPorts.length * 7^R ≤ (C*6^n)*7^R :=
        Nat.mul_le_mul_right _ (hboundary n)
      _ = (7^R*C)*6^n := by ac_rfl
  have hh := harea n
  omega

end SpectreFinite.HexSearch.PartialMarkedHexSystem
