module

public import SpectreGeometry.ReverseLocalStarIncidentRows00
public import SpectreGeometry.ReverseLocalStarIncidentRows01
public import SpectreGeometry.ReverseLocalStarIncidentRows02
public import SpectreGeometry.ReverseLocalStarIncidentRows03
public import SpectreGeometry.ReverseLocalStarIncidentRows04
public import SpectreGeometry.ReverseLocalStarIncidentRows05
public import SpectreGeometry.ReverseLocalStarIncidentRows06
public import SpectreGeometry.ReverseLocalStarIncidentRows07
public import SpectreGeometry.ReverseLocalStarIncidentRows10
public import SpectreGeometry.ReverseLocalStarIncidentRows11
public import SpectreGeometry.ReverseLocalStarIncidentRows12
public import SpectreGeometry.ReverseLocalStarIncidentRows13
public import SpectreGeometry.ReverseLocalStarIncidentRows14
public import SpectreGeometry.ReverseLocalStarIncidentRows15
public import SpectreGeometry.ReverseLocalStarIncidentRows16
public import SpectreGeometry.ReverseLocalStarIncidentRows17
public import SpectreGeometry.ReverseLocalStarIncidentRows18

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem all_incident_rows_bounded_false : ∀ i : Fin 128, i.val < (targetVertices (kindMark false)).length →
    calculatedIncidentRow false i.val = (if false then incidentRows1 else incidentRows0).getD i.val [] := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using incident_rows_0_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_0_1 ⟨i.val-16,by omega⟩
  by_cases h2 : i.val < 48
  · have hs : 32 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_0_2 ⟨i.val-32,by omega⟩
  by_cases h3 : i.val < 64
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_0_3 ⟨i.val-48,by omega⟩
  by_cases h4 : i.val < 80
  · have hs : 64 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_0_4 ⟨i.val-64,by omega⟩
  by_cases h5 : i.val < 96
  · have hs : 80 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_0_5 ⟨i.val-80,by omega⟩
  by_cases h6 : i.val < 112
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_0_6 ⟨i.val-96,by omega⟩
  have hs : 112 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using incident_rows_0_7 ⟨i.val-112,by omega⟩

theorem all_incident_rows_bounded_true : ∀ i : Fin 144, i.val < (targetVertices (kindMark true)).length →
    calculatedIncidentRow true i.val = (if true then incidentRows1 else incidentRows0).getD i.val [] := by
  intro i
  by_cases h0 : i.val < 16
  · simpa only [Nat.zero_add] using incident_rows_1_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 32
  · have hs : 16 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_1_1 ⟨i.val-16,by omega⟩
  by_cases h2 : i.val < 48
  · have hs : 32 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_1_2 ⟨i.val-32,by omega⟩
  by_cases h3 : i.val < 64
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_1_3 ⟨i.val-48,by omega⟩
  by_cases h4 : i.val < 80
  · have hs : 64 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_1_4 ⟨i.val-64,by omega⟩
  by_cases h5 : i.val < 96
  · have hs : 80 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_1_5 ⟨i.val-80,by omega⟩
  by_cases h6 : i.val < 112
  · have hs : 96 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_1_6 ⟨i.val-96,by omega⟩
  by_cases h7 : i.val < 128
  · have hs : 112 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using incident_rows_1_7 ⟨i.val-112,by omega⟩
  have hs : 128 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using incident_rows_1_8 ⟨i.val-128,by omega⟩

theorem all_incident_rows_correct : ∀ (big : Bool) (v : Nat),
    v < (targetVertices (kindMark big)).length →
    calculatedIncidentRow big v = (if big then incidentRows1 else incidentRows0).getD v [] := by
  intro big v
  cases big with
  | false =>
    intro hv
    have h : v < 128 := by
      change v < 127 at hv
      omega
    exact all_incident_rows_bounded_false ⟨v,h⟩ hv
  | true =>
    intro hv
    have h : v < 144 := by
      change v < 133 at hv
      omega
    exact all_incident_rows_bounded_true ⟨v,h⟩ hv

end SpectreGeometry.ReverseLocalStarOccurrences
