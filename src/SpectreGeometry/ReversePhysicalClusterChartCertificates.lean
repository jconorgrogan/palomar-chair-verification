module

public import SpectreGeometry.ReversePhysicalClusterChartBindings00
public import SpectreGeometry.ReversePhysicalClusterChartFaces00
public import SpectreGeometry.ReversePhysicalClusterChartBindings01
public import SpectreGeometry.ReversePhysicalClusterChartFaces01
public import SpectreGeometry.ReversePhysicalClusterChartBindings02
public import SpectreGeometry.ReversePhysicalClusterChartFaces02
public import SpectreGeometry.ReversePhysicalClusterChartBindings03
public import SpectreGeometry.ReversePhysicalClusterChartFaces03
public import SpectreGeometry.ReversePhysicalClusterChartBindings04
public import SpectreGeometry.ReversePhysicalClusterChartFaces04
public import SpectreGeometry.ReversePhysicalClusterChartBindings05
public import SpectreGeometry.ReversePhysicalClusterChartFaces05
public import SpectreGeometry.ReversePhysicalClusterChartBindings06
public import SpectreGeometry.ReversePhysicalClusterChartFaces06
public import SpectreGeometry.ReversePhysicalClusterChartBindings07
public import SpectreGeometry.ReversePhysicalClusterChartFaces07
public import SpectreGeometry.ReversePhysicalClusterChartBindings10
public import SpectreGeometry.ReversePhysicalClusterChartFaces10
public import SpectreGeometry.ReversePhysicalClusterChartBindings11
public import SpectreGeometry.ReversePhysicalClusterChartFaces11
public import SpectreGeometry.ReversePhysicalClusterChartBindings12
public import SpectreGeometry.ReversePhysicalClusterChartFaces12
public import SpectreGeometry.ReversePhysicalClusterChartBindings13
public import SpectreGeometry.ReversePhysicalClusterChartFaces13
public import SpectreGeometry.ReversePhysicalClusterChartBindings14
public import SpectreGeometry.ReversePhysicalClusterChartFaces14
public import SpectreGeometry.ReversePhysicalClusterChartBindings15
public import SpectreGeometry.ReversePhysicalClusterChartFaces15
public import SpectreGeometry.ReversePhysicalClusterChartBindings16
public import SpectreGeometry.ReversePhysicalClusterChartFaces16
public import SpectreGeometry.ReversePhysicalClusterChartBindings17
public import SpectreGeometry.ReversePhysicalClusterChartFaces17
public import SpectreGeometry.ReversePhysicalClusterChartBindings18
public import SpectreGeometry.ReversePhysicalClusterChartFaces18

@[expose] public section

namespace SpectreGeometry.ReversePhysicalClusterCharts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem all_chart_packet_bindings_bounded_false : ∀ i : Fin 96, ChartPacketBinding false i.val := by
  intro i
  by_cases h0 : i.val < 12
  · simpa only [Nat.zero_add] using chart_packet_bindings_0_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 24
  · have hs : 12 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_0_1 ⟨i.val-12,by omega⟩
  by_cases h2 : i.val < 36
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_0_2 ⟨i.val-24,by omega⟩
  by_cases h3 : i.val < 48
  · have hs : 36 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_0_3 ⟨i.val-36,by omega⟩
  by_cases h4 : i.val < 60
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_0_4 ⟨i.val-48,by omega⟩
  by_cases h5 : i.val < 72
  · have hs : 60 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_0_5 ⟨i.val-60,by omega⟩
  by_cases h6 : i.val < 84
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_0_6 ⟨i.val-72,by omega⟩
  have hs : 84 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_0_7 ⟨i.val-84,by omega⟩

theorem all_chart_face_rows_bounded_false : ∀ i : Fin 96, ChartFaceRowCheck false i.val := by
  intro i
  by_cases h0 : i.val < 12
  · simpa only [Nat.zero_add] using chart_face_rows_0_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 24
  · have hs : 12 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_0_1 ⟨i.val-12,by omega⟩
  by_cases h2 : i.val < 36
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_0_2 ⟨i.val-24,by omega⟩
  by_cases h3 : i.val < 48
  · have hs : 36 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_0_3 ⟨i.val-36,by omega⟩
  by_cases h4 : i.val < 60
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_0_4 ⟨i.val-48,by omega⟩
  by_cases h5 : i.val < 72
  · have hs : 60 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_0_5 ⟨i.val-60,by omega⟩
  by_cases h6 : i.val < 84
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_0_6 ⟨i.val-72,by omega⟩
  have hs : 84 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using chart_face_rows_0_7 ⟨i.val-84,by omega⟩

theorem all_chart_packet_bindings_bounded_true : ∀ i : Fin 108, ChartPacketBinding true i.val := by
  intro i
  by_cases h0 : i.val < 12
  · simpa only [Nat.zero_add] using chart_packet_bindings_1_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 24
  · have hs : 12 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_1 ⟨i.val-12,by omega⟩
  by_cases h2 : i.val < 36
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_2 ⟨i.val-24,by omega⟩
  by_cases h3 : i.val < 48
  · have hs : 36 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_3 ⟨i.val-36,by omega⟩
  by_cases h4 : i.val < 60
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_4 ⟨i.val-48,by omega⟩
  by_cases h5 : i.val < 72
  · have hs : 60 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_5 ⟨i.val-60,by omega⟩
  by_cases h6 : i.val < 84
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_6 ⟨i.val-72,by omega⟩
  by_cases h7 : i.val < 96
  · have hs : 84 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_7 ⟨i.val-84,by omega⟩
  have hs : 96 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using chart_packet_bindings_1_8 ⟨i.val-96,by omega⟩

theorem all_chart_face_rows_bounded_true : ∀ i : Fin 108, ChartFaceRowCheck true i.val := by
  intro i
  by_cases h0 : i.val < 12
  · simpa only [Nat.zero_add] using chart_face_rows_1_0 ⟨i.val,by omega⟩
  by_cases h1 : i.val < 24
  · have hs : 12 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_1 ⟨i.val-12,by omega⟩
  by_cases h2 : i.val < 36
  · have hs : 24 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_2 ⟨i.val-24,by omega⟩
  by_cases h3 : i.val < 48
  · have hs : 36 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_3 ⟨i.val-36,by omega⟩
  by_cases h4 : i.val < 60
  · have hs : 48 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_4 ⟨i.val-48,by omega⟩
  by_cases h5 : i.val < 72
  · have hs : 60 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_5 ⟨i.val-60,by omega⟩
  by_cases h6 : i.val < 84
  · have hs : 72 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_6 ⟨i.val-72,by omega⟩
  by_cases h7 : i.val < 96
  · have hs : 84 ≤ i.val := by omega
    simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_7 ⟨i.val-84,by omega⟩
  have hs : 96 ≤ i.val := by omega
  simpa only [Nat.add_sub_of_le hs] using chart_face_rows_1_8 ⟨i.val-96,by omega⟩

theorem all_chart_packet_bindings : ∀ (big : Bool) (z : Nat),
    z < (chartFamily big).length → ChartPacketBinding big z := by
  intro big z hz
  cases big with
  | false =>
    have hn : z < 96 := by exact hz
    exact all_chart_packet_bindings_bounded_false ⟨z,hn⟩
  | true =>
    have hn : z < 108 := by exact hz
    exact all_chart_packet_bindings_bounded_true ⟨z,hn⟩

theorem all_chart_face_rows : ∀ (big : Bool) (z : Nat),
    z < (chartFamily big).length → ChartFaceRowCheck big z := by
  intro big z hz
  cases big with
  | false =>
    have hn : z < 96 := by exact hz
    exact all_chart_face_rows_bounded_false ⟨z,hn⟩
  | true =>
    have hn : z < 108 := by exact hz
    exact all_chart_face_rows_bounded_true ⟨z,hn⟩

end SpectreGeometry.ReversePhysicalClusterCharts
