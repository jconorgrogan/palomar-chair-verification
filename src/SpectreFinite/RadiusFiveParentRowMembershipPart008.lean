module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem064 : ParentOwnership.parentRows064 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 64) (by decide)
theorem parentRow_mem1024 : ParentOwnership.parentRow1024 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 0) (by decide)
theorem parentRow_mem1025 : ParentOwnership.parentRow1025 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 1) (by decide)
theorem parentRow_mem1026 : ParentOwnership.parentRow1026 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 2) (by decide)
theorem parentRow_mem1027 : ParentOwnership.parentRow1027 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 3) (by decide)
theorem parentRow_mem1028 : ParentOwnership.parentRow1028 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 4) (by decide)
theorem parentRow_mem1029 : ParentOwnership.parentRow1029 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 5) (by decide)
theorem parentRow_mem1030 : ParentOwnership.parentRow1030 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 6) (by decide)
theorem parentRow_mem1031 : ParentOwnership.parentRow1031 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 7) (by decide)
theorem parentRow_mem1032 : ParentOwnership.parentRow1032 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 8) (by decide)
theorem parentRow_mem1033 : ParentOwnership.parentRow1033 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 9) (by decide)
theorem parentRow_mem1034 : ParentOwnership.parentRow1034 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 10) (by decide)
theorem parentRow_mem1035 : ParentOwnership.parentRow1035 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 11) (by decide)
theorem parentRow_mem1036 : ParentOwnership.parentRow1036 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 12) (by decide)
theorem parentRow_mem1037 : ParentOwnership.parentRow1037 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 13) (by decide)
theorem parentRow_mem1038 : ParentOwnership.parentRow1038 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 14) (by decide)
theorem parentRow_mem1039 : ParentOwnership.parentRow1039 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows064, parentChunk_mem064, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows064) (n := 15) (by decide)
theorem parentChunk_mem065 : ParentOwnership.parentRows065 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 65) (by decide)
theorem parentRow_mem1040 : ParentOwnership.parentRow1040 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 0) (by decide)
theorem parentRow_mem1041 : ParentOwnership.parentRow1041 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 1) (by decide)
theorem parentRow_mem1042 : ParentOwnership.parentRow1042 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 2) (by decide)
theorem parentRow_mem1043 : ParentOwnership.parentRow1043 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 3) (by decide)
theorem parentRow_mem1044 : ParentOwnership.parentRow1044 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 4) (by decide)
theorem parentRow_mem1045 : ParentOwnership.parentRow1045 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 5) (by decide)
theorem parentRow_mem1046 : ParentOwnership.parentRow1046 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 6) (by decide)
theorem parentRow_mem1047 : ParentOwnership.parentRow1047 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 7) (by decide)
theorem parentRow_mem1048 : ParentOwnership.parentRow1048 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 8) (by decide)
theorem parentRow_mem1049 : ParentOwnership.parentRow1049 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 9) (by decide)
theorem parentRow_mem1050 : ParentOwnership.parentRow1050 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 10) (by decide)
theorem parentRow_mem1051 : ParentOwnership.parentRow1051 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 11) (by decide)
theorem parentRow_mem1052 : ParentOwnership.parentRow1052 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 12) (by decide)
theorem parentRow_mem1053 : ParentOwnership.parentRow1053 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 13) (by decide)
theorem parentRow_mem1054 : ParentOwnership.parentRow1054 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 14) (by decide)
theorem parentRow_mem1055 : ParentOwnership.parentRow1055 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows065, parentChunk_mem065, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows065) (n := 15) (by decide)
theorem parentChunk_mem066 : ParentOwnership.parentRows066 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 66) (by decide)
theorem parentRow_mem1056 : ParentOwnership.parentRow1056 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 0) (by decide)
theorem parentRow_mem1057 : ParentOwnership.parentRow1057 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 1) (by decide)
theorem parentRow_mem1058 : ParentOwnership.parentRow1058 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 2) (by decide)
theorem parentRow_mem1059 : ParentOwnership.parentRow1059 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 3) (by decide)
theorem parentRow_mem1060 : ParentOwnership.parentRow1060 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 4) (by decide)
theorem parentRow_mem1061 : ParentOwnership.parentRow1061 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 5) (by decide)
theorem parentRow_mem1062 : ParentOwnership.parentRow1062 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 6) (by decide)
theorem parentRow_mem1063 : ParentOwnership.parentRow1063 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 7) (by decide)
theorem parentRow_mem1064 : ParentOwnership.parentRow1064 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 8) (by decide)
theorem parentRow_mem1065 : ParentOwnership.parentRow1065 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 9) (by decide)
theorem parentRow_mem1066 : ParentOwnership.parentRow1066 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 10) (by decide)
theorem parentRow_mem1067 : ParentOwnership.parentRow1067 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 11) (by decide)
theorem parentRow_mem1068 : ParentOwnership.parentRow1068 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 12) (by decide)
theorem parentRow_mem1069 : ParentOwnership.parentRow1069 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 13) (by decide)
theorem parentRow_mem1070 : ParentOwnership.parentRow1070 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 14) (by decide)
theorem parentRow_mem1071 : ParentOwnership.parentRow1071 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows066, parentChunk_mem066, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows066) (n := 15) (by decide)
theorem parentChunk_mem067 : ParentOwnership.parentRows067 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 67) (by decide)
theorem parentRow_mem1072 : ParentOwnership.parentRow1072 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 0) (by decide)
theorem parentRow_mem1073 : ParentOwnership.parentRow1073 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 1) (by decide)
theorem parentRow_mem1074 : ParentOwnership.parentRow1074 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 2) (by decide)
theorem parentRow_mem1075 : ParentOwnership.parentRow1075 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 3) (by decide)
theorem parentRow_mem1076 : ParentOwnership.parentRow1076 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 4) (by decide)
theorem parentRow_mem1077 : ParentOwnership.parentRow1077 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 5) (by decide)
theorem parentRow_mem1078 : ParentOwnership.parentRow1078 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 6) (by decide)
theorem parentRow_mem1079 : ParentOwnership.parentRow1079 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 7) (by decide)
theorem parentRow_mem1080 : ParentOwnership.parentRow1080 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 8) (by decide)
theorem parentRow_mem1081 : ParentOwnership.parentRow1081 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 9) (by decide)
theorem parentRow_mem1082 : ParentOwnership.parentRow1082 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 10) (by decide)
theorem parentRow_mem1083 : ParentOwnership.parentRow1083 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 11) (by decide)
theorem parentRow_mem1084 : ParentOwnership.parentRow1084 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 12) (by decide)
theorem parentRow_mem1085 : ParentOwnership.parentRow1085 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 13) (by decide)
theorem parentRow_mem1086 : ParentOwnership.parentRow1086 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 14) (by decide)
theorem parentRow_mem1087 : ParentOwnership.parentRow1087 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows067, parentChunk_mem067, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows067) (n := 15) (by decide)
theorem parentChunk_mem068 : ParentOwnership.parentRows068 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 68) (by decide)
theorem parentRow_mem1088 : ParentOwnership.parentRow1088 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 0) (by decide)
theorem parentRow_mem1089 : ParentOwnership.parentRow1089 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 1) (by decide)
theorem parentRow_mem1090 : ParentOwnership.parentRow1090 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 2) (by decide)
theorem parentRow_mem1091 : ParentOwnership.parentRow1091 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 3) (by decide)
theorem parentRow_mem1092 : ParentOwnership.parentRow1092 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 4) (by decide)
theorem parentRow_mem1093 : ParentOwnership.parentRow1093 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 5) (by decide)
theorem parentRow_mem1094 : ParentOwnership.parentRow1094 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 6) (by decide)
theorem parentRow_mem1095 : ParentOwnership.parentRow1095 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 7) (by decide)
theorem parentRow_mem1096 : ParentOwnership.parentRow1096 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 8) (by decide)
theorem parentRow_mem1097 : ParentOwnership.parentRow1097 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 9) (by decide)
theorem parentRow_mem1098 : ParentOwnership.parentRow1098 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 10) (by decide)
theorem parentRow_mem1099 : ParentOwnership.parentRow1099 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 11) (by decide)
theorem parentRow_mem1100 : ParentOwnership.parentRow1100 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 12) (by decide)
theorem parentRow_mem1101 : ParentOwnership.parentRow1101 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 13) (by decide)
theorem parentRow_mem1102 : ParentOwnership.parentRow1102 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 14) (by decide)
theorem parentRow_mem1103 : ParentOwnership.parentRow1103 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows068, parentChunk_mem068, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows068) (n := 15) (by decide)
theorem parentChunk_mem069 : ParentOwnership.parentRows069 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 69) (by decide)
theorem parentRow_mem1104 : ParentOwnership.parentRow1104 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 0) (by decide)
theorem parentRow_mem1105 : ParentOwnership.parentRow1105 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 1) (by decide)
theorem parentRow_mem1106 : ParentOwnership.parentRow1106 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 2) (by decide)
theorem parentRow_mem1107 : ParentOwnership.parentRow1107 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 3) (by decide)
theorem parentRow_mem1108 : ParentOwnership.parentRow1108 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 4) (by decide)
theorem parentRow_mem1109 : ParentOwnership.parentRow1109 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 5) (by decide)
theorem parentRow_mem1110 : ParentOwnership.parentRow1110 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 6) (by decide)
theorem parentRow_mem1111 : ParentOwnership.parentRow1111 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 7) (by decide)
theorem parentRow_mem1112 : ParentOwnership.parentRow1112 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 8) (by decide)
theorem parentRow_mem1113 : ParentOwnership.parentRow1113 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 9) (by decide)
theorem parentRow_mem1114 : ParentOwnership.parentRow1114 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 10) (by decide)
theorem parentRow_mem1115 : ParentOwnership.parentRow1115 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 11) (by decide)
theorem parentRow_mem1116 : ParentOwnership.parentRow1116 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 12) (by decide)
theorem parentRow_mem1117 : ParentOwnership.parentRow1117 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 13) (by decide)
theorem parentRow_mem1118 : ParentOwnership.parentRow1118 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 14) (by decide)
theorem parentRow_mem1119 : ParentOwnership.parentRow1119 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows069, parentChunk_mem069, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows069) (n := 15) (by decide)
theorem parentChunk_mem070 : ParentOwnership.parentRows070 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 70) (by decide)
theorem parentRow_mem1120 : ParentOwnership.parentRow1120 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 0) (by decide)
theorem parentRow_mem1121 : ParentOwnership.parentRow1121 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 1) (by decide)
theorem parentRow_mem1122 : ParentOwnership.parentRow1122 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 2) (by decide)
theorem parentRow_mem1123 : ParentOwnership.parentRow1123 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 3) (by decide)
theorem parentRow_mem1124 : ParentOwnership.parentRow1124 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 4) (by decide)
theorem parentRow_mem1125 : ParentOwnership.parentRow1125 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 5) (by decide)
theorem parentRow_mem1126 : ParentOwnership.parentRow1126 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 6) (by decide)
theorem parentRow_mem1127 : ParentOwnership.parentRow1127 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 7) (by decide)
theorem parentRow_mem1128 : ParentOwnership.parentRow1128 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 8) (by decide)
theorem parentRow_mem1129 : ParentOwnership.parentRow1129 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 9) (by decide)
theorem parentRow_mem1130 : ParentOwnership.parentRow1130 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 10) (by decide)
theorem parentRow_mem1131 : ParentOwnership.parentRow1131 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 11) (by decide)
theorem parentRow_mem1132 : ParentOwnership.parentRow1132 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 12) (by decide)
theorem parentRow_mem1133 : ParentOwnership.parentRow1133 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 13) (by decide)
theorem parentRow_mem1134 : ParentOwnership.parentRow1134 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 14) (by decide)
theorem parentRow_mem1135 : ParentOwnership.parentRow1135 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows070, parentChunk_mem070, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows070) (n := 15) (by decide)
theorem parentChunk_mem071 : ParentOwnership.parentRows071 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 71) (by decide)
theorem parentRow_mem1136 : ParentOwnership.parentRow1136 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 0) (by decide)
theorem parentRow_mem1137 : ParentOwnership.parentRow1137 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 1) (by decide)
theorem parentRow_mem1138 : ParentOwnership.parentRow1138 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 2) (by decide)
theorem parentRow_mem1139 : ParentOwnership.parentRow1139 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 3) (by decide)
theorem parentRow_mem1140 : ParentOwnership.parentRow1140 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 4) (by decide)
theorem parentRow_mem1141 : ParentOwnership.parentRow1141 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 5) (by decide)
theorem parentRow_mem1142 : ParentOwnership.parentRow1142 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 6) (by decide)
theorem parentRow_mem1143 : ParentOwnership.parentRow1143 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 7) (by decide)
theorem parentRow_mem1144 : ParentOwnership.parentRow1144 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 8) (by decide)
theorem parentRow_mem1145 : ParentOwnership.parentRow1145 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 9) (by decide)
theorem parentRow_mem1146 : ParentOwnership.parentRow1146 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 10) (by decide)
theorem parentRow_mem1147 : ParentOwnership.parentRow1147 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 11) (by decide)
theorem parentRow_mem1148 : ParentOwnership.parentRow1148 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 12) (by decide)
theorem parentRow_mem1149 : ParentOwnership.parentRow1149 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 13) (by decide)
theorem parentRow_mem1150 : ParentOwnership.parentRow1150 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 14) (by decide)
theorem parentRow_mem1151 : ParentOwnership.parentRow1151 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows071, parentChunk_mem071, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows071) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
