module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem080 : ParentOwnership.parentRows080 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 80) (by decide)
theorem parentRow_mem1280 : ParentOwnership.parentRow1280 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 0) (by decide)
theorem parentRow_mem1281 : ParentOwnership.parentRow1281 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 1) (by decide)
theorem parentRow_mem1282 : ParentOwnership.parentRow1282 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 2) (by decide)
theorem parentRow_mem1283 : ParentOwnership.parentRow1283 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 3) (by decide)
theorem parentRow_mem1284 : ParentOwnership.parentRow1284 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 4) (by decide)
theorem parentRow_mem1285 : ParentOwnership.parentRow1285 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 5) (by decide)
theorem parentRow_mem1286 : ParentOwnership.parentRow1286 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 6) (by decide)
theorem parentRow_mem1287 : ParentOwnership.parentRow1287 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 7) (by decide)
theorem parentRow_mem1288 : ParentOwnership.parentRow1288 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 8) (by decide)
theorem parentRow_mem1289 : ParentOwnership.parentRow1289 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 9) (by decide)
theorem parentRow_mem1290 : ParentOwnership.parentRow1290 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 10) (by decide)
theorem parentRow_mem1291 : ParentOwnership.parentRow1291 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 11) (by decide)
theorem parentRow_mem1292 : ParentOwnership.parentRow1292 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 12) (by decide)
theorem parentRow_mem1293 : ParentOwnership.parentRow1293 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 13) (by decide)
theorem parentRow_mem1294 : ParentOwnership.parentRow1294 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 14) (by decide)
theorem parentRow_mem1295 : ParentOwnership.parentRow1295 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows080, parentChunk_mem080, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows080) (n := 15) (by decide)
theorem parentChunk_mem081 : ParentOwnership.parentRows081 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 81) (by decide)
theorem parentRow_mem1296 : ParentOwnership.parentRow1296 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 0) (by decide)
theorem parentRow_mem1297 : ParentOwnership.parentRow1297 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 1) (by decide)
theorem parentRow_mem1298 : ParentOwnership.parentRow1298 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 2) (by decide)
theorem parentRow_mem1299 : ParentOwnership.parentRow1299 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 3) (by decide)
theorem parentRow_mem1300 : ParentOwnership.parentRow1300 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 4) (by decide)
theorem parentRow_mem1301 : ParentOwnership.parentRow1301 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 5) (by decide)
theorem parentRow_mem1302 : ParentOwnership.parentRow1302 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 6) (by decide)
theorem parentRow_mem1303 : ParentOwnership.parentRow1303 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 7) (by decide)
theorem parentRow_mem1304 : ParentOwnership.parentRow1304 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 8) (by decide)
theorem parentRow_mem1305 : ParentOwnership.parentRow1305 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 9) (by decide)
theorem parentRow_mem1306 : ParentOwnership.parentRow1306 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 10) (by decide)
theorem parentRow_mem1307 : ParentOwnership.parentRow1307 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 11) (by decide)
theorem parentRow_mem1308 : ParentOwnership.parentRow1308 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 12) (by decide)
theorem parentRow_mem1309 : ParentOwnership.parentRow1309 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 13) (by decide)
theorem parentRow_mem1310 : ParentOwnership.parentRow1310 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 14) (by decide)
theorem parentRow_mem1311 : ParentOwnership.parentRow1311 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows081, parentChunk_mem081, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows081) (n := 15) (by decide)
theorem parentChunk_mem082 : ParentOwnership.parentRows082 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 82) (by decide)
theorem parentRow_mem1312 : ParentOwnership.parentRow1312 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 0) (by decide)
theorem parentRow_mem1313 : ParentOwnership.parentRow1313 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 1) (by decide)
theorem parentRow_mem1314 : ParentOwnership.parentRow1314 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 2) (by decide)
theorem parentRow_mem1315 : ParentOwnership.parentRow1315 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 3) (by decide)
theorem parentRow_mem1316 : ParentOwnership.parentRow1316 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 4) (by decide)
theorem parentRow_mem1317 : ParentOwnership.parentRow1317 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 5) (by decide)
theorem parentRow_mem1318 : ParentOwnership.parentRow1318 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 6) (by decide)
theorem parentRow_mem1319 : ParentOwnership.parentRow1319 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 7) (by decide)
theorem parentRow_mem1320 : ParentOwnership.parentRow1320 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 8) (by decide)
theorem parentRow_mem1321 : ParentOwnership.parentRow1321 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 9) (by decide)
theorem parentRow_mem1322 : ParentOwnership.parentRow1322 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 10) (by decide)
theorem parentRow_mem1323 : ParentOwnership.parentRow1323 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 11) (by decide)
theorem parentRow_mem1324 : ParentOwnership.parentRow1324 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 12) (by decide)
theorem parentRow_mem1325 : ParentOwnership.parentRow1325 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 13) (by decide)
theorem parentRow_mem1326 : ParentOwnership.parentRow1326 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 14) (by decide)
theorem parentRow_mem1327 : ParentOwnership.parentRow1327 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows082, parentChunk_mem082, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows082) (n := 15) (by decide)
theorem parentChunk_mem083 : ParentOwnership.parentRows083 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 83) (by decide)
theorem parentRow_mem1328 : ParentOwnership.parentRow1328 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 0) (by decide)
theorem parentRow_mem1329 : ParentOwnership.parentRow1329 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 1) (by decide)
theorem parentRow_mem1330 : ParentOwnership.parentRow1330 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 2) (by decide)
theorem parentRow_mem1331 : ParentOwnership.parentRow1331 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 3) (by decide)
theorem parentRow_mem1332 : ParentOwnership.parentRow1332 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 4) (by decide)
theorem parentRow_mem1333 : ParentOwnership.parentRow1333 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 5) (by decide)
theorem parentRow_mem1334 : ParentOwnership.parentRow1334 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 6) (by decide)
theorem parentRow_mem1335 : ParentOwnership.parentRow1335 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 7) (by decide)
theorem parentRow_mem1336 : ParentOwnership.parentRow1336 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 8) (by decide)
theorem parentRow_mem1337 : ParentOwnership.parentRow1337 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 9) (by decide)
theorem parentRow_mem1338 : ParentOwnership.parentRow1338 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 10) (by decide)
theorem parentRow_mem1339 : ParentOwnership.parentRow1339 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 11) (by decide)
theorem parentRow_mem1340 : ParentOwnership.parentRow1340 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 12) (by decide)
theorem parentRow_mem1341 : ParentOwnership.parentRow1341 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 13) (by decide)
theorem parentRow_mem1342 : ParentOwnership.parentRow1342 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 14) (by decide)
theorem parentRow_mem1343 : ParentOwnership.parentRow1343 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows083, parentChunk_mem083, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows083) (n := 15) (by decide)
theorem parentChunk_mem084 : ParentOwnership.parentRows084 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 84) (by decide)
theorem parentRow_mem1344 : ParentOwnership.parentRow1344 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 0) (by decide)
theorem parentRow_mem1345 : ParentOwnership.parentRow1345 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 1) (by decide)
theorem parentRow_mem1346 : ParentOwnership.parentRow1346 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 2) (by decide)
theorem parentRow_mem1347 : ParentOwnership.parentRow1347 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 3) (by decide)
theorem parentRow_mem1348 : ParentOwnership.parentRow1348 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 4) (by decide)
theorem parentRow_mem1349 : ParentOwnership.parentRow1349 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 5) (by decide)
theorem parentRow_mem1350 : ParentOwnership.parentRow1350 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 6) (by decide)
theorem parentRow_mem1351 : ParentOwnership.parentRow1351 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 7) (by decide)
theorem parentRow_mem1352 : ParentOwnership.parentRow1352 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 8) (by decide)
theorem parentRow_mem1353 : ParentOwnership.parentRow1353 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 9) (by decide)
theorem parentRow_mem1354 : ParentOwnership.parentRow1354 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 10) (by decide)
theorem parentRow_mem1355 : ParentOwnership.parentRow1355 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 11) (by decide)
theorem parentRow_mem1356 : ParentOwnership.parentRow1356 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 12) (by decide)
theorem parentRow_mem1357 : ParentOwnership.parentRow1357 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 13) (by decide)
theorem parentRow_mem1358 : ParentOwnership.parentRow1358 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 14) (by decide)
theorem parentRow_mem1359 : ParentOwnership.parentRow1359 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows084, parentChunk_mem084, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows084) (n := 15) (by decide)
theorem parentChunk_mem085 : ParentOwnership.parentRows085 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 85) (by decide)
theorem parentRow_mem1360 : ParentOwnership.parentRow1360 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 0) (by decide)
theorem parentRow_mem1361 : ParentOwnership.parentRow1361 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 1) (by decide)
theorem parentRow_mem1362 : ParentOwnership.parentRow1362 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 2) (by decide)
theorem parentRow_mem1363 : ParentOwnership.parentRow1363 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 3) (by decide)
theorem parentRow_mem1364 : ParentOwnership.parentRow1364 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 4) (by decide)
theorem parentRow_mem1365 : ParentOwnership.parentRow1365 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 5) (by decide)
theorem parentRow_mem1366 : ParentOwnership.parentRow1366 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 6) (by decide)
theorem parentRow_mem1367 : ParentOwnership.parentRow1367 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 7) (by decide)
theorem parentRow_mem1368 : ParentOwnership.parentRow1368 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 8) (by decide)
theorem parentRow_mem1369 : ParentOwnership.parentRow1369 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 9) (by decide)
theorem parentRow_mem1370 : ParentOwnership.parentRow1370 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 10) (by decide)
theorem parentRow_mem1371 : ParentOwnership.parentRow1371 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 11) (by decide)
theorem parentRow_mem1372 : ParentOwnership.parentRow1372 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 12) (by decide)
theorem parentRow_mem1373 : ParentOwnership.parentRow1373 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 13) (by decide)
theorem parentRow_mem1374 : ParentOwnership.parentRow1374 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 14) (by decide)
theorem parentRow_mem1375 : ParentOwnership.parentRow1375 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows085, parentChunk_mem085, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows085) (n := 15) (by decide)
theorem parentChunk_mem086 : ParentOwnership.parentRows086 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 86) (by decide)
theorem parentRow_mem1376 : ParentOwnership.parentRow1376 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 0) (by decide)
theorem parentRow_mem1377 : ParentOwnership.parentRow1377 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 1) (by decide)
theorem parentRow_mem1378 : ParentOwnership.parentRow1378 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 2) (by decide)
theorem parentRow_mem1379 : ParentOwnership.parentRow1379 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 3) (by decide)
theorem parentRow_mem1380 : ParentOwnership.parentRow1380 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 4) (by decide)
theorem parentRow_mem1381 : ParentOwnership.parentRow1381 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 5) (by decide)
theorem parentRow_mem1382 : ParentOwnership.parentRow1382 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 6) (by decide)
theorem parentRow_mem1383 : ParentOwnership.parentRow1383 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 7) (by decide)
theorem parentRow_mem1384 : ParentOwnership.parentRow1384 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 8) (by decide)
theorem parentRow_mem1385 : ParentOwnership.parentRow1385 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 9) (by decide)
theorem parentRow_mem1386 : ParentOwnership.parentRow1386 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 10) (by decide)
theorem parentRow_mem1387 : ParentOwnership.parentRow1387 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 11) (by decide)
theorem parentRow_mem1388 : ParentOwnership.parentRow1388 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 12) (by decide)
theorem parentRow_mem1389 : ParentOwnership.parentRow1389 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 13) (by decide)
theorem parentRow_mem1390 : ParentOwnership.parentRow1390 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 14) (by decide)
theorem parentRow_mem1391 : ParentOwnership.parentRow1391 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows086, parentChunk_mem086, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows086) (n := 15) (by decide)
theorem parentChunk_mem087 : ParentOwnership.parentRows087 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 87) (by decide)
theorem parentRow_mem1392 : ParentOwnership.parentRow1392 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 0) (by decide)
theorem parentRow_mem1393 : ParentOwnership.parentRow1393 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 1) (by decide)
theorem parentRow_mem1394 : ParentOwnership.parentRow1394 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 2) (by decide)
theorem parentRow_mem1395 : ParentOwnership.parentRow1395 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 3) (by decide)
theorem parentRow_mem1396 : ParentOwnership.parentRow1396 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 4) (by decide)
theorem parentRow_mem1397 : ParentOwnership.parentRow1397 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 5) (by decide)
theorem parentRow_mem1398 : ParentOwnership.parentRow1398 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 6) (by decide)
theorem parentRow_mem1399 : ParentOwnership.parentRow1399 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 7) (by decide)
theorem parentRow_mem1400 : ParentOwnership.parentRow1400 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 8) (by decide)
theorem parentRow_mem1401 : ParentOwnership.parentRow1401 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 9) (by decide)
theorem parentRow_mem1402 : ParentOwnership.parentRow1402 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 10) (by decide)
theorem parentRow_mem1403 : ParentOwnership.parentRow1403 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 11) (by decide)
theorem parentRow_mem1404 : ParentOwnership.parentRow1404 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 12) (by decide)
theorem parentRow_mem1405 : ParentOwnership.parentRow1405 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 13) (by decide)
theorem parentRow_mem1406 : ParentOwnership.parentRow1406 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 14) (by decide)
theorem parentRow_mem1407 : ParentOwnership.parentRow1407 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows087, parentChunk_mem087, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows087) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
