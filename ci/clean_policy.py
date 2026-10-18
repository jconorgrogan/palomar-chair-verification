"""Pure two-run clean-source campaign receipt policy; no I/O, downloads, execution or activation.

The authenticated clean driver must use the unchanged StageRunner.run and
StageRunner.read_artifacts on fresh owned roots. Those native validators remain
mandatory. This module checks their retained, authenticated receipt projection;
a caller-supplied dictionary is never authentication or native admission.
"""
from __future__ import annotations
from copy import deepcopy
from datetime import datetime, timezone, timedelta
import re
import fresh_stage as f
import four_context_policy as p
import four_context_final as shared

TARGET_MODULE=shared.TARGET_MODULE
TARGET=shared.TARGET
TYPE=shared.TYPE
ALLOWED_AXIOMS=shared.ALLOWED_AXIOMS
DEFINING_SOURCE=shared.DEFINING_SOURCE
AUDIT_SHA256=shared.AUDIT_SHA256
AUDIT_OUTPUT=shared.AUDIT_OUTPUT
FINAL_ROLES=shared.FINAL_ROLES
FINAL_ARTIFACT_LIMIT=shared.FINAL_ARTIFACT_LIMIT
REPOSITORY=shared.REPOSITORY
REPOSITORY_ID=shared.REPOSITORY_ID
ACTIVATION_ALLOWED=False
MAX_AGE=518400
MAX_RESTORED=4*1024**3
ORIGINS=('PriorCleanOrigin','CurrentOrigin')
PRIOR_CLEAN_IDENTITY={'contract_sha256': 'e57a64341145562a07f779b8cbcbc7405c22162c1bdb014e901edd0d07799bd2', 'evidence_mode': 'clean_source_rebuild', 'lean_archive_sha256': 'b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049', 'pipeline_commit': '4221b0797acfb77b355dbb2051db0ce6b949c519', 'plan_sha256': 'c25336bffaf3ada115c7642840675f445cc3cef145fa1d70e9eec8988567a7ed', 'profiles_sha256': '770ccc2c5af5185e550432b678220f10d5981a77f3d3b2dc231fc755efb934dc', 'run_attempt': '1', 'run_id': '39096057205', 'run_started_at': '2026-10-18T04:08:25Z', 'runner_sha256': '9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d', 'source_commit': '5d0612a09e3b7d440be16e7b1dc511ae73035bbb', 'source_manifest_sha256': '09b0371c9acc07b07355824e7a7302a810c4247bbbce20d1e497bd4a02a23392', 'toolchain_inventory_sha256': '42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea'}
PRIOR_STAGE_PINS={'build_000': {'artifact_id': 12124329959, 'producer_job_id': 117582800328, 'artifact_zip_sha256': '15d509fd5067cdfe889df87efcfd7e7c0a157ef0ea00a411af6a29a3e99f8977', 'artifact_zip_bytes': 16844101, 'expires_at': '2026-10-25T04:13:45Z'}, 'build_001': {'artifact_id': 12124881962, 'producer_job_id': 117583563149, 'artifact_zip_sha256': '1ef64b1bb19c184a92fdad3e5fbbebc9bf8eae10bc8c5c5c607edfee1f898800', 'artifact_zip_bytes': 4200327, 'expires_at': '2026-10-25T04:18:01Z'}, 'build_002': {'artifact_id': 12124806270, 'producer_job_id': 117583563213, 'artifact_zip_sha256': 'b4a526ab542fe80c70433f2d8ed344d50c7bb5532772c3f670e84065d3d5a2f5', 'artifact_zip_bytes': 4136915, 'expires_at': '2026-10-25T04:17:13Z'}, 'build_003': {'artifact_id': 12125101289, 'producer_job_id': 117583563209, 'artifact_zip_sha256': '2efb085a545d54113a9f17619762bc350e5cad401be15e19ad7202daecd1402b', 'artifact_zip_bytes': 625242, 'expires_at': '2026-10-25T04:17:19Z'}, 'build_004': {'artifact_id': 12125185833, 'producer_job_id': 117583563179, 'artifact_zip_sha256': 'b7f50370edce9e78b07ba8bb01f651e531efbf6e2af33a549d6842f006e66586', 'artifact_zip_bytes': 583684, 'expires_at': '2026-10-25T04:17:22Z'}, 'build_005': {'artifact_id': 12124494988, 'producer_job_id': 117583563181, 'artifact_zip_sha256': 'a398e111a9883ac0a0e57d41d937f3c3c1dcaac39ed666fc0d4e0f796666ec15', 'artifact_zip_bytes': 3508406, 'expires_at': '2026-10-25T04:21:00Z'}, 'build_006': {'artifact_id': 12125085887, 'producer_job_id': 117583563189, 'artifact_zip_sha256': '0edc9ed0cf509aee867e68f9970cdc6d84d2f8445665bc1fff2123259e34b1e5', 'artifact_zip_bytes': 3715538, 'expires_at': '2026-10-25T04:21:20Z'}, 'build_007': {'artifact_id': 12124378668, 'producer_job_id': 117583563192, 'artifact_zip_sha256': '67b6abd4570dea3602b1fe13b9901f11611975b20652a871408981fe818c7207', 'artifact_zip_bytes': 4882256, 'expires_at': '2026-10-25T04:21:34Z'}, 'build_008': {'artifact_id': 12125425584, 'producer_job_id': 117583563239, 'artifact_zip_sha256': 'aad2517822b8a47dfe05c0ce7978ea47abb538dc9b53a372364cebd92647df97', 'artifact_zip_bytes': 9300839, 'expires_at': '2026-10-25T04:22:38Z'}, 'build_009': {'artifact_id': 12125281282, 'producer_job_id': 117583563237, 'artifact_zip_sha256': 'a59dedbbae1090dbcc0ee968c36280aa5523e45eb5cd9f001c21ec265ae1f320', 'artifact_zip_bytes': 6214332, 'expires_at': '2026-10-25T04:23:18Z'}, 'build_010': {'artifact_id': 12125945055, 'producer_job_id': 117585171847, 'artifact_zip_sha256': '206a7fdd785bb9ee3fc4836b6dcace593cd98cf21b036f4c916fe292fbe6ab39', 'artifact_zip_bytes': 39032132, 'expires_at': '2026-10-25T04:43:34Z'}, 'build_011': {'artifact_id': 12126096224, 'producer_job_id': 117588589569, 'artifact_zip_sha256': 'ca239cc899b827b6a10bb8d1c8e6b1b6d05b708226e98ef5c4f3ff01c316dba0', 'artifact_zip_bytes': 13469343, 'expires_at': '2026-10-25T05:01:31Z'}, 'build_013': {'artifact_id': 12127625159, 'producer_job_id': 117594625511, 'artifact_zip_sha256': '3ba8560742cee88b4180d6aa6eee10e5265cabf2470188d6e7a1aca921dbf0a5', 'artifact_zip_bytes': 37194853, 'expires_at': '2026-10-25T06:02:13Z'}, 'build_015': {'artifact_id': 12126930656, 'producer_job_id': 117594625574, 'artifact_zip_sha256': 'b52179d2625345fecfb938147a80d8ea983ed23e3919823aa23d0330250eca8c', 'artifact_zip_bytes': 4012879, 'expires_at': '2026-10-25T05:37:30Z'}, 'build_016': {'artifact_id': 12127535836, 'producer_job_id': 117594625504, 'artifact_zip_sha256': 'c4e113bfcc84adf37abf52d105525e1e297c491ac06dfbeee1d61503979df470', 'artifact_zip_bytes': 28348112, 'expires_at': '2026-10-25T06:00:31Z'}, 'build_017': {'artifact_id': 12127161084, 'producer_job_id': 117594625558, 'artifact_zip_sha256': '060ae5b99edaa39eca8fd8dea269f1ea9107f231b94f6b6b8cc13d32756b3d50', 'artifact_zip_bytes': 23228506, 'expires_at': '2026-10-25T05:49:49Z'}, 'build_018': {'artifact_id': 12126714093, 'producer_job_id': 117594625532, 'artifact_zip_sha256': '210fc8aded6c92050316505839c608c962828a7150f83477892eefdb70581ff5', 'artifact_zip_bytes': 38839644, 'expires_at': '2026-10-25T06:21:58Z'}, 'build_019': {'artifact_id': 12127980578, 'producer_job_id': 117594625512, 'artifact_zip_sha256': '0f4cc26e6492fb01167a2639d02a0a2e3eca35410064838c1631ab233bfb7a0e', 'artifact_zip_bytes': 47184408, 'expires_at': '2026-10-25T06:32:14Z'}, 'build_020': {'artifact_id': 12128440379, 'producer_job_id': 117594625550, 'artifact_zip_sha256': 'b4503eb1421f46c4514c26c7b51f26f6d62a63b1ed78339bef1eaee545a99d03', 'artifact_zip_bytes': 39764741, 'expires_at': '2026-10-25T06:39:51Z'}, 'build_024': {'artifact_id': 12125827084, 'producer_job_id': 117588589604, 'artifact_zip_sha256': '6f989410821515bbd2a953d112c87907f4639bedf1169945c445fa17d59884aa', 'artifact_zip_bytes': 837888, 'expires_at': '2026-10-25T04:58:13Z'}, 'build_025': {'artifact_id': 12125960814, 'producer_job_id': 117588589532, 'artifact_zip_sha256': '0aa77daf81b3532e8539917c32d1644f3d9912306c0e041ea97c9c55f1d41ccf', 'artifact_zip_bytes': 816937, 'expires_at': '2026-10-25T04:57:50Z'}, 'build_026': {'artifact_id': 12125443908, 'producer_job_id': 117588589577, 'artifact_zip_sha256': 'b0175fc06edb5050f1ed79cce9aaa314792d7e06e8600a295300fb5c3964ae5c', 'artifact_zip_bytes': 813208, 'expires_at': '2026-10-25T04:56:55Z'}, 'build_027': {'artifact_id': 12125887998, 'producer_job_id': 117588589567, 'artifact_zip_sha256': '51e3e48438a8672cd14612de1089cdee4bc7bea42f663155d161ee9d934ff09e', 'artifact_zip_bytes': 248254, 'expires_at': '2026-10-25T05:09:11Z'}, 'build_028': {'artifact_id': 12125942890, 'producer_job_id': 117588589571, 'artifact_zip_sha256': 'c754d663a1c1aa9b8172c38a0477c55ace46ca05da19fad0946ffa7dc1c8c84f', 'artifact_zip_bytes': 762124, 'expires_at': '2026-10-25T05:11:11Z'}, 'build_029': {'artifact_id': 12126266319, 'producer_job_id': 117588589568, 'artifact_zip_sha256': '738890d8a1bd32ddf436db16810ae2c9a7499fecfd885ddd34a092f6e395d63a', 'artifact_zip_bytes': 784336, 'expires_at': '2026-10-25T05:11:23Z'}, 'build_030': {'artifact_id': 12125717776, 'producer_job_id': 117588589554, 'artifact_zip_sha256': 'f62fe75465e76cfb6134a9a777ef0d8b3f5be769bc9c889389f1dab208fbe6a4', 'artifact_zip_bytes': 1620673, 'expires_at': '2026-10-25T05:14:37Z'}, 'build_031': {'artifact_id': 12126246882, 'producer_job_id': 117588589606, 'artifact_zip_sha256': '8f010ba473fbd5088d9eafce93b299fe5d508599c58007013fee040c7c35b225', 'artifact_zip_bytes': 2388522, 'expires_at': '2026-10-25T05:17:50Z'}, 'build_032': {'artifact_id': 12125978484, 'producer_job_id': 117588589687, 'artifact_zip_sha256': 'e3c9a969a81dcc7b854386bfab34f678c8cf3b708a30930cb3ebb8298e657c39', 'artifact_zip_bytes': 1264639, 'expires_at': '2026-10-25T05:19:34Z'}, 'build_033': {'artifact_id': 12127323248, 'producer_job_id': 117594625551, 'artifact_zip_sha256': 'c333828329afc70b6db0606cf620cea7d2744f34ec6a8a3b3f304e1a2a320272', 'artifact_zip_bytes': 12628789, 'expires_at': '2026-10-25T06:15:33Z'}}
PRIOR_STAGES=tuple(PRIOR_STAGE_PINS)
PRIOR_CLEAN_TERMINAL={'status': 'completed', 'conclusion': 'failure', 'updated_at': '2026-10-18T06:39:59Z'}
PRIOR_CLEAN_PREPARE_PIN={'producer_job_id':117582625110,'artifact_id': 12123539978, 'artifact_zip_sha256': '3adbfb00e39235f85047a71843aa9417cb5b17bc1ffe50c1e231d07331047092', 'artifact_zip_bytes': 3293974, 'expires_at': '2026-10-25T04:09:24Z'}
PRIOR_CLEAN_WORKFLOW={'head_branch': 'verify/hierarchy-c-clean-replay-20261018', 'path': '.github/workflows/hierarchy-c-clean-replay.yml', 'name': 'Verify hierarchy C clean replay', 'workflow_id': 388165550, 'source_sha256': '3967df73642ba77feaed86b5344b604a464b6445c41c35e919e8571e19a51a0c', 'roles': {'build_000': {'producer_job': 'wave_00', 'job_name': 'stage build_000', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_001': {'producer_job': 'wave_01', 'job_name': 'stage build_001', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_002': {'producer_job': 'wave_01', 'job_name': 'stage build_002', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_003': {'producer_job': 'wave_01', 'job_name': 'stage build_003', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_004': {'producer_job': 'wave_01', 'job_name': 'stage build_004', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_005': {'producer_job': 'wave_01', 'job_name': 'stage build_005', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_006': {'producer_job': 'wave_01', 'job_name': 'stage build_006', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_007': {'producer_job': 'wave_01', 'job_name': 'stage build_007', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_008': {'producer_job': 'wave_01', 'job_name': 'stage build_008', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_009': {'producer_job': 'wave_01', 'job_name': 'stage build_009', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_010': {'producer_job': 'wave_02', 'job_name': 'stage build_010', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_011': {'producer_job': 'wave_03', 'job_name': 'stage build_011', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_012': {'producer_job': 'wave_04', 'job_name': 'stage build_012', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_013': {'producer_job': 'wave_04', 'job_name': 'stage build_013', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_014': {'producer_job': 'wave_04', 'job_name': 'stage build_014', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_015': {'producer_job': 'wave_04', 'job_name': 'stage build_015', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_016': {'producer_job': 'wave_04', 'job_name': 'stage build_016', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_017': {'producer_job': 'wave_04', 'job_name': 'stage build_017', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_018': {'producer_job': 'wave_04', 'job_name': 'stage build_018', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_019': {'producer_job': 'wave_04', 'job_name': 'stage build_019', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_020': {'producer_job': 'wave_04', 'job_name': 'stage build_020', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_021': {'producer_job': 'wave_05', 'job_name': 'stage build_021', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_022': {'producer_job': 'wave_05', 'job_name': 'stage build_022', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_023': {'producer_job': 'wave_06', 'job_name': 'stage build_023', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_024': {'producer_job': 'wave_03', 'job_name': 'stage build_024', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_025': {'producer_job': 'wave_03', 'job_name': 'stage build_025', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_026': {'producer_job': 'wave_03', 'job_name': 'stage build_026', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_027': {'producer_job': 'wave_03', 'job_name': 'stage build_027', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_028': {'producer_job': 'wave_03', 'job_name': 'stage build_028', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_029': {'producer_job': 'wave_03', 'job_name': 'stage build_029', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_030': {'producer_job': 'wave_03', 'job_name': 'stage build_030', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_031': {'producer_job': 'wave_03', 'job_name': 'stage build_031', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_032': {'producer_job': 'wave_03', 'job_name': 'stage build_032', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_033': {'producer_job': 'wave_04', 'job_name': 'stage build_033', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_034': {'producer_job': 'wave_05', 'job_name': 'stage build_034', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_035': {'producer_job': 'wave_06', 'job_name': 'stage build_035', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_036': {'producer_job': 'wave_07', 'job_name': 'stage build_036', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_037': {'producer_job': 'wave_08', 'job_name': 'stage build_037', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_038': {'producer_job': 'wave_09', 'job_name': 'stage build_038', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_039': {'producer_job': 'wave_10', 'job_name': 'stage build_039', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_040': {'producer_job': 'wave_11', 'job_name': 'stage build_040', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_041': {'producer_job': 'wave_12', 'job_name': 'stage build_041', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_042': {'producer_job': 'wave_13', 'job_name': 'stage build_042', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_043': {'producer_job': 'wave_14', 'job_name': 'stage build_043', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_044': {'producer_job': 'wave_14', 'job_name': 'stage build_044', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_045': {'producer_job': 'wave_14', 'job_name': 'stage build_045', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_046': {'producer_job': 'wave_14', 'job_name': 'stage build_046', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_047': {'producer_job': 'wave_14', 'job_name': 'stage build_047', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_048': {'producer_job': 'wave_14', 'job_name': 'stage build_048', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_049': {'producer_job': 'wave_14', 'job_name': 'stage build_049', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_050': {'producer_job': 'wave_14', 'job_name': 'stage build_050', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_051': {'producer_job': 'wave_14', 'job_name': 'stage build_051', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_052': {'producer_job': 'wave_15', 'job_name': 'stage build_052', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_053': {'producer_job': 'wave_16', 'job_name': 'stage build_053', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_054': {'producer_job': 'wave_06', 'job_name': 'stage build_054', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_055': {'producer_job': 'wave_06', 'job_name': 'stage build_055', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_056': {'producer_job': 'wave_14', 'job_name': 'stage build_056', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_057': {'producer_job': 'wave_15', 'job_name': 'stage build_057', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_058': {'producer_job': 'wave_15', 'job_name': 'stage build_058', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_059': {'producer_job': 'wave_15', 'job_name': 'stage build_059', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_060': {'producer_job': 'wave_15', 'job_name': 'stage build_060', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_061': {'producer_job': 'wave_15', 'job_name': 'stage build_061', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_062': {'producer_job': 'wave_15', 'job_name': 'stage build_062', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_063': {'producer_job': 'wave_15', 'job_name': 'stage build_063', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_064': {'producer_job': 'wave_15', 'job_name': 'stage build_064', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_065': {'producer_job': 'wave_15', 'job_name': 'stage build_065', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_066': {'producer_job': 'wave_16', 'job_name': 'stage build_066', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_067': {'producer_job': 'wave_16', 'job_name': 'stage build_067', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_068': {'producer_job': 'wave_17', 'job_name': 'stage build_068', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_069': {'producer_job': 'wave_16', 'job_name': 'stage build_069', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_070': {'producer_job': 'wave_17', 'job_name': 'stage build_070', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_071': {'producer_job': 'wave_16', 'job_name': 'stage build_071', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_072': {'producer_job': 'wave_17', 'job_name': 'stage build_072', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_073': {'producer_job': 'wave_16', 'job_name': 'stage build_073', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_074': {'producer_job': 'wave_17', 'job_name': 'stage build_074', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_075': {'producer_job': 'wave_16', 'job_name': 'stage build_075', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_076': {'producer_job': 'wave_16', 'job_name': 'stage build_076', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_077': {'producer_job': 'wave_17', 'job_name': 'stage build_077', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_078': {'producer_job': 'wave_18', 'job_name': 'stage build_078', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_079': {'producer_job': 'wave_17', 'job_name': 'stage build_079', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_080': {'producer_job': 'wave_18', 'job_name': 'stage build_080', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_081': {'producer_job': 'wave_19', 'job_name': 'stage build_081', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_082': {'producer_job': 'wave_20', 'job_name': 'stage build_082', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_083': {'producer_job': 'wave_17', 'job_name': 'stage build_083', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_084': {'producer_job': 'wave_18', 'job_name': 'stage build_084', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_085': {'producer_job': 'wave_19', 'job_name': 'stage build_085', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_086': {'producer_job': 'wave_21', 'job_name': 'stage build_086', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_087': {'producer_job': 'wave_22', 'job_name': 'stage build_087', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_088': {'producer_job': 'wave_16', 'job_name': 'stage build_088', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_089': {'producer_job': 'wave_17', 'job_name': 'stage build_089', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_090': {'producer_job': 'wave_18', 'job_name': 'stage build_090', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_091': {'producer_job': 'wave_23', 'job_name': 'stage build_091', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'build_092': {'producer_job': 'wave_24', 'job_name': 'stage build_092', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'prepare': {'producer_job': 'prepare', 'job_name': 'prepare', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'export_target': {'producer_job': 'export_target', 'job_name': 'export_target', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'fresh_kernel': {'producer_job': 'fresh_kernel', 'job_name': 'fresh_kernel', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'lean_export': {'producer_job': 'lean_export', 'job_name': 'lean_export', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'nanoda': {'producer_job': 'nanoda', 'job_name': 'nanoda', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}, 'conron': {'producer_job': 'conron', 'job_name': 'conron', 'upload_locations': 1, 'verifier_step': {'number': 6, 'name': 'Run fail-closed verifier'}, 'upload_step': {'number': 7, 'name': "Upload only this job's new evidence"}}}}
PRIOR_CONTRACT_SHA256='e57a64341145562a07f779b8cbcbc7405c22162c1bdb014e901edd0d07799bd2'
PRIOR_PROFILES_SHA256='770ccc2c5af5185e550432b678220f10d5981a77f3d3b2dc231fc755efb934dc'
def origin_for_stage(sid):
    f.need(type(sid) is str and re.fullmatch(r'build_0[0-9]{2}',sid) and int(sid[-3:])<93,'unknown campaign stage')
    return 'PriorCleanOrigin' if sid in PRIOR_STAGES else 'CurrentOrigin'

CURRENT_WORKFLOW={'head_branch':'verify/hierarchy-c-clean-recovery-20261018',
    'path':'.github/workflows/hierarchy-c-clean-recovery.yml','name':'Verify hierarchy C clean recovery'}
FIXED_IDENTITY={'source_commit':p.PRIOR_SOURCE,'source_manifest_sha256':p.PRIOR_MANIFEST,
    'plan_sha256':p.PLAN_SHA256,'profiles_sha256':'991c8f91fbe22278945f423c6c2318a8a1d4f7cd4765dd95ab5856e6ecec32ad',
    'runner_sha256':'9085c9eea092c270fbd6952834839103c66519a7b4716fe09147001c7d96355d',
    'lean_archive_sha256':'b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049',
    'toolchain_inventory_sha256':'42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea',
    'evidence_mode':'clean_source_rebuild_campaign','run_attempt':'1'}
IDENTITY_KEYS=set(FIXED_IDENTITY)|{'pipeline_commit','contract_sha256','run_id','run_started_at'}
FORBIDDEN_RUNS={str(x) for x in (p.OLD_RUN,p.PRIOR_RUN,p.LATEST_RUN,p.EXCLUDED_RUN,39089923663,39096057205)}
_digest=shared._digest
_positive=shared._positive
_timestamp=shared._timestamp
# Use the existing exact command/configuration/axiom acceptance functions.
final_command_specs=shared.final_command_specs
validate_final_commands=shared.validate_final_commands
nanoda_configuration=shared.nanoda_configuration
_successful_command=shared._successful_command


def validate_identity(identity, contract_sha256, pipeline_commit):
    p.keys(identity,IDENTITY_KEYS,'clean identity')
    p.digest(contract_sha256,'clean contract')
    f.need(contract_sha256!=PRIOR_CLEAN_IDENTITY['contract_sha256'],'new campaign contract required')
    f.need(type(pipeline_commit) is str and f.COMMIT.fullmatch(pipeline_commit) and
        pipeline_commit not in {p.OLD_PIPELINE,p.PRIOR_PIPELINE,p.LATEST_PIPELINE,PRIOR_CLEAN_IDENTITY['pipeline_commit']},'new clean pipeline commit required')
    expected={**FIXED_IDENTITY,'contract_sha256':contract_sha256,'pipeline_commit':pipeline_commit}
    f.need(all(type(identity.get(k)) is type(v) and identity[k]==v for k,v in expected.items()),'clean fixed identity changed')
    f.need(type(identity['run_id']) is str and re.fullmatch('[1-9][0-9]*',identity['run_id']) and
        identity['run_id'] not in FORBIDDEN_RUNS,'distinct initial clean run required')
    f.need(_timestamp(identity['run_started_at'])>=_timestamp(PRIOR_CLEAN_TERMINAL['updated_at']),'campaign starts before prior-clean terminal state')
    return p.object_sha(identity)


def _inputs(plan,manifest,profiles,identity):
    validate_identity(identity,identity.get('contract_sha256'),identity.get('pipeline_commit'))
    p.validate_plan(plan)
    f.need(p.object_sha(manifest)==FIXED_IDENTITY['source_manifest_sha256'],'exact clean source manifest required')
    f.need(p.object_sha(profiles)==FIXED_IDENTITY['profiles_sha256'],'exact clean profile bytes required')
    entries=f.manifest_index(manifest)
    modules=[m for stage in plan['stages'] for m in stage['modules']]
    f.need(len(modules)==len(set(modules))==6369 and set(modules)==set(entries)==set(profiles['module_profiles']),
        'all 6369 clean source/profile modules required')
    return entries


def validate_workflow(workflow,plan):
    p.validate_plan(plan)
    p.keys(workflow,{'head_branch','name','path','workflow_id','source_sha256','roles'},'clean workflow')
    _positive(workflow['workflow_id'],'clean workflow ID');_digest(workflow['source_sha256'],'clean workflow source')
    f.need(all(workflow[k]==v for k,v in CURRENT_WORKFLOW.items()),'clean workflow identity changed')
    stages={s['stage_id']:s for s in plan['stages']}
    f.need(type(workflow['roles']) is dict and set(workflow['roles'])==(set(stages)-set(PRIOR_STAGES))|set(FINAL_ROLES)|{'prepare'},
        'exact clean provider role set required')
    for role,mapping in workflow['roles'].items():
        expected={'producer_job':stages[role]['producer_job'] if role in stages else role,
            'job_name':'stage '+role if role in stages else role,'upload_locations':1,
            'verifier_step':{'number':6,'name':'Run fail-closed verifier'},
            'upload_step':{'number':7,'name':"Upload only this job's new evidence"}}
        f.need(mapping==expected and p.object_sha(mapping)==p.object_sha(expected),'clean producer/upload binding changed')
    return workflow


def check_deadline(identity,now,*,artifact_expiries=(),previous_now=None,max_age_seconds=MAX_AGE):
    validate_identity(identity,identity.get('contract_sha256'),identity.get('pipeline_commit'))
    p.integer(max_age_seconds,'clean maximum age',MAX_AGE)
    f.need(type(now) is datetime and now.tzinfo is not None,'aware trusted clean clock required')
    if previous_now is not None:f.need(type(previous_now) is datetime and previous_now.tzinfo is not None and now>=previous_now,'clean clock moved backward')
    start=_timestamp(identity['run_started_at']);f.need(start<=now,'future clean run')
    prior_start=_timestamp(PRIOR_CLEAN_IDENTITY['run_started_at'])
    f.need(prior_start<=now,'future prior-clean origin')
    deadline=min([start+timedelta(seconds=max_age_seconds),prior_start+timedelta(seconds=max_age_seconds)]+[_timestamp(x) for x in artifact_expiries])
    f.need(now<deadline,'clean age/artifact expiry reached')
    return deadline


def _validate_wrapper(wrapper, identity, role, *, workflow, final=False):
    if not final:
        f.need(wrapper.get('origin')==origin_for_stage(role),'fixed campaign stage origin changed')
        if wrapper['origin']=='PriorCleanOrigin':
            identity=PRIOR_CLEAN_IDENTITY;workflow=PRIOR_CLEAN_WORKFLOW
    current_workflow_id=workflow['workflow_id']
    """Recheck complete producer metadata, never treating descriptor IDs as authority."""
    required = {'origin', 'native_descriptor', 'authenticated_metadata', 'raw_descriptor_sha256'}
    f.need(type(wrapper) is dict and set(wrapper) in (required, required | {'archive_path'}),
           'invalid origin wrapper fields')
    f.need(wrapper['origin'] in ORIGINS, 'unknown origin')
    if final:
        f.need(wrapper['origin'] == 'CurrentOrigin', 'historical final evidence forbidden')
    _digest(wrapper['raw_descriptor_sha256'], 'raw upload descriptor hash')
    d = wrapper['native_descriptor']
    f.need(type(d) is dict and 'archive_path' not in d and 'origin' not in d,
           'native descriptor rewritten with wrapper fields')
    f.need(d.get('identity') == identity and d.get('retention_days') == 7, 'descriptor origin/retention mismatch')
    f.need(d.get('schema') == ('fresh-final-upload-v1' if final else 'fresh-stage-upload-candidate-v1'),
           'descriptor schema mismatch')
    f.need(d.get('role' if final else 'stage_id') == role, 'descriptor role mismatch')
    _positive(d.get('artifact_id'), 'artifact ID')
    _positive(d.get('producer_job_id'), 'producer job ID')
    _positive(d.get('archive_bytes'), 'archive bytes')
    f.need(d['archive_bytes'] <= (FINAL_ARTIFACT_LIMIT if final else 1024**3), 'archive byte ceiling')
    for key in ('archive_sha256', 'receipt_sha256', 'artifact_zip_sha256'):
        _digest(d.get(key), key)
    f.need(d.get('producer_conclusion') == 'success', 'descriptor producer unsuccessful')
    meta = wrapper['authenticated_metadata']
    f.need(type(meta) is dict and set(meta) == {'run', 'job', 'artifact', 'role'}, 'authenticated metadata shape mismatch')
    run, job, artifact, mapping = (meta[k] for k in ('run', 'job', 'artifact', 'role'))
    f.need(type(run.get('id')) is int and str(run['id']) == identity['run_id'] and
           type(run.get('run_attempt')) is int and str(run['run_attempt']) == identity['run_attempt'] and
           run.get('head_sha') == identity['pipeline_commit'] and run.get('event') == 'push' and
           run.get('created_at') == identity['run_started_at'], 'authenticated producer run mismatch')
    for key in ('repository', 'head_repository'):
        repository = run.get(key, {})
        f.need(type(repository.get('id')) is int and repository['id'] == REPOSITORY_ID,
               'authenticated repository numeric identity mismatch')
    f.need(run['repository'].get('full_name') == REPOSITORY, 'authenticated repository name mismatch')
    if wrapper['origin'] in ORIGINS:
        # OriginTransport._metadata omits run.name; its authenticated _run
        # boundary validates that name before producing this exact projection.
        _positive(current_workflow_id, 'reviewed current workflow ID')
        f.need(type(run.get('workflow_id')) is int and run['workflow_id'] == current_workflow_id
               and all(run.get(key) == workflow[key] for key in ('path', 'head_branch')),
               'current workflow identity mismatch')
    f.need(type(mapping) is dict and set(mapping) == {'producer_job', 'job_name', 'verifier_step', 'upload_step', 'upload_locations'}
           and type(mapping['upload_locations']) is int and mapping['upload_locations'] == 1,
           'unreviewed producer/upload mapping')
    f.need(job.get('id') == d['producer_job_id'] and type(job.get('id')) is int and
           job.get('status') == 'completed' and job.get('conclusion') == 'success' and
           job.get('head_sha') == identity['pipeline_commit'] and job.get('name') == mapping['job_name'] and
           type(job.get('run_attempt')) is int and str(job['run_attempt']) == identity['run_attempt'] and
           str(job.get('run_id')) == identity['run_id'], 'actual successful producer mismatch')
    expected_name = role if final else 'stage '+role
    f.need(mapping['job_name'] == expected_name and
           (final or d.get('producer_job') == mapping['producer_job']), 'producer role mapping mismatch')
    steps = job.get('steps')
    f.need(type(steps) is list, 'producer step evidence absent')
    for key in ('verifier_step', 'upload_step'):
        step = mapping[key]
        f.need(type(step) is dict and set(step) == {'number', 'name'}, 'producer step mapping invalid')
        _positive(step['number'], 'producer step number')
        matches = [s for s in steps if s.get('number') == step['number'] and s.get('name') == step['name']]
        f.need(len(matches) == 1 and matches[0].get('status') == 'completed' and
               matches[0].get('conclusion') == 'success', 'verifier/upload step unsuccessful or missing')
    workflow_run = artifact.get('workflow_run', {})
    f.need(artifact.get('id') == d['artifact_id'] and type(artifact.get('id')) is int and
           artifact.get('expired') is False and artifact.get('digest') == 'sha256:'+d['artifact_zip_sha256'] and
           artifact.get('name') == 'hierarchy-c-'+identity['run_id']+'-'+identity['run_attempt']+'-'+role,
           'authenticated artifact identity/digest mismatch')
    _positive(artifact.get('size_in_bytes'), 'authoritative ZIP bytes')
    f.need(type(workflow_run.get('id')) is int and str(workflow_run['id']) == identity['run_id'] and
           workflow_run.get('head_sha') == identity['pipeline_commit'] and
           workflow_run.get('repository_id') == REPOSITORY_ID and workflow_run.get('head_repository_id') == REPOSITORY_ID,
           'artifact workflow/repository mismatch')
    f.need(mapping==workflow['roles'][role],'wrapper differs from fixed clean workflow role')
    if wrapper['origin']=='PriorCleanOrigin':
        pin=PRIOR_STAGE_PINS[role]
        f.need(run.get('status')=='completed' and run.get('conclusion')=='failure','original failed clean run state changed')
        f.need(all(d.get(k)==pin[k] for k in ('artifact_id','producer_job_id','artifact_zip_sha256')) and artifact['size_in_bytes']==pin['artifact_zip_bytes'] and artifact['expires_at']==pin['expires_at'],'pinned prior-clean producer or artifact changed')
    return d


def _provenance(plan,wrappers,identity,workflow):
    validate_workflow(workflow,plan)
    f.need(type(wrappers) is list and len(wrappers)==len(plan['stages'])==93,'all 93 clean stage wrappers required')
    rows=[];total=0
    for stage,wrapper in zip(plan['stages'],wrappers):
        d=_validate_wrapper(wrapper,identity,stage['stage_id'],workflow=workflow)
        f.need(d['producer_job']==stage['producer_job'],'clean stage producer differs from original plan')
        total+=d['archive_bytes']
        rows.append(deepcopy({k:v for k,v in wrapper.items() if k!='archive_path'}))
    f.need(total<=MAX_RESTORED,'clean global 4GiB raw archive budget exceeded')
    return rows


def _seal(rows,transfers):
    value={'rows':deepcopy(rows),'campaign_predecessor_transfers':deepcopy(transfers)}
    return {**value,'sha256':p.object_sha(value)}


def _unseal(provenance):
    p.keys(provenance,{'rows','campaign_predecessor_transfers','sha256'},'clean provenance')
    f.need(provenance==_seal(provenance['rows'],provenance['campaign_predecessor_transfers']),'clean provenance byte binding changed')
    return provenance['rows']


def validate_native_predecessor_order(*,plan,provenance,native_receipt_bytes):
    """Raw native bytes and exact two-run campaign chain; no semantic substitute."""
    p.validate_plan(plan);rows=_unseal(provenance)
    ids=[s['stage_id'] for s in plan['stages']]
    f.need(type(rows) is list and len(rows)==93 and type(native_receipt_bytes) is dict and set(native_receipt_bytes)==set(ids),
        'all 93 raw clean stage receipts required')
    transfers={};seen={};hashes={};current_identity=None
    for stage,wrapper in zip(plan['stages'],rows):
        sid=stage['stage_id'];d=wrapper['native_descriptor'];raw=native_receipt_bytes[sid]
        f.need(wrapper['origin']==origin_for_stage(sid) and d.get('stage_id')==sid,'campaign native order/origin changed')
        identity=d['identity']
        if wrapper['origin']=='PriorCleanOrigin':
            f.need(identity==PRIOR_CLEAN_IDENTITY and set(stage['required_predecessors'])<=set(PRIOR_STAGES),'prior-clean identity or closed predecessor chain changed')
        else:
            validate_identity(identity,identity.get('contract_sha256'),identity.get('pipeline_commit'))
            if current_identity is None:current_identity=identity
            f.need(identity==current_identity,'unselected current campaign run')
        f.need(type(raw) is bytes and p.sha(raw)==d['receipt_sha256'],'exact raw clean receipt changed')
        r=p.parse_json(raw)
        f.need(type(r) is dict and r.get('schema')=='fresh-stage-receipt-v1' and r.get('receipt_protocol')==f.READONLY_PROTOCOL and
            r.get('status')=='fresh_compile_check_pairs_only' and r.get('proof_pass_claimed') is False and
            r.get('identity')==identity and r.get('stage_id')==sid and r.get('producer_job')==stage['producer_job'],
            'clean native receipt envelope changed')
        predecessors=stage['required_predecessors']
        f.need(r.get('predecessors')==[seen[x] for x in predecessors],'clean same-run predecessor chain changed')
        transfers[sid]=list(predecessors);seen[sid]=d;hashes[sid]=p.sha(raw)
    f.need(provenance['campaign_predecessor_transfers']==transfers,'clean predecessor transfer ledger changed')
    return hashes


def _stage_map(plan,manifest,profiles,wrappers,native_receipt_bytes,identity,workflow):
    entries=_inputs(plan,manifest,profiles,identity);rows=_provenance(plan,wrappers,identity,workflow)
    transfers={s['stage_id']:list(s['required_predecessors']) for s in plan['stages']}
    provenance=_seal(rows,transfers)
    validate_native_predecessor_order(plan=plan,provenance=provenance,native_receipt_bytes=native_receipt_bytes)
    all_modules=[]
    for stage in plan['stages']:
        r=p.parse_json(native_receipt_bytes[stage['stage_id']]);records=r.get('modules')
        f.need(type(records) is list and [v.get('module') for v in records]==stage['modules'],'clean compiled module order/coverage changed')
        files=r.get('files');f.need(type(files) is dict,'native file map missing')
        for record in records:
            module=record['module'];all_modules.append(module);profile_id=profiles['module_profiles'][module]
            f.need(record.get('source_sha256')==entries[module]['sha256'] and record.get('profile')==profile_id,
                'clean source/profile record changed')
            outputs=record.get('outputs');expected=f.object_paths(module,f.MODERN_SUFFIXES)
            f.need(type(outputs) is dict and set(outputs)==set(expected),'six clean companions required')
            for name,digest in outputs.items():
                _digest(digest,'clean companion hash')
                f.need(name in files and files[name].get('sha256')==digest,'clean companion file binding changed')
                p.integer(files[name].get('bytes'),'clean companion bytes',1024**3,minimum=0)
            # This is the unchanged native success predicate. Full native file,
            # import, command-layout and sandbox checks still run in StageRunner.
            for phase in ('compile','check'):
                command=record.get(phase);f.need(type(command) is dict,'clean compile/check record missing')
                f.need(type(command.get('exit_code')) is int and command['exit_code']==0 and
                    command.get('timed_out') is False and command.get('log_overflow') is False and
                    command.get('memory_exceeded') is False and command.get('surviving_children') is False and
                    command.get('escaped_descendants') is False and command.get('process_group_empty') is True and
                    command.get('descendants_empty') is True,'unsuccessful clean native compile/check pair')
                expected_spec={'tool':'lean' if phase=='compile' else 'leanchecker',
                    'flags':profiles['profiles'][profile_id][phase+'_flags'],'module':module,
                    'source':entries[module]['path'] if phase=='compile' else None}
                f.need(command.get('spec')==expected_spec,'clean native command specification changed')
    f.need(len(all_modules)==len(set(all_modules))==6369 and set(all_modules)==set(entries),'clean compiled closure incomplete')
    return provenance


def validate_stage_map(plan,manifest,profiles,wrappers,native_bytes,identity,workflow):
    """Validate the full live-restored clean map, preserving every raw native byte."""
    ids={s['stage_id'] for s in p.validate_plan(plan)}
    f.need(type(native_bytes) is dict and set(native_bytes)==ids,'all93 raw native descriptor/receipt pairs required')
    receipts={}
    f.need(type(wrappers) is list and len(wrappers)==93,'all93 wrapper pairs required')
    for wrapper in wrappers:
        sid=wrapper['native_descriptor']['stage_id'];p.keys(native_bytes[sid],{'descriptor','receipt'},'clean native pair')
        p.validate_native_bytes(wrapper,native_bytes[sid]['descriptor'],native_bytes[sid]['receipt'])
        receipts[sid]=native_bytes[sid]['receipt']
    return _stage_map(plan,manifest,profiles,wrappers,receipts,identity,workflow)


def final_context(manifest,provenance,object_hashes,identity):
    """Context for an actual clean full-closure restore; final_verdict revalidates."""
    validate_identity(identity,identity.get('contract_sha256'),identity.get('pipeline_commit'))
    f.need(p.object_sha(manifest)==FIXED_IDENTITY['source_manifest_sha256'],'clean source manifest changed')
    rows=_unseal(provenance);entries=f.manifest_index(manifest)
    ids=[f'build_{i:03}' for i in range(93)]
    f.need(len(rows)==93 and [w['native_descriptor']['stage_id'] for w in rows]==ids and
        all(w['origin']==origin_for_stage(w['native_descriptor']['stage_id']) and w['native_descriptor']['identity']==(PRIOR_CLEAN_IDENTITY if w['origin']=='PriorCleanOrigin' else identity) for w in rows),'clean full native provenance required')
    f.need(set(provenance['campaign_predecessor_transfers'])==set(ids),'full clean predecessor ledger required')
    expected={name.removeprefix('objects/') for m in entries for name in f.object_paths(m,f.MODERN_SUFFIXES)}
    f.need(type(object_hashes) is dict and set(object_hashes)==expected,'all38214 clean companion hashes required')
    for digest in object_hashes.values():_digest(digest,'clean restored object hash')
    f.need(entries[DEFINING_SOURCE['module']]['sha256']==DEFINING_SOURCE['sha256'],'defining source mismatch')
    return {'target':TARGET,'expected_type':TYPE,'allowed_axioms':list(ALLOWED_AXIOMS),
        'defining_source':dict(DEFINING_SOURCE),'final_export_audit_sha256':AUDIT_SHA256,
        'source_manifest_sha256':identity['source_manifest_sha256'],'checked_source_count':manifest['source_count'],
        'checked_sources':{m:e['sha256'] for m,e in entries.items()},'restored_object_hashes':deepcopy(object_hashes),
        'resolved_provenance':deepcopy(rows),'resolved_provenance_sha256':provenance['sha256'],
        'campaign_predecessor_transfers':deepcopy(provenance['campaign_predecessor_transfers']),
        'initial_project_object_trees_empty':True,'project_artifact_imports':[{'origin':'PriorCleanOrigin','identity':deepcopy(PRIOR_CLEAN_IDENTITY),'stage_ids':list(PRIOR_STAGES)}],'compiled_source_count':6369,
        'source_rebuild_campaign':{'prior_identity':deepcopy(PRIOR_CLEAN_IDENTITY),'current_identity':deepcopy(identity),'prior_stage_ids':list(PRIOR_STAGES),'stage_origin':{sid:origin_for_stage(sid) for sid in ids}},
        'single_run_clean_rebuild':False,'independent_clean_reproduction':False}


def final_verdict(plan,manifest,profiles,identity,workflow,provenance,native_receipt_bytes,checked,now):
    """Campaign-only result after native admission and authenticated final checks.

    The authenticated driver, not these dictionaries, establishes empty roots and
    permitted input routes. All campaign predecessor imports are recorded explicitly;
    project_artifact_imports lists only external/prior-run project seed artifacts.
    """
    actual=_stage_map(plan,manifest,profiles,provenance['rows'],native_receipt_bytes,identity,workflow)
    f.need(actual==provenance,'clean full provenance/ledger changed')
    f.need(type(checked) is dict and set(checked)==set(FINAL_ROLES),'allfive clean final evidence roles required')
    # Bind final restore hashes to the exact accepted native receipt outputs.
    receipt_objects={name.removeprefix('objects/'):digest
        for sid in native_receipt_bytes
        for record in p.parse_json(native_receipt_bytes[sid])['modules']
        for name,digest in record['outputs'].items()}
    context=final_context(manifest,provenance,receipt_objects,identity)
    export_hash=_digest(checked['export_target']['receipt'].get('export_sha256'),'clean export hash')
    expiries=[w['authenticated_metadata']['artifact']['expires_at'] for w in provenance['rows']];artifacts={}
    for role in FINAL_ROLES:
        evidence=checked[role];p.keys(evidence,{'receipt','wrapper'},'clean final evidence')
        r=evidence['receipt'];w=evidence['wrapper']
        f.need(not (set(r)&{'selection_sha256','old_identity_sha256','prior_identity_sha256','latest_identity_sha256',
            'context_bundle_sha256','admission_certificate_sha256','admission_reconciliation_sha256'}),'continuation lineage in clean final receipt')
        d=_validate_wrapper(w,identity,role,workflow=workflow,final=True)
        f.need(d['receipt_sha256']==p.object_sha(r),'clean final receipt byte hash changed')
        f.need(r.get('schema')=='fresh-final-evidence-v1' and r.get('role')==role and
            r.get('status')=='completed_check_only' and r.get('proof_pass_claimed') is False and
            r.get('identity')==identity,'clean final receipt envelope changed')
        for key,value in context.items():f.need(type(r.get(key)) is type(value) and r[key]==value,'clean final context mismatch: '+key)
        if role!='fresh_kernel' or 'export_sha256' in r:f.need(r.get('export_sha256')==export_hash,'clean final export disagreement')
        validate_final_commands(r)
        expiries.append(w['authenticated_metadata']['artifact']['expires_at'])
        artifacts[role]=deepcopy({k:v for k,v in w.items() if k!='archive_path'})
    deadline=check_deadline(identity,now,artifact_expiries=expiries)
    return {'schema':'clean-source-campaign-hierarchy-c-verdict-v1','status':'clean_source_campaign_checks_passed',
        'identity':deepcopy(identity),**context,'exact_type':TYPE,'source_count':manifest['source_count'],
        'export_sha256':export_hash,'checks':{role:'passed' for role in FINAL_ROLES},'final_artifacts':artifacts,
        'acceptance_deadline':deadline.isoformat(),'clean_source_rebuild':'single_run_rebuild_pending',
        'bit_reproducibility_claim':False,'overall_task_complete':False,'activation_allowed':False,
        'scope':'Exact finite hierarchy C checks over a two-run clean-source campaign only. A successful independent single-run clean rebuild and official Palomar checks remain pending.'}
