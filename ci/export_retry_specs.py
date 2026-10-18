"""Inactive one-Lake semantic successor; no process or transport authority."""
from __future__ import annotations
import copy

ROLES = ('lake_export_axioms',)
ORIGINAL_PAIR = ('lean_from_export', 'lake_export_axioms')
JOB_SECONDS = 19800
SETUP_SECONDS = 1800
CLOSEOUT_SECONDS = 300
CAPS = {'lake_export_axioms': 17700}

def checker_spec(role, paths, final):
    final.f.need(role == 'lake_export_axioms', 'LAKE_ONLY_ROLE')
    original = final.final_command_specs('lean_export', paths)
    final.f.need([x['name'] for x in original] == list(ORIGINAL_PAIR), 'ORIGINAL_PAIR_CHANGED')
    result = copy.deepcopy(original[1])
    final.f.need(result['timeout_seconds'] == 9000, 'ORIGINAL_TIMEOUT_CHANGED')
    result['timeout_seconds'] = CAPS[role]
    return result
