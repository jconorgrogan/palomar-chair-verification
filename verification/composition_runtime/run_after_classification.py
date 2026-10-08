#!/usr/bin/env python3
"""Versioned namespace-only recovery. Compose exact HENRY after full classification.

All writes belong to this isolated workspace. This does not build classification,
change any inherited source/object, install anything, or publish anything.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time

if not __debug__:
    raise RuntimeError("Optimized Python is prohibited for this verifier")
sys.dont_write_bytecode = True
R = Path(__file__).resolve().parents[1]
W = R.parent
P, O, Q, L = (R / s for s in ("project", "objects", "receipts", "logs"))
CFG = json.loads((R / "PLAN.json").read_text())
C = Path(CFG["classification"])
B = Path(CFG["toolchain"])
KERNEL = (".olean", ".olean.private", ".olean.server")
SUFFIXES = (*KERNEL, ".ir", ".ir.sig")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
VERIFIED = {}


def require(condition, message):
    if not condition:
        raise RuntimeError(str(message))


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def stamp(path):
    p = Path(path)
    s, ls = p.stat(), p.lstat()
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns,
            ls.st_ino, ls.st_mtime_ns, str(p.resolve()))


def verify_file(path, expected):
    p = Path(path)
    require(p.is_file(), ("Missing required evidence", str(p)))
    before = stamp(p)
    old = VERIFIED.get(str(p))
    if old != (expected, before):
        require(sha(p) == expected, ("SHA256 mismatch", str(p)))
        require(stamp(p) == before, ("File changed during hashing", str(p)))
        VERIFIED[str(p)] = (expected, before)
    return p


def load(path):
    return json.loads(Path(path).read_text())


def owned_write_path(path, *, allow_leaf_symlink=False):
    """Reject linked output directories and paths outside this exact workspace."""
    p = Path(path).absolute()
    require(p.is_relative_to(R) and ".." not in p.parts, ("Write escaped isolated workspace", str(p)))
    for directory in [R, *reversed([x for x in p.parents if x != R and x.is_relative_to(R)])]:
        require(not directory.is_symlink(), ("Linked writable directory", str(directory)))
        require(not directory.exists() or directory.is_dir(), ("Non-directory output parent", str(directory)))
    require(allow_leaf_symlink or not p.is_symlink(), ("Linked writable leaf", str(p)))
    return p


def immutable(path, data):
    owned_write_path(path)
    text = json.dumps(data, indent=2, sort_keys=True) + "\n"
    if path.exists():
        require(path.read_text() == text, ("Refusing to overwrite evidence", str(path)))
        return
    tmp = path.with_name(path.name + f".tmp.{os.getpid()}.{time.time_ns()}")
    owned_write_path(tmp)
    with tmp.open("x") as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    try:
        os.link(tmp, path)
    finally:
        tmp.unlink()


def imports(source):
    result = []
    for line in source.read_text().splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.*)", line)
        if match:
            result.extend(x for x in match[1].split("--")[0].split() if x != "all")
    return result


def clean(receipt):
    return receipt.get("exit_code") == 0 and not any(receipt.get(k) for k in (
        "error", "timed_out", "rss_guard_triggered", "canceled_signals",
        "live_processes_after_cleanup", "audit_error", "forbidden_axioms"))


def object_hashes(entry):
    return {suffix: part["sha256"] for suffix, part in entry["objects"].items()}


def verify_receipt(path, module, entry, mode, expected_sha=None, embedded=None):
    """Bind successful process evidence to exact source and current objects."""
    if expected_sha is not None:
        verify_file(path, expected_sha)
    else:
        verify_file(path, sha(path))
    r = load(path)
    require(embedded is None or embedded == r, ("Embedded receipt mismatch", str(path)))
    require(clean(r), ("Unsuccessful receipt", str(path)))
    require(r.get("module") == module, ("Wrong receipt module", str(path)))
    require(r.get("source_sha256") == entry["source_sha256"], ("Receipt source", module))
    expected = object_hashes(entry)
    if "objects" in r:
        actual = {}
        for suffix, value in r["objects"].items():
            suffix = Path(suffix).name.removeprefix(module.split(".")[-1])
            actual[suffix] = value
        for suffix in KERNEL:
            require(actual.get(suffix) == expected.get(suffix), ("Receipt kernel object", module, suffix))
        for suffix in set(actual) & set(expected):
            require(actual[suffix] == expected[suffix], ("Receipt object", module, suffix))
    else:
        require(r.get("object_sha256") == expected[".olean"], ("Receipt object", module))
    cmd = r["command"]
    if mode == "check":
        require(cmd == [str(B / "leanchecker"), module], ("Not default official checker", module, cmd))
    else:
        require(cmd[0] == str(B / "lean") and "-j1" in cmd and "-M3072" in cmd and "-o" in cmd,
                ("Unexpected compiler command", module, cmd))
        if "-DautoImplicit=false" not in cmd:
            require(Path(path).parent.parent.name in {
                "compact_t7_acceptance_remaining201_run_20261007T1253",
                "compact_t7_acceptance_allm7_assembly_20261007T1253"},
                ("Unexpected historical autoImplicit setting", module))
        verify_file(cmd[-1], entry["source_sha256"])
    base = Path(path).parent.parent
    # The full-forward runner records a sibling .log, with no `log` field.
    # Its SHA256 is still present in both the receipt and checked ledger.
    log = Path(r["log"]) if "log" in r else Path(path).with_suffix(".log")
    if not log.is_absolute():
        log = base / log
    verify_file(log, r["log_sha256"])
    log_text = log.read_text()
    require("sorryAx" not in log_text and "Lean.ofReduceBool" not in log_text, ("Forbidden historical axiom", module))
    for raw in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log_text, re.S):
        require({x.strip() for x in raw.split(",") if x.strip()} <= ALLOWED, ("Nonstandard historical axiom", module))
    if "direct_inputs" in r:
        require(set(r["direct_inputs"]) == set(entry["imports"]), ("Historical import receipt mismatch", module))
        for part in r["direct_inputs"].values():
            verify_file(part["path"], part["sha256"])
        digest = hashlib.sha256(json.dumps(r["direct_inputs"], sort_keys=True).encode()).hexdigest()
        require(digest == r["input_fingerprint"], ("Historical dependency fingerprint", module))
    for key in ("process_identity", "identity"):
        if key in r:
            f = Path(r[key])
            verify_file(f if f.is_absolute() else base / f, r[key + "_sha256"])
    return r


def normalize(entry, origin):
    parts = {}
    for suffix, value in entry["objects"].items():
        require(suffix in SUFFIXES, ("Unexpected object suffix", suffix))
        parts[suffix] = {"path": value.get("origin", value.get("path")), "sha256": value["sha256"]}
    return {"source": entry.get("source_origin", entry.get("source")),
            "source_sha256": entry["source_sha256"], "imports": entry["imports"],
            "objects": parts, "evidence": [str(origin)]}


def merge(modules, module, entry):
    require(".olean" in entry["objects"], ("Missing kernel object", module))
    verify_file(entry["source"], entry["source_sha256"])
    # The inherited pre-module SiblingAudit has one legacy .olean. Modern
    # module-format imports, all classifier outputs, and all new outputs must
    # carry all three kernel parts.
    if re.match(r"\s*module\b", Path(entry["source"]).read_text()):
        require(set(KERNEL) <= set(entry["objects"]), ("Missing module-format kernel sidecars", module))
    require(imports(Path(entry["source"])) == entry["imports"], ("Import provenance mismatch", module))
    for part in entry["objects"].values():
        verify_file(part["path"], part["sha256"])
    if module not in modules:
        modules[module] = entry
        return
    old = modules[module]
    require(old["source_sha256"] == entry["source_sha256"] and old["imports"] == entry["imports"],
            ("Namespace source/import collision", module))
    for suffix, part in entry["objects"].items():
        if suffix in old["objects"]:
            require(old["objects"][suffix]["sha256"] == part["sha256"], ("Namespace object collision", module, suffix))
        else:
            old["objects"][suffix] = part
    old["evidence"].extend(entry["evidence"])


def parse_axioms(module, source, text):
    expected = re.findall(r"^#print axioms (\S+)", source.read_text(), re.M)
    pairs = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    found = {name: sorted(x.strip() for x in raw.split(",") if x.strip()) for name, raw in pairs}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        require(name not in found, ("Duplicate axiom report", module, name))
        found[name] = []
    require(len(found) == len(expected), ("Missing/duplicate axiom output", module, expected, list(found)))
    for name in expected:
        require(sum(n == name or n.endswith("." + name) for n in found) == 1, ("Wrong audited declaration", module, name))
    for name, values in found.items():
        require(set(values) <= ALLOWED, ("Nonstandard axiom", module, name, values))
    return found


def verify_packages(provenance):
    require(provenance["status"] == "PASSED", "Classifier cache provenance did not pass")
    verify_file(provenance["lake_manifest"], provenance["lake_manifest_sha256"])
    require(provenance["packages"]["mathlib"]["revision"] == CFG["mathlib_revision"], "Wrong Mathlib pin")
    for package in provenance["packages"].values():
        cmd = ["git", "--no-optional-locks", "-C", package["path"]]
        head = subprocess.check_output(cmd + ["rev-parse", "HEAD"], text=True).strip()
        status = subprocess.check_output(cmd + ["status", "--porcelain=v1", "--untracked-files=normal"], text=True)
        require(head == package["revision"] and status == package["status_porcelain"] == "",
                ("Package checkout changed", package["path"]))
    inventory = {}
    primary = {}
    for root in provenance["cache_roots"]:
        directory = Path(root)
        for path in sorted(directory.rglob("*")):
            if path.is_file() and path.name.endswith(SUFFIXES):
                require(str(path) in provenance["cache_files"], ("Unpinned cached object", str(path)))
                h = provenance["cache_files"][str(path)]
                verify_file(path, h)
                inventory[str(path)] = h
                if path.suffix == ".olean":
                    module = ".".join(path.relative_to(directory).with_suffix("").parts)
                    if module in primary:
                        require(sha(primary[module]) == h, ("Cache namespace shadowing", module))
                    else:
                        primary[module] = str(path)
    require(inventory == provenance["cache_files"] and primary == provenance["cache_primary_modules"],
            "Installed official/package object inventory changed")
    for path, h in provenance["pinned_prior_manifests_receipts"].items():
        verify_file(path, h)
    return primary


def verify_classifier(modules, plan, ready):
    require(ready["status"] == "all_passed" and ready["all_legal_contacts_classified"] is True
            and ready["physical_aperiodicity"] is True, "Classification not complete")
    require((ready["pairs"], ready["roots"], ready["leaves"], ready["modules"]) == (262144, 512, 1024, 1572),
            "Wrong completed finite domain")
    require(plan["identity"] == load(C / "WORKSPACE_IDENTITY.json") and plan["identity"]["destination"] == str(C),
            "Wrong classification workspace")
    for field, filename in (("build_plan_sha256", "BUILD_PLAN.json"),
                            ("reused_dependencies_sha256", "REUSED_DEPENDENCIES.json"),
                            ("source_object_manifest_sha256", "SOURCE_OBJECT_SHA256.json")):
        verify_file(C / filename, ready[field])
    frozen = load(C / "SOURCE_OBJECT_SHA256.json")
    for rel, h in frozen.items():
        path = C / rel
        require(path.resolve().is_relative_to(C.resolve()), ("Classification manifest escaped", rel))
        verify_file(path, h)
    order, planned = plan["order"], plan["modules"]
    require(len(order) == len(set(order)) == len(planned) == 1572 and set(order) == set(planned), "Invalid build order")
    leaves = [e for e in planned.values() if e["kind"] == "leaf"]
    require({(e["root_rank"], e["source_rank_first"], e["source_rank_stop"]) for e in leaves} ==
            {(root, block * 256, (block + 1) * 256) for root in range(512) for block in range(2)},
            "Classifier finite-domain coverage mismatch")
    require(sum(e["pairs"] for e in leaves) == 262144, "Wrong matched-pair count")
    names = {f"{mode}_{module}.json" for module in order for mode in ("compile", "check")}
    require(set(ready["receipt_hashes"]) == names, "Incomplete/extra classification success receipts")
    entries = {}
    for module in order:
        stem = module.replace(".", "/")
        source = C / "project" / (stem + ".lean")
        parts = {s: {"path": str(C / "project/.build/lib/lean" / (stem + s)),
                     "sha256": frozen["project/.build/lib/lean/" + stem + s]}
                 for s in SUFFIXES if "project/.build/lib/lean/" + stem + s in frozen}
        entry = {"source": str(source), "source_sha256": planned[module]["source_sha256"],
                 "imports": planned[module]["imports"], "objects": parts,
                 "evidence": [str(C / "CLASSIFICATION_READY.json")]}
        require(frozen["project/" + stem + ".lean"] == entry["source_sha256"], ("Planned source changed", module))
        merge(modules, module, entry)
        entries[module] = entry
        dh = {}
        for dep in entry["imports"]:
            if dep in planned:
                require(dep in entries, ("Forward or missing classification import", module, dep))
                dh[dep] = {"receipt_sha256": ready["receipt_hashes"]["check_" + dep + ".json"],
                           "objects": object_hashes(entries[dep])}
            else:
                dh[dep] = {"reused_dependency_manifest_sha256": plan["reused_dependencies_sha256"]}
        for mode in ("compile", "check"):
            name = f"{mode}_{module}.json"
            receipt = verify_receipt(C / "receipts" / name, module, entry, mode, ready["receipt_hashes"][name])
            require(receipt["kind"] == mode and receipt["build_plan_sha256"] == ready["build_plan_sha256"]
                    and receipt["lean_path"] == plan["lean_path"] and receipt["direct_dependencies"] == dh,
                    ("Classification receipt dependency mismatch", module, mode))
            if mode == "compile":
                require(receipt["command"] == [str(B / "lean"), "-j1", "-M3072", "-DautoImplicit=false",
                        "--root=" + str(C / "project"), "-o", parts[".olean"]["path"], str(source)],
                        ("Unexpected classifier compiler command", module))
                require({name: sorted(values) for name, values in receipt["axioms"].items()} ==
                        parse_axioms(module, source, (C / receipt["log"]).read_text()),
                        ("Classifier axiom audit mismatch", module))


def verify_established_receipts(modules):
    """Retain inherited checked-manifest ancestry; replay no old classification."""
    def inherited_match(module, record):
        require(module in modules, ("Inherited namespace missing", module))
        entry = modules[module]
        require(record["source_sha256"] == entry["source_sha256"], ("Inherited source lineage", module))
        require(".olean" in record["objects"], ("Historical kernel object missing", module))
        for suffix in set(KERNEL) & set(record["objects"]):
            value = record["objects"][suffix]
            expected = value["sha256"] if isinstance(value, dict) else value
            require(expected == entry["objects"][suffix]["sha256"], ("Inherited object lineage", module, suffix))

    # Historical checked manifests are retained as historical evidence, with
    # every source and kernel sidecar matched to this merged closure. Their
    # newer descendants additionally have exact guarded process receipts below.
    for name in ("compact_t7_conditional_physical_20261007T0842/delivery/SOURCE_OBJECT_RECEIPTS.json",
                 "compact_t7_scaling_checkpoint_20261007T1258/delivery/SOURCE_OBJECT_RECEIPTS.json"):
        for record in load(W / name):
            inherited_match(record["module"], record)
    scaling = load(W / "compact_t7_scaling_checkpoint_20261007T1258/delivery/FINAL_RECEIPT.json")
    require(scaling["independent_audit_passed"] is True and scaling["all_414_source_object_sets_verified"] is True
            and scaling["fresh_final_tree_interface_passed"] is True, "Historical scaling checkpoint incomplete")
    for name in ("compact_t7_full_forward_20261007T1253/FULL_SOURCE_OBJECT_MANIFEST.json",
                 "compact_t7_matched_key_delivery_20261007T1608/delivery/SOURCE_OBJECT_RECEIPTS.json"):
        for module, record in load(W / name).items():
            inherited_match(module, record)
    for name in ("compact_t7_exact_existence_checked_20261007T1633", "compact_t7_finite_symmetry_20261007T1542"):
        base = W / name
        for module, modes in load(base / "CHECKED_NEW_MODULES.json").items():
            for mode, item in modes.items():
                path = Path(item["receipt"])
                verify_receipt(path if path.is_absolute() else base / path, module, modules[module], mode,
                               item["receipt_sha256"], item["result"])
    forward = W / "compact_t7_full_forward_20261007T1253"
    require(load(forward / "RESULT.json")["status"] == "PASS_FULL_COMPACT_T7_FORWARD_RULES", "Forward proof not checked")
    for module, item in load(forward / "NEW_SOURCE_OBJECT_RECEIPTS.json").items():
        for mode, check in item["checks"].items():
            verify_receipt(forward / check["receipt"], module, modules[module],
                           "check" if mode == "leanchecker" else mode, check["receipt_sha256"], check["result"])
    for name, filename in (("compact_t7_acceptance_allm7_assembly_20261007T1253", "ASSEMBLY_READY.json"),
                           ("compact_t7_acceptance_remaining201_run_20261007T1253", "VALIDATION_RECEIPT.json")):
        base = W / name
        gate = load(base / filename)
        require(gate["status"] == "all_passed", ("Acceptance gate incomplete", name))
        verify_file(base / "SOURCE_OBJECT_SHA256.json", gate["source_object_manifest_sha256"])
        for rel, h in load(base / "SOURCE_OBJECT_SHA256.json").items():
            verify_file(base / rel, h)
        sets = [gate["receipt_hashes"]] if "receipt_hashes" in gate else [row["receipt_hashes"] for row in gate["row_results"]]
        for hashes in sets:
            for rel, h in hashes.items():
                r = load(verify_file(base / rel, h))
                mode = "check" if r["kind"] in ("check", "leanchecker") else "compile"
                verify_receipt(base / rel, r["module"], modules[r["module"]], mode, h)
    matched = W / "compact_t7_matched_key_delivery_20261007T1608/delivery"
    for module, modes in load(matched / "CHECKED_NEW_MODULES.json").items():
        for mode, item in modes.items():
            path = Path(item["receipt"])
            verify_receipt(path if path.is_absolute() else matched / path, module, modules[module], mode,
                           item["receipt_sha256"], item["result"])


def verify_compact_interface(modules):
    """Accept only the newly checked exact compact public representation."""
    interface = Path(CFG["compact_interface"])
    require(interface == W / "henry_compact_statement_prepared_20261007T2321", "Wrong compact interface root")
    require(not any(m.startswith("HENRY.") or m == "Solution" for m in modules),
            "An inherited tree already supplied stale public-interface objects")
    frozen_path = interface / "FROZEN.json"
    result_path = interface / "CHECKED_INTERFACE_RESULT.json"
    frozen, result = load(frozen_path), load(result_path)
    require(result["status"] == "PASS_GUARDED_COMPACT_INTERFACE_CHECKS", "Compact interface did not pass")
    require(result["frozen_candidate_sha256"] == sha(frozen_path), "Compact checks refer to a different frozen source")
    for rel, h in frozen["files"].items():
        path = interface / rel
        require(path.resolve().is_relative_to(interface.resolve()), ("Frozen compact evidence escaped", rel))
        verify_file(path, h)
    require(frozen["files"]["templates/Challenge.lean"] == CFG["compact_challenge_sha256"] ==
            "2d250d0118bed6cdac62d0bcf0b01ee09bc624b64f07378d4627f4837d891d03", "Wrong exact compact Challenge")
    require(frozen["files"]["project/HENRY/Statement.lean"] == CFG["compact_statement_sha256"] ==
            "23c373f64433047020cb656fafc3698aa0f7edec73413c4d05d1b9b1db9c0638", "Wrong exact compact Statement")
    for rel in ("Solution.lean", "HENRY/FinalExactTypeAudit.lean"):
        require(sha(P / rel) == frozen["files"]["project/" + rel], ("Final source differs from compact interface", rel))
    cfg = load(interface / "env.json")
    require(cfg["toolchain"] == str(B) and cfg["guard_sha256"] == CFG["guard_sha256"]
            and cfg["shared_serial_lock"] == CFG["serial_lock"] and cfg["mathlib_revision"] == CFG["mathlib_revision"],
            "Compact interface used different tools or guards")
    for executable, h in cfg["toolchain_sha256"].items():
        verify_file(B / executable, h)
    closure = load(interface / "evidence/DEPENDENCY_CLOSURE.json")
    require(closure["status"] == "PASS_HASH_VERIFIED_NO_LEAN" and closure["old_henry_objects_excluded"] is True,
            "Compact interface dependency namespace was not isolated")
    require(closure["module_count"] == len(closure["module_receipts"]), "Compact dependency count mismatch")
    for module, entry in closure["module_receipts"].items():
        require(not module.startswith("HENRY.") and module != "Solution" and module in modules,
                ("Stale or missing compact dependency", module))
        inherited = modules[module]
        require(entry["source_sha256"] == inherited["source_sha256"] and entry["imports"] == inherited["imports"],
                ("Compact dependency source/import mismatch", module))
        for suffix, part in entry["objects"].items():
            require(inherited["objects"][suffix]["sha256"] == part["sha256"], ("Compact dependency object mismatch", module, suffix))
            verify_file(interface / "dependencies" / (module.replace(".", "/") + suffix), part["sha256"])
    expected_modules = ["HENRY.Statement", "HENRY.CodecPilot", "HENRY.BodyBinding", "HENRY.StatementAudit", "HENRY.Transport"]
    require(CFG["recheck_inherited"] == expected_modules, "Compact interface recheck set changed")
    require(set(result["receipts"]) == {m + ":" + mode for m in expected_modules for mode in ("compile", "check")},
            "Compact interface requires exactly ten successful process receipts")
    reports = {}
    for module in expected_modules:
        stem = module.replace(".", "/")
        source = interface / "project" / (stem + ".lean")
        if module == "HENRY.Statement":
            require(all(i.startswith("Mathlib.") for i in imports(source)), "Independent Statement imports an implementation")
        require(not any("Challenge" in i for i in imports(source)), ("Public interface imports theorem hole", module))
        parts = {suffix: {"path": str(interface / "objects" / (stem + suffix)),
                          "sha256": CFG["pins"][str(interface / "objects" / (stem + suffix))]} for suffix in SUFFIXES}
        entry = {"source": str(source), "source_sha256": frozen["files"]["project/" + stem + ".lean"],
                 "imports": imports(source), "objects": parts, "evidence": [str(result_path), str(frozen_path)]}
        merge(modules, module, entry)
        for mode in ("compile", "check"):
            item = result["receipts"][module + ":" + mode]
            receipt_path = Path(item["path"])
            require(receipt_path.parent == interface / "logs", ("Compact receipt outside isolated run", module))
            r = verify_receipt(receipt_path, module, entry, mode, item["sha256"])
            require(r["mode"] == mode and r["frozen_candidate_sha256"] == sha(frozen_path), ("Wrong compact receipt binding", module, mode))
            require(r["global_lock"] == CFG["serial_lock"] and r["inherited_global_and_workspace_lock"] is True
                    and r["timeout_seconds"] == 120 and r["rss_guard_mib"] == 3584, ("Compact receipt guard mismatch", module, mode))
            require(r["object_sidecars"] == {"objects/" + stem + suffix: part["sha256"] for suffix, part in parts.items()},
                    ("Compact receipt does not bind every exact object part", module, mode))
            log = Path(r["log"])
            identity_path = log.with_suffix(".process.json")
            verify_file(identity_path, CFG["pins"][str(identity_path)])
            require(load(identity_path)["command"] == r["command"], ("Compact process identity command mismatch", module, mode))
            if mode == "compile":
                require(r["command"] == [str(B / "lean"), "-j1", "-M3072", "-DautoImplicit=false",
                        "--root=" + str(interface / "project"), "-o", parts[".olean"]["path"], str(source)],
                        ("Wrong exact compact compile command", module))
                reports.update(parse_axioms(module, source, log.read_text()))
    expected_axioms = {"HENRY.CodecPilot.first_chunk", "HENRY.CodecPilot.last_chunk", "HENRY.Binding.T7_eq",
                       "HENRY.Binding.keys7_length", "HENRY.Binding.tiling_iff",
                       "PalomarMonotiles.CompactStatementAudit.statement_iff_expanded",
                       "HENRY.Binding.strongClaim_of_internal", "HENRY.Binding.hasTiling",
                       "HENRY.Binding.strongClaim_of_contact_classification"}
    require(set(reports) == expected_axioms and reports == result["axioms"], "Compact interface nine-declaration axiom audit mismatch")


def preflight():
    require(str(R) == CFG["workspace"] and R.name == "henry_final_composition_compact_prepared_20261007T2332", "Wrong workspace")
    # This gate is deliberately first: no lock, assembly, compiler, or checker
    # process starts when the complete classification marker is missing.
    require((C / "CLASSIFICATION_READY.json").is_file(), "BLOCKED: CLASSIFICATION_READY.json is absent")
    verify_file(C / "CLASSIFICATION_READY.json", sha(C / "CLASSIFICATION_READY.json"))
    admission_path = R / "runtime_recovery/ADMISSION.json"
    admission = load(admission_path)
    require(admission["status"] == "REVIEWED_NAMESPACE_RECOVERY_PREPARATION", "Wrong recovery admission")
    verify_file(admission_path, sha(admission_path))
    verify_file(Path(__file__), admission["runtime_runner_sha256"])
    verify_file(R / "scripts/run_after_classification.py", admission["original_runner_sha256"])
    verify_file(R / "PACKAGE_MANIFEST.json", admission["original_package_manifest_sha256"])
    require(admission["materialized_modules"] == CFG["recheck_inherited"], "Recovery scope changed")
    for path, digest in admission["preserved_failure_evidence"].items():
        verify_file(path, digest)

    for rel, h in load(R / "PACKAGE_MANIFEST.json")["sha256"].items():
        verify_file(R / rel, h)
    for path, h in CFG["pins"].items():
        verify_file(path, h)
    for rel, h in CFG["sources"].items():
        source = verify_file(R / rel, h)
        require(not re.search(r"\b(sorry|admit|native_decide|ofReduceBool)\b|^\s*(axiom|unsafe)\b|\b(addDecl|setEnv|modifyEnv)\b",
                              source.read_text(), re.M), ("Forbidden new proof construct", rel))
        require(not any("Challenge" in i for i in imports(source)), ("Forbidden theorem-hole import", rel))
    require(sha(R / "scripts/guarded_process.py") == CFG["guard_sha256"] ==
            "c398b61e6d355268b6a4eaf53c69daf44cdc5028bba1d3466b89d8126c8eb26e", "Guard changed")
    plan = load(C / "BUILD_PLAN.json")
    deps = load(C / "REUSED_DEPENDENCIES.json")
    require(str(B) == plan["toolchain"] == deps["toolchain"], "Toolchain path mismatch")
    verify_file(B / "lean", deps["lean_binary_sha256"])
    verify_file(B / "leanchecker", deps["leanchecker_binary_sha256"])
    provenance = load(C / "PROVENANCE_AUDIT.json")
    primary = verify_packages(provenance)
    modules = {}
    statuses = {"compact_t7_exact_existence_checked_20261007T1633": "PASS_EXACT_COMPACT_T7_PHYSICAL_HAS_TILING",
                "compact_t7_finite_symmetry_20261007T1542": "PASS_CONDITIONAL_EXACT_T7_FULL_EUCLIDEAN_SYMMETRY_BOUND"}
    for name, status in statuses.items():
        base = W / name
        require(load(base / "RESULT.json")["status"] == status, ("Prerequisite did not pass", name))
        ledger = base / "SOURCE_OBJECT_RECEIPTS.json"
        for module, entry in load(ledger).items():
            merge(modules, module, normalize(entry, ledger))
    for module, data in deps["modules"].items():
        parts = {Path(path).name.removeprefix(module.split(".")[-1]): {"path": path, "sha256": h}
                 for path, h in data["objects"].items()}
        merge(modules, module, {**data, "objects": parts, "evidence": [str(C / "REUSED_DEPENDENCIES.json")]})
    # The checked matched-key delivery also includes three historical audits
    # unused by the reduced classifier. Retain their exact objects so its full
    # checked ledger can be verified without dangling namespace references.
    matched_ledger = W / "compact_t7_matched_key_delivery_20261007T1608/delivery/SOURCE_OBJECT_RECEIPTS.json"
    for module, data in load(matched_ledger).items():
        merge(modules, module, normalize(data, matched_ledger))
    for module, data in deps["external"].items():
        require(module in primary, ("Unpinned external namespace", module))
        for path, h in data["objects"].items():
            verify_file(path, h)
    for module, evidence in provenance["prior_project_evidence"].items():
        if evidence["kind"] == "matching_successful_compile_and_default_checker_receipts":
            for mode, path in evidence["receipts"].items():
                verify_receipt(Path(path), module, modules[module], mode,
                               provenance["pinned_prior_manifests_receipts"][path])
    verify_compact_interface(modules)
    verify_established_receipts(modules)
    verify_classifier(modules, plan, load(C / "CLASSIFICATION_READY.json"))
    require(set(modules).isdisjoint(primary), "Project namespace shadows a standard-library/package module")
    require(set(CFG["order"]).isdisjoint(set(modules) | set(primary)), "Prepared final module already exists in dependencies")
    allowed = set(modules) | set(CFG["order"]) | set(primary)
    for module, entry in modules.items():
        require(set(entry["imports"]) <= allowed, ("Unresolved inherited imports", module, set(entry["imports"]) - allowed))
    done = set(modules) | set(primary)
    for module in CFG["order"]:
        imps = imports(P / (module.replace(".", "/") + ".lean"))
        require(set(imps) <= done, ("Unresolved new imports", module, imps))
        done.add(module)
    return modules, provenance


def assemble(modules, provenance):
    for module, entry in modules.items():
        stem = module.replace(".", "/")
        for suffix, part in entry["objects"].items():
            dest = O / (stem + suffix)
            owned_write_path(dest, allow_leaf_symlink=True)
            dest.parent.mkdir(parents=True, exist_ok=True)
            if module in CFG["recheck_inherited"]:
                # Official leanchecker resolves target filenames before looking
                # up module names. These five targets need real local files.
                origin = Path(part["path"])
                verify_file(origin, part["sha256"])
                if dest.is_symlink():
                    require(dest.resolve() == origin.resolve(), ("Wrong merged link", str(dest)))
                    preserved = R / "runtime_recovery/preserved_links" / (stem + suffix)
                    owned_write_path(preserved, allow_leaf_symlink=True)
                    require(not preserved.exists() and not preserved.is_symlink(), ("Preserved link exists", str(preserved)))
                    preserved.parent.mkdir(parents=True, exist_ok=True)
                    dest.rename(preserved)
                if not dest.exists():
                    with origin.open("rb") as source, dest.open("xb") as output:
                        shutil.copyfileobj(source, output)
                require(not dest.is_symlink(), ("Checker target remains linked", str(dest)))
            elif dest.is_symlink():
                require(dest.resolve() == Path(part["path"]).resolve(), ("Wrong merged link", str(dest)))
            else:
                require(not dest.exists(), ("Refusing object overwrite", str(dest)))
                dest.symlink_to(part["path"])
            verify_file(dest, part["sha256"])
    union = {"status": "PASS_HASH_VERIFIED_INHERITED_UNION", "modules": modules,
             "classification_ready_sha256": sha(C / "CLASSIFICATION_READY.json"),
             "compact_interface_result_sha256": sha(Path(CFG["compact_interface"]) / "CHECKED_INTERFACE_RESULT.json"),
             "compact_interface_frozen_sha256": sha(Path(CFG["compact_interface"]) / "FROZEN.json"),
             "compact_statement_sha256": CFG["compact_statement_sha256"],
             "compact_challenge_sha256": CFG["compact_challenge_sha256"],
             "package_provenance_sha256": sha(C / "PROVENANCE_AUDIT.json"),
             "cache_roots": provenance["cache_roots"], "module_count": len(modules),
             "note": "Inherited objects retain their checked source/object manifest ancestry; fresh final modules are separate."}
    immutable(R / "DEPENDENCY_UNION.json", union)
    paths = [str(O)] + provenance["cache_roots"]
    require(len(paths) == len(set(paths)), "Duplicate LEAN_PATH roots")
    env = {key: value for key, value in os.environ.items() if not key.startswith("LEAN_")}
    env.update(PATH=str(B) + ":" + os.environ.get("PATH", ""), LEAN_PATH=":".join(paths), LEAN_NUM_THREADS="1")
    return env


def actual_objects(module):
    stem = O / module.replace(".", "/")
    return {suffix: sha(str(stem) + suffix) for suffix in SUFFIXES if Path(str(stem) + suffix).is_file()}


def ensure_namespace(modules):
    for directory in (P, O, Q, L):
        owned_write_path(directory)
        for child in directory.rglob("*"):
            if child.is_dir():
                require(not child.is_symlink(), ("Linked writable subtree", str(child)))
    for child in O.rglob("*"):
        if child.is_symlink():
            require(child.is_file() and child.name.endswith(SUFFIXES), ("Dangling or unexpected object link", str(child)))
    expected = {str(O / (m.replace(".", "/") + s)) for m, e in modules.items() for s in e["objects"]}
    for module in CFG["order"]:
        expected.update(str(O / (module.replace(".", "/") + s)) for s in actual_objects(module))
    actual = {str(p) for p in O.rglob("*") if p.is_file() and p.name.endswith(SUFFIXES)}
    require(actual == expected, ("Unexpected merged namespace artifacts", sorted(actual - expected)))
    require(not any(P.rglob("*.olean")), "Source tree may not contain shadowing objects")


def stable_inputs():
    for path, (_, previous) in VERIFIED.items():
        require(stamp(path) == previous, ("Verified input changed after preflight", path))


def direct_fingerprints(source, env):
    result = {}
    for module in imports(source):
        stem = module.replace(".", "/")
        candidates = [Path(root) / stem for root in env["LEAN_PATH"].split(":")
                      if (Path(root) / (stem + ".olean")).is_file()]
        require(len(candidates) == 1, ("Missing or shadowed direct import", module))
        base = candidates[0]
        result[module] = {"root": str(base.parent), "objects": {
            suffix: sha(str(base) + suffix) for suffix in SUFFIXES if Path(str(base) + suffix).is_file()}}
    return result


def execute(module, mode, modules, env, lock, run_guarded):
    stem = module.replace(".", "/")
    source = P / (stem + ".lean") if module in CFG["order"] else Path(modules[module]["source"])
    source_hash = sha(source)
    target = O / (stem + ".olean")
    cmd = ([str(B / "lean"), "-j1", "-M3072", "-DautoImplicit=false", "--root=" + str(P),
            "-o", str(target), str(source)] if mode == "compile" else [str(B / "leanchecker"), module])
    tag = mode + "_" + module.replace(".", "_")
    receipt_file = Q / (tag + ".json")
    bindings = {"module": module, "kind": mode, "source_sha256": source_hash, "command": cmd,
                "lean_path": env["LEAN_PATH"], "plan_sha256": sha(R / "PLAN.json"),
                "dependency_union_sha256": sha(R / "DEPENDENCY_UNION.json"),
                "classification_ready_sha256": sha(C / "CLASSIFICATION_READY.json"),
                "direct_dependencies": direct_fingerprints(source, env),
                "runtime_runner_sha256": sha(Path(__file__)),
                "runtime_admission_sha256": sha(R / "runtime_recovery/ADMISSION.json")}
    if receipt_file.exists():
        r = load(receipt_file)
        require(clean(r) and all(r.get(k) == v for k, v in bindings.items()), ("Invalid resume receipt", tag))
        require(r["objects"] == actual_objects(module), ("Resume object mismatch", tag))
        require(set(KERNEL) <= set(r["objects"]), ("Resume sidecar missing", tag))
        require(sha(R / r["log"]) == r["log_sha256"] and sha(R / r["process_identity"]) == r["process_identity_sha256"],
                ("Resume process evidence mismatch", tag))
        if mode == "compile":
            require(r["axioms"] == parse_axioms(module, source, (R / r["log"]).read_text()), ("Resume axiom mismatch", tag))
        print("VERIFIED_RESUME", tag, flush=True)
        return r
    if mode == "check" and module in CFG["order"]:
        r = load(Q / ("compile_" + module.replace(".", "_") + ".json"))
        require(clean(r) and r["source_sha256"] == source_hash and r["objects"] == actual_objects(module),
                ("No exact successful compile before checking", module))
    attempt = str(time.time_ns())
    log, ident = L / f"{tag}.{attempt}.log", L / f"{tag}.{attempt}.process.json"
    owned_write_path(log)
    owned_write_path(ident)

    def before_start():
        stable_inputs()
        ensure_namespace(modules)
        owned_write_path(log)
        owned_write_path(ident)
        owned_write_path(target, allow_leaf_symlink=module not in CFG["order"])
        if module in CFG["order"]:
            for suffix in SUFFIXES:
                owned_write_path(O / (stem + suffix))
        require(direct_fingerprints(source, env) == bindings["direct_dependencies"],
                ("Direct imports changed while waiting for shared lock", module))
        require(sha(source) == source_hash, ("Source changed while waiting for serial lock", module))
        limits = CFG["limits"]
        require(shutil.disk_usage(R).free >= limits["min_disk_free_gib"] * 1024**3, "Free-disk guard")
        available = int(re.search(r"^MemAvailable:\s+(\d+)", Path("/proc/meminfo").read_text(), re.M)[1])
        require(available >= limits["min_memavailable_mib"] * 1024, "Available-memory guard")
        budget = 0.0
        represented = set()
        for f in Q.glob("*.json"):
            r = load(f)
            used = (r.get("user_cpu_seconds") or 0) + (r.get("system_cpu_seconds") or 0)
            budget += used if clean(r) else max(used, limits["per_process_seconds"] + 10)
            if r.get("log"):
                represented.add(Path(r["log"]).name)
        budget += (limits["per_process_seconds"] + 10) * len({f.name for f in L.glob("*.log")} - represented)
        require(budget + limits["per_process_seconds"] + 10 <= limits["cpu_seconds"], "CPU guard: review preserved evidence")
        if mode == "compile" and actual_objects(module):
            # Preserve failed/unreceipted outputs locally; never reuse them.
            dest = R / "unreceipted_products" / module / attempt
            owned_write_path(dest)
            dest.mkdir(parents=True)
            for suffix in SUFFIXES:
                obj = O / (stem + suffix)
                if obj.exists():
                    require(not obj.is_symlink(), ("Refusing to move inherited object", str(obj)))
                    obj.rename(dest / obj.name)

    print("START", tag, flush=True)
    result = run_guarded(cmd, cwd=P, env=env, log_path=log, runner_lock_fd=lock.fileno(),
                         serial_lock_path=CFG["serial_lock"], timeout_seconds=CFG["limits"]["per_process_seconds"],
                         rss_limit_mib=CFG["limits"]["rss_mib"], identity_path=ident, before_start=before_start)
    result["reported_process_exit_code"] = result["exit_code"]
    result.update(bindings, objects=actual_objects(module), axioms={}, log=str(log.relative_to(R)),
                  log_sha256=sha(log) if log.exists() else None, process_identity=str(ident.relative_to(R)),
                  process_identity_sha256=sha(ident) if ident.exists() else None)
    if clean(result):
        try:
            require(set(KERNEL) <= set(result["objects"]), ("Missing fresh kernel sidecars", module))
            if mode == "compile":
                result["axioms"] = parse_axioms(module, source, log.read_text())
        except Exception as exc:
            result["audit_error"] = str(exc)
    if not clean(result):
        result["exit_code"] = result["exit_code"] or 1
    immutable(receipt_file if clean(result) else Q / f"{tag}.failed.{attempt}.json", result)
    require(clean(result), ("Stopped after failed guarded process", tag, result.get("audit_error") or result.get("error")))
    print("DONE", tag, flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute-reviewed", action="store_true", help="Explicitly start only after completed classification provenance passes")
    args = parser.parse_args()
    if not args.execute_reviewed:
        print("PREPARED UNEXECUTED. Four new Lean modules remain unverified. No build was requested.")
        return
    # No checked or frozen input tree is modified by any preparation stage.
    modules, provenance = preflight()
    owned_write_path(R / ".runner.lock")
    with (R / ".runner.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        stable_inputs()
        env = assemble(modules, provenance)
        ensure_namespace(modules)
        spec = importlib.util.spec_from_file_location("henry_owned_guard", R / "scripts/guarded_process.py")
        guard = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(guard)
        checks = {}
        for module in CFG["recheck_inherited"]:
            checks[module] = {"check": execute(module, "check", modules, env, lock, guard.run_guarded)}
        for module in CFG["order"]:
            checks[module] = {}
            for mode in ("compile", "check"):
                checks[module][mode] = execute(module, mode, modules, env, lock, guard.run_guarded)
        stable_inputs()
        ensure_namespace(modules)
        # Rehash every inherited source, object, receipt, log, and cached artifact
        # after the last check; unchanged metadata alone is not the final gate.
        for path, (expected, _) in VERIFIED.items():
            require(sha(path) == expected, ("Post-check provenance hash mismatch", path))
        for module in CFG["order"]:
            for mode in ("compile", "check"):
                require(checks[module][mode]["objects"] == actual_objects(module), ("Final object changed", module))
        axioms = {name: values for modes in checks.values() for result in modes.values()
                  for name, values in result["axioms"].items()}
        required = {"SparseMonotiles.ExactCompactT7Strong.final_bound", "PalomarMonotiles.T7_strongAperiodicity",
                    "SparseMonotiles.ExactCompactT7Strong.FreshAudit.final_bound_expanded",
                    "PalomarMonotiles.FinalExactTypeAudit.public_solution_expanded"}
        require(required <= set(axioms), "Missing final endpoint axiom closure")
        immutable(R / "AXIOM_AUDIT.json", {"status": "PASS_ALLOWED_STANDARD_AXIOMS_ONLY", "declarations": axioms})
        receipts = {p.name: sha(p) for p in Q.glob("*.json") if ".failed." not in p.name}
        require(len(receipts) == len(CFG["recheck_inherited"]) + 2 * len(CFG["order"]) == 13,
                "Incomplete final successful process set")
        immutable(R / "FINAL_COMPOSITION_READY.json", {
            "status": "PASS_EXACT_HENRY_STRONG_APERIODICITY", "public_endpoint": "PalomarMonotiles.T7_strongAperiodicity",
            "internal_endpoint": "SparseMonotiles.ExactCompactT7Strong.final_bound", "bound": 645120,
            "new_compiled_and_default_kernelchecked_modules": CFG["order"],
            "inherited_interface_modules_default_rechecked": CFG["recheck_inherited"],
            "dependency_union_sha256": sha(R / "DEPENDENCY_UNION.json"),
            "classification_ready_sha256": sha(C / "CLASSIFICATION_READY.json"),
            "compact_interface_result_sha256": sha(Path(CFG["compact_interface"]) / "CHECKED_INTERFACE_RESULT.json"),
            "compact_interface_frozen_sha256": sha(Path(CFG["compact_interface"]) / "FROZEN.json"),
            "compact_statement_sha256": CFG["compact_statement_sha256"],
            "compact_challenge_sha256": CFG["compact_challenge_sha256"],
            "axiom_audit_sha256": sha(R / "AXIOM_AUDIT.json"), "receipt_hashes": receipts,
            "source_sha256": {rel: sha(R / rel) for rel in CFG["sources"]},
            "new_objects": {m: actual_objects(m) for m in CFG["order"]},
            "runtime_runner_sha256": sha(Path(__file__)),
            "runtime_admission_sha256": sha(R / "runtime_recovery/ADMISSION.json"),
            "independent_external_preflight_run": False, "submission_or_external_writes_performed": False})
        print("FINAL_COMPOSITION_READY: exact internal and public results compiled and default-kernelchecked", flush=True)


if __name__ == "__main__":
    main()
