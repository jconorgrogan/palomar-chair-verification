"""Read-only, fixed Lean 4.35.0-rc2 runtime binding. No execution authority.

The sibling inventory is digest-pinned. No public API accepts an inventory,
alias allowlist, replacement deadline, executor, or completed receipt. This
module neither installs nor executes a runtime and does not alter the generic
no-symlink input/output scanner or enable any production controller.

Filesystem checking is not an atomic snapshot against a hostile writer. The
parent must own and exclude untrusted writers from the runtime through use,
pin this source and its dependency graph, and revalidate at consumption time.
Python object privacy is an accidental-misuse guard, not a hostile-host boundary.
"""
from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass, field
import hashlib
import json
import os
import stat
from types import MappingProxyType
from typing import Callable
import weakref


INVENTORY_SHA256 = "42bd268b1ca3e9bf89f4149ac427d6c0e76f735233b092a6df4ca27a2c2db7ea"
ARCHIVE_SHA256 = "b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049"
ARCHIVE_PREFIX = "lean-4.35.0-rc2-linux"
SCHEMA = "official-lean-release-inventory-v1"
_CHUNK = 256 * 1024
_MAX_INVENTORY = 4 * 1024 * 1024
_FLAGS = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
_ISSUED = weakref.WeakKeyDictionary()


class Rejected(RuntimeError):
    """Fail-closed inventory, filesystem, or binding rejection."""


def _need(ok, message):
    if not ok:
        raise Rejected(message)


def _relative(path):
    _need(type(path) is str and 0 < len(path) <= 1024, "relative path required")
    _need("\\" not in path and "\x00" not in path, "invalid relative path")
    parts = path.split("/")
    _need(len(parts) <= 32 and all(x not in ("", ".", "..") for x in parts),
          "noncanonical relative path")
    return path


def _absolute(path):
    _need(type(path) is str and path.startswith("/") and path != "/",
          "non-root absolute string required")
    _relative(path[1:])
    return path


def _identity(s):
    return (s.st_dev, s.st_ino, s.st_mode, s.st_uid, s.st_gid, s.st_nlink,
            s.st_size, s.st_mtime_ns, s.st_ctime_ns)


def _ancestor_identity(s):
    # Ancestors may contain unrelated work. Only their identity and permissions
    # bind; mtime/ctime changes there do not claim a runtime-tree mutation.
    return (s.st_dev, s.st_ino, s.st_mode, s.st_uid, s.st_gid)


def _same(a, b):
    _need(_identity(a) == _identity(b), "entry changed during verification")


def _owned(s, *, directory=False, symlink=False):
    _need(s.st_uid == os.getuid(), "runtime entry is not owned by verifier")
    if not symlink:
        _need(not s.st_mode & 0o7022, "runtime entry has unsafe mode")
    if directory:
        _need(stat.S_ISDIR(s.st_mode), "directory required")
    elif symlink:
        _need(stat.S_ISLNK(s.st_mode) and s.st_nlink == 1, "symlink alias or hardlink")
    else:
        _need(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, "regular file or hardlink")


@contextmanager
def _root(path, tick):
    """Open every absolute component with O_NOFOLLOW, including all ancestors."""
    _absolute(path)
    tick()
    fd = os.open("/", _FLAGS | os.O_DIRECTORY)
    ancestors = []
    try:
        ancestors.append(_ancestor_identity(os.fstat(fd)))
        for name in path[1:].split("/"):
            tick()
            before = os.stat(name, dir_fd=fd, follow_symlinks=False)
            _need(stat.S_ISDIR(before.st_mode), "root has a symlink or nondirectory component")
            child = os.open(name, _FLAGS | os.O_DIRECTORY, dir_fd=fd)
            try:
                tick()
                _same(before, os.fstat(child))
            except BaseException:
                os.close(child)
                raise
            os.close(fd)
            fd = child
            ancestors.append(_ancestor_identity(before))
        yield fd, tuple(ancestors)
    finally:
        os.close(fd)


@contextmanager
def _parent(root_fd, relative, tick, nodes):
    """No symlink is followed even when examining a recorded alias."""
    parts = _relative(relative).split("/")
    fd = os.dup(root_fd)
    try:
        _need(_identity(os.fstat(fd)) == nodes["."].identity, "resolution root changed")
        prefix = []
        for name in parts[:-1]:
            tick()
            before = os.stat(name, dir_fd=fd, follow_symlinks=False)
            _need(stat.S_ISDIR(before.st_mode), "path parent is not a real directory")
            prefix.append(name)
            _need(_identity(before) == nodes["/".join(prefix)].identity,
                  "resolution parent directory changed")
            child = os.open(name, _FLAGS | os.O_DIRECTORY, dir_fd=fd)
            try:
                _same(before, os.fstat(child))
            except BaseException:
                os.close(child)
                raise
            os.close(fd)
            fd = child
        tick()
        yield fd, parts[-1]
    finally:
        os.close(fd)


def _hash_file(fd, expected, tick, *, collect=False):
    tick()
    before = os.fstat(fd)
    _owned(before)
    _need(before.st_size == expected, "regular file byte count differs")
    digest, count, chunks = hashlib.sha256(), 0, []
    while True:
        tick()
        chunk = os.read(fd, min(_CHUNK, expected - count + 1))
        tick()
        if not chunk:
            break
        count += len(chunk)
        _need(count <= expected, "regular file grew during hash")
        digest.update(chunk)
        if collect:
            chunks.append(chunk)
        tick()
    _need(count == expected, "regular file truncated during hash")
    _same(before, os.fstat(fd))
    tick()
    return digest.hexdigest(), b"".join(chunks) if collect else None, _identity(before)


def _read_inventory(tick):
    # Relocatable sibling; source and inventory are jointly pinned by the parent.
    path = os.path.abspath(__file__)
    _absolute(path)
    parent, name = path.rsplit("/", 1)[0], "inventory.json"
    with _root(parent, tick) as (fd, ancestors):
        tick()
        before = os.stat(name, dir_fd=fd, follow_symlinks=False)
        _owned(before)
        _need(0 < before.st_size <= _MAX_INVENTORY, "inventory byte bound")
        child = os.open(name, _FLAGS, dir_fd=fd)
        try:
            _same(before, os.fstat(child))
            digest, raw, identity = _hash_file(child, before.st_size, tick, collect=True)
            _same(before, os.stat(name, dir_fd=fd, follow_symlinks=False))
        finally:
            os.close(child)
        _need(digest == INVENTORY_SHA256, "fixed official inventory digest differs")
        with _root(parent, tick) as (final_fd, final_ancestors):
            _need(final_ancestors == ancestors, "inventory path ancestry changed")
            _need(_identity(os.stat(name, dir_fd=final_fd, follow_symlinks=False)) == identity,
                  "inventory path changed")
    tick()
    return raw, (parent + "/" + name, ancestors, identity)


@dataclass(frozen=True)
class _Inventory:
    files: object
    aliases: object
    directories: frozenset
    children: object
    terminals: object
    digest: str


def _inventory(raw, tick, *, official):
    _need(type(raw) is bytes and 0 < len(raw) <= _MAX_INVENTORY, "inventory raw bytes")
    tick()

    def pairs(items):
        result = {}
        for key, value in items:
            tick()
            _need(key not in result, "duplicate inventory JSON member")
            result[key] = value
        return result

    try:
        obj = json.loads(raw, object_pairs_hook=pairs,
                         parse_constant=lambda _: (_ for _ in ()).throw(Rejected("nonfinite JSON")))
    except (ValueError, UnicodeError, RecursionError) as exc:
        raise Rejected("invalid inventory JSON") from exc
    tick()
    _need(type(obj) is dict and set(obj) == {
        "archive_prefix", "archive_sha256", "files", "logical_file_bytes", "schema", "symlinks"},
        "inventory schema fields")
    _need(obj["schema"] == SCHEMA and type(obj["schema"]) is str, "inventory schema")
    _need(obj["archive_prefix"] == ARCHIVE_PREFIX and obj["archive_sha256"] == ARCHIVE_SHA256,
          "inventory release identity")
    _need(type(obj["files"]) is dict and type(obj["symlinks"]) is dict, "inventory entry maps")
    _need(type(obj["logical_file_bytes"]) is int and obj["logical_file_bytes"] >= 0,
          "inventory total bytes")
    files, aliases = {}, dict(obj["symlinks"])
    _need(0 < len(obj["files"]) <= 20000 and len(aliases) <= 100, "inventory entry count")
    total = 0
    for path, spec in obj["files"].items():
        tick()
        _relative(path)
        _need(type(spec) is dict and set(spec) == {"bytes", "mode", "sha256"}, "file pin schema")
        size, mode, digest = spec["bytes"], spec["mode"], spec["sha256"]
        _need(type(size) is int and 0 <= size <= 4 * 1024**3, "file byte pin")
        _need(type(mode) is int and mode in (0o644, 0o755), "file mode pin")
        _need(type(digest) is str and len(digest) == 64 and
              all(c in "0123456789abcdef" for c in digest), "file hash pin")
        total += size
        files[path] = (size, mode, digest)
    _need(total == obj["logical_file_bytes"] and total <= 4 * 1024**3, "logical byte pin")
    for path, target in aliases.items():
        tick()
        _relative(path)
        _relative(target)
        _need(path not in files, "file/alias collision")
    directories = {"."}
    for path in files.keys() | aliases.keys():
        tick()
        parts = path.split("/")
        directories.update("/".join(parts[:i]) for i in range(1, len(parts)))
    _need(not (directories & (files.keys() | aliases.keys())), "nondirectory path parent")
    children = {p: set() for p in directories}
    for path in (files.keys() | aliases.keys() | directories) - {"."}:
        tick()
        parent, sep, name = path.rpartition("/")
        children[parent if sep else "."].add(name)
    terminals = {}
    for alias in aliases:
        tick()
        path, seen = alias, set()
        while path in aliases:
            tick()
            _need(path not in seen, "inventory symlink cycle")
            seen.add(path)
            parent, sep, _ = path.rpartition("/")
            path = (parent + "/" if sep else "") + aliases[path]
            _relative(path)
        _need(path in files, "alias target is missing, outside, or not a regular file")
        terminals[alias] = path
    digest = hashlib.sha256(raw).hexdigest()
    if official:
        _need(digest == INVENTORY_SHA256 and len(files) == 17918 and len(aliases) == 13
              and total == 3145390820, "fixed official inventory pins differ")
    tick()
    return _Inventory(MappingProxyType(files), MappingProxyType(aliases), frozenset(directories),
                      MappingProxyType({p: frozenset(v) for p, v in children.items()}),
                      MappingProxyType(terminals), digest)


@dataclass(frozen=True)
class EntryBinding:
    path: str
    kind: str
    identity: tuple
    sha256: str | None = None
    target: str | None = None
    resolved_path: str | None = None
    resolved_identity: tuple | None = None


@dataclass(frozen=True, eq=False)
class OfficialRuntimeBinding:
    """Inert receipt. Constructed lookalikes are rejected by revalidation."""
    root: str
    inventory_sha256: str
    entries: tuple[EntryBinding, ...]


@dataclass(frozen=True, eq=False)
class _SyntheticRuntimeBinding:
    """Explicit offline test output; never accepted by production revalidation."""
    root: str
    inventory_sha256: str
    entries: tuple[EntryBinding, ...]


@dataclass(frozen=True)
class _State:
    inventory: _Inventory
    check_deadline: Callable[[], None] = field(repr=False)
    root_ancestors: tuple
    inventory_binding: tuple | None


def _resolve(fd, path, inv, nodes, tick):
    seen = set()
    while path in inv.aliases:
        tick()
        _need(path not in seen, "filesystem alias cycle")
        seen.add(path)
        with _parent(fd, path, tick, nodes) as (parent, name):
            before = os.stat(name, dir_fd=parent, follow_symlinks=False)
            _owned(before, symlink=True)
            _need(_identity(before) == nodes[path].identity, "alias inode changed")
            tick()
            target = os.readlink(name, dir_fd=parent)
            _need(target == inv.aliases[path], "alias target text changed")
            tick()
            _same(before, os.stat(name, dir_fd=parent, follow_symlinks=False))
        prefix, sep, _ = path.rpartition("/")
        path = (prefix + "/" if sep else "") + target
        _relative(path)
    _need(path in inv.files, "alias resolved outside its recorded regular target")
    with _parent(fd, path, tick, nodes) as (parent, name):
        tick()
        before = os.stat(name, dir_fd=parent, follow_symlinks=False)
        _owned(before)
        _need(_identity(before) == nodes[path].identity, "alias resolved target inode changed")
        child = os.open(name, _FLAGS, dir_fd=parent)
        try:
            tick()
            _same(before, os.fstat(child))
            _same(before, os.stat(name, dir_fd=parent, follow_symlinks=False))
        finally:
            os.close(child)
    tick()
    return path, _identity(before)


def _snapshot(root, inv, tick):
    tick()
    with _root(root, tick) as (fd, ancestors):
        nodes, seen = {}, set()

        def walk(parent, path, *, final):
            tick()
            before = os.fstat(parent)
            _owned(before, directory=True)
            directory = EntryBinding(path, "directory", _identity(before))
            if final:
                _need(directory == nodes[path], "directory changed before final check")
            else:
                _need((before.st_dev, before.st_ino) not in seen, "directory inode alias")
                seen.add((before.st_dev, before.st_ino))
                nodes[path] = directory
            tick()
            names = set()
            # Refuse the first unexpected name instead of materializing an
            # attacker-sized directory listing before the next deadline check.
            with os.scandir(parent) as listing:
                for item in listing:
                    tick()
                    _need(item.name in inv.children[path] and item.name not in names,
                          "extra or duplicate runtime entry")
                    names.add(item.name)
            tick()
            _need(names == inv.children[path], "missing runtime entries")
            for name in sorted(names):
                tick()
                relative = name if path == "." else path + "/" + name
                entry = os.stat(name, dir_fd=parent, follow_symlinks=False)
                if relative in inv.directories:
                    _owned(entry, directory=True)
                    child = os.open(name, _FLAGS | os.O_DIRECTORY, dir_fd=parent)
                    try:
                        _same(entry, os.fstat(child))
                        walk(child, relative, final=final)
                        _same(entry, os.stat(name, dir_fd=parent, follow_symlinks=False))
                    finally:
                        os.close(child)
                elif relative in inv.files:
                    _owned(entry)
                    size, mode, digest = inv.files[relative]
                    _need(entry.st_size == size and stat.S_IMODE(entry.st_mode) == mode,
                          "regular file size/mode differs")
                    if final:
                        _need(_identity(entry) == nodes[relative].identity, "file changed before final check")
                    else:
                        inode = entry.st_dev, entry.st_ino
                        _need(inode not in seen, "regular file inode alias")
                        seen.add(inode)
                        child = os.open(name, _FLAGS, dir_fd=parent)
                        try:
                            _same(entry, os.fstat(child))
                            actual, _, identity = _hash_file(child, size, tick)
                            _need(actual == digest, "regular file hash differs")
                            _same(entry, os.stat(name, dir_fd=parent, follow_symlinks=False))
                        finally:
                            os.close(child)
                        nodes[relative] = EntryBinding(relative, "file", identity, actual)
                else:
                    _owned(entry, symlink=True)
                    tick()
                    target = os.readlink(name, dir_fd=parent)
                    _need(target == inv.aliases[relative], "alias target text differs")
                    _same(entry, os.stat(name, dir_fd=parent, follow_symlinks=False))
                    if final:
                        _need(_identity(entry) == nodes[relative].identity, "symlink changed before final check")
                    else:
                        inode = entry.st_dev, entry.st_ino
                        _need(inode not in seen, "symlink inode alias")
                        seen.add(inode)
                        nodes[relative] = EntryBinding(relative, "symlink", _identity(entry), target=target)
                tick()
            _same(before, os.fstat(parent))
            tick()

        walk(fd, ".", final=False)
        for path in sorted(inv.aliases):
            tick()
            resolved, identity = _resolve(fd, path, inv, nodes, tick)
            _need(resolved == inv.terminals[path], "alias resolution differs")
            old = nodes[path]
            nodes[path] = EntryBinding(path, "symlink", old.identity, target=old.target,
                                       resolved_path=resolved, resolved_identity=identity)
        # Reopen from /: reject replacement or aliases in any root component.
        with _root(root, tick) as (final_fd, final_ancestors):
            _need(final_ancestors == ancestors, "runtime root ancestry changed")
            walk(final_fd, ".", final=True)
            for path in sorted(inv.aliases):
                tick()
                resolved, identity = _resolve(final_fd, path, inv, nodes, tick)
                _need((resolved, identity) == (nodes[path].resolved_path, nodes[path].resolved_identity),
                      "final alias resolution differs")
            _need(_identity(os.fstat(final_fd)) == nodes["."].identity, "final runtime root changed")
            # Re-resolve the absolute root after the alias checks rather than
            # assuming a still-open directory descriptor retains its pathname.
            with _root(root, tick) as (last_fd, last_ancestors):
                _need(last_ancestors == ancestors and
                      _identity(os.fstat(last_fd)) == nodes["."].identity,
                      "runtime root resolution changed after final aliases")
            tick()
        tick()
        return tuple(nodes[p] for p in sorted(nodes)), ancestors


def bind_official_runtime(root: str, *, check_deadline: Callable[[], None]) -> OfficialRuntimeBinding:
    """Hash exact official runtime; retain this same parent's deadline callback.

    This expensive read is deliberately never run by the offline test suite.
    It reads 3,145,390,820 official runtime bytes when used in production.
    """
    _need(callable(check_deadline), "original deadline callback required")
    try:
        raw, inventory_binding = _read_inventory(check_deadline)
        inv = _inventory(raw, check_deadline, official=True)
        entries, ancestors = _snapshot(root, inv, check_deadline)
        # The pin document must also still denote the exact original inode.
        _, final_inventory = _read_inventory(check_deadline)
        _need(final_inventory == inventory_binding, "inventory replaced during runtime binding")
        check_deadline()
        binding = OfficialRuntimeBinding(root, inv.digest, entries)
        _ISSUED[binding] = _State(inv, check_deadline, ancestors, inventory_binding)
        return binding
    except OSError as exc:
        raise Rejected("official runtime filesystem check failed") from exc


def revalidate_official_runtime(binding: OfficialRuntimeBinding) -> None:
    """Rehash all runtime bytes and final alias resolutions under original deadline."""
    _need(type(binding) is OfficialRuntimeBinding and binding in _ISSUED,
          "unissued or synthetic official runtime binding")
    _revalidate(binding)


def _revalidate(binding):
    state = _ISSUED[binding]
    tick = state.check_deadline
    try:
        tick()
        if state.inventory_binding is not None:
            _, current_inventory = _read_inventory(tick)
            _need(current_inventory == state.inventory_binding, "bound inventory changed")
        entries, ancestors = _snapshot(binding.root, state.inventory, tick)
        _need(entries == binding.entries and ancestors == state.root_ancestors,
              "runtime differs from original inode/hash binding")
        if state.inventory_binding is not None:
            _, current_inventory = _read_inventory(tick)
            _need(current_inventory == state.inventory_binding, "bound inventory changed during revalidation")
        tick()
    except OSError as exc:
        raise Rejected("runtime revalidation filesystem check failed") from exc


def _bind_synthetic_inventory_for_tests(root: str, inventory_bytes: bytes, *, check_deadline):
    """Explicit synthetic seam. No production binding or execution authority."""
    _need(callable(check_deadline), "synthetic deadline callback required")
    try:
        inv = _inventory(inventory_bytes, check_deadline, official=False)
        entries, ancestors = _snapshot(root, inv, check_deadline)
        binding = _SyntheticRuntimeBinding(root, inv.digest, entries)
        _ISSUED[binding] = _State(inv, check_deadline, ancestors, None)
        return binding
    except OSError as exc:
        raise Rejected("synthetic runtime filesystem check failed") from exc


def _revalidate_synthetic_inventory_for_tests(binding):
    _need(type(binding) is _SyntheticRuntimeBinding and binding in _ISSUED,
          "unissued or nonsynthetic test binding")
    _revalidate(binding)
