"""Inactive Conron recovery specification and fixed read-only headroom gate.

No dispatch, upload, mount, cgroup write or process is implemented here.
The caller must be the reviewed hosted-VM driver, using its original Budget.
The full host hierarchy is an explicit hosted-VM assumption. The real-root
memory-interface check rejects a visible, constrained cgroup namespace root.
"""
from __future__ import annotations
import hashlib
import json
import os
import re
import stat

EXECUTION_RELEASED = False
GIB = 1024 ** 3
REQUIRED_HEADROOM = 8 * GIB
MAX_DEPTH = 64
MAX_TOTAL_READ = 1024 * 1024
MAX_REPORT_BYTES = 128 * 1024


class Rejected(RuntimeError):
    pass


def need(value, reason):
    if not value:
        raise Rejected(reason)


def conron_spec(toolchain_root, export_path):
    for value in (toolchain_root, export_path):
        need(type(value) is str and value.startswith('/') and value != '/' and
             all(x not in ('', '.', '..') for x in value[1:].split('/')) and
             '\x00' not in value, 'CONRON_PATH')
    return {'name': 'conron',
        'argv': [toolchain_root + '/bin/con-ron', '--verified', '--jobs=1', export_path],
        'timeout_seconds': 18000,
        'resource_limits': {'address_space_bytes': 24 * GIB,
            'rss_tree_bytes': 6 * GIB, 'max_created_file_bytes': 32 * 1024**2},
        'max_log_bytes': 32 * 1024**2,
        'new_sessions_explicitly_allowed': False}


def _identity(st):
    return (st.st_dev, st.st_ino, st.st_mode)


class _Reader:
    """Bounded no-follow reads; every owned FD closes on every return path."""
    def __init__(self, budget):
        self.budget = budget
        self.total = 0

    def read(self, path, cap, optional=False):
        self.budget.check()
        parts = path.split('/')[1:]
        need(path.startswith('/') and parts and len(parts) <= MAX_DEPTH + 6 and
             all(p not in ('', '.', '..') for p in parts), 'HEADROOM_PATH')
        fds, names = [], []
        raw = None
        try:
            fd = os.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            fds.append(fd)
            names.append(('/', _identity(os.fstat(fd))))
            prefix = ''
            for part in parts[:-1]:
                self.budget.check()
                fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                             dir_fd=fd)
                fds.append(fd)
                prefix += '/' + part
                names.append((prefix, _identity(os.fstat(fd))))
            try:
                file_fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                                  dir_fd=fd)
            except FileNotFoundError:
                need(optional, 'HEADROOM_REQUIRED_FILE')
                names.append((path, None))
            else:
                fds.append(file_fd)
                before = os.fstat(file_fd)
                need(stat.S_ISREG(before.st_mode), 'HEADROOM_FILE_TYPE')
                names.append((path, _identity(before)))
                data = bytearray()
                while True:
                    self.budget.check()
                    room = min(cap + 1 - len(data), MAX_TOTAL_READ + 1 - self.total)
                    need(room > 0, 'HEADROOM_READ_BOUND')
                    chunk = os.read(file_fd, min(65536, room))
                    self.total += len(chunk)
                    data.extend(chunk)
                    need(len(data) <= cap and self.total <= MAX_TOTAL_READ,
                         'HEADROOM_READ_BOUND')
                    if not chunk:
                        break
                need(_identity(os.fstat(file_fd)) == _identity(before),
                     'HEADROOM_FILE_CHANGED')
                raw = bytes(data)
        finally:
            error = None
            for fd in reversed(fds):
                try:
                    os.close(fd)
                except OSError as exc:
                    error = exc
            if error is not None:
                raise Rejected('HEADROOM_FD_CLOSE') from None
            self.budget.check()
        for name, expected in names:
            self.budget.check()
            try:
                actual = _identity(os.lstat(name))
            except FileNotFoundError:
                actual = None
            need(actual == expected, 'HEADROOM_PATH_CHANGED')
        self.budget.check()
        return raw

    def namespace(self):
        self.budget.check()
        own = _identity(os.stat('/proc/%d/ns/cgroup' % os.getpid()))
        self.budget.check()
        return own

    def mount_device(self):
        self.budget.check()
        st = os.lstat('/sys/fs/cgroup')
        need(stat.S_ISDIR(st.st_mode), 'HEADROOM_CGROUP_MOUNT')
        self.budget.check()
        return '%d:%d' % (os.major(st.st_dev), os.minor(st.st_dev))


def _text(raw):
    need(type(raw) is bytes and b'\x00' not in raw, 'HEADROOM_TEXT')
    try:
        return raw.decode('ascii')
    except UnicodeError:
        raise Rejected('HEADROOM_TEXT') from None


def _number(raw, allow_max=False):
    value = _text(raw)
    if allow_max and value == 'max\n':
        return None
    need(re.fullmatch(r'(0|[1-9][0-9]{0,19})\n', value) is not None,
         'HEADROOM_NUMBER')
    result = int(value)
    need(result < 2**63, 'HEADROOM_NUMBER')
    return result


def _controllers(raw):
    value = _text(raw)
    need(value.endswith('\n'), 'HEADROOM_CONTROLLERS')
    rows = value[:-1].split() if value[:-1] else []
    need(len(rows) <= 32 and len(set(rows)) == len(rows) and
         all(re.fullmatch(r'[a-z][a-z0-9_]{0,31}', x) for x in rows),
         'HEADROOM_CONTROLLERS')
    return sorted(rows)


def _membership(raw):
    value = _text(raw)
    need(value.startswith('0::/') and value.count('\n') == 1 and value.endswith('\n'),
         'HEADROOM_UNSUPPORTED_CGROUP')
    path = value[3:-1]
    parts = [] if path == '/' else path[1:].split('/')
    need(len(parts) <= MAX_DEPTH and all(x not in ('.', '..') and
         re.fullmatch(r'[A-Za-z0-9_.:@+-]{1,255}', x) for x in parts),
         'HEADROOM_CGROUP_PATH')
    return parts


def _mount(raw):
    rows = _text(raw).splitlines()
    need(len(rows) <= 2048, 'HEADROOM_MOUNT_BOUND')
    found = []
    for row in rows:
        columns = row.split(' ')
        need(columns.count('-') == 1, 'HEADROOM_MOUNT_SCHEMA')
        separator = columns.index('-')
        need(separator >= 6 and len(columns) >= separator + 4, 'HEADROOM_MOUNT_SCHEMA')
        kind = columns[separator + 1]
        need(kind != 'cgroup', 'HEADROOM_UNSUPPORTED_CGROUP')
        target = columns[4]
        need(not target.startswith('/sys/fs/cgroup/') and
             (target != '/sys/fs/cgroup' or kind == 'cgroup2'),
             'HEADROOM_CGROUP_COVERING_MOUNT')
        if kind == 'cgroup2':
            need(columns[3] == '/' and columns[4] == '/sys/fs/cgroup',
                 'HEADROOM_CGROUP_MOUNT')
            need(re.fullmatch(r'[0-9]+:[0-9]+', columns[2]) is not None,
                 'HEADROOM_MOUNT_SCHEMA')
            found.append(row)
    need(len(found) == 1, 'HEADROOM_CGROUP_MOUNT')
    return found[0]


def _host(raw):
    values = {}
    for line in _text(raw).splitlines():
        if line.startswith(('MemTotal:', 'MemAvailable:')):
            match = re.fullmatch(r'(MemTotal|MemAvailable): +([0-9]{1,20}) kB', line)
            need(match is not None and match[1] not in values, 'HEADROOM_MEMINFO')
            values[match[1]] = int(match[2]) * 1024
    need(set(values) == {'MemTotal', 'MemAvailable'} and
         0 <= values['MemAvailable'] <= values['MemTotal'] < 2**63,
         'HEADROOM_MEMINFO')
    return values


def _sample(reader):
    pid = os.getpid()
    membership_raw = reader.read('/proc/%d/cgroup' % pid, 8192)
    mount_raw = reader.read('/proc/%d/mountinfo' % pid, 128 * 1024)
    parts, mount = _membership(membership_raw), _mount(mount_raw)
    namespace = reader.namespace()
    need(reader.mount_device() == mount.split()[2], 'HEADROOM_CGROUP_DEVICE')
    host = _host(reader.read('/proc/meminfo', 64 * 1024))
    root = '/sys/fs/cgroup'
    rows = []
    parent_controls = None
    for depth in range(len(parts) + 1):
        path = root + (('/' + '/'.join(parts[:depth])) if depth else '')
        available_raw = reader.read(path + '/cgroup.controllers', 4096)
        available_controls = _controllers(available_raw)
        controls_raw = reader.read(path + '/cgroup.subtree_control', 4096)
        controls = _controllers(controls_raw)
        applies = depth == 0 or 'memory' in parent_controls
        need(set(controls).issubset(available_controls) and
             (('memory' in available_controls) == applies),
             'HEADROOM_CONTROLLER_INCONSISTENT')
        limit_raw = reader.read(path + '/memory.max', 128, optional=True)
        current_raw = reader.read(path + '/memory.current', 128, optional=True)
        need(depth != 0 or (limit_raw is None and current_raw is None),
             'HEADROOM_CGROUP_ROOT')
        # The real v2 root has no memory controller limit/current interface.
        # A missing non-root interface is accepted only when its parent has
        # explicitly not delegated memory, so the already-checked ancestor
        # owns the constraint. Unknown absence is never unlimited capacity.
        if limit_raw is None or current_raw is None:
            need(limit_raw is None and current_raw is None and
                 (depth == 0 or not applies), 'HEADROOM_REQUIRED_LIMIT')
            limit = current = available = None
        else:
            need(applies, 'HEADROOM_CONTROLLER_INCONSISTENT')
            limit, current = _number(limit_raw, True), _number(current_raw)
            available = None if limit is None else max(0, limit - current)
            need(reader.read(path + '/memory.max', 128) == limit_raw,
                 'HEADROOM_LIMIT_CHANGED')
        need(reader.read(path + '/cgroup.subtree_control', 4096) == controls_raw,
             'HEADROOM_CONTROLLERS_CHANGED')
        need(reader.read(path + '/cgroup.controllers', 4096) == available_raw,
             'HEADROOM_CONTROLLERS_CHANGED')
        rows.append({'path': path, 'limit': limit, 'current': current,
                     'available': available, 'subtree_control': controls,
                     'controllers': available_controls})
        parent_controls = controls
    need(reader.read('/proc/%d/cgroup' % pid, 8192) == membership_raw and
         reader.read('/proc/%d/mountinfo' % pid, 128 * 1024) == mount_raw and
         reader.namespace() == namespace and
         reader.mount_device() == mount.split()[2], 'HEADROOM_LAYOUT_CHANGED')
    remaining = [host['MemAvailable']] + [x['available'] for x in rows
                                         if x['available'] is not None]
    return {'host': host, 'ancestors': rows, 'minimum_available': min(remaining),
            'membership_sha256': hashlib.sha256(membership_raw).hexdigest(),
            'mountinfo_sha256': hashlib.sha256(mount_raw).hexdigest(),
            'mount': mount, 'namespace': list(namespace)}


def require_headroom(budget):
    """Use immediately before dispatch inside the original Budget.process call.

    The record is a measured precondition, never an execution capability or an
    exclusive reservation. Only unified v2 with the full hosted-VM root visible
    is supported. No filesystem, mount, namespace or cgroup settings are written.
    """
    budget.check()
    reader = _Reader(budget)
    first, last = _sample(reader), _sample(reader)
    for key in ('membership_sha256', 'mountinfo_sha256', 'mount', 'namespace'):
        need(first[key] == last[key], 'HEADROOM_LAYOUT_CHANGED')
    shape = lambda sample: [(r['path'], r['limit'], r['subtree_control'], r['controllers'])
                            for r in sample['ancestors']]
    need(shape(first) == shape(last), 'HEADROOM_LIMIT_CHANGED')
    available = min(first['minimum_available'], last['minimum_available'])
    need(available >= REQUIRED_HEADROOM, 'HEADROOM_INSUFFICIENT')
    result = {'schema': 'conron-host-headroom-v1', 'status': 'observed',
        'required_bytes': REQUIRED_HEADROOM, 'minimum_available_bytes': available,
        'samples': [first, last], 'read_bytes': reader.total,
        'exclusive_reservation': False, 'sufficient_checker_memory_proved': False,
        'host_initial_cgroup_namespace_is_trusted_environment_assumption': True}
    need(len(json.dumps(result, sort_keys=True, separators=(',', ':')).encode())
         <= MAX_REPORT_BYTES, 'HEADROOM_REPORT_BOUND')
    budget.check()
    return result
