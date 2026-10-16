#!/usr/bin/env python3
"""Fail-closed, read-only verifier for one restricted conditional artifact stream.

The caller, not this module, authenticates the expected manifest and provenance.
No network, extraction, compiler, object import, archive admission, or resumption.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import PurePosixPath
import re
import stat
import struct
import sys
import tarfile
import time
import zlib

CHUNK = 64 * 1024
MAX_METADATA = 4 * 1024**2
MAX_EXPECTATION = 8 * 1024**2
MAX_MEMBER = 512 * 1024**2
MAX_EVIDENCE = 124 * 1024**2
MAX_FILES = 40000
# Deliberately below 4 GiB. ZIP64 and 4-GiB raw archives are unsupported.
MAX_ZIP = 0xFFFFFFFE
MAX_SECONDS = 1800
REPOSITORY = 'jconorgrogan/palomar-chair-verification'
WORKFLOW = '.github/workflows/conditional-geometry.yml'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir.sig', '.ir', '.c')
META_KEYS = {'identity', 'stage_id', 'stage_modules', 'admitted_stages',
             'contract_sha256', 'interface_identity', 'producer_work',
             'runtime_inventory_sha256', 'predecessor_artifacts'}
SHA = re.compile(r'[0-9a-f]{64}')
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
STAGE = re.compile(r'F[0-4]_[a-z][a-z0-9_]*')


class Rejected(Exception):
    pass


def need(condition, message):
    if not condition:
        raise Rejected(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical_json(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode('utf-8')


def _pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def parse_json(data):
    try:
        return json.loads(data, object_pairs_hook=_pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(Rejected('nonfinite JSON')))
    except (ValueError, RecursionError, UnicodeError) as error:
        raise Rejected('invalid JSON') from error


def digest(value):
    return isinstance(value, str) and SHA.fullmatch(value) is not None


def positive(value):
    return type(value) is int and value > 0


def safe_name(name):
    need(isinstance(name, str) and name and '\\' not in name and '\x00' not in name,
         'invalid member path')
    path = PurePosixPath(name)
    need(not path.is_absolute() and str(path) == name
         and all(part not in ('', '.', '..') for part in path.parts)
         and len(path.parts) <= 12 and len(name.encode('utf-8')) <= 255,
         'noncanonical/escaping member path')
    return path


def tar_header(name, size):
    safe_name(name)
    info = tarfile.TarInfo(name)
    info.mode = 0o644
    info.size = size
    try:
        return info.tobuf(format=tarfile.USTAR_FORMAT, encoding='utf-8', errors='strict')
    except (ValueError, UnicodeError) as error:
        raise Rejected('unsupported canonical USTAR name/size') from error


def validate_expected(expected):
    """Validate, but never authenticate, a separately trusted expectation object."""
    need(type(expected) is dict and set(expected) == {
        'schema', 'origin', 'descriptor', 'descriptor_sha256', 'receipt'}, 'expectation keys')
    need(expected['schema'] == 'conditional-stream-expectation-v1', 'expectation schema')
    origin = expected['origin']
    origin_keys = {'identity', 'stage_id', 'workflow_path', 'workflow_id',
                   'artifact_id', 'artifact_name', 'artifact_zip_bytes', 'artifact_zip_sha256',
                   'producer_job_id', 'producer_job_name', 'producer_job_status',
                   'producer_conclusion', 'producer_job_log_sha256', 'producer_marker',
                   'producer_evidence_zip_sha256'}
    need(type(origin) is dict and set(origin) == origin_keys, 'origin keys')
    identity = origin['identity']
    need(type(identity) is dict and set(identity) == {
        'repository', 'run_id', 'run_attempt', 'workflow_commit'}, 'identity keys')
    need(identity['repository'] == REPOSITORY
         and all(isinstance(identity[k], str) and re.fullmatch(r'[1-9][0-9]*', identity[k])
                 for k in ('run_id', 'run_attempt'))
         and isinstance(identity['workflow_commit'], str)
         and re.fullmatch(r'[0-9a-f]{40}', identity['workflow_commit']), 'identity values')
    sid = origin['stage_id']
    need(isinstance(sid, str) and STAGE.fullmatch(sid), 'stage identity')
    name = f"conditional-geometry-{identity['run_id']}-{identity['run_attempt']}-{sid}-objects"
    need(origin['workflow_path'] == WORKFLOW and positive(origin['workflow_id'])
         and positive(origin['artifact_id']) and positive(origin['producer_job_id'])
         and origin['artifact_name'] == name
         and origin['producer_job_name'] == 'conditional ' + sid
         and origin['producer_job_status'] == 'completed'
         and origin['producer_conclusion'] == 'success', 'producer/workflow/artifact identity')
    need(type(origin['artifact_zip_bytes']) is int and 0 < origin['artifact_zip_bytes'] <= MAX_ZIP
         and all(digest(origin[k]) for k in ('artifact_zip_sha256', 'producer_job_log_sha256',
                                            'producer_evidence_zip_sha256')), 'origin bounds/digests')
    marker = {'stage_id': sid, 'artifact_id': str(origin['artifact_id']),
              'artifact_name': name, 'artifact_sha256': origin['artifact_zip_sha256']}
    need(origin['producer_marker'] == marker, 'producer marker differs')
    descriptor = expected['descriptor']
    need(type(descriptor) is dict and set(descriptor) == {
        'schema', 'stage_id', 'archive_bytes', 'archive_sha256', 'receipt_sha256'}, 'descriptor keys')
    need(descriptor['schema'] == 'conditional-stage-descriptor-v1' and descriptor['stage_id'] == sid
         and type(descriptor['archive_bytes']) is int and 0 < descriptor['archive_bytes'] <= MAX_ZIP
         and digest(descriptor['archive_sha256']) and digest(descriptor['receipt_sha256']),
         'descriptor identity/bounds')
    descriptor_data = canonical_json(descriptor)
    need(len(descriptor_data) <= MAX_METADATA and digest(expected['descriptor_sha256'])
         and sha(descriptor_data) == expected['descriptor_sha256'], 'trusted descriptor hash differs')
    receipt = expected['receipt']
    need(type(receipt) is dict and set(receipt) == {'schema', 'files', *META_KEYS}, 'receipt keys')
    need(receipt['schema'] == 'same-run-conditional-checked-objects-v1'
         and receipt['identity'] == identity and receipt['stage_id'] == sid, 'receipt identity')
    need(digest(receipt['contract_sha256']) and digest(receipt['runtime_inventory_sha256']), 'receipt hash fields')
    modules = receipt['stage_modules']
    need(type(modules) is list and 0 < len(modules) <= MAX_FILES // 7
         and all(isinstance(m, str) and MODULE.fullmatch(m) for m in modules)
         and len(set(modules)) == len(modules), 'stage modules')
    files = receipt['files']
    need(type(files) is dict and 0 < len(files) <= MAX_FILES, 'file count bound')
    own = {'objects/' + module.replace('.', '/') + suffix for module in modules for suffix in SUFFIXES}
    need({name for name in files if name.startswith('objects/')} == own
         and all(name.startswith(('objects/', 'evidence/')) for name in files), 'exact seven-companion inventory')
    directories = set()
    payload_bytes = evidence_bytes = 0
    for name, row in files.items():
        path = safe_name(name)
        directories.update(str(p) for p in path.parents if str(p) != '.')
        need(type(row) is dict and set(row) == {'bytes', 'sha256'}
             and type(row['bytes']) is int and 0 <= row['bytes'] <= MAX_MEMBER
             and digest(row['sha256']), 'member size/hash bound')
        tar_header(name, row['bytes'])
        payload_bytes += row['bytes']
        if name.startswith('evidence/'):
            evidence_bytes += row['bytes']
    need(not directories.intersection(files) and 'receipt.json' not in directories, 'path prefix alias')
    need(payload_bytes < MAX_ZIP and evidence_bytes <= MAX_EVIDENCE, 'payload/evidence byte cap')
    receipt_data = canonical_json(receipt)
    need(len(receipt_data) <= MAX_METADATA and sha(receipt_data) == descriptor['receipt_sha256'],
         'trusted receipt hash/size differs')
    sizes = [len(receipt_data), *(row['bytes'] for row in files.values())]
    raw_size = sum(512 + ((size + 511) // 512) * 512 for size in sizes)
    tar_bytes = ((raw_size + 1024 + 10239) // 10240) * 10240
    need(tar_bytes == descriptor['archive_bytes'], 'canonical tar length differs')
    # Two local headers/names/descriptors, two central headers/names, one EOCD.
    zip_bytes = len(descriptor_data) + tar_bytes + sum(30 + len(n) + 16 + 46 + len(n)
                 for n in (b'descriptor.json', b'stage.tar')) + 22
    need(zip_bytes == origin['artifact_zip_bytes'] and zip_bytes <= MAX_ZIP, 'restricted ZIP length differs')
    return descriptor_data, receipt_data


class ByteStream:
    def __init__(self, source, maximum, deadline):
        self.source, self.maximum, self.deadline = source, maximum, deadline
        self.count = 0
        self.hash = hashlib.sha256()

    def check_time(self):
        need(time.monotonic() < self.deadline, 'absolute streaming deadline exceeded')

    def take(self, count):
        need(type(count) is int and 0 <= count <= CHUNK, 'internal read bound')
        pieces = []
        remaining = count
        while remaining:
            self.check_time()
            data = self.source.read(remaining)
            self.check_time()
            need(type(data) is bytes and 0 < len(data) <= remaining, 'truncated/invalid stream read')
            self.count += len(data)
            need(self.count <= self.maximum, 'whole ZIP byte cap')
            self.hash.update(data)
            pieces.append(data)
            remaining -= len(data)
        return b''.join(pieces)

    def eof(self):
        self.check_time()
        data = self.source.read(1)
        self.check_time()
        need(type(data) is bytes and data == b'', 'trailing ZIP bytes or invalid EOF')


class Member:
    def __init__(self, stream, size):
        self.stream, self.size, self.remaining = stream, size, size
        self.crc = 0
        self.hash = hashlib.sha256()

    def take(self, count):
        need(0 <= count <= self.remaining, 'ZIP member overrun')
        data = self.stream.take(count)
        self.remaining -= len(data)
        self.crc = zlib.crc32(data, self.crc)
        self.hash.update(data)
        return data

    def consume(self, count, *, expected_hash=None, expected_bytes=None, zeros=False):
        h = hashlib.sha256()
        offset = 0
        while count:
            length = min(count, CHUNK)
            data = self.take(length)
            if expected_bytes is not None:
                need(data == expected_bytes[offset:offset + length], 'canonical metadata bytes differ')
            if zeros:
                need(not any(data), 'nonzero tar padding')
            h.update(data)
            count -= length
            offset += length
        if expected_hash is not None:
            need(h.hexdigest() == expected_hash, 'tar member hash differs')


class Verifier:
    """Single-use session. Every error makes this instance permanently unusable."""
    def __init__(self, source, expected, *, deadline):
        self.source, self.expected, self.deadline = source, expected, deadline
        self.state = 'new'

    def verify(self):
        need(self.state == 'new', 'verification session cannot be resumed or reused')
        self.state = 'running'
        try:
            result = self._verify()
        except BaseException:
            self.state = 'failed'
            raise
        self.state = 'accepted'
        return result

    def _verify(self):
        now = time.monotonic()
        need(type(self.deadline) in (int, float) and math.isfinite(self.deadline)
             and now < self.deadline <= now + MAX_SECONDS, 'invalid absolute deadline')
        descriptor_data, receipt_data = validate_expected(self.expected)
        expected = self.expected
        origin, descriptor, receipt = expected['origin'], expected['descriptor'], expected['receipt']
        stream = ByteStream(self.source, origin['artifact_zip_bytes'], self.deadline)
        records = []
        for name, size in ((b'descriptor.json', len(descriptor_data)),
                           (b'stage.tar', descriptor['archive_bytes'])):
            offset = stream.count
            local = struct.unpack('<4s5H3I2H', stream.take(30))
            sig, version, flags, method, mtime, mdate, crc, csize, usize, nlen, xlen = local
            need(sig == b'PK\x03\x04' and version == 20 and flags == 8 and method == 0
                 and crc == csize == usize == xlen == 0 and nlen == len(name), 'unsupported ZIP local header')
            need(stream.take(nlen) == name, 'ZIP member name/order differs')
            member = Member(stream, size)
            if name == b'descriptor.json':
                member.consume(size, expected_bytes=descriptor_data)
                need(member.hash.hexdigest() == expected['descriptor_sha256'], 'descriptor digest differs')
            else:
                need(member.take(512) == tar_header('receipt.json', len(receipt_data)),
                     'canonical receipt USTAR header differs')
                member.consume(len(receipt_data), expected_hash=descriptor['receipt_sha256'],
                               expected_bytes=receipt_data)
                member.consume((-len(receipt_data)) % 512, zeros=True)
                for path, row in sorted(receipt['files'].items()):
                    need(member.take(512) == tar_header(path, row['bytes']),
                         'canonical USTAR member name/order/size/header differs')
                    member.consume(row['bytes'], expected_hash=row['sha256'])
                    member.consume((-row['bytes']) % 512, zeros=True)
                need(1024 <= member.remaining <= 11263, 'canonical tar terminator length differs')
                member.consume(member.remaining, zeros=True)
                need(member.hash.hexdigest() == descriptor['archive_sha256'], 'raw tar SHA256 differs')
            need(member.remaining == 0, 'ZIP member length differs')
            need(stream.take(16) == struct.pack('<4s3I', b'PK\x07\x08', member.crc, size, size),
                 'signed 32-bit ZIP data descriptor CRC/size differs')
            records.append((name, size, offset, mtime, mdate, member.crc))
        central_start = stream.count
        for name, size, offset, mtime, mdate, crc in records:
            # Match GitHub upload-artifact's observed regular, Unix 0644 entry.
            expected_header = struct.pack('<4s6H3I5H2I', b'PK\x01\x02', 0x032d, 20, 8, 0,
                                          mtime, mdate, crc, size, size, len(name), 0, 0,
                                          0, 0, 0x81a40020, offset)
            need(stream.take(46) == expected_header, 'ZIP central header/CRC/size/offset/attributes differs')
            need(stream.take(len(name)) == name, 'ZIP central name/order differs')
        central_size = stream.count - central_start
        end = struct.pack('<4s4H2IH', b'PK\x05\x06', 0, 0, 2, 2, central_size, central_start, 0)
        need(stream.take(22) == end, 'ZIP EOCD count/offset/comment/ZIP64 differs')
        need(stream.count == origin['artifact_zip_bytes'], 'whole ZIP size differs')
        stream.eof()
        need(stream.hash.hexdigest() == origin['artifact_zip_sha256'], 'whole ZIP authenticated SHA256 differs')
        stream.check_time()
        return {'schema': 'conditional-stream-byte-verification-v1', 'status': 'BYTE_VERIFIED_ONLY',
                'archive_admission_performed': False, 'objects_executed_or_imported': False,
                'producer_commands_or_semantics_validated': False,
                'object_payload_bytes_written': 0, 'origin': origin,
                'descriptor_sha256': expected['descriptor_sha256'],
                'receipt_sha256': descriptor['receipt_sha256'],
                'archive_sha256': descriptor['archive_sha256'],
                'archive_bytes': descriptor['archive_bytes'],
                'verified_tar_members': len(receipt['files']) + 1,
                'verified_modules': len(receipt['stage_modules']),
                'streamed_zip_bytes': stream.count, 'complete_zip_eof_verified': True}


def verify_stream(source, expected, *, deadline):
    return Verifier(source, expected, deadline=deadline).verify()


def open_regular_readonly(path):
    # Input artifacts are trusted local file locations, never extracted paths.
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        need(stat.S_ISREG(os.fstat(fd).st_mode), 'local input must be a regular file')
        return os.fdopen(fd, 'rb')
    except BaseException:
        os.close(fd)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expectation', required=True)
    parser.add_argument('--expectation-sha256', required=True,
                        help='independently pinned SHA256 of trusted expectation JSON bytes')
    parser.add_argument('--zip', required=True, help='existing local ZIP; use - for an adapter-owned stdin stream')
    parser.add_argument('--seconds', type=int, default=600)
    args = parser.parse_args()
    try:
        need(digest(args.expectation_sha256), 'invalid expectation digest')
        need(0 < args.seconds <= MAX_SECONDS, 'invalid deadline duration')
        deadline = time.monotonic() + args.seconds
        with open_regular_readonly(args.expectation) as handle:
            data = handle.read(MAX_EXPECTATION + 1)
        need(len(data) <= MAX_EXPECTATION and sha(data) == args.expectation_sha256,
             'expectation size/digest differs')
        expected = parse_json(data)
        if args.zip == '-':
            result = verify_stream(sys.stdin.buffer, expected, deadline=deadline)
        else:
            with open_regular_readonly(args.zip) as handle:
                result = verify_stream(handle, expected, deadline=deadline)
        sys.stdout.buffer.write(canonical_json(result))
    except Exception as error:
        # Never expose raw source data, signed URLs, or partial success receipts.
        message = str(error) if isinstance(error, Rejected) else type(error).__name__
        print('REJECTED: ' + message, file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
