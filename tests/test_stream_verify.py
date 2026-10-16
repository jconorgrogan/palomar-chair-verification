"""Tiny inert fixtures only. This suite never opens retained producer artifacts."""
import copy
import hashlib
import io
import json
import struct
import tarfile
import time
import unittest
import zlib

import stream_verify as v


def build_zip(descriptor_data, tar_data):
    local, central, positions = bytearray(), bytearray(), {}
    for name, data in ((b'descriptor.json', descriptor_data), (b'stage.tar', tar_data)):
        offset = len(local)
        crc, size = zlib.crc32(data), len(data)
        local.extend(struct.pack('<4s5H3I2H', b'PK\x03\x04', 20, 8, 0, 29795, 23888,
                                 0, 0, 0, len(name), 0))
        local.extend(name)
        start = len(local)
        local.extend(data)
        dd = len(local)
        local.extend(struct.pack('<4s3I', b'PK\x07\x08', crc, size, size))
        central.extend(struct.pack('<4s6H3I5H2I', b'PK\x01\x02', 0x032d, 20, 8, 0,
                                   29795, 23888, crc, size, size, len(name), 0, 0,
                                   0, 0, 0x81a40020, offset))
        central.extend(name)
        positions[name.decode()] = {'local': offset, 'data': start, 'dd': dd}
    positions['central'] = len(local)
    end = struct.pack('<4s4H2IH', b'PK\x05\x06', 0, 0, 2, 2, len(central), len(local), 0)
    return bytes(local + central + end), positions


def seal(exp, tar_data):
    exp = copy.deepcopy(exp)
    exp['descriptor']['archive_sha256'] = v.sha(tar_data)
    exp['descriptor']['archive_bytes'] = len(tar_data)
    desc = v.canonical_json(exp['descriptor'])
    exp['descriptor_sha256'] = v.sha(desc)
    data, positions = build_zip(desc, tar_data)
    exp['origin']['artifact_zip_bytes'] = len(data)
    exp['origin']['artifact_zip_sha256'] = v.sha(data)
    exp['origin']['producer_marker']['artifact_sha256'] = v.sha(data)
    return exp, data, positions


def fixture():
    identity = {'repository': v.REPOSITORY, 'run_id': '123', 'run_attempt': '1',
                'workflow_commit': 'a' * 40}
    files = {'objects/Test/Tiny' + suffix: b'inert ' + suffix.encode() for suffix in v.SUFFIXES}
    files['evidence/result.json'] = b'{"tiny_inert_fixture":true}\n'
    receipt = {'schema': 'same-run-conditional-checked-objects-v1', 'identity': identity,
               'stage_id': 'F0_common', 'stage_modules': ['Test.Tiny'], 'admitted_stages': [],
               'contract_sha256': 'b' * 64, 'interface_identity': {},
               'producer_work': '/fixture', 'runtime_inventory_sha256': 'c' * 64,
               'predecessor_artifacts': [],
               'files': {n: {'bytes': len(data), 'sha256': v.sha(data)} for n, data in files.items()}}
    rb = v.canonical_json(receipt)
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode='w', format=tarfile.USTAR_FORMAT) as archive:
        for name, data in [('receipt.json', rb), *sorted(files.items())]:
            info = tarfile.TarInfo(name)
            info.mode, info.size = 0o644, len(data)
            archive.addfile(info, io.BytesIO(data))
    tar_data = out.getvalue()
    name = 'conditional-geometry-123-1-F0_common-objects'
    origin = {'identity': identity, 'stage_id': 'F0_common', 'workflow_path': v.WORKFLOW,
              'workflow_id': 1, 'artifact_id': 2, 'artifact_name': name,
              'artifact_zip_bytes': 1, 'artifact_zip_sha256': '0' * 64,
              'producer_job_id': 3, 'producer_job_name': 'conditional F0_common',
              'producer_job_status': 'completed', 'producer_conclusion': 'success',
              'producer_job_log_sha256': 'd' * 64, 'producer_evidence_zip_sha256': 'e' * 64,
              'producer_marker': {'stage_id': 'F0_common', 'artifact_id': '2',
                                  'artifact_name': name, 'artifact_sha256': '0' * 64}}
    descriptor = {'schema': 'conditional-stage-descriptor-v1', 'stage_id': 'F0_common',
                  'archive_bytes': len(tar_data), 'archive_sha256': v.sha(tar_data),
                  'receipt_sha256': v.sha(rb)}
    exp = {'schema': 'conditional-stream-expectation-v1', 'origin': origin,
           'descriptor': descriptor, 'descriptor_sha256': '0' * 64, 'receipt': receipt}
    exp, data, positions = seal(exp, tar_data)
    return exp, data, positions, tar_data


class ShortReads:
    def __init__(self, data, chunk=13):
        self.source, self.chunk, self.largest = io.BytesIO(data), chunk, 0
    def read(self, n):
        if n < 0 or n > v.CHUNK:
            raise AssertionError('unbounded read')
        self.largest = max(n, self.largest)
        return self.source.read(min(n, self.chunk))


class Tests(unittest.TestCase):
    def setUp(self):
        self.expected, self.data, self.pos, self.tar = fixture()

    def verify(self, data=None, expected=None):
        return v.verify_stream(io.BytesIO(self.data if data is None else data),
                               self.expected if expected is None else expected,
                               deadline=time.monotonic() + 30)

    def reject(self, data, expected=None, pattern=None):
        with self.assertRaisesRegex(v.Rejected, pattern or '.'):
            self.verify(data, expected)

    def mutate(self, offset, value, reseal_outer=True):
        data = bytearray(self.data)
        data[offset:offset + len(value)] = value
        exp = copy.deepcopy(self.expected)
        if reseal_outer:
            exp['origin']['artifact_zip_sha256'] = v.sha(data)
            exp['origin']['producer_marker']['artifact_sha256'] = v.sha(data)
        return bytes(data), exp

    def bad_tar(self, offset, value, pattern=None):
        tar = bytearray(self.tar)
        tar[offset:offset + len(value)] = value
        exp, data, _ = seal(self.expected, bytes(tar))
        self.reject(data, exp, pattern)

    def first_file_offset(self):
        rb = v.canonical_json(self.expected['receipt'])
        return 512 + ((len(rb) + 511) // 512) * 512

    def test_positive_tiny_inert(self):
        result = self.verify()
        self.assertEqual(result['status'], 'BYTE_VERIFIED_ONLY')
        self.assertEqual(result['verified_tar_members'], 9)
        self.assertFalse(result['archive_admission_performed'])
        self.assertFalse(result['producer_commands_or_semantics_validated'])
        self.assertEqual(result['object_payload_bytes_written'], 0)

    def test_short_reads_still_bounded(self):
        source = ShortReads(self.data)
        result = v.verify_stream(source, self.expected, deadline=time.monotonic() + 30)
        self.assertTrue(result['complete_zip_eof_verified'])
        self.assertLessEqual(source.largest, v.CHUNK)

    def test_truncation_at_structural_boundaries(self):
        offsets = [0, 1, 29, 30, 44, self.pos['descriptor.json']['dd'],
                   self.pos['stage.tar']['data'], self.pos['stage.tar']['data'] + 511,
                   self.pos['stage.tar']['dd'], self.pos['central'], len(self.data) - 1]
        for offset in offsets:
            with self.subTest(offset=offset):
                self.reject(self.data[:offset])

    def test_arbitrary_truncation_inside_small_archive(self):
        for offset in range(0, len(self.data), 257):
            with self.subTest(offset=offset):
                self.reject(self.data[:offset])

    def test_trailing_byte(self):
        self.reject(self.data + b'x', pattern='trailing ZIP')

    def test_extra_zip_member(self):
        at = self.pos['central']
        self.reject(self.data[:at] + self.data[:45] + self.data[at:])

    def test_wrong_whole_zip_digest_only(self):
        exp = copy.deepcopy(self.expected)
        exp['origin']['artifact_zip_sha256'] = 'f' * 64
        exp['origin']['producer_marker']['artifact_sha256'] = 'f' * 64
        self.reject(self.data, exp, 'whole ZIP authenticated SHA256')

    def test_unsupported_local_headers(self):
        for offset, value in [(0, b'NOPE'), (4, struct.pack('<H', 45)),
                              (6, struct.pack('<H', 9)), (8, struct.pack('<H', 8)),
                              (14, struct.pack('<I', 7)), (18, struct.pack('<I', 0xffffffff)),
                              (28, struct.pack('<H', 1))]:
            with self.subTest(offset=offset):
                data, exp = self.mutate(offset, value)
                self.reject(data, exp, 'ZIP local header')

    def test_zip_path_traversal_name(self):
        data, exp = self.mutate(30, b'../badname.json!')
        self.reject(data, exp, 'ZIP member name')

    def test_descriptor_bytes_altered(self):
        data, exp = self.mutate(self.pos['descriptor.json']['data'] + 10, b'X')
        self.reject(data, exp, 'metadata bytes')

    def test_both_data_descriptor_crc_and_size(self):
        for name in ('descriptor.json', 'stage.tar'):
            for relative in (4, 8, 12):
                with self.subTest(name=name, relative=relative):
                    data, exp = self.mutate(self.pos[name]['dd'] + relative, b'\xff\xff\xff\xff')
                    self.reject(data, exp, 'data descriptor')

    def test_unsigned_data_descriptor_rejected(self):
        at = self.pos['stage.tar']['dd']
        self.reject(self.data[:at] + self.data[at + 4:], pattern='data descriptor')

    def test_zip64_data_descriptor_rejected(self):
        at = self.pos['stage.tar']['dd']
        _, crc, size, _ = struct.unpack('<4s3I', self.data[at:at + 16])
        dd = struct.pack('<4sIQQ', b'PK\x07\x08', crc, size, size)
        self.reject(self.data[:at] + dd + self.data[at + 16:], pattern='data descriptor')

    def test_central_mutations(self):
        for relative, value in [(0, b'NOPE'), (8, b'\x09\0'), (16, b'\0\0\0\0'),
                                (20, b'\0\0\0\0'), (30, b'\x01\0'), (32, b'\x01\0'),
                                (38, b'\0\0\0\0'), (42, b'\x01\0\0\0')]:
            with self.subTest(relative=relative):
                data, exp = self.mutate(self.pos['central'] + relative, value)
                self.reject(data, exp, 'central header')

    def test_central_member_name(self):
        data, exp = self.mutate(self.pos['central'] + 46, b'x')
        self.reject(data, exp, 'central name')

    def test_eocd_disk_count_size_offset_comment_zip64(self):
        for relative, value in [(0, b'PK\x06\x06'), (4, b'\x01\0'), (8, b'\x03\0'),
                                (12, b'\xff' * 4), (16, b'\xff' * 4), (20, b'\x01\0')]:
            with self.subTest(relative=relative):
                data, exp = self.mutate(len(self.data) - 22 + relative, value)
                self.reject(data, exp, 'EOCD')

    def test_tar_receipt_header_and_size(self):
        for at, value in [(0, b'evil'), (124, b'77777777777\0'), (156, b'2'),
                          (257, b'xxxxx'), (148, b'0000000\0')]:
            with self.subTest(at=at):
                self.bad_tar(at, value, 'receipt USTAR header')

    def test_receipt_bytes(self):
        self.bad_tar(512 + 10, b'X', 'metadata bytes')

    def test_tar_member_path(self):
        self.bad_tar(self.first_file_offset(), b'../evil', 'USTAR member')

    def test_tar_member_size_and_header_modes(self):
        for relative, value in [(124, b'77777777777\0'), (156, b'1'), (100, b'0000777\0'),
                                (108, b'0000001\0'), (345, b'alias')]:
            with self.subTest(relative=relative):
                self.bad_tar(self.first_file_offset() + relative, value, 'USTAR member')

    def test_tar_member_hash_with_resealed_outer(self):
        self.bad_tar(self.first_file_offset() + 512, b'X', 'member hash')

    def test_tar_receipt_padding(self):
        at = 512 + len(v.canonical_json(self.expected['receipt']))
        self.bad_tar(at, b'X', 'nonzero tar padding')

    def test_tar_member_padding(self):
        first_name = sorted(self.expected['receipt']['files'])[0]
        at = self.first_file_offset() + 512 + self.expected['receipt']['files'][first_name]['bytes']
        self.bad_tar(at, b'X', 'nonzero tar padding')

    def test_tar_terminator_padding(self):
        self.bad_tar(len(self.tar) - 1, b'X', 'nonzero tar padding')

    def test_tar_extra_record(self):
        exp, data, _ = seal(self.expected, self.tar + bytes(10240))
        self.reject(data, exp, 'canonical tar length')

    def test_tar_archive_digest_only(self):
        exp = copy.deepcopy(self.expected)
        exp['descriptor']['archive_sha256'] = 'f' * 64
        desc = v.canonical_json(exp['descriptor'])
        exp['descriptor_sha256'] = v.sha(desc)
        data, _ = build_zip(desc, self.tar)
        exp['origin']['artifact_zip_sha256'] = v.sha(data)
        exp['origin']['producer_marker']['artifact_sha256'] = v.sha(data)
        self.reject(data, exp, 'raw tar SHA256')

    def test_missing_or_extra_companion(self):
        for add in (False, True):
            exp = copy.deepcopy(self.expected)
            files = exp['receipt']['files']
            if add:
                files['objects/Test/Tiny.extra'] = {'bytes': 0, 'sha256': v.sha(b'')}
            else:
                del files['objects/Test/Tiny.c']
            self.reject(self.data, exp, 'seven-companion')

    def test_expected_path_and_size_caps(self):
        for name, size in [('../escape', 0), ('evidence/../escape', 0),
                           ('evidence/a//b', 0), ('evidence/bad', v.MAX_MEMBER + 1)]:
            with self.subTest(name=name):
                exp = copy.deepcopy(self.expected)
                exp['receipt']['files'][name] = {'bytes': size, 'sha256': v.sha(b'')}
                self.reject(self.data, exp)

    def test_duplicate_json_and_nonfinite(self):
        for data in (b'{"a":1,"a":2}', b'{"a":NaN}', b'{"a":Infinity}'):
            with self.assertRaises(v.Rejected):
                v.parse_json(data)

    def test_wrong_producer_marker_and_failed_producer(self):
        for key, value in [('producer_conclusion', 'failure'), ('producer_job_status', 'in_progress'),
                           ('producer_marker', {})]:
            exp = copy.deepcopy(self.expected)
            exp['origin'][key] = value
            self.reject(self.data, exp)

    def test_absolute_deadline_and_poison(self):
        verifier = v.Verifier(io.BytesIO(self.data), self.expected, deadline=time.monotonic() - 1)
        with self.assertRaises(v.Rejected):
            verifier.verify()
        self.assertEqual(verifier.state, 'failed')
        with self.assertRaisesRegex(v.Rejected, 'cannot be resumed'):
            verifier.verify()

    def test_malformed_session_is_poisoned(self):
        verifier = v.Verifier(io.BytesIO(self.data[:-1]), self.expected, deadline=time.monotonic() + 30)
        with self.assertRaises(v.Rejected):
            verifier.verify()
        self.assertEqual(verifier.state, 'failed')
        with self.assertRaises(v.Rejected):
            verifier.verify()

    def test_success_is_also_single_use(self):
        verifier = v.Verifier(io.BytesIO(self.data), self.expected, deadline=time.monotonic() + 30)
        verifier.verify()
        self.assertEqual(verifier.state, 'accepted')
        with self.assertRaises(v.Rejected):
            verifier.verify()

    def test_expiry_during_read(self):
        class Expiring:
            def read(_, n):
                time.sleep(0.003)
                return self.data[:n]
        verifier = v.Verifier(Expiring(), self.expected, deadline=time.monotonic() + 0.001)
        with self.assertRaisesRegex(v.Rejected, 'deadline'):
            verifier.verify()
        self.assertEqual(verifier.state, 'failed')

    def test_io_error_poison(self):
        class Broken:
            def read(_, n):
                raise OSError('inert fixture failure')
        verifier = v.Verifier(Broken(), self.expected, deadline=time.monotonic() + 30)
        with self.assertRaises(OSError):
            verifier.verify()
        self.assertEqual(verifier.state, 'failed')


if __name__ == '__main__':
    unittest.main(verbosity=2)
