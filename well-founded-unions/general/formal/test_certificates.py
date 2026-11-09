"""End-to-end rejection tests for proof corruption and theorem-label drift."""
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
import kernel
import check_debruijn
import audit_branching

class CertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cert = json.loads(Path('proof.json').read_text())

    def temporary(self, cert):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        path = Path(tmp.name) / 'proof.json'
        path.write_text(json.dumps(cert, separators=(',', ':')))
        return str(path)

    def reject_both(self, cert):
        path = self.temporary(cert)
        for checker, exc in ((kernel.load_and_check, kernel.CheckError),
                             (check_debruijn.run, check_debruijn.Invalid)):
            with contextlib.redirect_stdout(io.StringIO()):
                try:
                    checker(path)
                except exc:
                    continue
            raise RuntimeError('Corrupt proof accepted by a checker')

    def test_invalid_primitive_rule_rejected(self):
        cert = copy.deepcopy(self.cert)
        cert['proof'][-1][0] = 'unproved_axiom'
        self.reject_both(cert)

    def test_circular_reference_rejected(self):
        cert = copy.deepcopy(self.cert)
        cert['proof'][-1][1][0] = len(cert['proof']) - 1
        self.reject_both(cert)

    def test_wrong_stored_conclusion_rejected(self):
        cert = copy.deepcopy(self.cert)
        name = 'finitely_branching_internal_relations_terminate'
        other = 'arbitrary_finite_acyclic_family_termination'
        cert['theorems'][name][1] = cert['theorems'][other][1]
        self.reject_both(cert)

    def test_finite_domain_theorem_cannot_masquerade_as_branching(self):
        cert = copy.deepcopy(self.cert)
        name = 'finitely_branching_internal_relations_terminate'
        cert['theorems'][name] = cert['theorems']['arbitrary_finite_acyclic_family_termination']
        path = self.temporary(cert)
        # Every inference remains valid. The external statement audit must reject
        # the mislabeled finite-domain theorem, not merely replay its proof.
        with contextlib.redirect_stdout(io.StringIO()):
            kernel.load_and_check(path)
            check_debruijn.run(path)
            try:
                audit_branching.run(path)
            except SystemExit as exc:
                if 'EXACT STATEMENT AUDIT FAILED' in str(exc):
                    return
                raise
        raise RuntimeError('Statement audit accepted the wrong theorem')

if __name__ == '__main__':
    unittest.main(verbosity=2)
