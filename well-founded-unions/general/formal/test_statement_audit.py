"""Negative controls for specification drift; no generator imports."""
import unittest
import check_debruijn as db
from audit_branching import intended_branching

class StatementTests(unittest.TestCase):
    def check_change(self,**changes):
        exact=db.prop(intended_branching())
        changed=db.prop(intended_branching(**changes))
        if exact==changed:raise RuntimeError('Audit fails to detect changed specification')
    def test_finite_carrier_is_not_silently_assumed(self):self.check_change(finite_domain=True)
    def test_shortened_conditions_cannot_be_dropped(self):self.check_change(shortened=False)
    def test_branching_is_not_required_at_endpoints(self):self.check_change(branch_all=True)
    def test_last_shortcut_is_retained(self):self.check_change(last_shortcut=False)
    def test_independent_closed_statement(self):
        if db.free(db.prop(intended_branching())):raise RuntimeError('Free term variable')
    def test_alpha_renaming_invariant(self):
        if db.prop(intended_branching())!=db.prop(intended_branching()):raise RuntimeError('Alpha mismatch')

if __name__=='__main__':unittest.main(verbosity=2)
