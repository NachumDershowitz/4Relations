"""Reject semantically weaker or altered statements without importing generators."""
import contextlib,io
import audit_extensions as a
import check_debruijn as d
with contextlib.redirect_stdout(io.StringIO()):checker,cert=d.run('proof.json')
def actual(name):return checker.results[cert['theorems'][name][0]][1]
def reject(name,formula,label):
    if actual(name)==d.prop(formula):raise RuntimeError('Mutation accepted: '+label)
    print('PASS: rejected '+label)
# 1. A silent finite-carrier assumption is not the unrestricted height theorem.
reject('arbitrary_family_mixed_height_termination',a.im(a.finite_type(a.X),a.expected_mixed()),'hidden finite-domain assumption')
# 2. Pointwise heights cannot replace uniform heights with all shortcuts kept.
saved=a.bounded;a.bounded=a.pointwise
reject('arbitrary_family_mixed_height_termination',a.expected_mixed(),'pointwise bound with full shortcuts')
a.bounded=saved
# 3. A decreasing rank assignment is not a canonical ordinal rank.
saved=a.lub;a.lub=lambda *args:a.im(a.false,a.false)
reject('arbitrary_family_limit_rank_obstruction',a.expected_ordinal(),'omitted least-upper-bound rank requirement')
a.lub=saved
# 4. The shortened condition is part of the ordinal theorem.
saved=a.short_at;a.short_at=lambda *args:a.im(a.false,a.false)
reject('arbitrary_family_limit_rank_obstruction',a.expected_ordinal(),'omitted shortened interaction')
a.short_at=saved
# 5. The obstruction asserts a genuine nonzero nonsuccessor rank.
saved=a.limitrank;a.limitrank=lambda L,r:a.neg(a.zerorank(L,r))
reject('arbitrary_family_limit_rank_obstruction',a.expected_ordinal(),'nonzero rank without the limit condition')
a.limitrank=saved
# 6. Uniform height and ordinal criteria are combined by a per-index disjunction.
reject('arbitrary_family_mixed_height_and_ordinal_termination',a.expected_ordinal(True),'only ordinal alternatives instead of the mixed theorem')
print('All six extension statement mutation tests passed.')
