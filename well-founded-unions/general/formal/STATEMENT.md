# Checked statements

Composition is read left to right. Let R_0,...,R_n be a finite ordered family,
T_i the union of R_i,...,R_n, P_i the union of the preceding relations, and
R=T_0. Relations need not be disjoint or transitive.

The full conditions are:

  T_1 R_0 ⊆ R_0 R* ∪ T_1;
  T_{i+1} R_i ⊆ P_i R* ∪ R_i+ ∪ T_{i+1}, for 1 ≤ i < n.

The shortened condition at i deletes only the last T_{i+1} alternative.

## Finite acyclicity

On any finite domain, individually acyclic constituents and the full conditions
imply acyclicity of R. The certificate also proves well-foundedness and the
finite acyclicity-to-accessibility bridge. There is no size bound.

## Mixed heights on arbitrary domains

Assume all constituents well-founded and the full conditions. Work in the
immortal set I, with all relations restricted to I. Let M be the R_0-minimal
points of I. For each internal index 1,...,n-2, either:

- there is one finite bound on the lengths of R_i paths from all points of M;
- every point of M has its own finite bound, and the shortened condition holds
  at i (it suffices that it hold within I).

Then R is well-founded. The first and last two relations have no additional
height assumption. The two cases may be mixed independently by index.

The finite-branching theorem, with shortened internal conditions and the full
final condition, is retained as a separate checked theorem. Neither it nor the
height theorem assumes that the carrier is finite.

### Exact finite-height encoding

For a relation B define N_B(H)(x) := forall y. B(x,y) implies H(y).
A height profile is a finite iterate N_B^k(empty), encoded by its empty/iteration
induction principle. Membership in N_B(N_B^k(empty)) says that no B-path of
length k+1 starts at the point. A uniform bound selects one such profile for
all points; a pointwise bound selects it after the point is quantified.
There is no finite-branching assumption hidden in this encoding.

## Ordinal layer results for arbitrary finite families

Use the canonical rank rho_i(x)=sup_{x R_i y}(rho_i(y)+1), within I.
Let M_i be the points of I without an outgoing edge in P_i.
A representative subset S ⊆ M_i is nonempty and has the property

  forall z in I. exists t in S. forall x in S. x R z implies x R t.

No projection function is selected simultaneously.

1. Successor-layer elimination, with the full condition: if all ranks on S
   are at most beta+1, the subset with rank strictly below beta+1 is nonempty
   and still has representatives.

2. Minimum layer rank, with the shortened condition at i: the subset of S
   attaining its minimum rank has representatives; that minimum is zero or
   a nonzero limit. Zero means that the current relation has no outgoing
   edge on the minimum stratum.

3. Limit-layer obstruction: if all internal conditions are shortened and R
   is not well-founded, some internal i has a nonempty representative subset
   S ⊆ M_i whose minimum rank is a nonzero limit.

4. Zero-or-successor criterion: R is well-founded if, at every internal i,
   all points of M have canonical rank zero or a successor, and the shortened
   condition holds. These successor ranks can be infinite. Only ranks at M
   are restricted; ranks outside M may be nonzero limits.

5. Mixed height/ordinal criterion: at each internal index choose either a
   uniform finite height bound on M, retaining all shortcuts, or the
   zero-or-successor criterion with the shortened condition.

### Abstract ordinal interface in the certificate

The rank type carries a strict total order L whose converse is well-founded.
Rank decrease and the least-strict-upper-bound property are explicit hypotheses:

  x B y implies rho(y) < rho(x);
  [forall y. x B y implies rho(y) < alpha] implies rho(x) <= alpha.

A successor alpha of beta satisfies beta < alpha and has no element strictly
between them. Zero has no predecessor; a nonzero limit is neither zero nor a
successor. These definitions and every use of them are independently audited.
No arbitrary decreasing labeling is silently treated as a canonical rank.
The certificate does not construct the ambient ordinal system or rank assignment.

## Foundations and scope

All mathematical lemmata are derived. The additional logical principle is
classical excluded middle. Well-foundedness is the accessibility-induction
principle. The certificate derives its consequences, not merely absence of
cycles. It also proves that the maximal serial subset is precisely the set of
nonaccessible points, without a dependent-choice premise.

The independent audits reconstruct statements without importing the proof
generators. The two checkers have independent bound-variable representations.
Their successful replay is not a claim of Rocq-kernel acceptance.
