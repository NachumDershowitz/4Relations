# Supplementary executable checks

These programs are independent diagnostics; none is a premise of the formal
certificate in `../formal/proof.json`.

`check_generalization.cpp` enumerates finite families of acyclic relations.
`check_representative_elimination.py` checks the representative-elimination step
on small domains. `check_height_elimination.py` checks its bounded-height analogue.
The programs under `checks/` cover the four-relation construction, rerouting
obligations, and additional small-domain cases. Some require Python's `z3-solver`
package. These are exhaustive or SMT checks of the stated cases, not replacements
for the general proof certificate.

The 722 nine-/ten-point cases mentioned in the manuscript are the reported total
from the finite search. Their original nine-/ten-point run archive is not part of
this package. The general finite-domain theorem and finite-branching theorem are
proved independently of that search.
