# Target and selection audit

The target is the original naturally labelled Neggers conjecture:
for every finite naturally labelled poset, its linear-extension descent
polynomial has only real zeros. A single naturally labelled poset with a
nonreal zero disproves the whole universal assertion. The same example
also disproves Stanley's extension to arbitrary labelings.

This project uses the W convention with exponent one plus the number of
descents, exactly as in Stembridge's published data. Labels are indexed
from zero in Lean; adding one recovers labels 1 through 17 without changing
any comparison or descent.

The mathematical counterexample is John R. Stembridge's example 14 in
section IV of his author-hosted data:
https://websites.umich.edu/~jrs//data/pocon/

Publication: J. R. Stembridge, *Counterexamples to the poset conjectures
of Neggers, Stanley, and Stembridge*, Transactions of the American
Mathematical Society 359 (2007), 1115–1128.
DOI: https://doi.org/10.1090/S0002-9947-06-04271-1

No new mathematical discovery or smallest-counterexample result is claimed.
In particular, this is not a resolution of additional graded-poset or
log-concavity conjectures.

## Selection checks, 2026-09-30

The previously considered small finite-certificate JSP entries had existing
complete-proof submissions. This result is not currently listed in the
JSP problem bank. An award application would require a recommendation and
acceptance of the problem before eligibility could be established.

Searches of GitHub Lean code, repository names, the JSP pull-request list,
and the local pinned Mathlib source found no Neggers formalization. This is
a bounded search, not proof of global priority. Keller's conjecture was
also checked and rejected as a target: a published end-to-end Lean
formalization already exists.

The formalization is original code developed in this workspace with Codex
assistance for the user. Mathematical credit remains with Stembridge;
the data source is attributed explicitly. Mathlib is a pinned dependency.

## Acceptance requirements

- A genuine strict partial order on 17 labels, with natural labeling proved.
- The generating polynomial defined over every valid permutation.
- A proof that the efficient enumerator is complete and duplicate-free.
- Counts checked by the Lean kernel, independently of the Python program.
- An actual nonreal complex root, not numerical approximations to roots.
- No unproved premise, sorry, custom axiom, or native-decide trust shortcut
  in either final theorem's dependency closure.
- A successful build and a separate trust-zero audit of the final statements.
