## Problem and original source

Please consider adding the naturally labelled Neggers conjecture, and
Stanley's broader labelled-poset version, to the JSP problem bank.

For a naturally labelled finite poset P, define its descent polynomial by
summing x raised to the number of label descents over all linear extensions
of P. The conjecture asserted that every zero of this polynomial is real.
Stembridge's equivalent W convention multiplies this polynomial by x.

Primary statement and explicit counterexample data:
https://websites.umich.edu/~jrs//data/pocon/ (sections I and IV, example 14).

Published mathematical resolution: John R. Stembridge, *Counterexamples to
the poset conjectures of Neggers, Stanley, and Stembridge*, Transactions of
the American Mathematical Society 359 (2007), 1115–1128.
https://doi.org/10.1090/S0002-9947-06-04271-1

The source dates Neggers' naturally labelled conjecture to 1978 and
Stanley's unrestricted-label extension to 1986. Mathematical credit for
the naturally labelled counterexample remains with Stembridge.

## Statement and significance

This is a classical algebraic-combinatorics conjecture about genuine finite
partial orders and the real-rootedness of their enumerative polynomials.
A single naturally labelled counterexample resolves the complete universal
question. No graded-poset or log-concavity variant is included in this
recommendation.

The proposed scope is the historical universal real-rootedness assertion,
not the minimal size of a counterexample. The 17-element witness is fully
formalized, including its order, all valid linear extensions and an actual
nonreal complex root.

## Known results and verification evidence

Original formalization repository owned by the submitting account:
https://github.com/aznikline/neggers-stanley-lean

Branch: `main`

Selected complete proof commit:
`714c43dca4167b279676fb58b7c15a04a9553c8e`

Exact standard-order theorem:
`NeggersStanley.exists_naturally_labeled_poset_with_nonreal_zero`

Statement and proof:
https://github.com/aznikline/neggers-stanley-lean/blob/714c43dca4167b279676fb58b7c15a04a9553c8e/NeggersStanley/StandardStatement.lean

The shifted convention and universal-negation theorem are also proved:
`NeggersStanley.neggers_stanley_counterexample` and
`NeggersStanley.not_neggersConjecture`.

The standard statement uses Mathlib's `PartialOrder (Fin 17)`. Its polynomial
is defined by filtering every permutation that respects that order. A
separate theorem proves the efficient enumerator is complete and contains
no duplicates. The Lean kernel checks all 7,016 linear extensions and the
coefficients. At x = -2, the exact Laguerre value is -18,495; a proved
real-factorization inequality then implies an actual nonreal complex zero.

Pinned Lean: `leanprover/lean4:v4.34.0`.
Pinned Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.

Reproduction:

```bash
git clone https://github.com/aznikline/neggers-stanley-lean.git
cd neggers-stanley-lean
git checkout 714c43dca4167b279676fb58b7c15a04a9553c8e
lake exe cache get
bash scripts/verify.sh
```

The full build and the separately executed trust-zero audit exited 0.
All final theorem dependencies are contained in
`[propext, Classical.choice, Quot.sound]`.
There is no sorry, admit, custom axiom, unsafe declaration or native_decide
in the project Lean source. The finite checks use `decide +kernel`.

Audit and scope evidence, pinned to the selected version:
https://github.com/aznikline/neggers-stanley-lean/blob/714c43dca4167b279676fb58b7c15a04a9553c8e/verification/axioms.txt
https://github.com/aznikline/neggers-stanley-lean/blob/714c43dca4167b279676fb58b7c15a04a9553c8e/verification/RESULT.md
https://github.com/aznikline/neggers-stanley-lean/blob/714c43dca4167b279676fb58b7c15a04a9553c8e/research/SCOPE.md

These are submitter-run local build/kernel checks using unchanged pinned
dependency artifacts. A fresh-machine rebuild and independent human review
are not claimed. Python is an independent reconstruction aid and is not a
Lean proof dependency.

## Related records and conflicts

A search of the JSP catalog, pull requests and issues found no Neggers entry
or related submission on 2026-09-30. A bounded search of public Lean code
and repository names found no prior formalization; this does not establish
global priority.

Formalization credit is claimed for aznikline's original implementation,
developed with Codex assistance. Historical mathematical discovery is not
claimed. The witness data and publication are attributed to Stembridge.
No independent human verifier or exclusive manual authorship is claimed.

This issue requests problem-bank consideration and review of the complete
formalization evidence. It does not announce a candidate, claim an award,
assign a JSP number, or establish entitlement to payment. Please advise
the appropriate catalog record and subsequent contribution-PR route if the
recommendation is accepted.
