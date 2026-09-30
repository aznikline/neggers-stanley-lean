# Neggers–Stanley: a complete finite counterexample in Lean

**Complete and kernel-checked.** The final theorem is
`NeggersStanley.exists_naturally_labeled_poset_with_nonreal_zero`.
The full build and the separate `--trust=0` audit passed. Final theorem
dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
The audit output is retained in `verification/axioms.txt`.

This project formalizes Stembridge's 17-element naturally labelled poset
counterexample to the Neggers conjecture. It also refutes Stanley's broader
version allowing arbitrary labelings. The mathematical result is historical;
this repository supplies a new, self-contained formal proof of this witness.

The public theorem uses Mathlib's `PartialOrder (Fin 17)`. It proves natural
labeling and the existence of a nonreal complex root of the actual descent
generating polynomial, summed over every linear extension. It has no
additional hypotheses. Both conventions for the generating polynomial are
covered: exponents `descents` and `1 + descents`.

## Proof

1. Seventeen explicit predecessor bit masks define the finite poset.
   The kernel checks irreflexivity, transitivity, and natural labeling.
2. The semantic polynomial is defined by filtering **all permutations**
   that respect this order. A separate theorem proves that the efficient
   minimum-removal enumerator returns exactly those permutations, each once.
3. The kernel recomputes the descent counts, yielding 7,016 linear
   extensions and

   `W(x) = x + 32x² + 336x³ + 1420x⁴ + 2534x⁵ + 1946x⁶ + 658x⁷ + 86x⁸ + 3x⁹`.

4. A polynomial with only real roots satisfies
   `(p'(x))² - p(x)p''(x) >= 0` for every real x. This is proved from
   factorization into real linear factors using the product identity
   `L(pq) = q² L(p) + p² L(q)`.
5. At x = -2 the exact values are `W = -130`, `W' = 1185`, and
   `W'' = -10944`, so `L(W) = -18495 < 0`. The fundamental theorem of
   algebra then supplies an actual complex root with nonzero imaginary part.

No numerical root finder, external solver, Python output, unproved
assumption, or native evaluation axiom is needed by the Lean proof.
The finite checks use `decide +kernel`. The Python program independently
reconstructs the poset and arithmetic as an additional reproduction aid.

## Reproduce

Install elan, preserve the supplied manifest, then run:

```sh
lake exe cache get
bash scripts/verify.sh
```

- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- `lake-manifest.json` pins all transitive dependencies.
- `verification/Audit.lean` prints the complete root statements,
  semantic definitions and transitive axiom dependencies.
- The large finite count is checked by the kernel; on the development
  host its module took approximately 90 seconds after dependency caching.

The development build reused unchanged local dependency artifacts. A fresh
machine run is not claimed. The reproduction instructions do not require
any neighboring project or the Python program for proof checking.

## Files

| File | Role |
|---|---|
| `Enumeration.lean` | Complete, duplicate-free linear-extension enumeration |
| `Definitions.lean` | Finite posets, canonical permutation-sum polynomial, coefficient bridge |
| `Witness.lean` | Explicit 17-element poset and kernel-checked descent counts |
| `Laguerre.lean` | Real-rootedness inequality and a nonreal-root criterion |
| `Main.lean` | Exact polynomial and disproof in the shifted W convention |
| `StandardStatement.lean` | Mathlib partial-order statement and unshifted convention |

All Lean module paths are relative to `NeggersStanley/`.

## Source and attribution

Mathematical construction: John R. Stembridge, example 14 of section IV in
the [author-hosted data](https://websites.umich.edu/~jrs//data/pocon/).
Published as *Counterexamples to the poset conjectures of Neggers, Stanley,
and Stembridge*, Transactions of the American Mathematical Society
359 (2007), 1115–1128,
[DOI 10.1090/S0002-9947-06-04271-1](https://doi.org/10.1090/S0002-9947-06-04271-1).
Labels 1 through 17 in that source correspond to indices 0 through 16 here.

Formalization: original code developed for the user in this workspace
with Codex assistance. Mathematical discovery, minimality of the
counterexample, and a new resolution of any graded-poset/log-concavity
problem are not claimed. Mathlib remains a separately pinned dependency.

## Award scope

This problem is not in the JSP catalog as checked on 2026-09-30. A problem
recommendation would be required before its award eligibility could be
reviewed. The proof does not itself establish eligibility, priority, an
award, or payment. The bounded prior-art and statement audit is in
`research/SCOPE.md`; no existing Lean formalization was found in that scan,
which is not a guarantee of global priority.
