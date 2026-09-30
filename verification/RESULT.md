# Verification result

Checked on the development host on 2026-09-30.

## Scope

The final standard statement exhibits a `PartialOrder (Fin 17)` that
respects the natural order of the integer labels, and an actual nonreal
complex root of its linear-extension descent polynomial. That polynomial
is defined over every permutation satisfying the partial order.

The executable poset data are not an additional hypothesis. Irreflexivity,
transitivity and natural labeling are kernel-proved for the supplied
17-element relation. The efficient enumerator is separately proved to be
a duplicate-free enumeration of all valid permutations.

## Checks passed

- `lake build`: exit 0, 3494 build jobs including dependencies.
- `lake env lean --trust=0 -DmaxRecDepth=100000 -DmaxHeartbeats=0 verification/Audit.lean`:
  exit 0. Exact statements and dependency closures are in `axioms.txt`.
- All nine dependency Git revisions match `lake-manifest.json`; their
  tracked source trees are clean.
- A source scan found no sorry, admit, custom axiom, native_decide, or
  unsafe declaration in the project's Lean files.
- `python3 research/verify_witness.py`: exit 0. It independently reconstructs
  the published covering relation, its predecessor masks, the 7016
  extensions, all coefficients, and the integer inequality certificate.
- The complete documented wrapper `bash scripts/verify.sh` was also run
  end to end and exited 0.
- Explicit elaborated terms were inspected: the partial-order comparisons
  in the standard statement and polynomial use the quantified order P;
  label descents and natural labeling use the ordinary integer order.

## Final theorem trust

`exists_naturally_labeled_poset_with_nonreal_zero`,
`neggers_stanley_counterexample`, and `not_neggersConjecture` depend only on

```text
[propext, Classical.choice, Quot.sound]
```

The finite count certificate `witness_counts` depends only on `propext`.
No generated numerical root or external solver output is trusted.

## Limits of this verification record

This is a local build and kernel audit with existing unchanged dependency
artifacts. It is not a fresh-machine rebuild or independent human review.
It establishes the formal counterexample, not a new mathematical discovery,
global formalization priority, or award eligibility.
