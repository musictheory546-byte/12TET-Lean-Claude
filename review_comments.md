# Suggested improvements

## 1. Close `prefixed_contains_complement` with `decide`

Not actionable. After `subst ht6; subst hp7`, the set `s : Finset (ZMod 12)` remains universally
quantified — it is a hypothesis, not a concrete value. `decide` requires a closed term; the goal
is not decidable in this form. The 10-step walk is necessary.

## 2. Extract the t-pinning pattern
Resolved. Added `tritone_eq` to `Consequences.lean`. The four call sites in `TwelveTET.lean` and
`MajorMinor.lean` now read `tritone_eq t ht c (by decide) (by decide)`.

## 3. Replace A5 + A5' with a single biconditional
Resolved. `perfect_unique` and `perfect_inv_closed` are now theorems derived from the single
axiom `perfect_iff`.

## 4. `interval_partition` could use `fin_cases` after fixing m = 12

Currently `Partition.lean` does not import `TwelveTET` and proves the partition generically, then
the `by_cases` cascade handles membership. If the theorem were stated with the 12TET hypothesis
(or in a section where `m = 12`), `fin_cases i` would close all cases computationally, making the
proof structure consistent with the rest of the development.
