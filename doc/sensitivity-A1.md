# Sensitivity to Axiom A1

## What A1 does

A1 (`tritone_exists`) asserts that a non-zero self-inverse interval exists, forcing the
modulus m to be even.  In the proof of `twelve_TET`, A1 supplies the concrete tritone
witness that activates A2, A6, and A8 — all three are stated conditionally on the
existence of a tritone.

Commenting out A1 leaves A2–A8 in force but renders their tritone-conditional clauses
vacuously true whenever no tritone exists.  The structure `HarmonicModel` was
reformulated accordingly: the `t` and `A1` fields are removed, and A2/A6/A8 are given
the signatures

    A2 : ∀ s u, IsTritone s → IsTritone u → s = u
    A6 : ∀ t, IsTritone t → ZMod.val t < ZMod.val p ∧ …
    A8 : ∀ t, IsTritone t → ∃ i, i ≠ 0 ∧ ¬isSelfInverse i ∧ ¬perf i

The theorems in `TwelveTET.lean` are unaffected: they are stated with an explicit
tritone argument, so they continue to hold — they just cannot be applied unless a
tritone is provided from outside.

## The role of A7

With A1 absent, A7 (`p + 5 = 0`) becomes the dominant constraint.  It pins p uniquely
in every ZMod m: `p = -5 mod m`.  The resulting values are:

| m  | p = −5 mod m |
|----|-------------|
| 3  | 1           |
| 4  | 3           |
| 5  | 0           |
| 6  | 1           |
| 7  | 2           |
| 8  | 3           |
| 9  | 4           |
| 10 | 5           |
| 11 | 6           |
| 12 | 7           |

## Results for m = 3 to 12

### m = 3 — model exists (`zmod3Model`)

ZMod 3 has no non-zero self-inverse element (it is odd), so A2, A6, A8 hold vacuously.
A7 gives p = 1, and 1 + 1 = 2 ≠ 0 so A4 is satisfied.  This is the tightest-constraint
witness: it shows A2–A8 alone do not force m = 12.

### m = 4 — no model (`no_model_4`)

A7 forces p = 3.  ZMod 4 has a tritone t = 2 (since 2 + 2 = 0 ≠ 0 is false — wait,
2 + 2 = 4 ≡ 0, and 2 ≠ 0).  A8 then demands a non-zero, non-self-inverse, non-perfect
element.  The non-zero non-self-inverse elements are {1, 3}, which equals {p⁻¹, p},
exhausted by A5.  No such element exists.

### m = 5 — no model (`no_model_5`)

In ZMod 5 the characteristic is 5, so 5 = 0.  A7 reads p + 0 = 0, giving p = 0
(unison).  But 0 + 0 = 0, so p is self-inverse, contradicting A4.

### m = 6 — no model (`no_model_6`)

A7 forces p = 1.  ZMod 6 has a tritone t = 3 (since 3 + 3 = 6 ≡ 0 and 3 ≠ 0).
A6 requires `ZMod.val t < ZMod.val p`, i.e. 3 < 1.  Contradiction.

### m = 7 — model exists (`zmod7Model`)

Odd modulus: no tritone.  A7 gives p = 2; p⁻¹ = 5.  A4 is satisfied (2 + 2 = 4 ≠ 0).
A2, A6, A8 hold vacuously.

### m = 8 — no model (`no_model_8`)

A7 forces p = 3.  ZMod 8 has a tritone t = 4 (since 4 + 4 = 8 ≡ 0 and 4 ≠ 0).
A6 requires `ZMod.val t < ZMod.val p`, i.e. 4 < 3.  Contradiction.

### m = 9 — model exists (`zmod9Model`)

Odd modulus: no tritone.  A7 gives p = 4; p⁻¹ = 5.  A4 satisfied (4 + 4 = 8 ≢ 0 mod 9).
A2, A6, A8 hold vacuously.

### m = 10 — no model (`no_model_10`)

A7 forces p = 5.  Then 5 + 5 = 10 ≡ 0, so p is self-inverse, contradicting A4.

### m = 11 — model exists (`zmod11Model`)

Odd modulus: no tritone.  A7 gives p = 6; p⁻¹ = 5.  A4 satisfied (6 + 6 = 12 ≢ 0 mod 11).
A2, A6, A8 hold vacuously.

### m = 12 — model exists (`zmod12Model`)

The standard model.  t = 6, p = 7, p⁻¹ = 5.  All axioms verified computationally.

## Summary table

| m  | Verdict      | Blocking axiom | Reason                                      |
|----|--------------|----------------|---------------------------------------------|
| 3  | model exists | —              | odd; A2/A6/A8 vacuous                       |
| 4  | no model     | A8             | {non-zero non-SI} = {p, p⁻¹}               |
| 5  | no model     | A4             | char 5 forces p = 0 (self-inverse)          |
| 6  | no model     | A6             | tritone t=3 sits above p=1                  |
| 7  | model exists | —              | odd; A2/A6/A8 vacuous                       |
| 8  | no model     | A6             | tritone t=4 sits above p=3                  |
| 9  | model exists | —              | odd; A2/A6/A8 vacuous                       |
| 10 | no model     | A4             | p = 5 is self-inverse                       |
| 11 | model exists | —              | odd; A2/A6/A8 vacuous                       |
| 12 | model exists | —              | the standard 12TET model                    |

## Interpretation

Without A1 the constraint system is satisfied by any odd m ≥ 3 (trivially, via vacuity)
and by m = 12 (non-trivially).  Among even moduli, A7 generates a p that is either
self-inverse (m = 10: p = 5; m = 5: p = 0) or sits *below* the tritone (m = 6: p=1 < t=3;
m = 8: p=3 < t=4), in both cases blocking one of A4 or A6.  The case m = 4 is subtler:
p and its inverse fill the entire non-SI class, leaving no room for A8.

A1 is therefore doing two jobs simultaneously: it rules out all odd m, and it provides
the tritone witness that allows A6 to pin p precisely one step above t (establishing
p = t + 1, which together with A7 forces 12 | m).
