# Review of v0.0.1
## Prompt:

Perform a rigorous review of this proof. Report on:
1. non-idiomatic use of Lean
1.1 suggest idioms to use instead
2. unclear lines of argument
2.2 suggest alternatives that express the idea more clearly

# Results

## Non-idiomatic use of Lean
1.1 Inv on an additive group (Basic.lean:12)

Suggested idiom: Drop the Inv instance and use -p everywhere. Axioms like q = p ∨ q = p⁻¹ become q = p ∨ q = -p, which is the standard Mathlib form for additive groups.

Rejected. Using  p⁻¹ rather than -p is a style choice that I believe maintains the musical sense. This isn't just number theory.

1.2 unison not @[simp] (Basic.lean:8)
resolved

1.3 inv_closed is dead code (Basic.lean:20)
Resolved

1.4 The tritone hypothesis is a raw conjunction throughout
Resolved.

1.5 m_ne_two/m_ne_four/m_ne_six are structurally redundant (TwelveTET.lean:95–132)
Resolved by: Alternatively, since twelve_TET calls them immediately, having them as private lemmas is fine, but their proofs could all follow a single tactic block pattern.

1.6 exact_mod_cast introduces an unnecessary step (TwelveTET.lean:76)
Resolved

1.7 Redundant have destructuring in m_even (TwelveTET.lean:83–84)
Resolved


1.8 Module docstring invokes Knaster-Tarski but the proof does not use it (MajorMinor.lean:13)
Resolved

## Unclear lines of argument

2.1 selfInverse_iff_eq_neg backward direction (Basic.lean:30)
Resolved. Replaced `linear_combination h` with `nth_rw 1 [h]; exact neg_add_cancel i`: rewrite only the first `i` to `-i`, giving `-i + i = 0`, then close with `neg_add_cancel`.

2.2 twelve_eq_zero — the algebraic identity is opaque (TwelveTET.lean:63–69)
Resolved.

2.3 m_even — the chain through Nat.card (TwelveTET.lean:86–88)
Resolved. Added `-- group order of ZMod m is m` on the `rwa` line.

2.4 m_ne_four — fin_cases cases are unlabelled (TwelveTET.lean:124–128)
Resolved. Added `-- i = 0: unison`, `-- i = 1 = p⁻¹`, `-- i = 2 = t`, `-- i = 3 = p` per case.

2.5 complement_SI_is_fixedPoint — backward step (MajorMinor.lean:89–90)
Resolved. Added comment `-- i ∈ univ \ selfInverseSet t, so i ∈ s (the first component of the union)`.

2.6 prefixed_contains_complement — concrete literals in step helper (MajorMinor.lean:139–149)
Resolved. Added `-- {7, 5} = {p, p⁻¹};  {0, 6} = selfInverseSet t` before the `have step` definition, and inline comments on both `Or.inl`/`Or.inr` branches naming which component of `stepMM` they target.

2.7 interval_partition — cascading by_cases with left/right (Partition.lean:20–23)
Resolved. Replaced `left; left; left` etc. with explicit `Or.inl (Or.inl (Or.inl h0))` etc. after the existing `simp only` has already unfolded union membership. The `Or.inl`/`Or.inr` form names the disjunct being proved rather than navigating by count.