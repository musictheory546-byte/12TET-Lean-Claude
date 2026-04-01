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

```lean
fun h => by simp only [isSelfInverse]; linear_combination h
```
Proves `i + i = 0` from `h : i = -i`. The `linear_combination` call is correct: the residual `(i + i) - (i - (-i))` reduces to 0 by `neg_neg`. The idea — substitute and cancel — is not visible from the tactic name alone.

Alternative that names the step:
```lean
fun h => by simp only [isSelfInverse]; rw [h]; exact neg_add_cancel i
```
`rw [h]` replaces `i` with `-i` giving `(-i) + (-i) = 0`, then `neg_add_cancel` applies.

2.2 twelve_eq_zero — the algebraic identity is opaque (TwelveTET.lean:63–69)

```lean
calc (12 : HarmonicInterval m)
    = (t + 6) + (t + 6) - (t + t) := by ring
  _ = 0 + 0 - 0                   := by rw [tritone_plus_six p t hp ht, ht.selfInverse]
  _ = 0                           := by ring
```
The identity `12 = 2(t+6) - (t+t)` is not explained; a reader must verify it. `linear_combination` makes the dependency explicit:
```lean
linear_combination 2 * tritone_plus_six p t hp ht - ht.selfInverse
```
This states directly: `12 = 2·(t+6=0) − (t+t=0)`.

2.3 m_even — the chain through Nat.card (TwelveTET.lean:86–88)

```lean
have h : addOrderOf t ∣ Nat.card (ZMod m) := addOrderOf_dvd_natCard t
rwa [Nat.card_eq_fintype_card, ZMod.card] at h
```
Three Mathlib facts are chained to establish `addOrderOf t ∣ m`. The prose reading — "the additive order of an element divides the group order, and `ZMod m` has order `m`" — is clear, but the rewrite chain does not say which lemma does which. A comment `-- group order = m` on the `rwa` line would help.

2.4 m_ne_four — fin_cases cases are unlabelled (TwelveTET.lean:124–128)

```lean
fin_cases i <;> simp only at *
· exact hine rfl
· exact hiP (by have := perfect_inv_closed p hp; rwa [hpi] at this)
· exact hiSI (by simp only [isSelfInverse]; decide)
· exact hiP (by rwa [hp3] at hp)
```
`fin_cases i` in `ZMod 4` produces `i = 0, 1, 2, 3`. The correspondence to musical roles (0 = unison, 1 = p⁻¹, 2 = t, 3 = p) is implicit. A `-- i = 0: unison` comment per case would make the case analysis self-documenting.

2.5 complement_SI_is_fixedPoint — backward step (MajorMinor.lean:89–90)

```lean
· intro hni
  exact ⟨Or.inl (Or.inl hni), hni⟩
```
`Or.inl (Or.inl hni)` places `i` in the `s` (i.e., `univ \ selfInverseSet t`) component of the three-way union `s ∪ frontier.image(·+1) ∪ frontier.image(·-1)`. The justification — `i ∈ s` because `hni : i ∉ selfInverseSet t` and `i ∈ univ` — is not stated. A one-line comment before the `exact` would suffice.

2.6 prefixed_contains_complement — concrete literals in step helper (MajorMinor.lean:139–149)

```lean
have step : ∀ j : ZMod 12,
    j ∈ s ∪ ({7, (5 : ZMod 12)} : Finset (ZMod 12)) →
    ∀ i : ZMod 12, (i = j + 1 ∨ i = j - 1) → i ∉ ({0, (6 : ZMod 12)} : Finset _) → i ∈ s
```
After `subst ht6; subst hp7` the names `p` and `t` are gone; `{7, 5}` and `{0, 6}` are their values without annotation. A comment `-- {7,5} = {p,p⁻¹}, {0,6} = selfInverseSet t` at the `have step` line removes the need to look back.

The proof of `step` closes each branch with:
```lean
· exact Or.inl (Or.inr ⟨j, Finset.mem_union.mp hj, rfl⟩)
· exact Or.inr ⟨j, Finset.mem_union.mp hj, rfl⟩
```
`Or.inl (Or.inr ...)` targets `frontier.image(·+1)`; `Or.inr ...` targets `frontier.image(·-1)`. This matches `stepMM`'s union structure but is not stated.

2.7 interval_partition — cascading by_cases with left/right (Partition.lean:20–23)
Resolved. Replaced `left; left; left` etc. with explicit `Or.inl (Or.inl (Or.inl h0))` etc. after the existing `simp only` has already unfolded union membership. The `Or.inl`/`Or.inr` form names the disjunct being proved rather than navigating by count.