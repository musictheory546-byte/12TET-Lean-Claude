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


instance [NeZero m] : Inv (HarmonicInterval m) where inv := Neg.neg
Inv is the multiplicative inverse class; Neg is the additive one. Installing Inv := Neg.neg is a type-class lie: it works mechanically but makes i⁻¹ mean -i, which is confusing and requires two boilerplate @[simp] lemmas (HI_inv_eq_neg, HI_inv_inv) plus repeated simp only [HI_inv_eq_neg, ...] calls throughout proofs.

Suggested idiom: Drop the Inv instance and use -p everywhere. Axioms like q = p ∨ q = p⁻¹ become q = p ∨ q = -p, which is the standard Mathlib form for additive groups.

1.2 unison not @[simp] (Basic.lean:8)


def unison [NeZero m] : HarmonicInterval m := 0
unison is exactly 0. Without @[simp] or @[reducible], simp will not unfold it, and unison_is_self_inverse uses simp [isSelfInverse, unison] to force the unfold explicitly. Every proof that reaches unison must carry this hint.

Suggested idiom: Either mark it @[simp] def unison ... := 0, or mark it abbrev so it unfolds transparently.

1.3 inv_closed is dead code (Basic.lean:20)


def inv_closed [NeZero m] (s : Finset (HarmonicInterval m)) : Prop := ∀ i ∈ s, i⁻¹ ∈ s
This definition is declared but never referenced in any subsequent module. It should be removed.

1.4 The tritone hypothesis is a raw conjunction throughout


(ht : t ≠ 0 ∧ isSelfInverse t)
This conjunction appears in thirteen theorem signatures. Every use destructures it as ht.1/ht.2. In Lean 4, the idiomatic approach is a named structure or predicate:


structure IsTritone [NeZero m] (t : HarmonicInterval m) : Prop where
  ne_zero     : t ≠ 0
  selfInverse : isSelfInverse t
Then ht.ne_zero, ht.selfInverse are self-documenting, and the axiom signatures read more cleanly.

1.5 m_ne_two/m_ne_four/m_ne_six are structurally redundant (TwelveTET.lean:95–132)

All three have the same pattern: assume m = n, subst, pin t (and sometimes p) by decide, derive a contradiction. They are factored out for legibility but twelve_TET already dispatches all cases via interval_cases m <;> omega — the three named lemmas serve only as labeled steps in that final proof. Inlining them (or reducing the set to h3/h4/h5 without separate names) would be more concise. Alternatively, since twelve_TET calls them immediately, having them as private lemmas is fine, but their proofs could all follow a single tactic block pattern.

1.6 exact_mod_cast introduces an unnecessary step (TwelveTET.lean:76)


have h : (12 : ZMod m) = 0 := twelve_eq_zero p t hp ht
have h12 : ((12 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
exact (CharP.cast_eq_zero_iff (ZMod m) m 12).mp h12
(12 : ZMod m) and ((12 : ℕ) : ZMod m) are definitionally equal. The cast step is not needed:


exact (CharP.cast_eq_zero_iff (ZMod m) m 12).mp (twelve_eq_zero p t hp ht)
1.7 Redundant have destructuring in m_even (TwelveTET.lean:83–84)


have h2t : t + t = 0 := ht.2
have ht0 : t ≠ 0   := ht.1
These two lines are immediately used in the next two subgoals. Lean 4 can reference ht.2 and ht.1 directly at the call site. The named intermediates add no information.

1.8 Module docstring invokes Knaster-Tarski but the proof does not use it (MajorMinor.lean:13)

"By the Knaster-Tarski theorem (OrderHom.lfp), the least fixed point exists."

OrderHom.lfp is never imported or invoked. The lfp is instead constructed manually as an intersection of prefixed points (Finset.univ.filter ...). The docstring is misleading.

Suggested: Replace with "We construct the lfp as the intersection of all prefixed points of stepMM."

## Unclear lines of argument
2.1 selfInverse_iff_eq_neg backward direction (Basic.lean:32)


fun h => by simp only [isSelfInverse]; linear_combination h
This proves i + i = 0 from i = -i. The linear_combination call is mechanically correct but opaque. The idea is simply i + i = i + (-i) = 0.

Clearer: fun h => by rw [h]; ring — this says exactly: substitute i = -i, then the equation (-i) + (-i) = 0 holds by the ring axioms... actually (-i) + (-i) is not 0 by ring alone; it would be -(i+i). Better: fun h => by rw [isSelfInverse, h, neg_add_cancel] or fun h => by linarith [h]. Actually this shows the linear_combination is a reasonable tactic here; the issue is just the simp only [isSelfInverse] step that unfolds the definition before linear_combination. A single simp [isSelfInverse, h, add_comm] might close it.

2.2 twelve_eq_zero — the algebraic identity is opaque (TwelveTET.lean:66–69)


calc (12 : HarmonicInterval m)
    = (t + 6) + (t + 6) - (t + t) := by ring
  _ = 0 + 0 - 0                   := by rw [tritone_plus_six p t hp ht, ht.2]
  _ = 0                           := by ring
The identity 12 = 2(t+6) - 2t is not explained. A reader must verify algebraically that this equals 12. A linear_combination statement makes the dependency explicit:


linear_combination 2 * tritone_plus_six p t hp ht - ht.2
This directly says: the proof is 2 × (t + 6 = 0) − (t + t = 0), i.e., 12 = 2(t+6) - (t+t) = 0.

2.3 m_even — the chain through Nat.card (TwelveTET.lean:90–92)


have h : addOrderOf t ∣ Nat.card (ZMod m) := addOrderOf_dvd_natCard t
rwa [Nat.card_eq_fintype_card, ZMod.card] at h
Three separate Mathlib facts are chained (addOrderOf_dvd_natCard, Nat.card_eq_fintype_card, ZMod.card) to establish addOrderOf t ∣ m. The reasoning — "the additive order of any element divides the group order, and ZMod m has order m" — is clear in prose but the rewrite chain obscures which lemma does what. A brief comment stating "group order = m" would help.

2.4 m_ne_four — fin_cases cases are unlabelled (TwelveTET.lean:128–132)


fin_cases i <;> simp only at *
· exact hine rfl
· exact hiP (by have := perfect_inv_closed p hp; rwa [hpi] at this)
· exact hiSI (by simp only [isSelfInverse]; decide)
· exact hiP (by rwa [hp3] at hp)
fin_cases i in ZMod 4 produces cases i = 0, i = 1, i = 2, i = 3. The correspondence to musical elements (0 = unison, 1 = p⁻¹, 2 = t, 3 = p) is entirely implicit. A comment per case — -- i = 0 = unison, etc. — would make the case analysis legible.

2.5 complement_SI_is_fixedPoint — backward step (MajorMinor.lean:89–90)


· intro hni
  exact ⟨Or.inl (Or.inl hni), hni⟩
Or.inl (Or.inl hni) places i in the s component of s ∪ frontier.image(·+1) ∪ frontier.image(·-1). The reason is that i ∈ s = univ \ selfInverseSet t (since hni : i ∉ selfInverseSet t and i ∈ univ). This single-sentence explanation is absent.

2.6 prefixed_contains_complement — step helper type (MajorMinor.lean:139–149)


have step : ∀ j : ZMod 12,
    j ∈ s ∪ ({7, (5 : ZMod 12)} : Finset (ZMod 12)) →
    ∀ i : ZMod 12, (i = j + 1 ∨ i = j - 1) → i ∉ ({0, (6 : ZMod 12)} : Finset _) → i ∈ s
{7, 5} is {p, p⁻¹} and {0, 6} is the self-inverse set. These concrete literals appear without explanation. After subst ht6; subst hp7, the original names p and t are gone and replaced by their concrete values. A comment -- {7,5} = {p, p⁻¹}, {0,6} = selfInverseSet t at the step definition site would be helpful.

The proof of step uses:


rcases hi with rfl | rfl
· exact Or.inl (Or.inr ⟨j, Finset.mem_union.mp hj, rfl⟩)
· exact Or.inr ⟨j, Finset.mem_union.mp hj, rfl⟩
Or.inl (Or.inr ...) targets the frontier.image(·+1) component of stepMM; Or.inr ... targets frontier.image(·-1). This matches the structure of stepMM but is not stated.

2.7 Partition.lean — cascading by_cases with left/right (Partition.lean:20–23)


by_cases h0  : i = 0;    · left; left; left;  exact h0
by_cases ht' : i = t;    · left; left; right; exact ht'
by_cases hp' : i = p;    · left; right; left; exact hp'
by_cases hpi : i = p⁻¹; · left; right; right; exact hpi
The argument is: dispatch on which of the four classes i belongs to. The left/right navigation encodes the union structure (selfInverseSet t) ∪ {p, p⁻¹} ∪ majorMinorIntervals p t which is a left-associated union of three sets. This is correct but fragile — any reordering of the union breaks it. It also relies on the reader to count union levels. Using Finset.mem_union rewrites explicitly, or using simp [selfInverseSet, ...] to reduce membership, would be more robust.