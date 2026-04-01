import Mathlib.Data.Finset.Card -- Finset.card_pair
import Music.Basic
import Music.Axioms

variable {m : ℕ}

theorem selfInverse_eq_zero_or_tritone [NeZero m]
    (t i : HarmonicInterval m) (ht : IsTritone t) (hi : isSelfInverse i) :
    i = 0 ∨ i = t := by
  by_cases h : i = 0
  · exact Or.inl h
  · exact Or.inr (tritone_unique i t ⟨h, hi⟩ ht)

theorem perfect_not_self_inverse [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : p ≠ p⁻¹ :=
  fun heq => perfect_not_SI p hp ((selfInverse_iff_inv_eq p).mpr heq.symm)

theorem perfect_pair_card [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) :
    ({p, p⁻¹} : Finset (HarmonicInterval m)).card = 2 :=
  Finset.card_pair (perfect_not_self_inverse p hp)
