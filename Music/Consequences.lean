import Mathlib.Data.Finset.Card -- Finset.card_pair
import Music.Basic
import Music.Axioms

variable {m : ℕ}

/-- Pin the tritone to a concrete value: if `c` is also a non-zero self-inverse then `t = c`. -/
theorem tritone_eq [NeZero m]
    (t : HarmonicInterval m) (ht : IsTritone t)
    (c : HarmonicInterval m) (hc0 : c ≠ 0) (hcsi : c + c = 0) : t = c :=
  tritone_unique t c ht { ne_zero := hc0, selfInverse := hcsi }

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
