import Music.Basic

variable {m : ℕ}

/-! ## Axioms -/

/-- **A1**: A non-zero self-inverse interval (the tritone) exists. Forces m even. -/
axiom tritone_exists [NeZero m] :
    ∃ t : HarmonicInterval m, IsTritone t

/-- **A2**: The tritone is unique. Rules out m = 8 (where 2 and 6 are both self-inverse). -/
axiom tritone_unique [NeZero m]
    (s t : HarmonicInterval m)
    (hs : IsTritone s)
    (ht : IsTritone t) : s = t

/-- **A3**: A perfect interval exists. -/
axiom perfect_exists [NeZero m] : ∃ p : HarmonicInterval m, isPerfect p

/-- **A4**: Perfect intervals are not self-inverse. -/
axiom perfect_not_SI [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : ¬isSelfInverse p

/-- Perfect intervals are non-unison. Derived from A4 and `unison_is_self_inverse`. -/
theorem perfect_nonzero [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : p ≠ 0 :=
  fun h => perfect_not_SI p hp (h ▸ unison_is_self_inverse)

/-- **A5**: The perfect class is exactly the pair {p, p⁻¹}. -/
axiom perfect_iff [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p)
    (q : HarmonicInterval m) : isPerfect q ↔ q = p ∨ q = p⁻¹

theorem perfect_unique [NeZero m]
    (p q : HarmonicInterval m) (hp : isPerfect p) (hq : isPerfect q) : q = p ∨ q = p⁻¹ :=
  (perfect_iff p hp q).mp hq

theorem perfect_inv_closed [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : isPerfect p⁻¹ :=
  (perfect_iff p hp p⁻¹).mpr (Or.inr rfl)

/-- **A7**: The perfect interval sits one semitone above the tritone. In 12TET: 7 = 6+1. -/
axiom perfect_above_tritone [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    p = t + 1

/-- **A8**: Five semitones above the perfect interval reaches unison. In 12TET: 7+5=0. -/
axiom five_above_perfect [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : p + 5 = 0

/-- **A9**: A major/minor interval exists. Rules out m = 4. -/
axiom major_minor_exists [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    ∃ i : HarmonicInterval m, i ≠ 0 ∧ ¬isSelfInverse i ∧ ¬isPerfect i
