import Music.Basic

variable {m : ℕ}

/-! ## Axioms -/

/-- **A1**: A non-zero self-inverse interval (the tritone) exists. Forces m even. -/
axiom tritone_exists [NeZero m] :
    ∃ t : HarmonicInterval m, t ≠ 0 ∧ isSelfInverse t

/-- **A2**: The tritone is unique. Rules out m = 8 (where 2 and 6 are both self-inverse). -/
axiom tritone_unique [NeZero m]
    (s t : HarmonicInterval m)
    (hs : s ≠ 0 ∧ isSelfInverse s)
    (ht : t ≠ 0 ∧ isSelfInverse t) : s = t

/-- **A3**: A perfect interval exists. -/
axiom perfect_exists [NeZero m] : ∃ p : HarmonicInterval m, isPerfect p

/-- **A4**: Perfect intervals are non-unison. -/
axiom perfect_nonzero [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : p ≠ 0

/-- **A4'**: Perfect intervals are not self-inverse. -/
axiom perfect_not_SI [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : ¬isSelfInverse p

/-- **A5**: The perfect interval is unique as a pair. -/
axiom perfect_unique [NeZero m]
    (p q : HarmonicInterval m) (hp : isPerfect p) (hq : isPerfect q) : q = p ∨ q = p⁻¹

/-- **A5'**: The inverse of a perfect interval is perfect. -/
axiom perfect_inv_closed [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : isPerfect p⁻¹

/-- **A6**: The perfect interval generates ZMod m (circle of fifths). -/
axiom perfect_generates [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : IsUnit p

/-- **A7**: The perfect interval sits one semitone above the tritone. In 12TET: 7 = 6+1. -/
axiom perfect_above_tritone [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    p = t + 1

/-- **A8**: Five semitones above the perfect interval reaches unison. In 12TET: 7+5=0. -/
axiom five_above_perfect [NeZero m]
    (p : HarmonicInterval m) (hp : isPerfect p) : p + 5 = 0

/-- **A9**: A major/minor interval exists. Rules out m = 4. -/
axiom major_minor_exists [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    ∃ i : HarmonicInterval m, i ≠ 0 ∧ ¬isSelfInverse i ∧ ¬isPerfect i
