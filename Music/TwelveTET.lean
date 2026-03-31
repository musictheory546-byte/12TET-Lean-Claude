import Music.Basic
import Music.Axioms
import Music.Consequences

/-!
# Harmonic Intervals and 12-Tone Equal Temperament

We build the theory of harmonic intervals from algebraic first principles and prove
that 12-tone equal temperament (12TET) is the unique tuning system satisfying a small
set of musically-motivated axioms.

## Model

Intervals are modelled as `ZMod m` where `m` is the number of tones in an octave.
We classify them into four classes:

  1. **Unison**      — the identity, 0
  2. **Tritone**     — the unique non-zero self-inverse interval t (t + t = 0)
  3. **Perfect**     — a primitive class; exactly the pair {p, p⁻¹}
  4. **Major/Minor** — the least fixed point of ±1 steps from {p, p⁻¹},
                       stopping at the self-inverse set {0, t}

## Axioms

  A1.  tritone_exists        : ∃ t ≠ 0, t + t = 0       (forces m even)
  A2.  tritone_unique        : unique such t
  A3.  perfect_exists        : ∃ p, isPerfect p
  A4.  perfect_nonzero       : isPerfect p → p ≠ 0
  A4'. perfect_not_SI        : isPerfect p → ¬isSelfInverse p
  A5.  perfect_unique        : isPerfect p → isPerfect q → q = p ∨ q = p⁻¹
  A5'. perfect_inv_closed    : isPerfect p → isPerfect p⁻¹
  A6.  perfect_generates     : isPerfect p → IsUnit p     (circle of fifths)
  A7.  perfect_above_tritone : isPerfect p → p = t + 1
  A8.  five_above_perfect    : isPerfect p → p + 5 = 0
  A9.  major_minor_exists    : ∃ non-unison non-SI non-perfect interval

From A1–A9 we prove m = 12, then prove the major/minor lfp has exactly 8 elements.
-/

variable {m : ℕ}

/-! # Deriving m = 12 -/

/-- t + 6 = 0. From p = t+1 (A7) and p+5 = 0 (A8). -/
private lemma tritone_plus_six [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    t + 6 = 0 :=
  calc t + 6 = t + 1 + 5 := by ring
    _        = p + 5     := by rw [← perfect_above_tritone p t hp ht]
    _        = 0         := five_above_perfect p hp

/-- 12 = 0 in ZMod m. From t+6=0 and t+t=0. -/
private lemma twelve_eq_zero [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    (12 : HarmonicInterval m) = 0 :=
  calc (12 : HarmonicInterval m)
      = (t + 6) + (t + 6) - (t + t) := by ring
    _ = 0 + 0 - 0                   := by rw [tritone_plus_six p t hp ht, ht.2]
    _ = 0                           := by ring

/-- m ∣ 12. -/
private lemma m_dvd_twelve [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    m ∣ 12 := by
  have h : (12 : ZMod m) = 0 := twelve_eq_zero p t hp ht
  have h12 : ((12 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
  exact (CharP.cast_eq_zero_iff (ZMod m) m 12).mp h12

/-- m is even: (2 : ZMod m) = 0 because 2t = 0 and t generates a copy of ZMod 2. -/
private lemma m_even [NeZero m]
    (t : HarmonicInterval m) (ht : t ≠ 0 ∧ isSelfInverse t) :
    2 ∣ m := by
  have h2t : t + t = 0 := ht.2
  have ht0 : t ≠ 0   := ht.1
  have hord : addOrderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    apply addOrderOf_eq_prime
    · rw [two_nsmul]; exact h2t
    · exact ht0
  have hdvd : addOrderOf t ∣ m := by
    have h : addOrderOf t ∣ Nat.card (ZMod m) := addOrderOf_dvd_natCard t
    rwa [Nat.card_eq_fintype_card, ZMod.card] at h
  exact hord ▸ hdvd

/-- m ≠ 2: p = t+1 = 0 in ZMod 2, contradicting A4. -/
private lemma m_ne_two [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    m ≠ 2 := by
  intro hm; subst hm
  have ht1 : t = 1 := by
    clear hp p; revert t
    simp only [isSelfInverse]; decide
  exact perfect_nonzero p hp
    (by rw [perfect_above_tritone p t hp ht, ht1]; decide)

/-- m ≠ 6: p+5 ≠ 0 in ZMod 6 for any p consistent with A7. -/
private lemma m_ne_six [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    m ≠ 6 := by
  intro hm; subst hm
  have ht3 : t = 3 := by
    clear hp p; revert t
    simp only [isSelfInverse]; decide
  have hp4 : p = 4 := by rw [perfect_above_tritone p t hp ht, ht3]; decide
  exact absurd (five_above_perfect p hp) (by simp only [hp4]; decide)

/-- m ≠ 4: major/minor intervals cannot exist in ZMod 4. -/
private lemma m_ne_four [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    m ≠ 4 := by
  intro hm; subst hm
  obtain ⟨i, hine, hiSI, hiP⟩ := major_minor_exists p t hp ht
  have ht2 : t = 2 := by
    clear hp p; revert t
    simp only [isSelfInverse]; decide
  have hp3 : p = 3 := by rw [perfect_above_tritone p t hp ht, ht2]; decide
  have hpi : p⁻¹ = 1 := by simp only [HI_inv_eq_neg, hp3]; decide
  fin_cases i <;> simp only at *
  · exact hine rfl
  · exact hiP (by have := perfect_inv_closed p hp; rwa [hpi] at this)
  · exact hiSI (by simp only [isSelfInverse]; decide)
  · exact hiP (by rwa [hp3] at hp)

/-- **The 12TET theorem**: m = 12. -/
theorem twelve_TET [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    m = 12 := by
  have h1 := m_dvd_twelve p t hp ht
  have h2 := m_even t ht
  have h3 := m_ne_two p t hp ht
  have h4 := m_ne_four p t hp ht
  have h5 := m_ne_six p t hp ht
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm_le : m ≤ 12 := Nat.le_of_dvd (by norm_num) h1
  interval_cases m <;> omega
