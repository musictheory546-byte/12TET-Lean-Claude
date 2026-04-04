import Mathlib.Algebra.CharP.Defs         -- CharP.cast_eq_zero_iff
import Mathlib.Algebra.Group.Defs         -- two_nsmul
import Mathlib.Data.Nat.Prime.Defs        -- Nat.Prime
import Mathlib.Data.ZMod.Basic            -- CharP instance for ZMod, ZMod.card
import Mathlib.GroupTheory.OrderOfElement  -- addOrderOf_eq_prime, addOrderOf_dvd_natCard
import Mathlib.Logic.Basic                -- Fact
import Mathlib.SetTheory.Cardinal.Finite  -- Nat.card_eq_fintype_card
import Mathlib.Tactic.IntervalCases       -- interval_cases
import Mathlib.Tactic.NormNum            -- norm_num
import Mathlib.Tactic.LinearCombination  -- linear_combination
import Mathlib.Tactic.Ring               -- ring
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
  A4.  perfect_not_SI        : isPerfect p → ¬isSelfInverse p
       perfect_nonzero       : derived from A4 + unison_is_self_inverse
  A5.  perfect_iff           : isPerfect q ↔ q = p ∨ q = p⁻¹
       perfect_unique        : derived from A5
       perfect_inv_closed    : derived from A5
  A6.  perfect_least_above_tritone : p is the least non-SI interval above t
       perfect_above_tritone : p = t + 1, derived from A6 and m ≥ 4
  A7.  five_above_perfect    : isPerfect p → p + 5 = 0
  A8.  major_minor_exists    : ∃ non-unison non-SI non-perfect interval

From A1–A8 we prove m = 12, then prove the major/minor lfp has exactly 8 elements.
-/

variable {m : ℕ}

/-! # Deriving m = 12 -/

/-- m is even: 2t = 0 and t generates a copy of ZMod 2. -/
private lemma m_even [NeZero m]
    (t : HarmonicInterval m) (ht : IsTritone t) :
    2 ∣ m := by
  have hord : addOrderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    apply addOrderOf_eq_prime
    · rw [two_nsmul]; exact ht.selfInverse
    · exact ht.ne_zero
  have hdvd : addOrderOf t ∣ m := by
    have h : addOrderOf t ∣ Nat.card (ZMod m) := addOrderOf_dvd_natCard t
    rwa [Nat.card_eq_fintype_card, ZMod.card] at h  -- group order of ZMod m is m
  exact hord ▸ hdvd

/-- m ≠ 2: in ZMod 2 every element is self-inverse, contradicting A4. -/
private lemma m_ne_two [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    m ≠ 2 := by
  intro hm; subst hm
  exact perfect_not_SI p hp (show p + p = 0 from by fin_cases p <;> decide)

/-- p = t + 1. Derived from A6 (minimality) and the fact that t+1 is non-self-inverse. -/
lemma perfect_above_tritone [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    p = t + 1 := by
  obtain ⟨hgt, hmin⟩ := perfect_least_above_tritone p t hp ht
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  -- m ≥ 4: m is even and ≠ 2
  have hm4 : 4 ≤ m := by
    obtain ⟨k, hk⟩ := m_even t ht; have hn2 := m_ne_two p t hp ht; omega
  -- 2 ≠ 0 in ZMod m since m ≥ 4
  have h2ne : (2 : HarmonicInterval m) ≠ 0 := fun h =>
    absurd (Nat.le_of_dvd (by norm_num) ((CharP.cast_eq_zero_iff (ZMod m) m 2).mp h))
           (by omega)
  -- t + 1 is not self-inverse: (t+1)+(t+1) = 2t+2 = 2 ≠ 0
  have ht1_nsi : ¬isSelfInverse (t + 1) := by
    intro h
    apply h2ne
    have : t + 1 + (t + 1) = 0 := h
    have : t + t = 0 := ht.selfInverse
    linear_combination ‹t + 1 + (t + 1) = 0› - ‹t + t = 0›
  -- t + 1 ≠ 0
  have ht1_ne0 : t + 1 ≠ 0 := fun h => ht1_nsi (h ▸ unison_is_self_inverse)
  -- val(t + 1) = val t + 1: no wraparound since val t + 1 < m
  have hv1 : ZMod.val (1 : HarmonicInterval m) = 1 := ZMod.val_one'' (by omega)
  have hlt_m : ZMod.val t + ZMod.val (1 : HarmonicInterval m) < m := by
    rw [hv1]
    by_contra h
    push Not at h
    have heq : ZMod.val t + 1 = m := by have := ZMod.val_lt t; omega
    exact ht1_ne0 ((ZMod.val_eq_zero _).mp (by rw [ZMod.val_add, hv1, heq, Nat.mod_self]))
  have hval : ZMod.val (t + 1) = ZMod.val t + 1 := by
    rw [ZMod.val_add_of_lt hlt_m, hv1]
  -- By minimality: val p ≤ val(t+1) = val t + 1
  have hle : ZMod.val p ≤ ZMod.val (t + 1) :=
    hmin (t + 1) ht1_nsi (by omega)
  -- val p = val(t+1), so p = t+1
  exact ZMod.val_injective m (by omega)

/-- t + 6 = 0. From p = t+1 and p+5 = 0. -/
private lemma tritone_plus_six [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    t + 6 = 0 :=
  calc t + 6 = t + 1 + 5 := by ring
    _        = p + 5     := by rw [← perfect_above_tritone p t hp ht]
    _        = 0         := five_above_perfect p hp

/-- 12 = 0 in ZMod m. From t+6=0 and t+t=0. -/
private lemma twelve_eq_zero [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    (12 : HarmonicInterval m) = 0 := by
  have hsi : t + t = 0 := ht.selfInverse
  linear_combination 2 * tritone_plus_six p t hp ht - hsi

/-- m ∣ 12. -/
private lemma m_dvd_twelve [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    m ∣ 12 :=
  (CharP.cast_eq_zero_iff (ZMod m) m 12).mp (twelve_eq_zero p t hp ht)

/-- m ≠ 6: p+5 ≠ 0 in ZMod 6 for any p consistent with A6. -/
private lemma m_ne_six [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    m ≠ 6 := by
  intro hm; subst hm
  have ht3 : t = 3 := tritone_eq t ht 3 (by decide) (by decide)
  have hp4 : p = 4 := by rw [perfect_above_tritone p t hp ht, ht3]; decide
  exact absurd (five_above_perfect p hp) (by simp only [hp4]; decide)

/-- m ≠ 4: major/minor intervals cannot exist in ZMod 4. -/
private lemma m_ne_four [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    m ≠ 4 := by
  intro hm; subst hm
  obtain ⟨i, hine, hiSI, hiP⟩ := major_minor_exists p t hp ht
  have ht2 : t = 2 := tritone_eq t ht 2 (by decide) (by decide)
  have hp3 : p = 3 := by rw [perfect_above_tritone p t hp ht, ht2]; decide
  have hpi : p⁻¹ = 1 := by simp only [HI_inv_eq_neg, hp3]; decide
  fin_cases i <;> simp only at *
  · exact hine rfl                                               -- i = 0: unison
  · exact hiP (by have := perfect_inv_closed p hp; rwa [hpi] at this)  -- i = 1 = p⁻¹
  · exact hiSI (by simp only [isSelfInverse]; decide)           -- i = 2 = t
  · exact hiP (by rwa [hp3] at hp)                              -- i = 3 = p

/-- **The 12TET theorem**: m = 12. -/
theorem twelve_TET [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : IsTritone t) :
    m = 12 := by
  have h1 := m_dvd_twelve p t hp ht
  have h2 := m_even t ht
  have h3 := m_ne_two p t hp ht
  have h4 := m_ne_four p t hp ht
  have h5 := m_ne_six p t hp ht
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm_le : m ≤ 12 := Nat.le_of_dvd (by norm_num) h1
  interval_cases m <;> omega
