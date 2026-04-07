import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Music.Basic

/-!
# Consistency of the axiom system

`isPerfect` is opaque, so the axioms in `Axioms.lean` cannot be proved as
theorems.  Instead we bundle the seven axiom *conditions* (A1 commented out)
into a structure `HarmonicModel`, parameterised over an explicit predicate `perf`
that plays the role of `isPerfect`.  Constructing a term of this type for a
specific modulus constitutes a consistency proof: it shows the conditions are
jointly satisfiable.

The standard model is `ZMod 12` with `p = 7` and `perf i ↔ i = 7 ∨ i = 5`.

A tightest-constraint model is `ZMod 3` with `p = 1` and `perf i ↔ i = 1 ∨ i = 2`,
witnessing that A2–A8 alone do not force m = 12.
-/

variable {m : ℕ}

/-- The seven axiom conditions (A1 commented out), with `perf` playing the role of `isPerfect`. -/
structure HarmonicModel (m : ℕ) [NeZero m] where
  p : HarmonicInterval m
  perf : HarmonicInterval m → Prop
  /-- A2: the tritone, if one exists, is unique. -/
  A2   : ∀ s u : HarmonicInterval m, IsTritone s → IsTritone u → s = u
  /-- A3: a perfect interval exists. -/
  A3   : perf p
  /-- A4: perfect intervals are not self-inverse. -/
  A4   : ∀ q, perf q → ¬isSelfInverse q
  /-- A5: the perfect class is exactly {p, p⁻¹}. -/
  A5   : ∀ q, perf q ↔ q = p ∨ q = p⁻¹
  /-- A6: if a tritone t exists, p is the least non-self-inverse interval above it. -/
  A6   : ∀ t : HarmonicInterval m, IsTritone t →
         ZMod.val t < ZMod.val p ∧
         ∀ i : HarmonicInterval m, ¬isSelfInverse i →
           ZMod.val t < ZMod.val i → ZMod.val p ≤ ZMod.val i
  /-- A7: five semitones above p reaches unison. -/
  A7   : p + 5 = 0
  /-- A8: if a tritone t exists, a non-unison non-self-inverse non-perfect interval exists. -/
  A8   : ∀ t : HarmonicInterval m, IsTritone t →
         ∃ i : HarmonicInterval m, i ≠ 0 ∧ ¬isSelfInverse i ∧ ¬perf i

/-- The unique tritone in ZMod 12 is 6. -/
private lemma zmod12_tritone_is_six (s : HarmonicInterval 12) (hs : IsTritone s) : s = 6 := by
  obtain ⟨hne, hsi⟩ := hs
  simp only [isSelfInverse] at hsi
  fin_cases s <;> first | rfl | exact absurd rfl hne | exact absurd hsi (by decide)

/-- The standard model: `ZMod 12`, `p = 7`, `perf = {7, 5}`.
All conditions are verified by `decide` or `fin_cases`. -/
def zmod12Model : HarmonicModel 12 where
  p    := 7
  perf := fun i => i = 7 ∨ i = 5
  A2   := fun s u hs hu =>
    (zmod12_tritone_is_six s hs).trans (zmod12_tritone_is_six u hu).symm
  A3   := Or.inl rfl
  A4   := by
    intro q hq
    rcases hq with rfl | rfl <;> simp only [isSelfInverse] <;> decide
  A5   := fun _ => Iff.rfl
  A6   := by
    intro t ht
    have ht6 := zmod12_tritone_is_six t ht; subst ht6
    exact ⟨by decide, by
      intro i hisi hgt
      fin_cases i <;> revert hisi hgt <;> simp only [isSelfInverse] <;> decide⟩
  A7   := by decide
  A8   := by
    intro t ht
    have ht6 := zmod12_tritone_is_six t ht; subst ht6
    exact ⟨1, by decide, by simp only [isSelfInverse]; decide, by decide⟩

/-- ZMod 3 has no tritone: odd modulus means no non-zero element is self-inverse. -/
private lemma zmod3_no_tritone (s : HarmonicInterval 3) : ¬IsTritone s := by
  intro ⟨hne, hsi⟩
  fin_cases s
  · exact hne rfl
  · simp only [isSelfInverse] at hsi; exact absurd hsi (by decide)
  · simp only [isSelfInverse] at hsi; exact absurd hsi (by decide)

/-- The tightest-constraint model: `ZMod 3`, `p = 1`, `perf = {1, 2}`.
No tritone exists in ZMod 3 (odd modulus: 1+1=2≠0 and 2+2=1≠0), so A2, A6, A8
hold vacuously.  A7 holds because 1 + 5 = 6 ≡ 0 (mod 3).
This witnesses that A2–A8 alone do not force m = 12. -/
def zmod3Model : HarmonicModel 3 where
  p    := 1
  perf := fun i => i = 1 ∨ i = 2
  A2   := fun s _ hs _ => absurd hs (zmod3_no_tritone s)
  A3   := Or.inl rfl
  A4   := by
    intro q hq
    rcases hq with rfl | rfl <;> simp only [isSelfInverse] <;> decide
  A5   := fun _ => Iff.rfl
  A6   := fun t ht => absurd ht (zmod3_no_tritone t)
  A7   := by decide
  A8   := fun t ht => absurd ht (zmod3_no_tritone t)

/-!
### Non-existence results for m = 4 and m = 5

Neither `HarmonicModel 4` nor `HarmonicModel 5` can be constructed:
- m = 5: A7 forces p = 0 (unison), which is self-inverse, contradicting A4.
- m = 4: A7 forces p = 3; ZMod 4 has a tritone t = 2; A8 then demands a
  non-unison non-self-inverse non-perfect element, but {1, 3} = {p⁻¹, p}
  exhausts the non-zero non-self-inverse elements.
-/

/-- No `HarmonicModel 5` exists: A7 forces p = 0, which is self-inverse, contradicting A4. -/
theorem no_model_5 : ¬Nonempty (HarmonicModel 5) := by
  rintro ⟨⟨p, perf, _, A3, A4, _, _, A7, _⟩⟩
  -- In ZMod 5, char = 5 so 5 = 0; A7 : p + 5 = 0 becomes p = 0
  have hp0 : p = 0 := by
    have h5 : (5 : HarmonicInterval 5) = 0 := by decide
    have := A7; rw [h5, add_zero] at this; exact this
  exact A4 p A3 (hp0 ▸ unison_is_self_inverse)

/-- No `HarmonicModel 4` exists: A7 forces p = 3; t = 2 is the unique tritone;
A8 then requires a non-perfect non-SI non-zero element, but none exists. -/
theorem no_model_4 : ¬Nonempty (HarmonicModel 4) := by
  rintro ⟨⟨p, perf, _, A3, _, A5, _, A7, A8⟩⟩
  -- In ZMod 4, 5 = 1; A7 : p + 1 = 0 so p = -1 = 3
  have hp3 : p = 3 := by
    have h5 : (5 : HarmonicInterval 4) = 1 := by decide
    have hA7' : p + 1 = 0 := by rwa [h5] at A7
    have hm1 : (-1 : HarmonicInterval 4) = 3 := by decide
    rw [← hm1, ← eq_neg_of_add_eq_zero_left hA7']
  have ht2 : IsTritone (2 : HarmonicInterval 4) :=
    ⟨by decide, by simp [isSelfInverse]; decide⟩
  obtain ⟨i, hine, hiSI, hiP⟩ := A8 2 ht2
  have hpi1 : p⁻¹ = (1 : HarmonicInterval 4) := by
    simp only [HI_inv_eq_neg, hp3]; decide
  fin_cases i
  · exact hine rfl
  · exact hiP ((A5 1).mpr (Or.inr hpi1.symm))
  · exact hiSI (by simp [isSelfInverse]; decide)
  · exact hiP ((A5 3).mpr (Or.inl hp3.symm))

/-!
### Models for m = 7, 9, 11 (odd moduli, no tritone)

In each case A7 determines p = -5, and since the modulus is odd there is no
non-zero self-inverse element, so A2, A6, and A8 hold vacuously.
-/

private lemma zmod7_no_tritone (s : HarmonicInterval 7) : ¬IsTritone s := by
  intro ⟨hne, hsi⟩
  fin_cases s
  · exact hne rfl
  all_goals (simp only [isSelfInverse] at hsi; exact absurd hsi (by decide))

private lemma zmod9_no_tritone (s : HarmonicInterval 9) : ¬IsTritone s := by
  intro ⟨hne, hsi⟩
  fin_cases s
  · exact hne rfl
  all_goals (simp only [isSelfInverse] at hsi; exact absurd hsi (by decide))

private lemma zmod11_no_tritone (s : HarmonicInterval 11) : ¬IsTritone s := by
  intro ⟨hne, hsi⟩
  fin_cases s
  · exact hne rfl
  all_goals (simp only [isSelfInverse] at hsi; exact absurd hsi (by decide))

/-- Model for m = 7: p = 2, perf = {2, 5}. No tritone; A2/A6/A8 vacuous. -/
def zmod7Model : HarmonicModel 7 where
  p    := 2
  perf := fun i => i = 2 ∨ i = 5
  A2   := fun s _ hs _ => absurd hs (zmod7_no_tritone s)
  A3   := Or.inl rfl
  A4   := by
    intro q hq
    rcases hq with rfl | rfl <;> simp only [isSelfInverse] <;> decide
  A5   := fun _ => Iff.rfl
  A6   := fun t ht => absurd ht (zmod7_no_tritone t)
  A7   := by decide
  A8   := fun t ht => absurd ht (zmod7_no_tritone t)

/-- Model for m = 9: p = 4, perf = {4, 5}. No tritone; A2/A6/A8 vacuous. -/
def zmod9Model : HarmonicModel 9 where
  p    := 4
  perf := fun i => i = 4 ∨ i = 5
  A2   := fun s _ hs _ => absurd hs (zmod9_no_tritone s)
  A3   := Or.inl rfl
  A4   := by
    intro q hq
    rcases hq with rfl | rfl <;> simp only [isSelfInverse] <;> decide
  A5   := fun _ => Iff.rfl
  A6   := fun t ht => absurd ht (zmod9_no_tritone t)
  A7   := by decide
  A8   := fun t ht => absurd ht (zmod9_no_tritone t)

/-- Model for m = 11: p = 6, perf = {6, 5}. No tritone; A2/A6/A8 vacuous. -/
def zmod11Model : HarmonicModel 11 where
  p    := 6
  perf := fun i => i = 6 ∨ i = 5
  A2   := fun s _ hs _ => absurd hs (zmod11_no_tritone s)
  A3   := Or.inl rfl
  A4   := by
    intro q hq
    rcases hq with rfl | rfl <;> simp only [isSelfInverse] <;> decide
  A5   := fun _ => Iff.rfl
  A6   := fun t ht => absurd ht (zmod11_no_tritone t)
  A7   := by decide
  A8   := fun t ht => absurd ht (zmod11_no_tritone t)

/-!
### Non-existence results for m = 6, 8, 10
-/

/-- No `HarmonicModel 6` exists: A7 forces p = 1; t = 3 is a tritone;
A6 then requires val(3) < val(1), i.e. 3 < 1. Contradiction. -/
theorem no_model_6 : ¬Nonempty (HarmonicModel 6) := by
  rintro ⟨⟨p, perf, _, _, _, _, A6, A7, _⟩⟩
  have hp : p = -5 := eq_neg_of_add_eq_zero_left A7
  subst hp
  have ht3 : IsTritone (3 : HarmonicInterval 6) :=
    ⟨by decide, by simp only [isSelfInverse]; decide⟩
  exact absurd (A6 3 ht3).1 (by decide)

/-- No `HarmonicModel 8` exists: A7 forces p = 3; t = 4 is a tritone;
A6 then requires val(4) < val(3), i.e. 4 < 3. Contradiction. -/
theorem no_model_8 : ¬Nonempty (HarmonicModel 8) := by
  rintro ⟨⟨p, perf, _, _, _, _, A6, A7, _⟩⟩
  have hp : p = -5 := eq_neg_of_add_eq_zero_left A7
  subst hp
  have ht4 : IsTritone (4 : HarmonicInterval 8) :=
    ⟨by decide, by simp only [isSelfInverse]; decide⟩
  exact absurd (A6 4 ht4).1 (by decide)

/-- No `HarmonicModel 10` exists: A7 forces p = 5, which is self-inverse, contradicting A4. -/
theorem no_model_10 : ¬Nonempty (HarmonicModel 10) := by
  rintro ⟨⟨p, perf, _, A3, A4, _, _, A7, _⟩⟩
  have hp : p = -5 := eq_neg_of_add_eq_zero_left A7
  subst hp
  exact A4 (-5) A3 (by simp only [isSelfInverse]; decide)
