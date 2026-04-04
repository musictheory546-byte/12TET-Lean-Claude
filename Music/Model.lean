import Mathlib.Tactic.FinCases
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
