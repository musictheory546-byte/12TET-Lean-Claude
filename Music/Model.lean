import Mathlib.Tactic.FinCases
import Music.Basic

/-!
# Consistency of the axiom system

`isPerfect` is opaque, so the axioms in `Axioms.lean` cannot be proved as
theorems.  Instead we bundle the eight axiom *conditions* into a structure
`HarmonicModel`, parameterised over an explicit predicate `perf` that plays
the role of `isPerfect`.  Constructing a term of this type for a specific
modulus constitutes a consistency proof: it shows the conditions are jointly
satisfiable.

The model is `ZMod 12` with `t = 6`, `p = 7`, and
`perf i ↔ i = 7 ∨ i = 5`.  All conditions are verified computationally.
-/

variable {m : ℕ}

/-- The eight axiom conditions, with `perf` playing the role of `isPerfect`. -/
structure HarmonicModel (m : ℕ) [NeZero m] where
  t    : HarmonicInterval m
  p    : HarmonicInterval m
  perf : HarmonicInterval m → Prop
  /-- A1: a non-zero self-inverse interval exists. -/
  A1   : IsTritone t
  /-- A2: the tritone is unique. -/
  A2   : ∀ s : HarmonicInterval m, IsTritone s → s = t
  /-- A3: a perfect interval exists. -/
  A3   : perf p
  /-- A4: perfect intervals are not self-inverse. -/
  A4   : ∀ q, perf q → ¬isSelfInverse q
  /-- A5: the perfect class is exactly {p, p⁻¹}. -/
  A5   : ∀ q, perf q ↔ q = p ∨ q = p⁻¹
  /-- A6: p is the least non-self-inverse interval above t. -/
  A6   : ZMod.val t < ZMod.val p ∧
         ∀ i : HarmonicInterval m, ¬isSelfInverse i →
           ZMod.val t < ZMod.val i → ZMod.val p ≤ ZMod.val i
  /-- A7: five semitones above p reaches unison. -/
  A7   : p + 5 = 0
  /-- A8: a non-unison non-self-inverse non-perfect interval exists. -/
  A8   : ∃ i : HarmonicInterval m, i ≠ 0 ∧ ¬isSelfInverse i ∧ ¬perf i

/-- The standard model: `ZMod 12`, `t = 6`, `p = 7`, `perf = {7, 5}`.
All conditions are verified by `decide` or `fin_cases` + `decide`. -/
def zmod12Model : HarmonicModel 12 where
  t    := 6
  p    := 7
  perf := fun i => i = 7 ∨ i = 5
  A1   := ⟨by decide, by decide⟩
  A2   := by
    intro s ⟨hne, hsi⟩
    fin_cases s <;> simp_all [isSelfInverse]
  A3   := Or.inl rfl
  A4   := by
    intro q hq
    rcases hq with rfl | rfl <;> simp only [isSelfInverse] <;> decide
  A5   := by
    intro q
    simp only [HI_inv_eq_neg]
    fin_cases q <;> decide
  A6   := ⟨by decide, by
    intro i hsi hgt
    fin_cases i <;> revert hsi hgt <;> simp only [isSelfInverse] <;> decide⟩
  A7   := by decide
  A8   := ⟨1, by decide, by simp only [isSelfInverse]; decide, by decide⟩
