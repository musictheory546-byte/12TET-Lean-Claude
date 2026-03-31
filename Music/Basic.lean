import Mathlib

abbrev HarmonicInterval (m : ℕ) := ZMod m

def unison [NeZero m] : HarmonicInterval m := 0

variable {m : ℕ}

instance [NeZero m] : Inv (HarmonicInterval m) where inv := Neg.neg

@[simp] lemma HI_inv_eq_neg [NeZero m] (i : HarmonicInterval m) : i⁻¹ = -i := rfl
@[simp] lemma HI_inv_inv [NeZero m] (i : HarmonicInterval m) : i⁻¹⁻¹ = i := neg_neg i

theorem inverses_span_octaves [NeZero m] (i : HarmonicInterval m) : i + i⁻¹ = unison :=
  add_neg_cancel i

def inv_closed [NeZero m] (s : Finset (HarmonicInterval m)) : Prop := ∀ i ∈ s, i⁻¹ ∈ s

/-! ## Self-inverse intervals -/

/-- i is self-inverse if i + i = 0: it divides the octave exactly in half. -/
def isSelfInverse [NeZero m] (i : HarmonicInterval m) : Prop := i + i = 0

theorem unison_is_self_inverse [NeZero m] : isSelfInverse (unison (m := m)) := by
  simp [isSelfInverse, unison]

theorem selfInverse_iff_eq_neg [NeZero m] (i : HarmonicInterval m) :
    isSelfInverse i ↔ i = -i :=
  ⟨eq_neg_of_add_eq_zero_left, fun h => by simp only [isSelfInverse]; linear_combination h⟩

theorem selfInverse_iff_inv_eq [NeZero m] (i : HarmonicInterval m) :
    isSelfInverse i ↔ i⁻¹ = i := by
  rw [HI_inv_eq_neg, selfInverse_iff_eq_neg]; exact ⟨(·.symm), (·.symm)⟩

/-! ## Perfect intervals — a primitive predicate

`isPerfect` is opaque: not defined in terms of other properties, only constrained
by axioms. This is essential — defining it as `i ≠ 0 ∧ ¬isSelfInverse i` would
make every major/minor interval "perfect", causing `perfect_unique` to force m = 4.
-/

opaque isPerfect [NeZero m] : HarmonicInterval m → Prop
