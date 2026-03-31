import Mathlib.Data.Finset.Card          -- Finset.card_pair, Finset.card_sdiff
import Mathlib.Data.Finset.Lattice.Basic -- Finset.inter_eq_left
import Mathlib.Data.Fintype.Card         -- Finset.card_univ
import Mathlib.Data.ZMod.Basic           -- ZMod.card
import Music.Basic
import Music.Axioms
import Music.Consequences
import Music.TwelveTET
import Music.MajorMinor

variable {m : ℕ}

/-! ## Cardinality -/

theorem selfInverseSet_card [NeZero m]
    (t : HarmonicInterval m) (ht : t ≠ 0 ∧ isSelfInverse t) :
    (selfInverseSet t).card = 2 :=
  Finset.card_pair (Ne.symm ht.1)

private theorem nonSIReachable_card [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    (nonSIReachable p t).card = m - 2 := by
  rw [nonSIReachable_eq_complement p t hp ht, Finset.card_sdiff]
  simp [Finset.card_univ, ZMod.card, selfInverseSet_card t ht]

private theorem perfect_pair_subset_nonSIReachable [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    ({p, p⁻¹} : Finset (HarmonicInterval m)) ⊆ nonSIReachable p t := by
  rw [nonSIReachable_eq_complement p t hp ht]
  simp only [selfInverseSet, Finset.subset_sdiff, Finset.subset_univ, true_and,
             Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
  intro i hi
  rcases hi with rfl | rfl
  · simp only [not_or]
    exact ⟨perfect_nonzero _ hp, fun h => perfect_not_SI _ hp (h ▸ ht.2)⟩
  · simp only [not_or]
    exact ⟨by simp [HI_inv_eq_neg, neg_eq_zero, perfect_nonzero _ hp],
           fun h => perfect_not_SI _ (perfect_inv_closed _ hp) (h ▸ ht.2)⟩

/-- The major/minor class has m - 4 elements. -/
theorem majorMinor_card [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    (majorMinorIntervals p t).card = m - 4 := by
  simp only [majorMinorIntervals]
  have hsub := perfect_pair_subset_nonSIReachable p t hp ht
  have hcard_r := nonSIReachable_card p t hp ht
  have hcard_p := perfect_pair_card p hp
  rw [Finset.card_sdiff]
  have hint : {p, p⁻¹} ∩ nonSIReachable p t = {p, p⁻¹} :=
    Finset.inter_eq_left.mpr hsub
  rw [hint, hcard_r, hcard_p]; omega

/-- **The major/minor cardinality theorem**: 8 elements in 12TET. -/
theorem majorMinor_card_12 [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    (majorMinorIntervals p t).card = 8 := by
  rw [majorMinor_card p t hp ht, twelve_TET p t hp ht]
