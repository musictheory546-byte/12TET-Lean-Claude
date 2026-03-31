import Mathlib.Data.Finset.Basic -- Finset.mem_univ, Finset.mem_union, Finset.mem_sdiff
import Music.Basic
import Music.Axioms
import Music.MajorMinor

variable {m : ℕ}

/-! ## The partition theorem -/

/-- The four classes partition ZMod m. -/
theorem interval_partition [NeZero m]
    (p t : HarmonicInterval m) (hp : isPerfect p) (ht : t ≠ 0 ∧ isSelfInverse t) :
    (Finset.univ : Finset (HarmonicInterval m)) =
      selfInverseSet t ∪ {p, p⁻¹} ∪ majorMinorIntervals p t := by
  simp only [majorMinorIntervals, selfInverseSet]
  rw [nonSIReachable_eq_complement p t hp ht]
  ext i
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
             Finset.mem_sdiff, true_iff]
  by_cases h0  : i = 0;    · left; left; left;  exact h0
  by_cases ht' : i = t;    · left; left; right; exact ht'
  by_cases hp' : i = p;    · left; right; left; exact hp'
  by_cases hpi : i = p⁻¹; · left; right; right; exact hpi
  · right
    refine ⟨⟨trivial, ?_⟩, ?_⟩
    · simp only [selfInverseSet, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h0, ht'⟩
    · simp only [not_or]
      exact ⟨hp', by rwa [HI_inv_eq_neg]⟩
