import Mathlib.Data.Finset.Basic   -- Finset operations, Finset.mem_filter
import Mathlib.Data.Fintype.Basic  -- Finset.univ
import Mathlib.Tactic.FinCases     -- fin_cases
import Mathlib.Tactic.PushNeg      -- push Not
import Music.TwelveTET

variable {m : ℕ}

/-! ## The major/minor intervals as a least fixed point

The major/minor class is the least fixed point of a monotone step operator `stepMM`
on the complete lattice `(Finset (HarmonicInterval m), ⊆)`. The operator steps ±1
from `s ∪ {p, p⁻¹}` and removes the self-inverse set `{0, t}`.

We construct the lfp as the intersection of all prefixed points of `stepMM`, and prove
it equals `Finset.univ \ {0, t}` by a 10-step walk argument in ZMod 12.

Tracing the iteration in ZMod 12 (t=6, p=7, p⁻¹=5):

  s₀ = ∅
  s₁ = {8, 4}                        (±1 from {7,5}, remove {0,6})
  s₂ = {3, 4, 5, 7, 8, 9}
  s₃ = {2, 3, 4, 5, 7, 8, 9, 10}
  s₄ = {1, 2, 3, 4, 5, 7, 8, 9, 10, 11}   ← fixed point = ZMod 12 \ {0,6}
-/

/-- The self-inverse set {0, t}: the walls the ±1 walk does not cross. -/
def selfInverseSet [NeZero m] (t : HarmonicInterval m) : Finset (HarmonicInterval m) :=
  {0, t}

/-- The step operator. -/
def stepMM [NeZero m]
    (p t : HarmonicInterval m)
    (s : Finset (HarmonicInterval m)) : Finset (HarmonicInterval m) :=
  let frontier := s ∪ {p, p⁻¹}
  (s ∪ frontier.image (· + 1) ∪ frontier.image (· - 1)) \ selfInverseSet t

/-- stepMM is monotone. -/
private theorem stepMM_monotone [NeZero m] (p t : HarmonicInterval m) : Monotone (stepMM p t) := by
  intro s s' hss' i hi
  simp only [stepMM, selfInverseSet, Finset.mem_sdiff, Finset.mem_union,
             Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at *
  obtain ⟨h, hni⟩ := hi
  refine ⟨?_, hni⟩
  rcases h with ((hs | hi1) | hi2)
  · exact Or.inl (Or.inl (hss' hs))
  · obtain ⟨j, hj, rfl⟩ := hi1
    rcases hj with hs | hp
    · exact Or.inl (Or.inr ⟨j, Or.inl (hss' hs), rfl⟩)
    · exact Or.inl (Or.inr ⟨j, Or.inr hp, rfl⟩)
  · obtain ⟨j, hj, rfl⟩ := hi2
    rcases hj with hs | hp
    · exact Or.inr ⟨j, Or.inl (hss' hs), rfl⟩
    · exact Or.inr ⟨j, Or.inr hp, rfl⟩

/-- The non-self-inverse reachable set: intersection of all prefixed points of stepMM.
This is the least prefixed point = least fixed point, constructed without CompleteLattice. -/
noncomputable def nonSIReachable [NeZero m]
    (p t : HarmonicInterval m) : Finset (HarmonicInterval m) :=
  Finset.univ.filter (fun i =>
    ∀ s : Finset (HarmonicInterval m), stepMM p t s ⊆ s → i ∈ s)

private theorem nonSIReachable_least [NeZero m]
    (p t : HarmonicInterval m) (s : Finset (HarmonicInterval m))
    (hs : stepMM p t s ⊆ s) : nonSIReachable p t ⊆ s := by
  intro i hi
  unfold nonSIReachable at hi
  rw [Finset.mem_filter] at hi
  exact hi.2 s hs

/-- The major/minor class: nonSIReachable minus the perfect pair. -/
noncomputable def majorMinorIntervals [NeZero m]
    (p t : HarmonicInterval m) : Finset (HarmonicInterval m) :=
  nonSIReachable p t \ {p, p⁻¹}

/-! ### The lfp equals Finset.univ \ selfInverseSet t -/

/-- `Finset.univ \ selfInverseSet t` is a fixed point of stepMM. -/
private theorem complement_SI_is_fixedPoint [NeZero m]
    (p t : HarmonicInterval m) :
    stepMM p t (Finset.univ \ selfInverseSet t) = Finset.univ \ selfInverseSet t := by
  ext i
  simp only [stepMM, selfInverseSet, Finset.mem_sdiff, Finset.mem_univ, true_and,
             Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨_, hni⟩; exact hni
  · intro hni
    -- i ∈ univ \ selfInverseSet t, so i ∈ s (the first component of the union)
    exact ⟨Or.inl (Or.inl hni), hni⟩

/-- The lfp is contained in the complement of the self-inverse set. -/
private theorem nonSIReachable_subset_complement [NeZero m]
    (p t : HarmonicInterval m) :
    nonSIReachable p t ⊆ Finset.univ \ selfInverseSet t :=
  nonSIReachable_least p t _ (complement_SI_is_fixedPoint p t).le

/-!
### The 10-step walk: every prefixed point contains univ \ {0,t}

A set `s` is a prefixed point of `stepMM p t` if `stepMM p t s ⊆ s`, meaning:
for every `j` in the frontier `s ∪ {p, p⁻¹}`, both `j+1` and `j-1` are in
`s ∪ {0,t}`. In other words: stepping ±1 from the frontier either stays in s
or hits a self-inverse element.

We show that any such s must contain all 10 elements of ZMod 12 \ {0,t}.
The walk order (in ZMod 12 with p=7, p⁻¹=5, t=6):

  From p=7  upward:   p+1=8, p+2=9, p+3=10, p+4=11  (stops: p+5=0)
  From p⁻¹=5 downward: p⁻¹-1=4, p⁻¹-2=3, p⁻¹-3=2, p⁻¹-4=1  (stops: p⁻¹-5=0)
  Then back: p=7 via (p+1)-1, p⁻¹=5 via (p⁻¹-1)+1

Each step uses: j ∈ frontier → j±1 ∉ {0,t} → j±1 ∈ s.
-/

/--
Every prefixed point of `stepMM p t` in ZMod 12 contains `Finset.univ \ selfInverseSet t`.

The proof specialises to m=12 using `twelve_TET`, identifies p=7 and t=6 concretely
via `fin_cases`, then executes the 10-step walk using `decide` at each step.
-/
private theorem prefixed_contains_complement [NeZero m]
    (p t : HarmonicInterval m)
    (hp : isPerfect p)
    (ht : IsTritone t)
    (s : Finset (HarmonicInterval m))
    (hpre : stepMM p t s ⊆ s) :
    Finset.univ \ selfInverseSet t ⊆ s := by
  have hm := twelve_TET p t hp ht
  subst hm
  have ht6 : t = 6 := tritone_eq t ht 6 (by decide) (by decide)
  have hp7 : p = 7 := by
    have := perfect_above_tritone p t hp ht; rw [ht6] at this; simpa using this
  have hpi5 : p⁻¹ = 5 := by
    simp only [HI_inv_eq_neg, hp7]; decide
  subst ht6; subst hp7
  -- {7, 5} = {p, p⁻¹};  {0, 6} = selfInverseSet t
  have step : ∀ j : ZMod 12,
      j ∈ s ∪ ({7, (5 : ZMod 12)} : Finset (ZMod 12)) →
      ∀ i : ZMod 12, (i = j + 1 ∨ i = j - 1) → i ∉ ({0, (6 : ZMod 12)} : Finset _) → i ∈ s := by
    intro j hj i hi hni
    apply hpre
    simp only [stepMM, selfInverseSet, Finset.mem_sdiff, Finset.mem_union,
               Finset.mem_image, hpi5]
    refine ⟨?_, hni⟩
    rcases hi with rfl | rfl
    · exact Or.inl (Or.inr ⟨j, Finset.mem_union.mp hj, rfl⟩)  -- i = j+1: frontier.image(·+1)
    · exact Or.inr ⟨j, Finset.mem_union.mp hj, rfl⟩            -- i = j-1: frontier.image(·-1)
  have fp7 : (7 : ZMod 12) ∈ s ∪ ({7, (5:ZMod 12)} : Finset _) := by simp
  have fp5 : (5 : ZMod 12) ∈ s ∪ ({7, (5:ZMod 12)} : Finset _) := by simp
  have h1 : (8 : ZMod 12) ∈ s :=
    step 7 fp7 8 (Or.inl (by decide)) (by decide)
  have h2 : (9 : ZMod 12) ∈ s :=
    step 8 (Finset.mem_union_left _ h1) 9 (Or.inl (by decide)) (by decide)
  have h3 : (10 : ZMod 12) ∈ s :=
    step 9 (Finset.mem_union_left _ h2) 10 (Or.inl (by decide)) (by decide)
  have h4 : (11 : ZMod 12) ∈ s :=
    step 10 (Finset.mem_union_left _ h3) 11 (Or.inl (by decide)) (by decide)
  have h5 : (4 : ZMod 12) ∈ s :=
    step 5 fp5 4 (Or.inr (by decide)) (by decide)
  have h6 : (3 : ZMod 12) ∈ s :=
    step 4 (Finset.mem_union_left _ h5) 3 (Or.inr (by decide)) (by decide)
  have h7 : (2 : ZMod 12) ∈ s :=
    step 3 (Finset.mem_union_left _ h6) 2 (Or.inr (by decide)) (by decide)
  have h8 : (1 : ZMod 12) ∈ s :=
    step 2 (Finset.mem_union_left _ h7) 1 (Or.inr (by decide)) (by decide)
  have h9 : (7 : ZMod 12) ∈ s :=
    step 8 (Finset.mem_union_left _ h1) 7 (Or.inr (by decide)) (by decide)
  have h10 : (5 : ZMod 12) ∈ s :=
    step 4 (Finset.mem_union_left _ h5) 5 (Or.inl (by decide)) (by decide)
  intro i hi
  simp only [selfInverseSet, Finset.mem_sdiff, Finset.mem_univ, true_and,
             Finset.mem_insert, Finset.mem_singleton] at hi
  push Not at hi
  obtain ⟨hi0, hi6⟩ := hi
  fin_cases i
  · exact absurd rfl hi0
  · exact h8
  · exact h7
  · exact h6
  · exact h5
  · exact h10
  · exact absurd rfl hi6
  · exact h9
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The complement of the self-inverse set is contained in the lfp. -/
private theorem complement_subset_nonSIReachable [NeZero m]
    (p t : HarmonicInterval m)
    (hp : isPerfect p)
    (ht : IsTritone t) :
    Finset.univ \ selfInverseSet t ⊆ nonSIReachable p t := by
  intro i hi
  unfold nonSIReachable
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun s hs => prefixed_contains_complement p t hp ht s hs hi⟩

/-- The lfp equals the complement of the self-inverse set. -/
theorem nonSIReachable_eq_complement [NeZero m]
    (p t : HarmonicInterval m)
    (hp : isPerfect p)
    (ht : IsTritone t) :
    nonSIReachable p t = Finset.univ \ selfInverseSet t :=
  Finset.Subset.antisymm
    (nonSIReachable_subset_complement p t)
    (complement_subset_nonSIReachable p t hp ht)
