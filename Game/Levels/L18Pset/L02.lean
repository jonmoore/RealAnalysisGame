import Game.Levels.L18Pset.L01
open Finset

World "L18Pset"
Level 2
Title "Series_abs_add"
Introduction "
# Level 2: `Series_abs_add`

Prove `Series_abs_add`:

"

DisabledTheorem Series_abs_add

/-- Prove `Series_abs_add`
-/
Statement (a : ℕ → ℝ) {n m : ℕ} (hmn : n ≤ m) :
  |∑ k ∈ Ico n m, a k| ≤ ∑ k ∈ Ico n m, |a k| := by
induction' m with m hm
bound
by_cases hm' : n ≤ m
specialize hm hm'
rewrite [sum_Ico_succ hm']
rewrite [sum_Ico_succ hm']
have f : |∑ k ∈ Ico n m, a k + a m|  ≤ |∑ k ∈ Ico n m, a k| + |a m| := by apply abs_add_le
linarith [f, hm]
have hn : n = m+1 := by bound
rewrite [hn]
bound

Conclusion "
"
