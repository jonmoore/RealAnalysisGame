import Game.Levels.L7Lecture
import Game.Levels.L6PsetIntro

World "L7Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1

Suppose that a sequence `a : ℕ → ℝ` converges to `L ≠ 0`. Show that eventually `|a n|` is at most
`2|L|`.

"

/-- If `a : ℕ → ℝ` converges to `L` and `L ≠ 0`, then `|a n|` is eventually bounded by `2 * |L|`. -/
TheoremDoc EventuallyBdd_of_SeqConv as "EventuallyBdd_of_SeqConv" in "aₙ"

/-- Prove the statement. -/
Statement EventuallyBdd_of_SeqConv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (hL : L ≠ 0) :
  ∃ N, ∀ n ≥ N, |a n| ≤ 2 * |L| := by
have absL : 0 < |L| := by apply abs_pos_of_nonzero hL
specialize ha |L| absL
choose N hN using ha
use N
intro n hn
specialize hN n hn
have f1 : |a n| = |a n - L + L| := by ring_nf
have f2 : |a n - L + L| ≤ |a n - L| + |L| := by apply abs_add_le
linarith [f1, f2, hN]

Conclusion "Done."
