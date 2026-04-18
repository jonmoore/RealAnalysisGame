import Game.Levels.L4Lecture
import Game.Levels.L3PsetIntro

World "L4Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1

Let `a (n)` be a sequence that alternates between
`3 - 1 / n` and `1 + 1 / n`. Prove that this sequence diverges.

**Hint:** You may wish to argue using `N` that's slightly
larger than the smallest possible value.

**Hint 2:** If your desired `have` is a consequence of two facts put together, you can separate them by a semicolon. For example, if you know that `h : X = Y + Z`,
and you want to add a hypothesis `h' : |X - Y| = |Z|`, which is a combination of rewriting by `h` and a ring operation, then you can say:

`have h' : |X - Y| = |Z| := by rewrite [h]; ring_nf`.

This might come in handy!...
"

/-- Prove that this sequence diverges. -/
Statement (a : ℕ → ℝ) (ha2n : ∀ n, a (2 * n) = 3 - 1 / n) (ha2np1 : ∀ n, a (2 * n + 1) = 1 + 1 / n)
  : ¬ SeqConv a := by
  intro h
  choose L hL using h
  have f : (0 : ℝ) < 1 / 2 := by norm_num
  specialize hL (1 / 2) f
  choose N hN using hL

  have f1 : a (2 * (N + 5)) = 3 - 1 / (N + 5) := by exact_mod_cast ha2n (N + 5)
  have f2 : |3 - a (2 * (N + 5))| = |(1 : ℝ) / (N + 5)| := by
    rewrite [f1]; ring_nf
  have f3 : (0 : ℝ) ≤ 1 / (N + 5) := by bound
  have f4 : (1 : ℝ) / (N + 5) ≤ 1 / 4 := by bound
  have f5 : |(1 : ℝ) / (N + 5)| = 1 / (N + 5) := by apply abs_of_nonneg f3
  rewrite [f5] at f2
  have f6 : N ≤ 2 * (N + 5) := by bound
  have f7 : |a (2 * (N + 5)) - L| < 1 / 2 := by apply hN (2 * (N + 5)) f6

  have f1' : a (2 * (N + 5) + 1) = 1 + 1 / (N + 5) := by exact_mod_cast ha2np1 (N + 5)
  have f2' : |1 - a (2 * (N + 5) + 1)| = |-((1 : ℝ) / (N + 5))| := by
    rewrite [f1']; ring_nf
  have f5' : |-((1 : ℝ) / (N + 5))| = |(1 : ℝ) / (N + 5)| := by apply abs_neg
  rewrite [f5'] at f2'
  rewrite [f5] at f2'
  have f6' : N ≤ 2 * (N + 5) + 1 := by bound
  have f7' : |a (2 * (N + 5) + 1) - L| < 1 / 2 := by apply hN (2 * (N + 5) + 1) f6'

  have f8 : (2 : ℝ) = |2| := (abs_of_pos two_pos).symm
  have f9 : |(2 : ℝ)| = |(3 - L) + (L - 1)| := by congr 1; ring
  have f10 : |(3 - L) + (L - 1)| ≤ |(3 - L)| + |(L - 1)| := by apply abs_add_le
  have f11 : |(3 - L)| = |(3 - a (2 * (N + 5))) + (a (2 * (N + 5)) - L)| := by congr 1; ring
  have f12 : |(3 - a (2 * (N + 5))) + (a (2 * (N + 5)) - L)| ≤
    |(3 - a (2 * (N + 5)))| + |(a (2 * (N + 5)) - L)| := by apply abs_add_le

  have f13 : |(L - 1)| = |-(1 - L)| := by congr 1; ring
  have f14 : |-(1 - L)| = |(1 - L)| := by apply abs_neg
  have f15 : |(1 - L)| = |(1 - a (2 * (N + 5) + 1)) + (a (2 * (N + 5) + 1) - L)| := by congr 1; ring
  have f16 : |(1 - a (2 * (N + 5) + 1)) + (a (2 * (N + 5) + 1) - L)| ≤ |(1 - a (2 * (N + 5) + 1))| + |(a (2 * (N + 5) + 1) - L)| := by apply abs_add_le

  have f17 : (2 : ℝ) ≤ 1 / 4 + 1 / 2 + 1 / 4 + 1 / 2 := by linarith [f8, f9, f10, f11, f12, f13, f14, f15, f16, f7, f7', f2, f2', f4]
  norm_num at f17

Conclusion "Done."
