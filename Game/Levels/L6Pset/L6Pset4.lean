import Game.Levels.L6Pset.L6Pset3

World "L6Pset"
Level 4
Title "Problem 4"

Introduction "# Problem 4

You are given that a sequence `a : ℕ → ℝ` with the property that it takes arbitrarily large values exceeding 10 in absolute value.
Prove that cannot have a limit less than 5.
"

/-- Prove the statement. -/
Statement (a : ℕ → ℝ) (ha : ∀ N, ∃ n ≥ N, |a n| > 10)
  : ¬ ∃ L, |L| < 5 ∧ SeqLim a L := by
intro h
choose L hL using h
have f1 : |L| < 5 := by apply hL.1
have ha' : SeqLim a L := by apply hL.2
have f0 : (0 : ℝ) < 5 := by norm_num
specialize ha' 5 f0
choose N hN using ha'
specialize ha N
choose n hn using ha
specialize hN n hn.1
have ha : |a n| > 10 := by apply hn.2
have f2 : |a n| = |(a n - L) + L| := by ring_nf
have f3 : |(a n - L) + L| ≤ |(a n - L)| + |L| := by apply abs_add_le
linarith [f1, ha, f2, f3, hN]

Conclusion "Done."
