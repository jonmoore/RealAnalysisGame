import Game.Levels.L7Pset.L7Pset2

World "L7Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3

Prove `abs_Lipschitz`, obviously without referring to that theorem!
(Hint: you'll want to break things into cases according to whether `0 ≤ x` or not,
then systematically use `abs_of_nonneg` and `abs_neg`...)

"

/-- Prove the statement. -/
Statement (x y : ℝ) :
  |(|x| - |y|)| ≤ |x - y| := by
by_cases hx : 0 ≤ x
have absx : |x| = x := by apply abs_of_nonneg hx
rewrite [absx]
by_cases hy : 0 ≤ y
have absy : |y| = y := by apply abs_of_nonneg hy
rewrite [absy]
bound
have hy : 0 ≤ -y := by bound
have absy : |-y| = |y| := by apply abs_neg
have absy' : |-y| = -y := by apply abs_of_nonneg hy
have xsubneg : |x - -y| = |x + y| := by ring_nf
rewrite [← absy, absy', xsubneg]
have f1 : |x + y| ≤ |x| + |y| := by apply abs_add_le
rewrite [absx, ← absy, absy'] at f1
have f2 : x + -y = x - y := by ring_nf
rewrite [f2] at f1
have xy : 0 ≤ x - y := by bound
have absxy : |x - y| = x - y := by apply abs_of_nonneg xy
rewrite [← absxy] at f1
apply f1
have hx' : 0 ≤ -x := by bound
have absxneg : |-x| = |x| := by apply abs_neg
have absxeq : |-x| = -x := by apply abs_of_nonneg hx'
rewrite [← absxneg, absxeq]
by_cases hy : 0 ≤ y
have absy : |y| = y := by apply abs_of_nonneg hy
rewrite [absy]
have f1 : |-x - y| = |-(x + y)| := by ring_nf
have f2 : |-(x + y)| = |(x + y)| := by apply abs_neg
have xy : 0 ≤ -(x - y) := by bound
have absxy : |-(x - y)| = -(x - y) := by apply abs_of_nonneg xy
have absxy' : |-(x - y)| = |x - y| := by apply abs_neg
rewrite [f1, f2, ← absxy', absxy]
have f3 : |x + y| ≤ |x| + |y| := by apply abs_add_le
rewrite [absy, ← absxneg, absxeq] at f3
have f4 : -(x - y) = -x + y := by ring_nf
rewrite [f4]
apply f3
have hy' : 0 ≤ -y := by bound
have absyneg : |-y| = |y| := by apply abs_neg
have absyeq : |-y| = -y := by apply abs_of_nonneg hy'
rewrite [← absyneg, absyeq]
have f1 : |-x - -y| = |-(x - y)| := by ring_nf
have f2 : |-(x - y)| = |(x - y)| := by apply abs_neg
rewrite [f1, f2]
linarith

Conclusion "Done."
