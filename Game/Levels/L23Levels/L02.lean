import Game.Levels.L23Levels.L01

open Finset Set

World "Lecture23"
Level 2
Title "Integration Converges!"
Introduction "
# Level 2: Integration Converges!

**The Big Question**: We know that continuous functions *should* be integrable, but proving this rigorously is surprisingly subtle. The key insight is that we need *uniform* continuity, not just pointwise continuity.

**What We're Proving**: If `f` is uniformly continuous on `[a,b]`, then the sequence of Riemann sums `{RiemannSum f a b n}` converges as `n → ∞`. This means the integral exists!

**The Strategy**: We'll prove convergence by showing the Riemann sum sequence is Cauchy. For any `ε > 0`:
1. Use uniform continuity to get a `δ` that works everywhere on `[a,b]`
2. Choose `N` large enough so that partitions with `≥ N` subintervals are all fine enough
3. For any `m, n ≥ N`, compare `RiemannSum f a b m` and `RiemannSum f a b n` by using their common multiple `m * n` as an intermediate step
4. Apply your Level 1 theorem twice to bound the total error

**New Definition - Uniform Continuity**:

`def UnifContOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, |x - y| < δ → |f x - f y| < ε`

**Key Insight**: Notice the quantifier order! Unlike pointwise continuity where `δ` can depend on the specific point `x`, uniform continuity requires a single `δ` that works for *all* pairs of points simultaneously. This seemingly small change makes all the difference for integration theory.
"

def UnifContOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, |y - x| < δ → |f y - f x| < ε

/-- `(f : ℝ → ℝ) (S : Set ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, |y - x| < δ → |f y - f x| < ε`

For any `ε > 0`, there exists a `δ > 0` such that for all `x, y ∈ S`, if `|x - y| < δ`, then `|f x - f y| < ε`.
-/
DefinitionDoc UnifContOn as "UnifContOn"

NewDefinition UnifContOn

/--
If a function `f` is uniformly continuous on `[a,b]`, then the Riemann sums of `f` converge to a limit as `N → ∞`.
-/
TheoremDoc HasIntegral_of_UnifContOn as "HasIntegral_of_UnifContOn" in "∫f"

Statement HasIntegral_of_UnifContOn (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : UnifContOn f (Icc a b)) :
    IntegrableOn f a b := by
apply SeqConv_of_IsCauchy
intro ε hε
choose δ hδ₁ hδ₂ using hf (ε / (2 * (b - a))) (by bound)
choose N hN using ArchProp (show 0 < δ / (2 * (b - a)) by bound)
use N
intro n hn m hnm
have pos1 : 0 < 1 / (δ / (2 * (b - a))) := by bound
have NposR : (0 : ℝ) < N := by linarith [hN, pos1]
have Npos : 0 < N := by exact_mod_cast NposR
have npos : 0 < n := by bound
have mpos : 0 < m := by bound
change |RiemannSum f a b m - RiemannSum f a b n| < ε
have hn_small : 2 * (b - a) / n < δ := by sorry
have hm_small : 2 * (b - a) / m < δ := by sorry
have f1 : |RiemannSum f a b m - RiemannSum f a b n| ≤
    |RiemannSum f a b m - RiemannSum f a b (m * n)| + |RiemannSum f a b (n * m) - RiemannSum f a b n| := by
  rewrite [show RiemannSum f a b m - RiemannSum f a b n =
      (RiemannSum f a b m - RiemannSum f a b (m * n)) +
      (RiemannSum f a b (n * m) - RiemannSum f a b n) by ring_nf]
  apply abs_add_le
have hfn := RiemannSumRefinement f hab (show n ≠ 0 by bound) (show m ≠ 0 by bound) (show 0 < ε / (2 * (b - a)) by bound)
    (show 0 < δ by bound) hδ₂ hn_small
have hfm := RiemannSumRefinement f hab (show m ≠ 0 by bound) (show n ≠ 0 by bound) (show 0 < ε / (2 * (b - a)) by bound)
    (show 0 < δ by bound) hδ₂ hm_small
rewrite [show |RiemannSum f a b (m * n) - RiemannSum f a b m| =
    |RiemannSum f a b m - RiemannSum f a b (m * n)| by apply abs_sub_comm] at hfm
have bapos : 0 < b - a := by linarith [hab]
rewrite [show (b - a) * (ε / (2 * (b - a))) = ε / 2 by field_simp] at hfn hfm
linarith [f1, hfn, hfm]

Conclusion "
# A Major Milestone!

Congratulations! You've just proved one of the fundamental theorems of real analysis: **uniformly continuous functions are integrable**.

**What Makes This Proof Beautiful**:
- **The Cauchy Strategy**: Instead of guessing what the integral should be, we proved convergence by showing the Riemann sum sequence is Cauchy. This is a powerful technique that works even when you don't know the limit in advance.
- **The Common Multiple Trick**: The key insight was using `m * n` as an intermediate step to compare Riemann sums with `m` and `n` partitions. This transformed a seemingly difficult comparison into two applications of your Level 1 theorem.
- **The ε/2 Split**: Dividing the tolerance in half and applying the triangle inequality is a classic move in analysis that you'll see again and again.

**The Historical Context**: This result was crucial for putting Riemann's theory of integration on solid foundations. Riemann himself understood this intuitively, but the rigorous proof required careful attention to uniform continuity - a concept that wasn't fully formalized until later.

**What's Still Missing**: We've shown that *uniformly* continuous functions are integrable, but when is a continuous function *uniformly* continuous? The answer involves one of the most important concepts in mathematics: **compactness**.

**Looking Ahead**: In Level 3, we'll prove that continuous functions on compact sets (like closed intervals `[a,b]`) are automatically uniformly continuous. Combined with today's result, this will show that *every* continuous function on `[a,b]` is integrable - the foundation of calculus!

This is why topology matters for analysis: the 'right' topological framework (compactness) makes analytical problems (integration) much more tractable.
"
