import Game.Levels.L11Levels.L02_IsCauchyOfSum

open Finset

World "Lecture11"
Level 3
Title "Level 3 : Cauchy Implies Bounded"


Introduction "
# Level 3: Cauchy Implies Bounded

We've seen that convergent sequences are bounded. Now we'll prove that **Cauchy sequences are also bounded**—without ever mentioning a limit!

This is a beautiful result because it shows that the Cauchy property alone (terms getting close to *each other*) is strong enough to guarantee boundedness, even though we don't know if the sequence converges or *where* it might converge to.

## The Setup

Given:
- `a : ℕ → ℝ` is Cauchy

Prove: `a` is bounded (i.e., `∃ M, ∀ n, |a n| ≤ M`)

## The Key Insight

If a sequence is Cauchy, then eventually all terms are clustered together. Specifically, if we use `ε = 1` in the Cauchy definition, then for all `m ≥ N`, we have:

$|a_m - a_N| < 1$

This means all terms after `N` stay within distance 1 of $a_N$, so they're all bounded by $|a_N| + 1$.

But what about the finitely many terms *before* `N`? We just take their maximum (or what's technically easier: their sum)!

## Strategy

1. **Apply Cauchy with `ε = 1`**: Get an `N` such that all terms after `N` are within distance 1 of $a_N$
2. **Bound the tail**: Show that for `m ≥ N`, we have $|a_m| ≤ |a_N| + 1$ using the triangle inequality
3. **Bound the initial segment**: The terms $a_0, a_1, ..., a_{N-1}$ are finitely many, so their sum of absolute values bounds each one
4. **Combine**: Take $M = |a_N| + 1 + \\sum_{k < N} |a_k|$ as your overall bound
5. **Case split**: Use `by_cases` to handle `m < N` versus `m ≥ N` separately

Good luck!
"

/--
If a sequence `a` is Cauchy, then it is eventually bounded.
-/
TheoremDoc IsBdd_of_Cauchy as "IsBdd_of_Cauchy" in "aₙ"

/-- Prove this
-/
Statement IsBdd_of_Cauchy {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : IsCauchy a)
    : SeqBdd a := by
choose N hN using ha 1 (by bound)
use |a N| + 1 + ∑ k ∈ range N, |a k|
have aNnonneg : 0 ≤ |a N| := by bound
have sumNonneg : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg (by bound)
have f1 : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by apply TermLeSum a N
split_ands
linarith [aNnonneg, sumNonneg]
intro m
specialize hN N (by bound) m
by_cases hm : m < N
specialize f1 m hm
linarith [f1, aNnonneg]
specialize hN (by bound)
have f2 : |a m| = |(a m - a N) + a N| := by ring_nf
have f3 : |(a m - a N) + a N| ≤ |a m - a N| + |a N| := by apply abs_add_le
linarith [f2, f3, hN, sumNonneg]

Conclusion "
# Outstanding! You've proven that Cauchy sequences are bounded!

This was a challenging proof involving case analysis, finite sums, and careful bookkeeping—but you did it! You've shown that the self-referential Cauchy property is powerful enough to guarantee boundedness.

## What you've accomplished

You've now proven that Cauchy sequences share two key properties with convergent sequences:
1. **They're bounded** (this level)
2. **They're closed under addition** (previous level)

And you did all this **without ever mentioning where they converge**!

## Why this matters

This theorem is absolutely crucial for the theory of real numbers:

- In the rationals `ℚ`, there are Cauchy sequences that don't converge (like the decimal approximations to `√2`)
- But they're still *bounded*, which means they're not escaping to infinity
- This boundedness will be essential when we prove the **Bolzano-Weierstrauss theorem**: every bounded sequence has a convergent subsequence
- Eventually, we'll use these facts to show that in `ℝ` (but not in `ℚ`), every Cauchy sequence *does* converge—this is called **completeness**

## The technique you mastered

The key technique here was splitting into cases:
- **Finitely many terms** (`m < N`): Handled by taking a maximum
- **Infinitely many terms** (`m ≥ N`): Handled by the Cauchy property

This \"finite + infinite\" splitting technique appears throughout analysis!

## Looking ahead

You've now built up the basic theory of Cauchy sequences. Next, we'll start connecting this back to the real numbers and exploring what it means for ℝ to be **complete**—the property that makes real analysis work!

Congratulations on completing this lecture!
"
