import Game.Levels.L19Levels.L02

open Finset Function

World "Lecture19"
Level 3
Title "**Big Boss**: Rearrangement Theorem"
Introduction "
# Level 3 **Big Boss**: Rearrangement Theorem

This is it—the moment we've been building toward! We're about to prove one of the most profound and beautiful theorems in all of real analysis.

## The Fundamental Theorem

**Theorem** (`RearrangementThm`): If a series `∑ a_n` converges absolutely, then for any rearrangement `σ : ℕ → ℕ`, the rearranged series `∑ a_(σ(n))` converges to the same limit.

In symbols: If `AbsSeriesConv a`, then there exists `L` such that, for all `Rearrangement`s, `σ`, (including the identity) and `SeriesLim (a ∘ σ) L`.

## The Deep Meaning

This theorem reveals a profound truth about infinite summation:

**Infinite summation is commutative if and only if the series is absolutely convergent.**

For finite sums, we can add terms in any order—the sum doesn't change. This theorem says that absolute convergence is *exactly* what's needed to extend this property to infinite sums!

## Why This is a Big Deal

Remember from Lecture 18 how we showed that rearranging the infinite matrix changed its sum from 0 to -2? That's because those series were *not* absolutely convergent.

For absolutely convergent series, we have complete freedom: reorder the terms however you like, and the sum stays the same. It's as if absolute convergence gives infinite series the \"finite property\" of commutativity.

## New Theorems

- `Series_image`: Relates the rearranged series to a sum over the image of `σ`
- `sum_sdiff`: Handles sums over set differences: `∑ (S₂ \\ S₁) + ∑ S₁ = ∑ S₂`
- `abs_sum_le_sum_abs`: Triangle inequality for finite sums

## The Proof Strategy

We'll combine everything from Levels 1 and 2:
1. The strong Cauchy property tells us that scattered large-index terms contribute negligibly
2. The eventually covers property tells us that rearrangements eventually include all early terms
3. We'll show the rearranged series stays close to the original by bounding the \"uncovered\" terms

This is a technical proof, but the idea is beautiful: absolute convergence gives us enough \"slack\" that scrambling the order doesn't matter.

Your task: Prove the Rearrangement Theorem—and unlock one of the deepest truths about infinite series!
"

theorem Series_image (a : ℕ → ℝ) (σ : ℕ → ℕ) (hσ : Injective σ) (n : ℕ) : Series (a ∘ σ) n = ∑ k ∈ image σ (range n), a k := by
rewrite [sum_image]
rfl
apply hσ.injOn

/--
For a sequence `a : ℕ → ℝ` and an injective `σ : ℕ → ℕ`, we have that:
`Series (a ∘ σ) n = ∑ k ∈ image σ (range n), a k` holds for any `n`.
-/
TheoremDoc Series_image as "Series_image" in "∑aₙ"

/--
If `s₁ ⊆ s₂`, then `∑ x ∈ s₂ \ s₁, f x + ∑ x ∈ s₁, f x = ∑ x ∈ s₂, f x`.
-/
TheoremDoc Finset.sum_sdiff as "sum_sdiff" in "∑aₙ"

/--
`|∑ x ∈ s, f x ≤ ∑ x ∈ s, |f x|`. (More general version of `Series_abs_add`)
-/
TheoremDoc Finset.abs_sum_le_sum_abs as "abs_sum_le_sum_abs" in "∑aₙ"


NewTheorem Finset.sum_sdiff Finset.abs_sum_le_sum_abs Series_image

/--
  If `Series a` converges absolutely, then any rearrangement of `a` also converges, and to the same sum.
-/
TheoremDoc RearrangementThm as "RearrangementThm" in "∑aₙ"

Statement RearrangementThm {a : ℕ → ℝ} (ha : AbsSeriesConv a) :
  ∃ L, ∀ (σ : ℕ → ℕ) (_ : Rearrangement σ), SeriesLim (a ∘ σ) L := by
choose L hL using Conv_of_AbsSeriesConv ha
use L
intro σ hσ
intro ε hε
apply IsCauchy_of_SeqConv at ha
choose N1 hN1 using ha (ε / 2) (by bound)
choose N2 hN2 using hL (ε / 2) (by bound)
choose N3 hN3 using EventuallyCovers_of_Rearrangement hσ (N1 + N2)
use N1 + N2 + N3 + 1
intro n hn
specialize hN2 (N1 + N2) (by bound)
specialize hN1 (N1 + N2) (by bound)
rewrite [show Series (a ∘ σ) n - L =
  (Series (a ∘ σ) n - Series a (N1 + N2)) + (Series a (N1 + N2) - L) by ring_nf]
have f1 : |Series (a ∘ σ) n - Series a (N1 + N2) + (Series a (N1 + N2) - L)|
        ≤ |Series (a ∘ σ) n - Series a (N1 + N2)| + |(Series a (N1 + N2) - L)| := by apply abs_add_le
have f2 : |Series (a ∘ σ) n - Series a (N1 + N2)| =
    |∑ k ∈ image σ (range n) \ range (N1 + N2), a k| := by
  have f : Series (a ∘ σ) n = ∑ k ∈ image σ (range n), a k := Series_image a σ hσ.1 n
  rewrite [f]
  change |(∑ k ∈ image σ (range n), a k) - (∑ k ∈ range (N1 + N2), a k)| = |(∑ k ∈ image σ (range n) \ range (N1 + N2), a k)|
  rewrite [← Finset.sum_sdiff (hN3 n (by bound))]
  ring_nf
have f3 : |∑ k ∈ image σ (range n) \ range (N1 + N2), a k|
    ≤ ∑ k ∈ image σ (range n) \ range (N1 + N2), |a k| := by
  apply abs_sum_le_sum_abs
let M := N1 + N2 + 1 + ∑ k ∈ range n, σ k
have Mis : M = N1 + N2 + 1 + ∑ k ∈ range n, σ k := by rfl
have Mbnd : ∀ k ∈ range n, σ k < M := by
  intro k hk
  rewrite [Mis]
  have f : σ k ≤ ∑ j ∈ range n, σ j := by apply sum_le_mem_of_nonneg hk; intro i hi; bound
  linarith [f]
have f4 : ∑ k ∈ image σ (range n) \ range (N1 + N2), |a k| ≤ ∑ k ∈ Ico (N1 + N2) M, |a k| := by
  apply sum_le_sum_of_nonneg
  intro i hi
  rewrite [mem_Ico]
  rewrite [mem_sdiff] at hi
  rewrite [mem_range] at hi
  rewrite [mem_image] at hi
  have hi2 : N1 + N2 ≤ i := by bound
  split_ands
  apply hi2
  have hi1 : ∃ a ∈ range n, σ a = i := by apply hi.1
  choose a ha using hi1
  rewrite [← ha.2]
  apply Mbnd a ha.1
  intro i hi;
  bound
have sNonneg : 0 ≤ ∑ k ∈ range n, σ k := by
  apply sum_nonneg
  intro i hi
  bound
have Mbnd : N1 + N2 ≤ M := by rewrite [Mis]; linarith [sNonneg]
specialize hN1 M Mbnd
rewrite [DiffOfSeries _ Mbnd] at hN1
have f5 : ∑ k ∈ Ico (N1 + N2) M, |a k| ≤ |∑ k ∈ Ico (N1 + N2) M, (|a k|)| := by bound
linarith [f1, hN2, f2, f3, f4, f5, hN1, hN3]


Conclusion "
# Congratulations!

You've just proven the **Rearrangement Theorem**—one of the crown jewels of real analysis!

## What We've Accomplished

This theorem completely characterizes when infinite summation is commutative. For absolutely convergent series, we can reorder terms with complete freedom—the sum is invariant. This is a profound result that took mathematicians centuries to fully understand and prove rigorously.

## The Proof: A Symphony of Ideas

The proof beautifully orchestrated all the machinery we've built:
- **Strong Cauchy property (Level 1)**: Any scattered collection of large-index terms has negligible sum
- **Eventually covers property (Level 2)**: Rearrangements eventually capture all early terms
- **Clever decomposition**: We split the difference between rearranged and original sums into \"covered\" and \"uncovered\" parts

The covered part is close to the limit by convergence of the original series. The uncovered part consists only of large-index terms, which by strong Cauchy have negligible sum. Together: the rearranged series converges to the same limit!

## Historical Significance

This theorem was understood by Cauchy and Abel in the 1820s, during the period when mathematicians were establishing rigorous foundations for calculus. It marked a crucial distinction between finite and infinite operations.

The realization that *order matters* for infinite sums was shocking at first. But this theorem shows the situation is elegant: absolute convergence is exactly the dividing line between order-independent (\"finite-like\") and order-dependent behavior.

## A Complete Dichotomy

We now have half of a stunning dichotomy:
- **This level**: Absolute convergence → rearrangement invariance
- **Next level**: Conditional convergence → complete chaos (any sum is possible!)

Together, these theorems show that there's no middle ground. A series either has an order-independent sum, or its sum can be manipulated to be anything we want by choosing the right rearrangement.

## The Power of Absolute Convergence

This theorem explains why absolute convergence is so important throughout analysis:
- It's the condition needed for term-by-term integration and differentiation
- It's required for multiplying infinite series (Cauchy product)
- It guarantees that double sums can be computed in either order (Fubini's theorem)

Absolute convergence is the \"gold standard\" that makes infinite series behave like finite sums.

## What's Next?

In Level 4, we'll see the shocking flip side: Riemann's Rearrangement Theorem. For conditionally convergent series, rearrangements can make the sum equal to *any* real number. The contrast couldn't be more dramatic!
"
