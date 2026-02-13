import Game.Levels.L10PsetIntro

World "Lecture11"
Level 1
Title "Big Boss : Limits are Cauchy"


Introduction "
# Level 1: Big Boss - Limits are Cauchy

Now that we understand what a Cauchy sequence is, let's prove our first major theorem: **every convergent sequence is Cauchy**.

This might seem obvious at first—if a sequence converges to some limit `L`, then the terms should eventually be close to each other. But making this intuition rigorous requires careful epsilon management!

## The Key Insight

If `aₙ → L`, then for large `n` and `m`, both `aₙ` and `aₘ` are close to `L`. By the triangle inequality, this means they must be close to *each other*:

`|aₙ - aₘ| = |(aₙ - L) + (L - aₘ)| ≤ |aₙ - L| + |L - aₘ|`

## Strategy

1. **Extract the limit**: Since the sequence converges, use `choose` to get the limit `L`
2. **Clever epsilon choice**: Apply the definition of `aₙ → L` with `ε/2` (not `ε`!)
3. **Rewrite the goal**: Express `|aₙ - aₘ|` in terms of differences from `L`
4. **Apply triangle inequality**: Split the absolute value of a sum
5. **Use symmetry**: Apply `abs_sub_comm` to get `|L - aₘ| = |aₘ - L|`
6. **Finish with arithmetic**: Both pieces are less than `ε/2`, so the sum is less than `ε`

## New Definition

**`IsCauchy a`**: A sequence `a : ℕ → ℝ` is Cauchy if
`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε`

## New Theorem

**`abs_sub_comm`**: `|x - y| = |y - x|`
(Subtraction is commutative inside absolute values)

This is your first Big Boss level working with the Cauchy definition. Take your time, and remember: when in doubt, divide epsilon by 2!
"

/--
Usage: `have factName : |x - y| = |y - x| := by apply abs_sub_comm`
-/
TheoremDoc abs_sub_comm as "abs_sub_comm" in "|x|"

NewTheorem abs_sub_comm

/-- `(a : ℕ → X) : Prop := ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε`

For a sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) is said to satisfy `IsCauchy` (that is, the sequence \"is Cauchy\") if: for every `ε > 0`, there exists `N : ℕ` such that for all `n ≥ N` and `m ≥ n`, we have `|a m - a n| < ε`. -/
DefinitionDoc IsCauchy as "IsCauchy"

NewDefinition IsCauchy

def IsCauchy {X : Type*} [NormedAddGroup X] [Lattice X] (a : ℕ → X) : Prop :=
  ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε

/--
If a sequence `a : ℕ → ℝ` converges, then it is Cauchy.
-/
TheoremDoc IsCauchy_of_SeqConv as "IsCauchy_of_SeqConv" in "aₙ"

/-- Prove this
-/
Statement IsCauchy_of_SeqConv {a : ℕ → ℝ} (ha : SeqConv a)
    : IsCauchy a := by
choose L hL using ha
intro ε hε
choose N hN using hL (ε / 2) (by bound)
use N
intro n hn m hm
have hn' : |a n - L| < ε / 2 := by apply hN n hn
have hm' : |a m - L| < ε / 2 := by apply hN m (by bound)
rewrite [(by ring_nf : |a m - a n| = |(a m - L) + (L - a n)|)]
have f1 : |(a m - L) + (L - a n)| ≤ |a m - L| + |L - a n| := by apply abs_add_le
have f2 : |L - a n| = |a n - L| := by apply abs_sub_comm
linarith [f1, f2, hn', hm']

Conclusion "
# Congratulations! You've proven that convergence implies Cauchy!

This is one of the most fundamental results in analysis. You've just shown that the \"self-referential\" Cauchy property is a *necessary condition* for convergence.

## What you've learned

- How to work with the Cauchy definition using multiple indices `m` and `n`
- The power of the `ε/2` trick to make inequalities work out
- How to use `abs_sub_comm` to flip differences inside absolute values
- How to connect a sequence to itself rather than to an external limit

## The Big Question

You've proven: **convergence ⟹ Cauchy**

But what about the converse? Is every Cauchy sequence convergent?

- **For rational sequences**: NO! The sequence `1, 1.4, 1.41, 1.414, ...` is Cauchy in ℚ but doesn't converge to a rational number.
- **For real sequences**: This is the *Cauchy Completeness Theorem*, and it's **YES**! But we'll need to carefully construct the real numbers first to prove it.

This is why Cauchy sequences are so important—they give us a way to *define* the real numbers as the completion of the rationals!

Onward to the next level!
"
