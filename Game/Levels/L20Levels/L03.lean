import Game.Levels.L20Levels.L02

World "Lecture20"
Level 3
Title "Sum of Continuous Functions"
Introduction "
# Level 3: Sum of Continuous Functions

One of the most powerful aspects of continuity is that it behaves well with respect to algebraic operations. Let's prove our first **continuity theorem**: the sum of continuous functions is continuous!

## The Theorem

**Theorem:** If `f` and `g` are both continuous at `c`, then `f + g` is continuous at `c`.

This seems intuitive: if `f(x)` stays close to `f(c)` and `g(x)` stays close to `g(c)` when `x` is near `c`, then their sum should stay close to `f(c) + g(c)`.

## The Strategy: The `ε/2` Trick

Given `ε > 0`, we want to make `|(f + g)(x) - (f + g)(c)| < ε`.

Notice that:

`|(f + g)(x) - (f + g)(c)| = |f(x) + g(x) - f(c) - g(c)|`

`                           = |[f(x) - f(c)] + [g(x) - g(c)]|`

`                           ≤ |f(x) - f(c)| + |g(x) - g(c)|`

So if we can make each term less than `ε/2`, their sum will be less than `ε`!

Since `f` is continuous at `c`, there exists `δ₁ > 0` such that `|x - c| < δ₁` implies `|f(x) - f(c)| < ε/2`.

Since `g` is continuous at `c`, there exists `δ₂ > 0` such that `|x - c| < δ₂` implies `|g(x) - g(c)| < ε/2`.

Taking `δ = min δ₁ δ₂` ensures both conditions hold simultaneously!

## Your Challenge

Prove that if `f` and `g` are continuous at `c`, then their sum is continuous at `c`:

`FunContAt f c → FunContAt g c → FunContAt (fun x ↦ f x + g x) c`

**Hint:** After introducing `ε` and `hε`, use the hypotheses `hf` and `hg` with `ε/2` to choose `δ₁` and `δ₂`. Then `use min δ₁ δ₂`. You'll need to show this is positive and that it works. The triangle inequality and `bound` will be your friends!

"

/-- The sum of continuous functions is continuous.
-/
TheoremDoc FunContAtAdd as "FunContAtAdd" in "f(x)"

Statement FunContAtAdd {f g : ℝ → ℝ} {c : ℝ}
    (hf : FunContAt f c) (hg : FunContAt g c) :
    FunContAt (fun x ↦ f x + g x) c := by
intro ε hε
choose δ₁ hδ₁ hf using hf (ε / 2) (by bound)
choose δ₂ hδ₂ hg using hg (ε / 2) (by bound)
use min δ₁ δ₂
split_ands
bound
intro x hx
have hd1 : min δ₁ δ₂ ≤ δ₁ := by bound
have hx1 : |x - c| < δ₁ := by bound
have hd2 : min δ₁ δ₂ ≤ δ₂ := by bound
have hx2 : |x - c| < δ₂ := by bound
specialize hf x hx1
specialize hg x hx2
change |f x + g x - (f c + g c)| < ε
rewrite [show f x + g x - (f c + g c) = (f x - f c) + (g x - g c) by ring_nf]
have f1 : |(f x - f c) + (g x - g c)| ≤ |(f x - f c)| + |(g x - g c)| := by apply abs_add_le
linarith [f1, hf, hg]

Conclusion "
## What We've Learned

This theorem marks a major milestone: we've proven that continuity is **preserved under addition**!

### The `ε/2` Trick

This is one of the most elegant techniques in analysis:

- We need to make `|(f + g)(x) - (f + g)(c)| < ε`
- By the triangle inequality: `|(f + g)(x) - (f + g)(c)| ≤ |f(x) - f(c)| + |g(x) - g(c)|`
- If each piece is less than `ε/2`, the sum is less than `ε`!

The beauty: we **split the budget**. Each function gets half the tolerance.

### The `min(δ₁, δ₂)` Strategy

Why take the minimum of two deltas?

- `δ₁` works for `f`: guarantees `|f(x) - f(c)| < ε/2` when `|x - c| < δ₁`
- `δ₂` works for `g`: guarantees `|g(x) - g(c)| < ε/2` when `|x - c| < δ₂`
- `min(δ₁, δ₂)` works for **both**: it's the \"most restrictive\" requirement

**Key insight:** When combining guarantees, take the stronger (smaller) constraint!

### Building Up From Simple Pieces

This is the beginning of a powerful story. We can now prove:
- Sums of continuous functions are continuous ✓
- Products of continuous functions are continuous (similar proof!)
- Compositions of continuous functions are continuous (chain rule!)
- Therefore: all polynomials, rational functions, trig functions, etc. are continuous!

We've just laid the foundation for understanding continuity of essentially every function in calculus.
"
