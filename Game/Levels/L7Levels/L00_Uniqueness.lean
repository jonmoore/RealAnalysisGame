import Game.Levels.L6Lecture

World "Lecture7"
Level 1
Title "Uniqueness of Limits"

Introduction "
# Level 1: Uniqueness of Limits

One of the fundamental properties of convergent sequences is that they converge to a
**unique** limit. This might seem obvious at first glance—after all, how could a sequence
be getting arbitrarily close to two different numbers? But as with many intuitive facts
in analysis, the rigorous proof requires careful reasoning with our epsilon-N definitions.

The key to proving uniqueness is **proof by contradiction**. We'll assume a sequence
converges to two different limits `L` and `M`, and show this leads to an impossibility.
The strategy involves choosing epsilon to be half the distance between `L` and `M`, then
showing the sequence can't simultaneously stay that close to both limits.

## New Tools You'll Need

### Proof by Contradiction: `by_contra`

The `by_contra` tactic allows us to prove a statement by assuming its negation and deriving
a contradiction. The syntax is `by_contra h`, which adds a hypothesis `h` containing the
negation of the current goal and changes the goal to `False`.

### `abs_pos_of_nonzero`

If `x ≠ 0`, then `0 < |x|`. This theorem is essential for working with distances between
distinct points.

## The Strategy

Here's how the proof works:

1. Assume for contradiction that `L ≠ M`
2. Then `|L - M| > 0`, so we can use `ε := |L - M| / 2` as our tolerance
3. Apply the convergence condition to get `N₁` and `N₂` for sequences converging to `L` and `M`
4. Take `N = N₁ + N₂` and evaluate at `n = N`
5. Use the triangle inequality to show `|L - M| ≤ |a N - L| + |a N - M| < ε + ε = |L - M|`
6. This gives the contradiction: `|L - M| < |L - M|`

The algebra in step 5 is the key: we write `L - M = (L - a(N)) + (a(N) - M)` and apply
the triangle inequality to get the impossible conclusion.
"


/-- To give a proof by contradiction, the syntax is : `by_contra h`, which adds a hypothesis with the name `h` (or whatever you want), which is the negation of the current Goal, and changes the goal to `false`. -/
TacticDoc by_contra

NewTactic by_contra

theorem abs_pos_of_nonzero {x : ℝ} (h : x ≠ 0) : 0 < |x| :=
abs_pos.mpr h

/-- If `x ≠ 0`, then `0 < |x|`. -/
TheoremDoc abs_pos_of_nonzero as "abs_pos_of_nonzero" in "|x|"

NewTheorem abs_pos_of_nonzero

/-- If `a : ℕ → ℝ` converges to `L` and `M`, then `L = M`. -/
TheoremDoc LimUnique as "LimUnique" in "aₙ"

/-- Prove that limits are unique.
-/
Statement LimUnique (a : ℕ → ℝ) (L M : ℝ) (aToL : SeqLim a L) (aToM : SeqLim a M) :
    L = M := by
by_contra h
have f0 : L - M ≠ 0 := by bound
have f1 : 0 < |L - M| := by apply abs_pos_of_nonzero f0
have f2 : 0 < |L - M| / 2 := by bound
specialize aToL (|L - M| / 2) f2
specialize aToM (|L - M| / 2) f2
choose N1 hN1 using aToL
choose N2 hN2 using aToM
have f3 : N1 ≤ N1 + N2 := by bound
have f4 : N2 ≤ N1 + N2 := by bound
specialize hN1 (N1 + N2) f3
specialize hN2 (N1 + N2) f4
have f5 : |L - M| = |(L - a (N1+N2)) + (a (N1 + N2) - M)| := by ring_nf
have f6 : |(L - a (N1+N2)) + (a (N1 + N2) - M)| ≤
    |(L - a (N1+N2))| + |(a (N1 + N2) - M)| := by apply abs_add_le
have f7 : |(L - a (N1+N2))| = |-(a (N1+N2) - L)| := by ring_nf
have f8 : |-(a (N1+N2) - L)| = |(a (N1+N2) - L)| := by apply abs_neg
linarith [f5, f6, f7, f8, hN1, hN2]


Conclusion "
## What You've Proven

Congratulations! You've just established one of the most important foundational results in
analysis: **limits are unique**.

This theorem justifies our use of the definite article—we can speak of \"**the** limit\"
of a sequence rather than \"**a** limit.\" Without uniqueness, the entire theory of limits
would be ambiguous and potentially inconsistent.

## Why Uniqueness Matters

The uniqueness of limits is fundamental to the entire edifice of analysis. It ensures that:

- When we define continuous functions using limits, the definitions are unambiguous
- Limit notation like `lim_{n→∞} a(n) = L` is well-defined
- We can safely use limits in computations without worrying about multiple possible values
- Many standard theorems that rely on \"the limit\" make sense

## The Power of Contradiction

This proof also showcased the power of **proof by contradiction** (`by_contra`). When
direct proof seems difficult, assuming the opposite and deriving an impossibility can be
an elegant and effective strategy. You'll use this technique many times throughout
analysis.

The key insight was geometric: if two points are separated by distance `d`, then no third
point can be within distance `d/2` of both. This simple observation, made rigorous through
epsilon-N arguments, gave us our contradiction.
"
