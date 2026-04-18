import Game.Levels.L14Lecture

World "Lecture15"
Level 1
Title "Completeness"

Introduction "
# Level 1 **Big Boss:** Completeness!

We now know that Cauchy sequences of rational numbers converge to real numbers. In fact, they **are** real numbers—that's how we constructed ℝ! Let's make this official:

## New theorem: `Conv_of_IsCauchy`
If a sequence `a : ℕ → ℚ` satisfies `IsCauchy a`, then `SeqConv a` holds—the sequence converges.

Given that such a limit exists, we can name it:

## New definition: `Real_of_CauSeq`
This takes a proof `ha : IsCauchy a` (for `a : ℕ → ℚ`) and returns the real number that `a` converges to.

This real number behaves exactly as we'd hope:

## New theorem: `SeqLim_of_Real_of_Cau`
If `ha : IsCauchy a` for `a : ℕ → ℚ`, then `SeqLim a (Real_of_CauSeq ha)`.

---

## The Big Question: What About Cauchy Sequences of Reals?

We've completed the rationals by adding limits of Cauchy sequences, creating ℝ. But now we can ask: do Cauchy sequences of **real** numbers converge to real numbers? Or do we need yet another number system (the \"hyperreals\" or \"surreals\" for the Conway fans out there...)?

**The answer:** No! The reals are **complete**.

This is a general phenomenon: when you \"complete\" a space by adding equivalence classes of Cauchy sequences, the resulting space is automatically complete—all Cauchy sequences in the completed space converge within that same space.

**Our goal:** Prove that any Cauchy sequence of real numbers converges to a real number.

---

## Unpacking the Problem: Cauchy Sequences of Cauchy Sequences

Here's where things get interesting. Real numbers **are** Cauchy sequences of rationals (or rather, equivalence classes thereof). So what does it mean for `x : ℕ → ℝ` to be a Cauchy sequence of reals?

Let's write `x = (x₀, x₁, x₂, ...)` as our sequence of reals.

Each real `xₙ` is secretly a Cauchy sequence of rationals:
- `x₀` is represented by the Cauchy sequence `(q₀₀, q₀₁, q₀₂, ...)`
- `x₁` is represented by the Cauchy sequence `(q₁₀, q₁₁, q₁₂, ...)`
- `x₂` is represented by the Cauchy sequence `(q₂₀, q₂₁, q₂₂, ...)`
- and so on...

Each `xₙ` is itself a function `ℕ → ℚ`, so the entire setup is really a **double-indexed array** of rationals:

`q : ℕ → ℕ → ℚ`

Visualized:
```
       j=0    j=1    j=2    j=3    ...
i=0:   q₀₀    q₀₁    q₀₂    q₀₃    ...   ← represents x₀
i=1:   q₁₀    q₁₁    q₁₂    q₁₃    ...   ← represents x₁
i=2:   q₂₀    q₂₁    q₂₂    q₂₃    ...   ← represents x₂
i=3:   q₃₀    q₃₁    q₃₂    q₃₃    ...   ← represents x₃
 ⋮      ⋮      ⋮      ⋮      ⋮
```

Each **row** `(qₙ₀, qₙ₁, qₙ₂, ...)` is a Cauchy sequence converging to `xₙ`.

Let `hq : ∀ n, IsCauchy (q n)` denote the fact that each row is Cauchy.

To say that `x` itself is Cauchy means:
```lean
∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ n,
  |Real_of_CauSeq (hq m) - Real_of_CauSeq (hq n)| < ε
```

**Our task:** Given this Cauchy sequence `x` of reals, construct a single Cauchy sequence `y : ℕ → ℚ` of rationals such that:
- `hy : IsCauchy y`
- `SeqLim (fun n ↦ Real_of_CauSeq (hq n)) (Real_of_CauSeq hy)`

In other words, prove that `xₙ → Real_of_CauSeq hy`.

---

## The Key Idea: Diagonalization (But Carefully!)

We need to extract a **single sequence of rationals** from this infinite double array. This is reminiscent of Cantor's famous **diagonalization** arguments.

### Naive Attempt: The Diagonal

Why not just take the diagonal sequence `(q₀₀, q₁₁, q₂₂, q₃₃, ...)`?

**Problem:** Each row converges at its **own rate**!
- Row `k` might need to reach index `1000k` before getting within `ε` of its limit
- Row `k+1` might need to reach index `k²` before converging
- The diagonal only samples row `k` at position `k`, which could be way too early!

The diagonal doesn't respect the different convergence rates of each row.

### The Solution: Choose Convergence Points Wisely

**Strategy:** For each row `k`, pick an index `N(k)` where row `k` has \"converged well enough.\" Then define:

`y k = q k (N k)`

This way, we sample each row at a point where it's already close to its limit.

**How to choose `N(k)`?**

Use the fact that `xₖ = Real_of_CauSeq (hq k)`, so row `k` converges to `xₖ`. For any tolerance—say `1/(k+1)` to keep things strictly positive—there exists an index `N(k)` such that:

`∀ m ≥ N(k), |q k m - xₖ| < 1/(k+1)`

**That's our `N(k)`!**

---

## Your Mission

Construct the sequence `y`, prove it's Cauchy, and prove that the sequence of reals `x` converges to `Real_of_CauSeq hy`.

This will require:
1. **Choosing the convergence points:** Use `SeqLim_of_Real_of_Cau (hq n)` with tolerance `1/(n+1)` to get `N(n)` for each row
2. **Proving `y` is Cauchy:** Use a triangle inequality argument splitting `|yₘ - yₙ|` into three manageable pieces
3. **Proving convergence:** Show `|xₙ - Real_of_CauSeq hy|` gets arbitrarily small

The proof involves careful bookkeeping with multiple `N` values (from the Cauchy property of `x`, from the Archimedean property, and from the convergence of `y`), all orchestrated via triangle inequalities and the `linarith` tactic.

Good luck! This is the capstone result that shows the reals are truly complete.
"

theorem Conv_of_IsCauchy {a : ℕ → ℚ} (ha : IsCauchy a) : SeqConv (a ·) := by
-- in Mathlib
  sorry

/-- `{a : ℕ → ℚ} (ha : IsCauchy a) : ℝ`

A sequence `a : ℕ → ℚ` that is Cauchy converges to a real number; this *is* that real number. -/
DefinitionDoc Real_of_CauSeq as "Real_of_CauSeq"

NewDefinition Real_of_CauSeq

noncomputable def Real_of_CauSeq {a : ℕ → ℚ} (ha : IsCauchy a) : ℝ := by
  choose L hL using Conv_of_IsCauchy ha
  exact L


theorem SeqLim_of_Real_of_Cau {a : ℕ → ℚ} (ha : IsCauchy a) : SeqLim (a ·) (Real_of_CauSeq ha) :=
Classical.choose_spec (Conv_of_IsCauchy ha)

/-- If a sequence `a : ℕ → ℚ` is Cauchy, then it converges (that is, `SeqLim` holds)
to the real number defined in `Real_of_CauSeq`. -/
TheoremDoc SeqLim_of_Real_of_Cau as "SeqLim_of_Real_of_Cau" in "aₙ"

NewTheorem SeqLim_of_Real_of_Cau

/-- The real numbers are complete; Cauchy sequences in the reals converge to a real number. -/
TheoremDoc Reals_are_Complete as "Reals_are_Complete" in "aₙ"

Statement Reals_are_Complete (q : ℕ → ℕ → ℚ) (x : ℕ → ℝ) (hq : ∀ n, IsCauchy (q n))
  (hx : ∀ n, x n = Real_of_CauSeq (hq n))
  (hxCau : IsCauchy x) :
  ∃ (y : ℕ → ℚ) (hy : IsCauchy y), SeqLim x (Real_of_CauSeq hy) := by
choose N hN using fun (n : ℕ) ↦ SeqLim_of_Real_of_Cau (hq n) (1 / (n + 1)) (by bound)
have hN : ∀ n, ∀ m ≥ N n, |(q n m) - x n| < 1 / (n + 1) := by intro n m hm; rewrite [hx n]; apply hN n m hm
let y := fun n ↦ q n (N n)
use y
have hy : IsCauchy y := by
  intro ε hε
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  choose N1 hN1 using hxCau (ε / 3) (by norm_num; bound)
  choose N2 hN2 using ArchProp (show (0 : ℝ) < ε / 3 by norm_num; bound)
  use N1 + N2
  intro n hn m hm
  change |(q m (N m)) - q n (N n)| < ε
  specialize hN1 n (by bound) m hm
  have qnBnd := hN n (N n) (by bound)
  have qmBnd := hN m (N m) (by bound)
  have f1 : |(q m (N m) : ℝ) - q n (N n)| = |(q m (N m) - x m) + ((x n - q n (N n)) + (x m - x n))| := by ring_nf
  have f2 : |(q m (N m) - x m) + ((x n - q n (N n)) + (x m - x n))| ≤
    |(q m (N m) - x m)| + |(x n - q n (N n)) + (x m - x n)| := by apply abs_add_le
  have f3 : |(x n - q n (N n)) + (x m - x n)| ≤ |(x n - q n (N n))| + |(x m - x n)| := by apply abs_add_le
  have f3' : |(x n - q n (N n))| = |q n (N n) - x n| := by apply abs_sub_comm
  field_simp at hN2
  have hn' : (N1 : ℝ) + N2 ≤ n := by exact_mod_cast hn
  have hm' : (n : ℝ) ≤ m := by exact_mod_cast hm
  have f4' : (N2 : ℝ) ≤ n := by bound
  have f4'' : (N2 : ℝ) * ε ≤ n * ε := by bound
  have f4 : (1 : ℝ) / (n + 1) < ε / 3 := by field_simp; bound
  have f5' : (N2 : ℝ) ≤ m := by bound
  have f5'' : (N2 : ℝ) * ε ≤ m * ε := by bound
  have f5 : (1 : ℝ) / (m + 1) < ε / 3 := by field_simp; bound
  have f6 : |(q m (N m) : ℝ) - q n (N n)| < ε := by linarith [f1, f2, f3, f4, f5, qnBnd, qmBnd, hN1, f3']
  exact_mod_cast f6
use hy

intro ε hε
choose N1 hN1 using hxCau (ε / 2) (by norm_num; bound)
choose N2 hN2 using ArchProp (show (0 : ℝ) < ε / 2 by norm_num; bound)
choose N3 hN3 using SeqLim_of_Real_of_Cau hy (ε / 2) (by norm_num; bound)
use N1 + N2 + N3
intro n hn

let L := Real_of_CauSeq hy
change |x n - L| < ε
change ∀ n ≥ N3, |y n - L| < ε / 2 at hN3

rewrite [show |x n - L| = |(x n - y n) + (y n - L)| by ring_nf]
have f1 : |(x n - y n) + (y n - L)| ≤ |(x n - y n)| + |(y n - L)| := by apply abs_add_le
specialize hN n (N n) (by bound)
change |y n - x n| < 1 / (n + 1) at hN
rewrite [show |y n - x n| = |x n - y n| by apply abs_sub_comm] at hN
specialize hN3 n (by bound)

field_simp at hN2
have hn' : (N1 : ℝ) + N2 + N3 ≤ n := by norm_cast
have f2' : (N2 : ℝ) ≤ n := by bound
have f2'' : (N2 : ℝ) * ε ≤ n * ε := by bound
have f2 : (1 : ℝ) / (n + 1) < ε / 2 := by field_simp; bound

linarith [f1, f2, hN, hN3]

Conclusion "
# Conclusion: The Reals Are Complete

Congratulations! You've just proved one of the most fundamental theorems in real analysis: **the real numbers are complete**.

## What We Accomplished

We showed that any Cauchy sequence of real numbers converges to a real number. This means:
- We don't need to construct yet another number system beyond ℝ
- The completion process terminates: ℚ → ℝ → ... → ℝ (we're done!)
- Every \"should converge\" sequence in ℝ actually does converge in ℝ

## The Beauty of the Construction

The proof relied on a clever diagonal-inspired construction:
- Each real `xₙ` is secretly a Cauchy sequence of rationals (row `n` of our array)
- We extracted a **single** sequence `y` by sampling one rational from each row
- The key: we sampled row `k` at index `N(k)` where it had already converged to within `1/(k+1)` of its limit
- This ensured `y` itself was Cauchy, and that `y` captured the limit of the sequence of reals

The technique—choosing convergence points rather than blindly taking the diagonal—is fundamental in analysis. You'll see variations of this argument in:
- Arzela-Ascoli theorem (equicontinuous families)
- Weak compactness arguments (functional analysis)
- Diagonal extraction arguments throughout measure theory

## Why Completeness Matters

Completeness is what makes analysis possible. Here's what we can now guarantee:

**Closure under limits:** Take limits freely within ℝ without worrying about \"escaping\" the space.

**Convergence of series:** Infinite sums `∑ aₙ` converge whenever their partial sums are Cauchy.

**Fixed point theorems:** Contractions have fixed points, found by iterating `x₀, f(x₀), f(f(x₀)), ...`

**Function construction:** Define `eˣ`, `sin(x)`, `cos(x)` as limits of sequences/series with confidence they converge.

**Completeness + Archimedean + Ordered Field = ℝ:** Any mathematical structure with these properties is isomorphic to the real numbers. We've fully characterized ℝ!

## The Completion Journey

Let's recap how we got here:

1. **Started with ℚ** - algebraically nice but full of holes
2. **Defined Cauchy sequences** - identified \"should converge\" sequences
3. **Took equivalence classes** - two sequences are the same if their difference → 0
4. **Created ℝ** - the set of these equivalence classes
5. **Proved completeness** - Cauchy sequences in ℝ converge in ℝ

This is the **completion** of a metric space, and it's a universal construction in mathematics.

## Beyond the Reals

The completeness property isn't unique to ℝ:

**Other complete spaces:**
- ℂ (complex numbers) - complete in the same sense
- ℝⁿ (Euclidean space) - complete under the Euclidean metric
- Lᵖ spaces - complete normed vector spaces of functions
- C[a,b] - continuous functions with sup norm

**Incomplete spaces that need completion:**
- ℚ needs completion → ℝ
- ℚₚ (p-adics) from ℚ with p-adic absolute value
- Continuous functions with L² norm need completion → L² space

The pattern is always the same: Cauchy sequences → equivalence classes → completed space.

## Looking Ahead

With completeness established, we've finished building the real number system. We now have:
- ✓ An ordered field (arithmetic that respects order)
- ✓ Archimedean property (no infinitesimals)
- ✓ Monotone Convergence Theorem (bounded monotone sequences converge)
- ✓ Bolzano-Weierstrass Theorem (bounded sequences have convergent subsequences)
- ✓ Completeness (Cauchy sequences converge)

These properties collectively **characterize** ℝ up to isomorphism.

Now we can move beyond the construction of ℝ to actually **doing analysis**:
- Continuous functions and the Intermediate Value Theorem
- Differentiability and the Mean Value Theorem
- Integration and the Fundamental Theorem of Calculus
- Uniform convergence and series of functions
- Power series and analytic functions

The foundation is solid. The real mathematics begins now!

## A Final Thought

There's something philosophically profound about completeness. To achieve it, we had to:
- Accept infinite processes as completed objects
- Embrace numbers that can't be written as finite expressions
- Work with equivalence classes rather than concrete representations

But in return, we gained a number system where:
- Every bounded monotone sequence converges
- Every continuous function on [a,b] attains its maximum
- The Intermediate Value Theorem holds
- Calculus works!

We traded the simplicity of ℚ (every number is p/q) for the completeness of ℝ (every Cauchy sequence converges). This trade-off—giving up finite describability to gain analytic power—is at the heart of modern mathematics.

**Welcome to the real numbers. They're complete, they're beautiful, and they're ready for analysis.**
"
