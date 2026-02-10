import Game.Levels.L14Lecture

open Finset

World "Lecture15"
Level 1
Title "Completeness"
Introduction "
# Level 1 **Big Boss:**  Completeness!

We now know that Cauchy sequences of rational numbers converge to real numbers. (Because they *are* real numbers.) Let's record this as a theorem:

## New theorem: `Conv_of_IsCauchy` : If a sequence `(a : ℕ → ℚ)` satisfies `IsCauchy a`, then that implies that `SeqConv a`.

Given that a limit exists, let us make the following

## New definition: `Real_of_CauSeq`. This takes `IsCauchy a` and returns a real number.

This real number does what we want:

## New theorem: `SeqLim_of_Real_of_Cau` : `ha : IsCauchy (a : ℕ → ℚ)` implies that `SeqLim a (Real_of_CauSeq ha)`.


Ok, but what about Cauchy sequences of real numbers? Do we need a whole other number system (the \"hyperreals\" or perhaps \"surreals\", for the Conway fans out there...)
to capture limits of reals?

No! And this is a general phenomenon: when you
\"complete\" a space by replacing it with equivalence classes of Cauchy sequences from
that space, the space itself is automatically \"complete\", that is, all Cauchy
sequences in the completed space already converge in the same. Let's prove it for the reals!

So again, we want to show that:
any Cauchy sequence of *real* numbers converges to a real number.
But we just learned that real numbers are themselves Cauchy sequences of rationals
(or rather, equivalence classes thereof).
Now that real numbers are represented by Cauchy sequences of rationals, what does it mean for $x_n$ to be a Cauchy sequence of reals? A Cauchy sequence of Cauchy sequences?? Let's unpack that.

Let's say that we have an infinite sequence of real numbers, `x : ℕ → ℝ`, thought of as `x = (x₀, x₁, x₂, ...)`.
 Each
real `xₙ` is secretly represented by a Cauchy sequence `(qₙ₀, qₙ₁, qₙ₂,...)` of rationals.
So each `xₙ` is a map `ℕ → ℚ`, and the original `x` is actually a map:

`q : ℕ → ℕ → ℚ`

That is, `x` is really a double-indexed array of rationals:

```
       j=0    j=1    j=2    j=3    ...
i=0:   q₀₀    q₀₁    q₀₂    q₀₃    ...   ← represents x₀
i=1:   q₁₀    q₁₁    q₁₂    q₁₃    ...   ← represents x₁
i=2:   q₂₀    q₂₁    q₂₂    q₂₃    ...   ← represents x₂
i=3:   q₃₀    q₃₁    q₃₂    q₃₃    ...   ← represents x₃
 ⋮      ⋮      ⋮      ⋮      ⋮
```

Each **row** is a Cauchy sequence of rationals `qₙₘ` converging to the corresponding real `xₙ`. Wild! Let's call `hq` the condition that each of these rows is a Cauchy sequence:

`hq : ∀ n, IsCauchy (q n)`

Then to say that this sequence (of sequences) `xₙ` is itself \"Cauchy\" is to say (as we already know) that:

`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ n, |Real_of_CauSeq (hq m) - Real_of_CauSeq (hq n)| < ε`

Now, let's assume this condition on our Cauchy sequence (of sequences) `x`. Our goal is to show that this sequence has a real limit, that is,
that there is a single sequence `y : ℕ → ℚ`, satisfying

`hy : IsCauchy y`

and so that `xₙ → y`, which means:

`SeqLim (fun n ↦ Real_of_CauSeq (hq n)) (Real_of_CauSeq hy)`.

How are we supposed to construct such a thing?!?!

The key insight (reminiscent of Cantor's **diagonalization** arguments, very prevalent
in real analysis): we need to extract a single sequence of rationals from this array!

**The naive attempt:** Take the diagonal sequence `(q₀₀, q₁₁, q₂₂, q₃₃, ...)`

**The problem:** Each row converges at **its own rate**! Row `k` might need to go out to
index `1000k` before it's within `ε` of its limit, and row `k+1` might need to go to index `k^2`, etc. But the diagonal only samples row `k`
at position `k`, which might be way too early!

**The solution:** For each row `k`, we need to pick an index `N(k)` that's far enough
out that row `k` has \"converged well enough\" by that point. Then we take:

`y k = q k (N (k))`

This sequence `y` will be Cauchy, and it will represent the limit of our sequence of reals!

**How to choose `N(k)`?** Use the fact that each `x k` (as a real number) is the limit of
its Cauchy sequence. So for any tolerance (say `1/k`, or rather, `1/(k+1)` so it's always strictly positive), there exists an index `N(k)`
so that for all `n ≥ m ≥ N(k)`, `q k m` stays within `1/(k+1)` of `q k n`. *That* is what we'll choose!

**Your task:** Construct this sequence `y`, prove it's Cauchy, and prove that the
sequence of reals converges to the real represented by `y`.

"

def SeqDiffBy (q : ℕ → ℚ) (r : ℕ → ℚ) (ε : ℚ) : Prop := ∃ M, ∀ i ≥ M, |q i - r i| < ε

Statement (q : ℕ → ℕ → ℚ) (hq : ∀ n, IsCauchy (q n))
  (hx : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ n, SeqDiffBy (q m) (q n) ε) :
  ∃ (y : ℕ → ℚ), (IsCauchy y) ∧
  ∀ ε > 0, ∃ N, ∀ n ≥ N, SeqDiffBy (q n) y ε
  := by
choose N hN using fun n ↦ hq n (1 / (n + 1)) (by bound)
let N' := fun n ↦ ∑ k ∈ range n, N k
have N'mono : Monotone N' := by sorry
have N'bnd : ∀ m, N m ≤ N' m := by sorry
have N'bnd' : ∀ m, ∀ n ≤ m, N n ≤ N' m := by
  intro m n hn
  linarith [N'bnd n, N'mono hn]
let y := fun n ↦ q n (N' n)
use y
split_ands
intro ε hε
choose N1 hN1 using hx (ε / 2) (by bound)
choose N2 hN2 using ArchProp (show (0 : ℝ) < ε / 2 by norm_num; bound)
use N1 + N2
intro n hn m hm
change |q m (N' m) - q n (N' n)| < ε
have f1 : |q m (N' m) - q n (N' n)| = |(q m (N' m) -  q n (N' m)) + (q n (N' m) - q n (N' n))| := by ring_nf
have f2 : |(q m (N' m) -  q n (N' m)) + (q n (N' m) - q n (N' n))| ≤
  |(q m (N' m) -  q n (N' m))| + |(q n (N' m) - q n (N' n))| := by apply abs_add_le
have := (N'bnd' m n hm)
have := hN1
--have := hN m (N' m) (N'bnd m) (N' n) (by apply N'mono hm)










sorry
sorry

#exit
choose N hN using fun (n : ℕ) ↦ SeqLim_of_Real_of_Cau (hq n) (1 / (n + 1)) (by bound)
change  ∀ n, ∀ m ≥ N n, |(q n m) - Real_of_CauSeq (hq n)| < 1 / (n + 1) at hN
let y := fun n ↦ q n (N n)
use y
have hy : IsCauchy y := by
  intro ε hε
  choose N1 hN1 using hx (ε / 3) (by norm_num; bound)
  choose N2 hN2 using ArchProp (show (0 : ℝ) < ε / 3 by norm_num; bound)
  use N1 + N2
  intro n hn m hm
  change |(q m (N m)) - q n (N n)| < ε
  specialize hN1 n (by bound) m hm
  let xn := Real_of_CauSeq (hq n)
  let xm := Real_of_CauSeq (hq m)
  change |(xm - xn)| < ε / 3  at hN1
  have qnBnd := hN n (N n) (by bound)
  change |(q n (N n)) - xn| < 1 / (n + 1) at qnBnd
  have qmBnd := hN m (N m) (by bound)
  change |(q m (N m)) - xm| < 1 / (m + 1) at qmBnd
  have f1 : |(q m (N m) : ℝ) - q n (N n)| = |(q m (N m) - xm) + ((xn - q n (N n)) + (xm - xn))| := by ring_nf
  have f2 : |(q m (N m) - xm) + ((xn - q n (N n)) + (xm - xn))| ≤
    |(q m (N m) - xm)| + |(xn - q n (N n)) + (xm - xn)| := by apply abs_add_le
  have f3 : |(xn - q n (N n)) + (xm - xn)| ≤ |(xn - q n (N n))| + |(xm - xn)| := by apply abs_add_le
  have f3' : |(xn - q n (N n))| = |q n (N n) - xn| := by apply abs_sub_comm
  have f4 : (1 : ℝ) / (n + 1) < ε / 3 := by sorry
  have f5 : (1 : ℝ) / (m + 1) < ε / 3 := by sorry
  have f6 : |(q m (N m) : ℝ) - q n (N n)| < ε := by linarith [f1, f2, f3, f4, f5, qnBnd, qmBnd, hN1, f3']
  exact_mod_cast f6
use hy

intro ε hε
choose N1 hN1 using hx (ε / 2) (by norm_num; bound)
choose N2 hN2 using ArchProp (show (0 : ℝ) < ε / 2 by norm_num; bound)
choose N3 hN3 using SeqLim_of_Real_of_Cau hy (ε / 2) (by norm_num; bound)
use N1 + N2 + N3
intro n hn

let xn := Real_of_CauSeq (hq n)
let L := Real_of_CauSeq hy
change |xn - L| < ε
change ∀ n ≥ N3, |y n - L| < ε / 2 at hN3

rewrite [show |xn - L| = |(xn - y n) + (y n - L)| by ring_nf]
have f1 : |(xn - y n) + (y n - L)| ≤ |(xn - y n)| + |(y n - L)| := by apply abs_add_le
specialize hN n (N n) (by bound)
change |y n - xn| < 1 / (n + 1) at hN
rewrite [show |y n - xn| = |xn - y n| by apply abs_sub_comm] at hN
specialize hN3 n (by bound)

have f2 : (1 : ℝ) / (n + 1) < ε / 2 := by sorry

linarith [f1, f2, hN, hN3]

Conclusion "
"
-- TALK ABOUT THE NEED  (And HOW) TO DO THIS FOR EQUIVALENCE CLASSES
















#exit


WRONG:

Excellent! You've just proved that the diagonal sequence is Cauchy!

This is the heart of the completeness proof. The full argument would show that:

1. The diagonal sequence `y = (q₀₀, q₁₁, q₂₂, ...)` is Cauchy ✓ (what you just proved!)
2. Each real `xₙ` is equivalent to subsequences of `y`
3. Therefore `(xₙ)` converges to `[y]` (the equivalence class of `y`)

The beautiful thing is that **completeness becomes almost tautological** with
this construction: Cauchy sequences of Cauchy sequences give you a Cauchy sequence!

This is why mathematicians like this construction of ℝ - the main theorem
(completeness) essentially falls out of the definition for free.

**Philosophical note:** With the Dedekind cut construction, completeness is also
\"automatic\" but for different reasons. With Cauchy sequences, it's more direct:
we literally construct limits as equivalence classes of sequences that \"should\"
converge.






OLD:


First of all, how can we tell when two real numbers differ by at most $ε$?
If $x$ is represented by the rational Cauchy sequence $(q_n)$ and `y:ℝ` by $(r_n)$, then what does it mean when we say that `|x - y| < ε`? Idea: it means that *eventually* the Cauchy sequences also differ by at most `ε`!

**Def** `SeqDiffBy (q : ℕ → ℚ) (r : ℕ → ℚ) (ε : ℚ) : Prop :=`
`∃ N, ∀ n ≥ N, ∀ m ≥ N, |q m - r n| < ε`.

This is a kind of \"mixed Cauchy\" condition!
But notice that we are **no longer** assuming that `m ≥ n ≥ N`; because
we don't want to necessarily force that, now that there's no symmetry between `q m` and `r n`.

Now


...


Wild!  This sequence (of sequences) is \"Cauchy\" iff (as we already know):

`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ n, SeqDiffBy (q m) (q n) ε`

`∀ ε > 0, ∃ N, ∀ n ≥ N, SeqDiffBy (q n) y ε`



....


choose N hN using fun (k : ℕ) ↦ hx ((1 : ℚ) / (k + 1)) (by bound)
change ∀ k, ∀ n ≥ N k, ∀ m ≥ n, ∃ M, ∀ i ≥ M, ∀ j ≥ M, |q m j - q n i| < (1 / (k + 1)) at hN
use fun k ↦ q k (N k)
split_ands
intro ε hε
change ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ n, ∃ M, ∀ i ≥ M, ∀ j ≥ M, |q m j - q n i| < ε at hx
choose N1 hN1 using hx (ε / 3) (by norm_num; bound)
choose N2 hN2 using ArchProp (show (0 : ℝ) < ε / 3 by norm_num; bound)
use N1 + N2
intro n hn m hm
change |(q m (N m)) - q n (N n)| < ε
have qnBnd := hN n (N n) (by bound)
have qmBnd := hN m (N m) (by bound)
specialize hN1 n (by bound) m hm
