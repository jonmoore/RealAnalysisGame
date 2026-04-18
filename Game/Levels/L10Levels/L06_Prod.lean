import Game.Levels.L9PsetIntro

World "Lecture10"
Level 1
Title "Big Boss : Product of Sequences"


Introduction "
# Level 1: Big Boss - Product of Sequences

This is the capstone of the Algebraic Limit Theorem! We've already proven that limits behave well under addition, scalar multiplication, and inversion. Now we tackle multiplication of sequences.

**The Challenge:** If `a n → L` and `b n → M`, prove that `a n * b n → L * M`.

**The Key Insight:** We need to write the error `a n * b n - L * M` in a way that separates the contributions from each sequence. The trick is to add and subtract `b n * L`:

```
a n * b n - L * M = (a n - L) * b n + L * (b n - M)
```

**Why does this work?** Think about rectangles! The product `a n * b n` is the area of a rectangle with dimensions `a n` by `b n`, while `L * M` is the limiting rectangle. The difference decomposes into two strips:
- `(a n - L) * b n`: a thin vertical strip (small width, bounded height)
- `L * (b n - M)`: a thin horizontal strip (bounded width, small height)

The corner piece `(a n - L) * (b n - M)` gets absorbed into the first term—it's doubly small so it doesn't hurt us!

**The Strategy:**
1. Use `Bdd_of_ConvNonzero` to get a bound `K` on the sequence `b`
2. Make `|a n - L| < ε/(2*K)` to control the first term
3. Make `|b n - M| < ε/(2*|L|)` to control the second term
4. Combine using the triangle inequality


Good luck!
"

/--
If sequences `a b : ℕ → ℝ` converge with `a` going to `L ≠ 0` and `b` going to `M ≠ 0`, then `a n * b n` converges to `L * M`.
-/
TheoremDoc ProdLimNeNe as "ProdLimNeNe" in "aₙ"

/-- Prove this
-/
Statement ProdLimNeNe (a b c : ℕ → ℝ) (L M : ℝ) (hL : L ≠ 0) (hM : M ≠ 0) (ha : SeqLim a L)
    (hb : SeqLim b M) (hc : ∀ n, c n = a n * b n):
    SeqLim c (L * M) := by
intro ε hε
choose K hK using Bdd_of_ConvNonzero b M hb hM
have ε1 : 0 < ε / (2 * K) := by bound
have absL : 0 < |L| := by apply abs_pos_of_nonzero hL
have ε2 : 0 < ε / (2 * |L|) := by bound
specialize ha (ε / (2 * K)) ε1
specialize hb (ε / (2 * |L|)) ε2
choose N1 hN1 using ha
choose N2 hN2 using hb
use N1 + N2
intro n hn
have hn1 : N1 ≤ n := by bound
have hn2 : N2 ≤ n := by bound
specialize hN1 n hn1
specialize hN2 n hn2
specialize hc n
rewrite [hc]
have f1 : |a n * b n - L * M| = |(a n - L) * b n + (L * (b n -  M))| := by ring_nf
have f2 : |(a n - L) * b n + (L * (b n -  M))| ≤ |(a n - L) * b n| + |(L * (b n -  M))| := by apply abs_add_le
have f3 : |(a n - L) * b n| = |(a n - L)| * |b n| := by apply abs_mul
have bnBnd : |b n| ≤ K := by apply hK.2 n
have f5 : |(a n - L)| * |b n| ≤ ε / (2 * K) * K := by bound
have Kpos : 0 < K := by apply hK.1
have f6 : ε / (2 * K) * K = ε / 2 := by field_simp
have f7 : |(L * (b n -  M))| = |L| * |b n -  M| := by apply abs_mul
have f8 :  |L| * |b n -  M| < |L| * (ε / (2 * |L|)) := by bound
have f9 : |L| * (ε / (2 * |L|)) = ε / 2 := by field_simp
linarith [f1, f2, f3, f5, f6, f7, f8, f9]


Conclusion "
Congratulations! You've completed the hardest part of the Algebraic Limit Theorem.

Postscript:
**Why would you think to add and subtract `b n * L`?**

Think about the product rule in calculus: `(fg)' = f'g + fg'`. Multiplication always corresponds to a rectangle. When you have two quantities `f` and `g` both changing, the change in their product `fg` can be visualized as the change in area:

```
      f        Δf
   +-----+-------+
   |     |       |
 g |     |       |
   +-----+-------+
 Δg|     |  tiny |
   +-----+-------+
```

The total change is `(f + Δf)(g + Δg) - fg = f·Δg + g·Δf + Δf·Δg`.

In our proof, we replaced `M` with `b n` (adding and subtracting `b n * L`) to get the same decomposition. The `Δf·Δg` term (the tiny corner) gets absorbed into `(a n - L) * b n`, and since both factors are small, it doesn't cause problems.

This geometric picture explains the algebraic trick: we're decomposing the area difference into two manageable strips that we can control independently.

# Algebraic Limit Theorem - Complete!

You can now:
- **Add** sequences: if `a n → L` and `b n → M`, then `a n + b n → L + M`
- **Multiply by constants**: if `a n → L`, then `c * a n → c * L`
- **Multiply** sequences: if `a n → L` and `b n → M`, then `a n * b n → L * M`
- **Invert** (when limit is nonzero): if `a n → L ≠ 0`, then `1 / a n → 1 / L`

This is incredibly powerful! For any algebraic combination of convergent sequences, you can compute the limit by just plugging in the individual limits.

**Example:** If `a n → L` and `b n → M`, what is
```
lim ((a n)² + 2*a n + b n) / (3*b n + 2 - (a n)²)
```

**Answer:** `(L² + 2*L + M) / (3*M + 2 - L²)` (provided the denominator ≠ 0).

You can build this up step by step using the algebraic limit rules!

**Note:** The case where `L = 0` or `M = 0` is left as an exercise. The proof requires slightly different techniques since you can't divide by `|L|` or ensure `b` is bounded away from zero. Try it yourself!
"
