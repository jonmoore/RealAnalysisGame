import Game.Levels.L23Levels.L02

open Finset Set

World "Lecture23"
Level 3
Title "Compactness"
Introduction "
# Level 3: Compactness

**The Final Puzzle Piece**: We've shown that uniformly continuous functions are integrable. But when is a continuous function *uniformly* continuous? The beautiful answer involves one of mathematics' most elegant concepts: **compactness**.

**The Big Theorem**: Every continuous function on a compact set is automatically uniformly continuous on that set. Combined with Level 2, this means every continuous function on a compact set is integrable!

**What Is Compactness?**: Intuitively, a set is compact if it's \"small enough\" that any covering by open balls can be reduced to a finite covering. Here's the key insight for uniform continuity:

1. **Start with continuity**: At each point `x` in your set `S`, continuity gives you a ball around `x` where the function doesn't vary much
2. **Cover the set**: These balls cover your entire set `S`
3. **Apply compactness**: Extract a *finite* subcover
4. **Take the minimum**: Since you now have only finitely many balls, you can take the minimum of their radii to get a uniform `δ`!

**New Definitions**:

Open ball of radius `r` around `x`:

`def Ball (x : ℝ) (r : ℝ) : Set ℝ := Ioo (x - r) (x + r)`

Compactness (every open cover has a finite subcover):

`def IsCompact (S : Set ℝ) : Prop :=
  ∀ (ι : Type) (xs : ι → ℝ) (δs : ι → ℝ), (∀ i, 0 < δs i) →
    (S ⊆ ⋃ i, Ball (xs i) (δs i)) →
    ∃ (V : Finset ι), S ⊆ ⋃ i ∈ V, Ball (xs i) (δs i)`

**The Magic**: The index type `ι` can be *anything* - natural numbers, real numbers, even uncountable sets. But compactness guarantees we can always reduce to a finite subcover!

**Key Tools**:
- `mem_Union`: `(x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i`
- `FinMinPos`: From finitely many positive numbers, you can extract a positive lower bound

**Your Mission**: Prove that continuous + compact = uniformly continuous!
"

namespace RealAnalysisGame

def Ball (x : ℝ) (r : ℝ) : Set ℝ := Ioo (x - r) (x + r)

/-- `Ball (x : ℝ) (r : ℝ) : Set ℝ := Ioo (x - r) (x + r)`

A ball of radius `r` centered at `x` is the open interval `(x - r, x + r)`.
-/
DefinitionDoc Ball as "Ball"

theorem mem_Union {α : Type*} {ι : Sort*} {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i := Set.mem_iUnion

/--
An element `x` is in the union of sets `s i` if and only if there exists an index `i` such that `x` is in `s i`.
-/
TheoremDoc RealAnalysisGame.mem_Union as "mem_Union" in "x∈U"

lemma FinMinPos (ι : Type) (V : Finset ι) (δs : ι → ℝ) (hδs : ∀ i, δs i > 0) :
    ∃ δ > 0, ∀ i ∈ V, δ ≤ δs i := by
  by_cases h_nonempty : V.Nonempty
  sorry
  use 1, by bound
  intro i hi
  exfalso
  simp only [Finset.not_nonempty_iff_eq_empty] at h_nonempty
  rewrite [h_nonempty] at hi
  contradiction

/--
Given an indexing type `ι`, a finite subset `V` of `ι`, and a function `δs : ι → ℝ` that assigns a positive real number to each index, there exists a positive real number `δ` such that for all indices `i` in the finite set `V`, `δ` is less than or equal to `δs i`.
-/
TheoremDoc RealAnalysisGame.FinMinPos as "FinMinPos" in "Theorems"

NewTheorem RealAnalysisGame.FinMinPos RealAnalysisGame.mem_Union

def IsCompact (S : Set ℝ) : Prop :=
  ∀ (ι : Type) (xs : ι → ℝ) (rs : ι → ℝ), (∀ i, 0 < rs i) → (S ⊆ ⋃ i, Ball (xs i) (rs i)) →
    ∃ (V : Finset ι), S ⊆ ⋃ i ∈ V, Ball (xs i) (rs i)

/-- `IsCompact (S : Set ℝ) : Prop :=
  ∀ (ι : Type) (xs : ι → ℝ) (δs : ι → ℝ), (∀ i, 0 < δs i) → (S ⊆ ⋃ i, Ball (xs i) (δs i)) →
    ∃ (V : Finset ι), S ⊆ ⋃ i ∈ V, Ball (xs i) (δs i)`

A set `S` is compact if for every cover of `S` by balls, there exists a finite subcover.
-/
DefinitionDoc IsCompact as "IsCompact"

/--
A `Type` is an arbitrary mathematical object.
-/
DefinitionDoc «Type» as "Type"

NewDefinition IsCompact Ball  «Type»

/--
A continuous function on a compact set is uniformly continuous on that set.
-/
TheoremDoc RealAnalysisGame.UnifContOn_of_Compact as "UnifContOn_of_Compact" in "f(x)"

Statement UnifContOn_of_Compact (f : ℝ → ℝ) (hf : FunCont f) (S : Set ℝ) (hS : IsCompact S) : UnifContOn f S := by
intro ε hε
have h1 : ∀ x ∈ S, ∃ δ > 0, ∀ y ∈ S, |y - x| < δ → |f y - f x| < ε / 2 := by
  intro x hx
  choose δ δpos hδ using hf x (ε / 2) (by bound)
  use δ, δpos
  intro y hy hxy
  apply hδ y hxy
choose δs δspos hδs using h1
let ι : Type := S
let xs : ι → ℝ := fun i ↦ i
let δ's : ι → ℝ := fun i ↦ (δs (xs i) i.2 / 2)
have δ'spos : ∀ i, 0 < δ's i := by
  intro i
  change 0 < δs (xs i) i.2 / 2
  linarith [δspos i.1 i.2]
have hScover : S ⊆ ⋃ i, Ball (xs i) (δ's i) := by
  intro x hx
  rewrite [mem_Union]
  use ⟨x, hx⟩
  change x ∈ Ioo (x - (δs x hx) / 2) (x + (δs x hx) / 2)
  rewrite [Set.mem_Ioo]
  split_ands
  linarith [(δspos x hx)]
  linarith [(δspos x hx)]
choose V hV using hS ι xs δ's δ'spos hScover
choose δ δpos hδ using FinMinPos ι V δ's δ'spos
use δ, δpos
intro x hx y hy hxy
have hx1 := hV hx
have hx1' : ∃ i ∈ V, x ∈ Ball (xs i) (δ's i) := by
  sorry
choose i i_in_V x_in_Ball using hx1'
have hxxi : |x - xs i| < (δs (xs i) i.2) / 2 := by
  sorry
have hxxi' : |x - xs i| < (δs (xs i) i.2) := by
  sorry
have hxy' : |y - x| < (δs i i.2) / 2 := by
  sorry
have hyxi : |y - xs i| < (δs i i.2) := by
  rewrite [show y - xs i = (y - x) + (x - xs i) by ring_nf]
  have h1 : |(y - x) + (x - xs i)| ≤ |y - x| + |x - xs i| := by apply abs_add_le
  have h2 : |x - xs i| = |xs i - x| := by apply abs_sub_comm
  linarith [hxy', hxxi, h1, h2]
have fyfxi := hδs (xs i) i.2 y hy hyxi
have fxix := hδs (xs i) i.2 x hx hxxi'
rewrite [show f y - f x = (f y - f (xs i)) + (f (xs i) - f x) by ring_nf]
have h1 : |(f y - f (xs i)) + (f (xs i) - f x)| ≤ |f y - f (xs i)| + |f (xs i) - f x| := by apply abs_add_le
rewrite [show |f (xs i) - f x| = |f x - f (xs i)| by apply abs_sub_comm] at h1
linarith [fyfxi, fxix, h1]

end RealAnalysisGame


Conclusion "
# The Grand Synthesis!

You've just completed one of the most beautiful proofs in mathematics! You've shown that **continuity + compactness = uniform continuity**.

**What Makes This Proof Extraordinary**:
- **Local to Global**: You started with local information (continuity at each point) and used compactness to extract global information (uniform continuity everywhere)
- **Infinite to Finite**: The proof converts an infinite covering problem into a finite one, where you can actually compute minima
- **Abstract to Concrete**: You used the abstract concept of compactness to solve the concrete problem of finding a uniform δ

**The Complete Picture**: Combining all three levels, you've now proved the fundamental chain:

`Continuous on [a,b] → Uniformly Continuous on [a,b] → Integrable on [a,b]`

**Why This Matters Historically**:
- **Riemann** (1850s) defined integration but couldn't rigorously prove when it worked
- **Cauchy** earlier made errors by missing the uniformity requirement
- **Heine-Borel** (1890s-1900s) finally clarified compactness
- **Lebesgue** (1900s) built on these foundations for modern integration theory

**The Topological Revolution**: Before topology, mathematicians did analysis with intuition and clever tricks. Compactness gave them the 'right' framework to make rigorous arguments. This is why closed bounded intervals `[a,b]` are so special in calculus - they're exactly the compact sets in `ℝ`!

**Real-World Impact**: Every time you compute `∫₀¹ f(x)dx` in calculus and trust that it exists, you're using today's theorem. Every continuous function on `[0,1]` is integrable because `[0,1]` is compact!

**Looking Forward**: You've seen how topology (compactness) illuminates analysis (integration). This pattern repeats throughout mathematics - the 'right' abstract framework often makes concrete problems much clearer. Welcome to the power of mathematical abstraction!
"
