import Game.Levels.L24Levels.L01

open Set

World "Lecture24"
Level 2
Title "Heine-Borel Theorem: Part 1b"
Introduction "
# Level 2: Heine-Borel Theorem: Part 1b

**The Goal**: Complete the first direction of Heine-Borel by proving that every compact set is closed.

**New Topology Vocabulary**:
- **Open Set**: `IsOpen S := ∀ x ∈ S, ∃ δ > 0, Ball x δ ⊆ S`
  - Translation: \"Around every point in `S`, there's a whole ball that stays inside `S`\"
  - Think: \"No boundary points belong to the set\"
- **Closed Set**: `IsClosed S := IsOpen Sᶜ`
  - Translation: \"The complement is open\"
  - Think: \"All boundary points belong to the set\"

**The Challenge**: To prove `S` is closed, we need to prove `Sᶜ` is open. That means: for any point `y ∉ S`, we need to find a ball around `y` that stays completely outside `S`.

**The Strategy - Separation by Compactness**:
1. **Local Separation**: For each point `x ∈ S`, the distance `|y - x|` is positive (since `y ∉ S`). Create a ball around `x` of radius `|y - x|/2` - this ball contains `x` but can't reach `y`.

2. **Covering**: These balls cover `S`, so by compactness, finitely many suffice.

3. **Uniform Separation**: Take the minimum of the finitely many separating distances. This gives you a uniform `δ > 0` such that `Ball(y, δ)` stays away from all of `S`.

**Why This Works**: You're using compactness to convert \"local separation\" (each point in `S` is some positive distance from `y`) into \"uniform separation\" (there's a single `δ` that works everywhere).

**Your Mission**: Formalize this separation argument to show that `Sᶜ` is open!
"

namespace RealAnalysisGame

def IsOpen (S : Set ℝ) : Prop := ∀ x ∈ S, ∃ r > 0, Ball x r ⊆ S

/-- `(S : Set ℝ) : Prop := ∀ x ∈ S, ∃ r > 0, Ball x r ⊆ S`

A set is open if for every point `x` in the set, there exists a radius `r > 0` such that the ball of radius `r` centered at `x` is entirely contained within the set.
-/
DefinitionDoc IsOpen as "IsOpen"

def IsClosed (S : Set ℝ) : Prop := IsOpen Sᶜ

/-- `(S : Set ℝ) : Prop := IsOpen Sᶜ`

A set is closed if its complement is open.
-/
DefinitionDoc IsClosed as "IsClosed"

NewDefinition IsClosed IsOpen

/--
A compact set is closed.
-/
TheoremDoc RealAnalysisGame.IsClosed_of_Compact as "IsClosed_of_Compact" in "x∈U"

Statement IsClosed_of_Compact (S : Set ℝ) (hcomp : IsCompact S) : IsClosed S := by
by_cases Snonempty : S.Nonempty
change IsOpen Sᶜ
intro y hy
change y ∉ S at hy
let ι : Type := S
let xs : ι → ℝ := fun x => x.1
let δs : ι → ℝ := fun x => |y - x.1| / 2
have δspos : ∀ i : ι, δs i > 0 := by
  intro i
  let x : ℝ := i.1
  have hx : x ∈ S := i.2
  have hneq : y ≠ x := by
    intro h
    rw [h] at hy
    contradiction
  have hneq' : y - x ≠ 0 := by bound
  have hdist : |y - x| > 0 := by apply abs_pos_of_nonzero hneq'
  bound
have hcover : S ⊆ ⋃ i : ι, Ball (xs i) (δs i) := by
  intro x hx
  rewrite [mem_Union]
  use ⟨x, hx⟩
  change x ∈ Ioo _ _
  rewrite [mem_Ioo]
  specialize δspos ⟨x, hx⟩
  split_ands
  change x - _ < x
  linarith [δspos]
  change x < x + _
  linarith [δspos]
specialize hcomp ι xs δs δspos hcover
choose V hV using hcomp
choose r rpos hr using FinMinPos ι V δs δspos
use r, rpos
intro z hz
change z ∉ S
intro z_in_S
specialize hV z_in_S
rewrite [mem_Union] at hV
choose i ball_i i_in_V s_in_Ball using hV
change z ∈ Ioo _ _ at hz
rewrite [mem_Ioo] at hz
have hz' : |y - z| < r := by
  rewrite [abs_lt]
  split_ands
  linarith [hz.2]
  linarith [hz.1]
rewrite [mem_range] at i_in_V
choose hi hi' using i_in_V
specialize hr i hi
set ri := δs i
set xi := xs i
let ripos : 0 < ri := by apply δspos i
have hr' : r ≤ ri := by linarith [hr]
have hdist : 2 * ri ≤ |y - xi| := by
  change 2 * (|y - xi| / 2) ≤ |y - xi|
  linarith
have hz'' : |z - xi| < ri := by
  rewrite [← hi'] at s_in_Ball
  change z ∈ Ioo _ _ at s_in_Ball
  rewrite [mem_Ioo] at s_in_Ball
  rewrite [abs_lt]
  split_ands
  linarith [hr, s_in_Ball.1]
  linarith [hr, s_in_Ball.2]
have hz''' : |y - z| ≤ ri := by linarith [hz', hr]
have hiy : |y - xi| ≤ |y - z| + |z - xi| := by
  rewrite [show y - xi = (y - z) + (z - xi) by ring_nf]
  apply abs_add_le
linarith [hdist, hz'', hz''', hiy, ripos]

intro z hz
push_neg at Snonempty
use 1, (by bound)
intro z hz
change z ∉ S
rewrite [Snonempty]
intro h
contradiction

end RealAnalysisGame

Conclusion "
# Compactness ⟹ Closed and Bounded: Complete!

Excellent! You've just proved that **compact ⟹ closed**. Combined with Level 1, you've now established the full first direction of Heine-Borel:

**Compact ⟹ Closed and Bounded** ✓

**What Made This Proof Ingenious**:
- **The Separation Trick**: The key insight was using balls of radius `|y - x|/2` around points in `S`. These balls contain points of `S` but can never reach the outside point `y`.
- **Local to Uniform**: You converted the fact that `y` is separated from each individual point in `S` into uniform separation from the entire set `S`. This is compactness at its finest!
- **Finite Extraction**: Once again, compactness let you reduce an infinite problem (separation from all points in `S`) to a finite one (separation from finitely many covering balls).

**The Geometric Picture**: Imagine trying to \"push\" the outside point `y` into the compact set `S`. The proof shows this is impossible - there's always a \"safety buffer\" around `y` that keeps it separated from `S`.

**Why This Direction Is \"Easy\"**: Compactness gives you such strong control (every cover reduces to a finite subcover) that proving additional properties becomes manageable. The hard direction will be the converse!

**What's Next**: Now comes the serious work. In Level 3, you'll prove the **Least Upper Bound Property** of ℝ - every bounded set has a supremum. This fundamental property of the real numbers is what makes the converse direction possible.

**Looking Ahead**: Levels 4-5 will prove **Closed and Bounded ⟹ Compact**. This is where the real analysis gets deep, and you'll see why the completeness of ℝ matters!

The easy direction is done - now for the hard one! 🚀
"
