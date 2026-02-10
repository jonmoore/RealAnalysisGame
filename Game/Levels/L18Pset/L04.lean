import Game.Levels.L18Pset.L03
open Finset

World "L18Pset"
Level 4
Title "CoherenceOfReals"
Introduction "
# Level 4: `CoherenceOfReals`

Prove `CoherenceOfReals`:

"

DisabledTheorem CoherenceOfReals

/-- Prove `CoherenceOfReals`
-/
Statement {a b : ℕ → ℝ} {L M : ℝ} (ha : SeqLim a L) (hb : SeqLim b M) (hab : SeqLim (fun n ↦ a n - b n) 0) : L = M := by
by_contra h
let ε := |L - M|
have εIs : ε = |L - M| := by rfl
have hε : 0 < ε := by apply abs_pos_of_nonzero (by bound)
choose N1 hN1 using ha (ε/3) (by bound)
choose N2 hN2 using hb (ε/3) (by bound)
choose N3 hN3 using hab (ε/3) (by bound)
let n := N1 + N2 + N3
have nIs : n = N1 + N2 + N3 := by bound
specialize hN1 n (by bound)
specialize hN2 n (by bound)
specialize hN3 n (by bound)
ring_nf at hN3
have f1 : |L - M| = |(L - a n) + ((a n - b n) + (b n - M))| := by ring_nf
have f2 : |(L - a n) + ((a n - b n) + (b n - M))| ≤ |(L - a n)| + |((a n - b n) + (b n - M))| := by apply abs_add_le
have f3 : |((a n - b n) + (b n - M))| ≤ |(a n - b n)| + |(b n - M)| := by apply abs_add_le
have f4 : |(L - a n)| = |a n - L| := by apply abs_sub_comm
linarith[ f1, f2, f3,f4, hN1, hN2, hN3]


Conclusion "
"
