import Game.Levels.L7Levels.L02_SeqOfAbs
World "Lecture7"
Level 4
Title "SeqInvLim"
/-- For any real numbers `x` and `y`, we have `|x / y| = |x| / |y|`. -/
TheoremDoc abs_div as "abs_div" in "|x|"
theorem nonzero_of_abs_pos {x : ℝ} (h : 0 < |x|) : x ≠ 0 := abs_pos.mp h
/-- If `0 < |x|`, then `x ≠ 0`. -/
TheoremDoc nonzero_of_abs_pos as "nonzero_of_abs_pos" in "|x|"
NewTheorem nonzero_of_abs_pos abs_div
/-- If `a : ℕ → ℝ` converges to `L`, and `b : ℕ → ℝ` is its inverse, `b n = 1 / a n` for all `n`, then `b` converges to `1 / L`, provided `L ≠ 0`. -/
TheoremDoc InvLim as "InvLim" in "aₙ"
Statement InvLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L)
 (LneZero : L ≠ 0) (b : ℕ → ℝ) (bEqInva : ∀ n, b n = 1 / a n) :
    SeqLim b (1 / L) := by

intro ε εspos
have absLgt0: 0 < |L| := by apply abs_pos_of_nonzero LneZero
have epsL2gt0: 0 < ε * (|L| * |L|) / 2 := by bound
have _2gt0: 0 < 2 := by norm_num
have abs_flip: ∀ (p q: ℝ), |p-q| = |q-p| := by {
  intro p q
  have f2: q-p=-(p-q) := by ring_nf
  rewrite [f2]
  have f3: |-(p-q)| = |p-q| := by apply abs_neg
  rewrite [f3]; rfl
}
have hmin: ∀ (p q: ℝ), (p+q-|p-q|)/2 <= p ∧ (p+q-|p-q|)/2 <= q := by {
     intro p q
     split_ands
     have f1 : (q-p)/2 <= |q-p|/2:= by bound
     case refine_1 =>
       -- ⊢ (p + q - |p - q|) / 2 ≤ p
       rewrite [← abs_flip p q] at f1
       linarith [f1]
     case refine_2 =>
       -- ⊢ (p + q - |p - q|) / 2 ≤ q
       have f2 : (p-q)/2 <= |p-q|/2:= by bound
       linarith [f2]
}
have lemR: ∀ (x : ℝ), (x < 0 ∨ x ≥ 0) := by {
  intro x
  by_contra h
  have h1 : x < 0 := by
    by_contra h2
    have h5 : x ≥ 0 := by linarith [h2]
    apply h; right; apply h5
  apply h; left; apply h1
}
have hmin2: ∀ (p q: ℝ), (p+q-|p-q|)/2 >= p ∨ (p+q-|p-q|)/2 >= q := by {
     intro p q
     have h1 := lemR (p-q)
     cases' h1 with hp hq

     rewrite [abs_flip p q]
     have h3: |q-p| = q-p := by apply abs_of_nonneg (by bound)
     rewrite [h3]; ring_nf;
     left; bound

     have h5: |p-q| = p-q := by apply abs_of_nonneg (by bound)
     rewrite [h5]; ring_nf
     right; bound
}
have dmin: ∀ (p q: ℝ), ∃ m, m=(p+q-|p-q|)/2 := by {
  intro p q;
  use (p+q-|p-q|)/2
}
have cty: ∃ δ > 0, ∀ x, |x - L| < δ → |1/x - 1/L| < ε := by {
  choose δ hδ using dmin (ε * (|L| * |L|) / 2) (|L|/2)
  use δ
  split_ands
  -- δ > 0
  case h.refine_1 =>
    rewrite [hδ]
    have f1 := hmin2  (ε * (|L| * |L|) / 2) (|L|/2)
    cases' f1 with c1 c2
    linarith [c1, epsL2gt0]
    linarith [c2, absLgt0]
  -- ∀ x, ... x δ-near → 1/x ε-near
  case h.refine_2 =>
    intro x xnear
    have f7: δ ≤ |L| / 2 := by {
      rewrite [hδ]
      apply (hmin  (ε * (|L| * |L|) / 2) (|L|/2)).right
    }
    have f8: |x-L| < |L|/2 := by linarith [xnear, f7]
    have f9: |x| >= |L|/2 := by {
      have f10: |L-x+x| <= |L-x|+|x| := by apply abs_add
      ring_nf at f10
      rewrite [abs_flip L x] at f10
      linarith [f8, f10]
    }
    have absxgt0: 0 < |x| := by {
      linarith [f9, absLgt0]
    }
    have xneZero: x≠0 := by apply nonzero_of_abs_pos absxgt0
    field_simp
    rewrite [abs_div]
    rewrite [abs_flip L x]
    rewrite [abs_mul]
    field_simp
    have f11: δ ≤ (ε * (|L| * |L|) / 2) := by {
      rewrite [hδ]
      apply (hmin  (ε * (|L| * |L|) / 2) (|L|/2)).left
    }
    have f12: |x - L| < ε * (|L| * |L|) / 2 := by bound
    have f13: (|L|/2) * |L| * ε  <= |x| * |L| * ε := by bound
    ring_nf at f13
    linarith [f12, f13]
}
choose δ hδ using cty
have δpos := hδ.left
have hxfer := hδ.right
specialize aToL δ δpos
choose N hN using aToL
use N
intro n hn
specialize bEqInva n
rewrite [bEqInva]
specialize hN n hn
specialize hxfer (a n) hN
apply hxfer
