-- stamp r7 2026-11-03
import ContractDesignPolymatroids.Convex.Model

/-!
# Convex costs: transcendental best responses and a transcendental optimal share

The example at the start of the STOC version's Appendix D.3 (`app:convex`,
`stoc-sections/appF-convex.tex:3-7`): "For convex costs in general, the best responses and an
optimal contract share can be transcendental, as the following example shows." Section 3 refers to
it ("even a single best response or the share of an optimal contract can be transcendental
(`app:convex`)", 05-best-response.tex:6), as do Section 5.2 ("exact best responses can be
transcendental (`app:convex`)", 08c-convex.tex:3) and the introduction ("Exact best responses may be
transcendental", 01-introduction.tex:26). The example has one element `e` (vectors over `Unit`, the
polymatroid `oneF 3` with `f({e}) = 3`) and `m_e = 1`, so `r(x) = x_e`, and it is an instance of
the setting of `thm:convexfptas` (`setting_exp`).

* "Take one element with `f({e}) = 3`, `m_e = 1`, and `c(x) = (exp(x) − 1)/8`" (`expCost`). "The
  agent maximizes the strictly concave function `αx − (exp(x) − 1)/8` over `[0, 3]`, whose
  derivative is `α − exp(x)/8`" (`expObj`, `expObj_strictConcaveOn`, `hasDerivAt_expObj`). "As
  `ln(8α) ∈ [0, ln 8] ⊆ [0, 3]` for `α ∈ [1/8, 1]`" (`log_eight_le_three`), "this gives"
  `x*(α) = 0` for `α < 1/8` and `x*(α) = ln(8α)` for `1/8 ≤ α ≤ 1` (`exp_isBR_iff_low`,
  `exp_isBR_iff`; a strictly concave function is largest where its derivative vanishes,
  `lt_of_strictConcaveOn`). "So `U_P = 0` on `[0, 1/8]` and at `1`, and `U_P(α) = (1 − α) ln(8α)` is
  strictly concave on `[1/8, 1]`" (`exp_profit`, `exp_profit_zero`, `exp_strictConcaveOn`), "with
  derivative zero where `(1 − α)/α = ln(8α)`, that is, `8α = exp(1/α − 1)`" (`hasDerivAt_expShape`,
  `expDeriv_eq_zero_iff`). "This solution is the optimal contract `α* ≈ 0.4419`" (`exp_optimal`:
  the maximum of `U_P`, which exists, `expShape_exists_isMaxOn`, is interior, the derivative
  vanishes there, no other share is optimal, and `0.4419 < α* < 0.44195`, `exp_optimal_approx`,
  bounds that the paper does not give). "If `α*` were algebraic, then `1/α* − 1 ≠ 0` would be
  algebraic, and `exp(1/α* − 1) = 8α*` would be transcendental by the Lindemann–Weierstrass theorem,
  a contradiction" (`exp_optimal_transcendental`, `exp_optimal_share_transcendental`), and "In the
  same way, `x*(α) = ln(8α)` is transcendental for every algebraic `α ∈ (1/8, 1]`"
  (`exp_response_transcendental`). The theorem enters in the form of Hermite and Lindemann
  (`HermiteLindemann`: `exp(q)` is transcendental for every algebraic `q ≠ 0`), which Mathlib does
  not contain, as a hypothesis.

Taken over on 2026-10-20 from `Research/S14/Examples.lean` (series 14) for the STOC version
(`stoc.tex`); from then on this copy follows the STOC version. Max Klimm's final version (429ca68)
dropped the examples of `app:convex`, and this file kept the first one, marked "not in the paper";
Philipp Warode's fixes of the findings (1865a3c) brought it back at the start of `app:convex`. The
second example of the earlier version (`δ`-optimal responses near a jump of the reward) has no claim
in the paper and stays deleted.
-/

namespace Stoc.Convex

open Set

/-- With a unique best response `y` at `α`, `r(x*(α)) = r(y)`. -/
lemma Setting.S_eq_of_unique {E : Type*} [Fintype E] {P : Set (E → ℝ)} {m : E → ℝ}
    {c : (E → ℝ) → ℝ} {rb : ℝ} (h : Setting P m c rb) {α : ℝ} {y : E → ℝ}
    (huniq : ∀ z, IsBR P m c α z → z = y) : S P m c α = reward m y := by
  obtain ⟨z, hz, hzS⟩ := h.exists_favourable α
  rw [← hzS, huniq z hz]

lemma sum_unit (F : Unit → ℝ) : ∑ e, F e = F () := by simp

/-- A function that is strictly concave on a set `S ⊆ ℝ` and has the derivative `d` at a point
`x₀ ∈ S` is smaller than at `x₀` at every point `y ∈ S` with `y > x₀` if `d ≤ 0`, and at every
point `y ∈ S` with `y < x₀` if `d ≥ 0`; so for `d = 0`, `x₀` is its only maximizer on `S` (the
example uses this without proof). -/
lemma lt_of_strictConcaveOn {S : Set ℝ} {φ : ℝ → ℝ} (hφ : StrictConcaveOn ℝ S φ) {x₀ d : ℝ}
    (hx₀ : x₀ ∈ S) (hd : HasDerivAt φ d x₀) {y : ℝ} (hy : y ∈ S) :
    (x₀ < y → d ≤ 0 → φ y < φ x₀) ∧ (y < x₀ → 0 ≤ d → φ y < φ x₀) := by
  refine ⟨fun hlt hd0 => ?_, fun hlt hd0 => ?_⟩
  · -- the slope from `x₀` to `y` is smaller than `d ≤ 0`
    have h := hφ.slope_lt_of_hasDerivAt hx₀ hy hlt hd
    rw [slope_def_field, div_lt_iff₀ (sub_pos.2 hlt)] at h
    nlinarith
  · -- the slope from `y` to `x₀` is larger than `d ≥ 0`
    have h := hφ.lt_slope_of_hasDerivAt hy hx₀ hlt hd
    rw [slope_def_field, lt_div_iff₀ (sub_pos.2 hlt)] at h
    nlinarith

/-! ### The example: the exponential cost -/

section Exp

/-- The cost `c(x) = (exp(x) − 1)/8` of one element with `f({e}) = 3` (the example: "Take one
element with `f({e}) = 3`, `m_e = 1`, and `c(x) = (exp(x) − 1)/8`"). -/
noncomputable def expCost (x : Unit → ℝ) : ℝ :=
  (Real.exp (x ()) - 1) / 8

/-- The example lies in the setting of `thm:convexfptas`, with the reward of success `r̄ = 3` (the
choice `r̄ = ∑_e m_e f({e})` of the footnote of 02-preliminaries.tex:12, `rbar_oneF`), the
subgradient `g(x) = exp(x)/8` and the bound `G = exp(3)/8` (the example leaves this implicit). -/
lemma setting_exp :
    PolySetting (oneF 3) 1 expCost (fun x _ => Real.exp (x ()) / 8) (Real.exp 3 / 8) 3 where
  rank := isRankFunction_oneF (by norm_num)
  m_nonneg _ := zero_le_one
  rbar_pos := by norm_num
  reward_le x hx := (reward_le_rbar (fun _ => zero_le_one) hx).trans_eq (rbar_oneF 3)
  cost := ⟨fun x hx => by
      have := Real.one_le_exp (hx ())
      unfold expCost
      linarith, by simp [expCost]⟩
  convexOn := ⟨convex_indepPoly _, fun x _ y _ a b ha hb hab => by
    have := convexOn_exp.2 (mem_univ (x ())) (mem_univ (y ())) ha hb hab
    simp only [smul_eq_mul] at this
    simp only [expCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : a * ((Real.exp (x ()) - 1) / 8) + b * ((Real.exp (y ()) - 1) / 8) =
        (a * Real.exp (x ()) + b * Real.exp (y ()) - 1) / 8 := by
      linear_combination (-1 / 8 : ℝ) * hab
    rw [e]
    linarith⟩
  subgrad x _ y _ := by
    have h1 := Real.add_one_le_exp (y () - x ())
    have h2 : Real.exp (y ()) = Real.exp (x ()) * Real.exp (y () - x ()) := by
      rw [← Real.exp_add]; ring_nf
    rw [sum_unit]
    unfold expCost
    rw [h2]
    nlinarith [Real.exp_pos (x ())]
  bound x hx _ := by
    rw [abs_of_pos (by positivity)]
    have := (mem_indepPoly_oneF.1 hx).2
    gcongr

/-- The function `αx − (exp(x) − 1)/8` that the agent maximizes over `[0, 3]` (the example). -/
noncomputable def expObj (α x : ℝ) : ℝ := α * x - (Real.exp x - 1) / 8

/-- The agent's utility is `U_A(x | α) = αx_e − (exp(x_e) − 1)/8`. -/
lemma util_exp (α : ℝ) (x : Unit → ℝ) : util 1 expCost α x = expObj α (x ()) := by
  rw [util, reward_one_unit, expCost, expObj]

/-- The example: the function `αx − (exp(x) − 1)/8`, "whose derivative is `α − exp(x)/8`". -/
lemma hasDerivAt_expObj (α x : ℝ) : HasDerivAt (expObj α) (α - Real.exp x / 8) x := by
  have h1 : HasDerivAt (fun x : ℝ => α * x) α x := by
    simpa using (hasDerivAt_id x).const_mul α
  have h2 : HasDerivAt (fun x : ℝ => (Real.exp x - 1) / 8) (Real.exp x / 8) x :=
    ((Real.hasDerivAt_exp x).sub_const 1).div_const 8
  exact h1.sub h2

/-- The example: "the strictly concave function `αx − (exp(x) − 1)/8`" on `[0, 3]` (the example
asserts the strict concavity; the derivative `α − exp(x)/8` is strictly decreasing). -/
lemma expObj_strictConcaveOn (α : ℝ) : StrictConcaveOn ℝ (Icc 0 3) (expObj α) := by
  have hd : deriv (expObj α) = fun x => α - Real.exp x / 8 :=
    funext fun x => (hasDerivAt_expObj α x).deriv
  refine (StrictAnti.strictConcaveOn_univ_of_deriv ?_ ?_).subset (subset_univ _) (convex_Icc 0 3)
  · exact continuous_iff_continuousAt.2 fun x => (hasDerivAt_expObj α x).continuousAt
  · rw [hd]
    intro a b hab
    show α - Real.exp b / 8 < α - Real.exp a / 8
    have := Real.exp_lt_exp.2 hab
    linarith

/-- `ln 8 ≤ 3`, so that "`ln(8α) ∈ [0, ln 8] ⊆ [0, 3]` for `α ∈ [1/8, 1]`" (the example uses
`ln 8 ≤ 3` without proof). -/
lemma log_eight_le_three : Real.log 8 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)
  linarith

/-- The example, its display for `1/8 ≤ α ≤ 1`: "The agent maximizes the strictly concave
function `αx − (exp(x) − 1)/8` over `[0, 3]`, whose derivative is `α − exp(x)/8`. As
`ln(8α) ∈ [0, ln 8] ⊆ [0, 3]` for `α ∈ [1/8, 1]`, this gives" `x*(α) = ln(8α)`: the derivative
vanishes at `ln(8α) ∈ [0, 3]`, so by the strict concavity `ln(8α)` is the only maximizer over
`[0, 3]`, the only best response (`lt_of_strictConcaveOn`). -/
theorem exp_isBR_iff {α : ℝ} (hα : α ∈ Icc (1 / 8 : ℝ) 1) (y : Unit → ℝ) :
    IsBR (indepPoly (oneF 3)) 1 expCost α y ↔ y = fun _ => Real.log (8 * α) := by
  -- "As `ln(8α) ∈ [0, ln 8] ⊆ [0, 3]` for `α ∈ [1/8, 1]`,"
  have h8 : 1 ≤ 8 * α := by linarith [hα.1]
  set x₀ := Real.log (8 * α) with hx₀
  have hx₀I : x₀ ∈ Icc (0 : ℝ) 3 := ⟨Real.log_nonneg h8,
    (Real.log_le_log (by linarith) (by linarith [hα.2])).trans log_eight_le_three⟩
  -- the derivative `α − exp(x)/8` vanishes at `x₀ = ln(8α)`
  have hd : HasDerivAt (expObj α) 0 x₀ := by
    have h := hasDerivAt_expObj α x₀
    rwa [hx₀, Real.exp_log (by linarith), show α - 8 * α / 8 = 0 by ring] at h
  -- "this gives `x*(α) = ln(8α)`": by the strict concavity, `x₀` is the only maximizer over
  -- `[0, 3]`
  have hlt : ∀ z ∈ Icc (0 : ℝ) 3, z ≠ x₀ → expObj α z < expObj α x₀ := fun z hz hne => by
    have h := lt_of_strictConcaveOn (expObj_strictConcaveOn α) hx₀I hd hz
    rcases hne.lt_or_gt with hzx | hzx
    · exact h.2 hzx le_rfl
    · exact h.1 hzx le_rfl
  have hmem : (fun _ => x₀ : Unit → ℝ) ∈ indepPoly (oneF 3) := mem_indepPoly_oneF.2 hx₀I
  constructor
  · intro hy
    funext u
    by_contra hne
    have := hy.2 _ hmem
    rw [util_exp, util_exp] at this
    exact absurd this (not_le.2 (hlt (y ()) (mem_indepPoly_oneF.1 hy.1) hne))
  · rintro rfl
    refine ⟨hmem, fun z hz => ?_⟩
    rw [util_exp, util_exp]
    rcases eq_or_ne (z ()) x₀ with h | h
    · rw [h]
    · exact (hlt (z ()) (mem_indepPoly_oneF.1 hz) h).le

/-- The example, its display for `α < 1/8`: "this gives" `x*(α) = 0`: the derivative
`α − exp(x)/8` is `α − 1/8 < 0` at `0`, so by the strict concavity `0` is the only maximizer over
`[0, 3]`, the only best response (`lt_of_strictConcaveOn`). -/
theorem exp_isBR_iff_low {α : ℝ} (hα : α < 1 / 8) (y : Unit → ℝ) :
    IsBR (indepPoly (oneF 3)) 1 expCost α y ↔ y = 0 := by
  -- the derivative `α − exp(x)/8` is `α − 1/8 < 0` at `0`
  have hd : HasDerivAt (expObj α) (α - 1 / 8) 0 := by
    simpa using hasDerivAt_expObj α 0
  -- "this gives `x*(α) = 0`": by the strict concavity, `0` is the only maximizer over `[0, 3]`
  have hlt : ∀ z ∈ Icc (0 : ℝ) 3, z ≠ 0 → expObj α z < expObj α 0 := fun z hz hne =>
    (lt_of_strictConcaveOn (expObj_strictConcaveOn α) ⟨le_rfl, by norm_num⟩ hd hz).1
      (lt_of_le_of_ne hz.1 (Ne.symm hne)) (by linarith)
  have hmem : (0 : Unit → ℝ) ∈ indepPoly (oneF 3) :=
    zero_mem_indepPoly (isRankFunction_oneF (by norm_num))
  constructor
  · intro hy
    funext u
    by_contra hne
    have := hy.2 _ hmem
    rw [util_exp, util_exp] at this
    exact absurd this (not_le.2 (hlt (y ()) (mem_indepPoly_oneF.1 hy.1) hne))
  · rintro rfl
    refine ⟨hmem, fun z hz => ?_⟩
    rw [util_exp, util_exp]
    rcases eq_or_ne (z ()) 0 with h | h
    · rw [h]
      rfl
    · exact (hlt (z ()) (mem_indepPoly_oneF.1 hz) h).le

/-- The example: "So `U_P = 0` on `[0, 1/8]` and at `1`, and `U_P(α) = (1 − α) ln(8α)`" on
`[1/8, 1]` (at `α = 1/8` both give `0`), by the display (`exp_isBR_iff_low`, `exp_isBR_iff`). -/
theorem exp_profit {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    profit (indepPoly (oneF 3)) 1 expCost α =
      if α < 1 / 8 then 0 else (1 - α) * Real.log (8 * α) := by
  split_ifs with hlt
  · rw [profit, setting_exp.toSetting.S_eq_of_unique (y := 0)
      fun z hz => (exp_isBR_iff_low hlt z).1 hz, reward_one_unit]
    simp
  · rw [profit, setting_exp.toSetting.S_eq_of_unique (y := fun _ => Real.log (8 * α))
      fun z hz => (exp_isBR_iff ⟨not_lt.1 hlt, hα.2⟩ z).1 hz, reward_one_unit]

/-- The example: "So `U_P = 0` on `[0, 1/8]` and at `1`". -/
theorem exp_profit_zero : (∀ α ∈ Icc (0 : ℝ) (1 / 8), profit (indepPoly (oneF 3)) 1 expCost α = 0) ∧
    profit (indepPoly (oneF 3)) 1 expCost 1 = 0 := by
  refine ⟨fun α hα => ?_, by simp [profit]⟩
  rw [exp_profit ⟨hα.1, by linarith [hα.2]⟩]
  split_ifs with hlt
  · rfl
  · rw [show α = 1 / 8 by linarith [hα.2, not_lt.1 hlt]]
    norm_num

/-- `U_P(α) = (1 − α) ln(8α)` on `[1/8, 1]`, as a function of `α`. -/
noncomputable def expShape (α : ℝ) : ℝ := (1 - α) * Real.log (8 * α)

/-- Its derivative `(1 − α)/α − ln(8α)`. -/
noncomputable def expDeriv (α : ℝ) : ℝ := (1 - α) / α - Real.log (8 * α)

/-- The example: the derivative of `U_P(α) = (1 − α) ln(8α)`, `(1 − α)/α − ln(8α)` for `α > 0`. -/
lemma hasDerivAt_expShape {α : ℝ} (hα : 0 < α) : HasDerivAt expShape (expDeriv α) α := by
  have h1 : HasDerivAt (fun α : ℝ => 1 - α) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub 1
  have h2 : HasDerivAt (fun α : ℝ => Real.log (8 * α)) (1 / α) α := by
    have h3 : HasDerivAt (fun α : ℝ => 8 * α) 8 α := by
      simpa using (hasDerivAt_id α).const_mul 8
    convert h3.log (by positivity) using 1
    field_simp
  show HasDerivAt (fun α : ℝ => (1 - α) * Real.log (8 * α)) (expDeriv α) α
  convert h1.mul h2 using 1
  unfold expDeriv
  field_simp
  ring

/-- The derivative `(1 − α)/α − ln(8α)` is strictly decreasing on `(0, ∞)` (the example asserts
the strict concavity without proof). -/
lemma expDeriv_strictAntiOn : StrictAntiOn expDeriv (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have h1 : (1 - b) / b < (1 - a) / a := by
    rw [div_lt_div_iff₀ hb' ha']
    nlinarith
  have h2 : Real.log (8 * a) < Real.log (8 * b) := Real.log_lt_log (by positivity) (by linarith)
  unfold expDeriv
  linarith

/-- The example: "`U_P(α) = (1 − α) ln(8α)` is strictly concave on `[1/8, 1]`", as its derivative
is strictly decreasing. -/
theorem exp_strictConcaveOn : StrictConcaveOn ℝ (Icc (1 / 8 : ℝ) 1) expShape := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _)
    (fun α hα => (hasDerivAt_expShape (by linarith [hα.1])).continuousAt.continuousWithinAt) ?_
  intro a ha b hb hab
  rw [interior_Icc] at ha hb
  have ha0 : (0 : ℝ) < a := by linarith [ha.1]
  have hb0 : (0 : ℝ) < b := by linarith [hb.1]
  rw [(hasDerivAt_expShape ha0).deriv, (hasDerivAt_expShape hb0).deriv]
  exact expDeriv_strictAntiOn ha0 hb0 hab

/-- The example: the derivative is zero "where `(1 − α)/α = ln(8α)`, that is, `8α = exp(1/α − 1)`"
(for `α > 0`). -/
theorem expDeriv_eq_zero_iff {α : ℝ} (hα : 0 < α) :
    expDeriv α = 0 ↔ 8 * α = Real.exp (1 / α - 1) := by
  have e : (1 - α) / α = 1 / α - 1 := by field_simp
  unfold expDeriv
  rw [sub_eq_zero, e]
  constructor
  · intro h
    rw [h, Real.exp_log (by positivity)]
  · intro h
    rw [h, Real.log_exp]

/-- `U_P(α) = (1 − α) ln(8α)` attains its maximum over `[1/8, 1]` (the example leaves implicit that
the maximum exists, as `(1 − α) ln(8α)` is continuous on the compact interval `[1/8, 1]`). -/
lemma expShape_exists_isMaxOn : ∃ αs ∈ Icc (1 / 8 : ℝ) 1, IsMaxOn expShape (Icc (1 / 8) 1) αs :=
  isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by norm_num)) fun α hα =>
    (hasDerivAt_expShape (by linarith [hα.1])).continuousAt.continuousWithinAt

/-- The derivative is positive exactly where `8α < exp(1/α − 1)` (not in the paper: only the
bounds of `exp_optimal_approx` use it). -/
lemma expDeriv_pos_iff {α : ℝ} (hα : 0 < α) : 0 < expDeriv α ↔ 8 * α < Real.exp (1 / α - 1) := by
  have e : (1 - α) / α = 1 / α - 1 := by field_simp
  unfold expDeriv
  rw [e, sub_pos, Real.log_lt_iff_lt_exp (by positivity)]

/-- The derivative is negative exactly where `exp(1/α − 1) < 8α` (not in the paper: only the
bounds of `exp_optimal_approx` use it). -/
lemma expDeriv_neg_iff {α : ℝ} (hα : 0 < α) : expDeriv α < 0 ↔ Real.exp (1 / α - 1) < 8 * α := by
  have e : (1 - α) / α = 1 / α - 1 := by field_simp
  unfold expDeriv
  rw [e, sub_neg, Real.lt_log_iff_exp_lt (by positivity)]

/-- `8α < exp(1/α − 1)` at `α = 0.4419`: `exp(1 + 1162/4419) > 3.5352`, from `e > 2.7182818283` and
`exp(x) ≥ 1 + x + x²/2 + x³/6 + x⁴/24` for `x ≥ 0` (not in the paper: it states `α* ≈ 0.4419`
without proof). -/
lemma exp_lower_4419 : 8 * (4419 / 10000 : ℝ) < Real.exp (1 / (4419 / 10000) - 1) := by
  have h1 : (1 : ℝ) / (4419 / 10000) - 1 = 1 + 1162 / 4419 := by norm_num
  rw [h1, Real.exp_add]
  have he := Real.exp_one_gt_d9
  set x : ℝ := 1162 / 4419 with hx
  have hx0 : 0 ≤ x := by norm_num [hx]
  -- `exp(x) ≥ 1 + x + x²/2 + x³/6 + x⁴/24`
  have hq : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ Real.exp x := by
    have := Real.sum_le_exp_of_nonneg hx0 5
    simpa [Finset.sum_range_succ, Nat.factorial] using this
  have hpos : (0 : ℝ) < 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by positivity
  calc (8 : ℝ) * (4419 / 10000) < 2.7182818283 * (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24) := by
        rw [hx]; norm_num
    _ ≤ Real.exp 1 * Real.exp x := mul_le_mul he.le hq hpos.le (Real.exp_pos 1).le

/-- `exp(1/α − 1) < 8α` at `α = 0.44195`: `exp(1 + 11610/44195) < 3.5356`, from `e < 2.7182818286`
and the Taylor bound of order `5` (`Real.exp_bound'`) (not in the paper, as above). -/
lemma exp_upper_44195 : Real.exp (1 / (44195 / 100000) - 1) < 8 * (44195 / 100000 : ℝ) := by
  have h1 : (1 : ℝ) / (44195 / 100000) - 1 = 1 + 11610 / 44195 := by norm_num
  rw [h1, Real.exp_add]
  have he := Real.exp_one_lt_d9
  have hb := Real.exp_bound' (show (0 : ℝ) ≤ 11610 / 44195 by norm_num)
    (show (11610 : ℝ) / 44195 ≤ 1 by norm_num) (show 0 < 5 by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  calc Real.exp 1 * Real.exp (11610 / 44195) < 2.7182818286 * Real.exp (11610 / 44195) :=
        mul_lt_mul_of_pos_right he (Real.exp_pos _)
    _ ≤ 2.7182818286 * (1 + 11610 / 44195 + (11610 / 44195) ^ 2 / 2 + (11610 / 44195) ^ 3 / 6 +
          (11610 / 44195) ^ 4 / 24 + (11610 / 44195) ^ 5 * 6 / (120 * 5)) := by
        gcongr
        linarith
    _ < 8 * (44195 / 100000) := by norm_num

/-- "`α* ≈ 0.4419`" (appF-convex.tex:7): every solution `α > 0` of `8α = exp(1/α − 1)` satisfies
`0.4419 < α < 0.44195` (not in the paper: it states `α* ≈ 0.4419` without the bounds). The
derivative `(1 − α)/α − ln(8α)` is zero at `α` (`expDeriv_eq_zero_iff`), positive at `0.4419`
(`exp_lower_4419`), negative at `0.44195` (`exp_upper_44195`) and strictly decreasing
(`expDeriv_strictAntiOn`). -/
lemma exp_optimal_approx {α : ℝ} (hα : 0 < α) (heq : 8 * α = Real.exp (1 / α - 1)) :
    4419 / 10000 < α ∧ α < 44195 / 100000 := by
  have hzero : expDeriv α = 0 := (expDeriv_eq_zero_iff hα).2 heq
  constructor
  · -- `α > 0.4419`: the derivative is positive at `0.4419`
    by_contra hle
    push Not at hle
    have hpos : 0 < expDeriv (4419 / 10000) := (expDeriv_pos_iff (by norm_num)).2 exp_lower_4419
    rcases hle.lt_or_eq with hl | he
    · have := expDeriv_strictAntiOn (show (0 : ℝ) < α from hα)
        (show (0 : ℝ) < 4419 / 10000 by norm_num) hl
      linarith
    · rw [he] at hzero
      linarith
  · -- `α < 0.44195`: the derivative is negative at `0.44195`
    by_contra hle
    push Not at hle
    have hneg : expDeriv (44195 / 100000) < 0 :=
      (expDeriv_neg_iff (by norm_num)).2 exp_upper_44195
    rcases hle.lt_or_eq with hl | he
    · have := expDeriv_strictAntiOn (show (0 : ℝ) < 44195 / 100000 by norm_num)
        (show (0 : ℝ) < α from hα) hl
      linarith
    · rw [← he] at hzero
      linarith

/-- The example (appF-convex.tex:7): the solution of `8α = exp(1/α − 1)` "is the optimal contract
`α* ≈ 0.4419`": the example has exactly one optimal share `α*`, it lies in `(1/8, 1)`, it solves
`8α = exp(1/α − 1)`, and `0.4419 < α* < 0.44195`.

The proof is the example's: (1) "`U_P = 0` on `[0, 1/8]` and at `1`"
(`exp_profit_zero`); (2) "`U_P(α) = (1 − α) ln(8α)` is strictly concave on `[1/8, 1]`"
(`exp_profit`, `exp_strictConcaveOn`); (3) so the maximum of `U_P` is interior: it exists
(`expShape_exists_isMaxOn`), and `U_P(1/2) > 0 = U_P(1/8) = U_P(1)` by the strict concavity;
(4) the derivative vanishes there, "with derivative zero where `(1 − α)/α = ln(8α)`, that is,
`8α = exp(1/α − 1)`" (`hasDerivAt_expShape`, `expDeriv_eq_zero_iff`); (5) "This solution is the
optimal contract": as `U_P` is strictly concave on `[1/8, 1]` and `0` on `[0, 1/8]`, no other share
is optimal; (6) "`α* ≈ 0.4419`" (`exp_optimal_approx`, with bounds that the paper does not give). -/
theorem exp_optimal : ∃ αs ∈ Ioo (1 / 8 : ℝ) 1, 8 * αs = Real.exp (1 / αs - 1) ∧
    (∀ α ∈ Icc (0 : ℝ) 1, IsMaxOn (profit (indepPoly (oneF 3)) 1 expCost) (Icc 0 1) α ↔ α = αs) ∧
    4419 / 10000 < αs ∧ αs < 44195 / 100000 := by
  -- (1) "So `U_P = 0` on `[0, 1/8]` and at `1`,"
  obtain ⟨hlow, hone⟩ := exp_profit_zero
  have h18 : profit (indepPoly (oneF 3)) 1 expCost (1 / 8) = 0 := hlow _ ⟨by norm_num, le_rfl⟩
  -- (2) "and `U_P(α) = (1 − α) ln(8α)` is strictly concave on `[1/8, 1]`"
  have hshape : ∀ α ∈ Icc (1 / 8 : ℝ) 1, profit (indepPoly (oneF 3)) 1 expCost α = expShape α := by
    intro α hα
    rw [exp_profit ⟨by linarith [hα.1], hα.2⟩]
    simp only [not_lt.2 hα.1, ↓reduceIte, expShape]
  have hconc := exp_strictConcaveOn
  -- (3) so the maximum is interior: `U_P(1/2) > 0`, between the zeros `U_P(1/8) = U_P(1) = 0`
  have hhalf : 0 < expShape (1 / 2) := by
    have := hconc.2 (show (1 / 8 : ℝ) ∈ Icc (1 / 8 : ℝ) 1 by norm_num)
      (show (1 : ℝ) ∈ Icc (1 / 8 : ℝ) 1 by norm_num) (by norm_num)
      (show (0 : ℝ) < 4 / 7 by norm_num) (show (0 : ℝ) < 3 / 7 by norm_num) (by norm_num)
    rw [← hshape _ (by norm_num), ← hshape _ (by norm_num), h18, hone] at this
    norm_num at this
    exact this
  obtain ⟨αs, hαsI, hmax⟩ := expShape_exists_isMaxOn
  have hvalpos : 0 < expShape αs :=
    hhalf.trans_le (hmax (show (1 / 2 : ℝ) ∈ Icc (1 / 8 : ℝ) 1 by norm_num))
  have hαs : αs ∈ Ioo (1 / 8 : ℝ) 1 := by
    refine ⟨hαsI.1.lt_of_ne fun he => ?_, hαsI.2.lt_of_ne fun he => ?_⟩
    · rw [← he, ← hshape _ (by norm_num), h18] at hvalpos
      exact lt_irrefl _ hvalpos
    · rw [he, ← hshape _ (by norm_num), hone] at hvalpos
      exact lt_irrefl _ hvalpos
  have hαs0 : 0 < αs := lt_trans (by norm_num) hαs.1
  -- (4) "with derivative zero where `(1 − α)/α = ln(8α)`, that is, `8α = exp(1/α − 1)`."
  have hzero : expDeriv αs = 0 :=
    (hmax.isLocalMax (Icc_mem_nhds hαs.1 hαs.2)).hasDerivAt_eq_zero (hasDerivAt_expShape hαs0)
  have heq : 8 * αs = Real.exp (1 / αs - 1) := (expDeriv_eq_zero_iff hαs0).1 hzero
  -- (5) "This solution is the optimal contract": `U_P = 0 < U_P(α*)` on `[0, 1/8]`, and on
  -- `[1/8, 1]` the strictly concave `U_P` has at most one maximizer
  have hαsmax : IsMaxOn (profit (indepPoly (oneF 3)) 1 expCost) (Icc 0 1) αs := by
    refine isMaxOn_iff.2 fun β hβ => ?_
    rw [hshape αs hαsI]
    rcases le_total β (1 / 8) with hb | hb
    · rw [hlow β ⟨hβ.1, hb⟩]
      exact hvalpos.le
    · rw [hshape β ⟨hb, hβ.2⟩]
      exact hmax ⟨hb, hβ.2⟩
  -- (6) "`α* ≈ 0.4419`" (`exp_optimal_approx`); the two goals left are the rest of (5): every
  -- optimal share is `α*`, by the strict concavity, and `α*` is optimal
  refine ⟨αs, hαs, heq, fun α hα => ⟨fun hαmax => ?_, ?_⟩, exp_optimal_approx hαs0 heq⟩
  · have hle := isMaxOn_iff.1 hαmax αs ⟨hαs0.le, hαsI.2⟩
    rw [hshape αs hαsI] at hle
    have hα8 : 1 / 8 ≤ α := by
      by_contra hlt
      rw [hlow α ⟨hα.1, (not_le.1 hlt).le⟩] at hle
      linarith
    have hαI : α ∈ Icc (1 / 8 : ℝ) 1 := ⟨hα8, hα.2⟩
    refine hconc.eq_of_isMaxOn (isMaxOn_iff.2 fun β hβ => ?_) hmax hαI hαsI
    rw [← hshape β hβ, ← hshape α hαI]
    exact isMaxOn_iff.1 hαmax β ⟨by linarith [hβ.1], hβ.2⟩
  · rintro rfl
    exact hαsmax

/-- The Hermite–Lindemann theorem: `exp(q)` is transcendental for every algebraic `q ≠ 0`, the case
of the Lindemann–Weierstrass theorem that the example uses. Mathlib contains only the analytic part
of the Lindemann–Weierstrass theorem, so it enters as a hypothesis. -/
def HermiteLindemann : Prop :=
  ∀ q : ℝ, IsAlgebraic ℚ q → q ≠ 0 → Transcendental ℚ (Real.exp q)

/-- The example: "If `α*` were algebraic, then `1/α* − 1 ≠ 0` would be algebraic, and
`exp(1/α* − 1) = 8α*` would be transcendental by the Lindemann–Weierstrass theorem, a
contradiction" (for every solution `α* ∈ (1/8, 1)` of `8α = exp(1/α − 1)`). -/
theorem exp_optimal_transcendental (hHL : HermiteLindemann) {αs : ℝ}
    (hαs : αs ∈ Ioo (1 / 8 : ℝ) 1) (heq : 8 * αs = Real.exp (1 / αs - 1)) :
    Transcendental ℚ αs := by
  intro halg
  have hq : IsAlgebraic ℚ (1 / αs - 1) := by
    rw [one_div]
    exact halg.inv.sub isAlgebraic_one
  have hq0 : 1 / αs - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, one_div, inv_eq_one]
    exact hαs.2.ne
  have h8 : IsAlgebraic ℚ (8 * αs) := by
    have : IsAlgebraic ℚ ((8 : ℝ)) := by
      have := isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 8
      simpa using this
    exact this.mul halg
  exact hHL _ hq hq0 (heq ▸ h8)

/-- "an optimal contract share can be transcendental" (appF-convex.tex:3; 05-best-response.tex:6
cites it): in the example (given `HermiteLindemann`) there is exactly one optimal share `α*`; it
lies in `(1/8, 1)`, it solves `8α = exp(1/α − 1)`, and it is transcendental (`exp_optimal`,
`exp_optimal_transcendental`). -/
theorem exp_optimal_share_transcendental (hHL : HermiteLindemann) :
    ∃ αs ∈ Ioo (1 / 8 : ℝ) 1,
      (∀ α ∈ Icc (0 : ℝ) 1, IsMaxOn (profit (indepPoly (oneF 3)) 1 expCost) (Icc 0 1) α ↔ α = αs) ∧
      8 * αs = Real.exp (1 / αs - 1) ∧ Transcendental ℚ αs := by
  obtain ⟨αs, hαs, heq, hiff, -⟩ := exp_optimal
  exact ⟨αs, hαs, hiff, heq, exp_optimal_transcendental hHL hαs heq⟩

/-- "the best responses … can be transcendental" (appF-convex.tex:3; 08c-convex.tex:3,
05-best-response.tex:6 and 01-introduction.tex:26 cite it): in the example (given
`HermiteLindemann`), at every algebraic share `α ∈ (1/8, 1]` the only best response is
`x*(α) = ln(8α)` (`exp_isBR_iff`), and "In the same way, `x*(α) = ln(8α)` is transcendental for
every algebraic `α ∈ (1/8, 1]`": otherwise `exp(ln(8α)) = 8α` with the algebraic `ln(8α) ≠ 0` would
be transcendental. -/
theorem exp_response_transcendental (hHL : HermiteLindemann) {α : ℝ}
    (hα : α ∈ Ioc (1 / 8 : ℝ) 1) (halg : IsAlgebraic ℚ α) :
    (∀ y, IsBR (indepPoly (oneF 3)) 1 expCost α y ↔ y = fun _ => Real.log (8 * α)) ∧
      Transcendental ℚ (Real.log (8 * α)) := by
  refine ⟨exp_isBR_iff ⟨hα.1.le, hα.2⟩, fun hl => ?_⟩
  have h8 : 1 < 8 * α := by linarith [hα.1]
  have hne : Real.log (8 * α) ≠ 0 := (Real.log_pos h8).ne'
  have hexp : Real.exp (Real.log (8 * α)) = 8 * α := Real.exp_log (by linarith)
  have h8a : IsAlgebraic ℚ (8 * α) := by
    have : IsAlgebraic ℚ ((8 : ℝ)) := by
      have := isAlgebraic_algebraMap (R := ℚ) (A := ℝ) 8
      simpa using this
    exact this.mul halg
  exact hHL _ hl hne (by rw [hexp]; exact h8a)

end Exp

end Stoc.Convex
