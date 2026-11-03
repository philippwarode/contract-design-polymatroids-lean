-- stamp r8 2026-11-03
import ContractDesignPolymatroids.Convex.Model

/-!
# Convex costs: a share bound from the welfare

The STOC version's `lem:welfare` (`stoc-sections/appF-convex.tex`:32-52, in `app:convex`):
`OPT ≤ W ≤ r̄`, and if `W > 0`, then `OPT ≥ W/(2 ln(2r̄/W))` (`welfare_lemma`), in the setting of
`prop:convexscheme` (`Setting`).

The proof is the STOC version's: "We first prove the upper bounds", from `U_P(α) ≤ W` for every
share (`V ≥ 0`); "Now we prove the lower bound", by the increments `eq:F-incr` (`incr`), whose
right-hand inequality is summed over the uniform partition `α_i = ia/N` of `[0, a]`,
`a = 1 − W/(2r̄)`, and over `[a, 1]`; the sum is a Riemann sum of `α ↦ 1/(1 − α)`
(`tendsto_riemannSum`), which tends to `ln(2r̄/W)` as `N → ∞`.
-/

namespace Stoc.Convex

open Set Filter Topology MeasureTheory

/-- The Riemann sums of a continuous function `φ` on `[0, a]` with the uniform partition into `N`
intervals and their right endpoints tend to `∫_0^a φ` as `N → ∞` (not in the paper: it uses
this without proof, "The sum is a Riemann sum of the continuous function `α ↦ 1/(1 − α)` on
`[0, a]`, so it tends to `∫_0^a dα/(1 − α)`"). -/
lemma tendsto_riemannSum {φ : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hφ : ContinuousOn φ (Icc 0 a)) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, a / N * φ ((i + 1) * a / N)) atTop
      (𝓝 (∫ x in (0 : ℝ)..a, φ x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- uniform continuity of `φ` on `[0, a]`
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hφ
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδφ⟩ := huc (ε / (a + 1)) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (a / δ)
  refine ⟨N₀ + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmesh : a / N < δ := by
    rw [div_lt_iff₀ hNpos]
    have : a / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast (show N₀ ≤ N by omega))
    rw [div_lt_iff₀ hδ] at this
    linarith
  set t : ℕ → ℝ := fun i => i * a / N with ht
  have ht_mem : ∀ i ≤ N, t i ∈ Icc 0 a := fun i hi => by
    refine ⟨by positivity, ?_⟩
    rw [ht]
    simp only
    rw [div_le_iff₀ hNpos]
    have : (i : ℝ) ≤ N := by exact_mod_cast hi
    nlinarith
  have hsub : ∀ i < N, uIcc (t i) (t (i + 1)) ⊆ Icc 0 a := fun i hi =>
    uIcc_subset_Icc (ht_mem i hi.le) (ht_mem (i + 1) hi)
  have hint : ∀ i < N, IntervalIntegrable φ volume (t i) (t (i + 1)) := fun i hi =>
    (hφ.mono (hsub i hi)).intervalIntegrable
  -- `∫_0^a φ = ∑_{i < N} ∫_{t_i}^{t_{i+1}} φ`
  have hsum : ∫ x in (0 : ℝ)..a, φ x = ∑ i ∈ Finset.range N, ∫ x in t i..t (i + 1), φ x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint]
    congr 1
    · simp [ht]
    · simp only [ht]
      field_simp
  have hlen : ∀ i, t (i + 1) - t i = a / N := fun i => by
    simp only [ht]; push_cast; ring
  -- each term differs from the integral by at most `ε/(a + 1) · a/N`
  have hterm : ∀ i ∈ Finset.range N,
      |a / N * φ ((i + 1) * a / N) - ∫ x in t i..t (i + 1), φ x| ≤ ε / (a + 1) * (a / N) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hti : t (i + 1) = (i + 1) * a / N := by simp only [ht]; push_cast; ring
    have hle : t i ≤ t (i + 1) := by linarith [hlen i, div_nonneg ha hNpos.le]
    have hconst : a / N * φ ((i + 1) * a / N) = ∫ _ in t i..t (i + 1), φ (t (i + 1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen i, hti]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint i hi')]
    have hbound : ∀ x ∈ uIoc (t i) (t (i + 1)), ‖φ (t (i + 1)) - φ x‖ ≤ ε / (a + 1) := by
      intro x hx
      rw [uIoc_of_le hle] at hx
      have hx' : x ∈ Icc 0 a := hsub i hi' (Ioc_subset_Icc_self.trans Icc_subset_uIcc hx)
      have hd : dist (t (i + 1)) x < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.2])]
        linarith [hx.1, hlen i]
      exact (hδφ _ (ht_mem (i + 1) hi') x hx' hd).le
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hlen i] : (0 : ℝ) ≤ t (i + 1) - t i),
      hlen i] at this
    exact this
  rw [Real.dist_eq, hsum, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range N, (a / N * φ ((i + 1) * a / N) - ∫ x in t i..t (i + 1), φ x)|
      ≤ ∑ i ∈ Finset.range N, |a / N * φ ((i + 1) * a / N) - ∫ x in t i..t (i + 1), φ x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, ε / (a + 1) * (a / N) := Finset.sum_le_sum hterm
    _ = ε * (a / (a + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
    _ < ε := by
        have : a / (a + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        nlinarith

variable {E : Type*} [Fintype E] {P : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ} {rb : ℝ}

/-- **`eq:F-incr`** (appF-convex.tex:41-44): for `0 ≤ α < α' ≤ 1`, "the best response `x*(α')` is
feasible at `α`, and `x*(α)` at `α'`, so `V(α) ≥ V(α') − (α' − α) r(x*(α'))` and
`V(α') ≥ V(α) + (α' − α) r(x*(α))`, that is,
`(α' − α) r(x*(α)) ≤ V(α') − V(α) ≤ (α' − α) r(x*(α'))`". (The bounds on `α`, `α'` are not
used.) -/
theorem incr (h : Setting P m c rb) {α α' : ℝ} (_hα : 0 ≤ α) (_hαα' : α < α') (_hα' : α' ≤ 1) :
    (α' - α) * S P m c α ≤ V P m c α' - V P m c α ∧
      V P m c α' - V P m c α ≤ (α' - α) * S P m c α' := by
  obtain ⟨y, hy, hyS⟩ := h.exists_favourable α
  obtain ⟨y', hy', hy'S⟩ := h.exists_favourable α'
  -- "… `x*(α')` is feasible at `α`, …": `V(α) ≥ U_A(x*(α') | α) = V(α') − (α' − α) r(x*(α'))`
  have h1 : V P m c α' - (α' - α) * reward m y' ≤ V P m c α := by
    have := h.util_le_V (α := α) hy'.1
    rw [hy'.V_eq]
    simp only [util] at this ⊢
    linarith
  -- "… and `x*(α)` at `α'`, …": `V(α') ≥ U_A(x*(α) | α') = V(α) + (α' − α) r(x*(α))`
  have h2 : V P m c α + (α' - α) * reward m y ≤ V P m c α' := by
    have := h.util_le_V (α := α') hy.1
    rw [hy.V_eq]
    simp only [util] at this ⊢
    linarith
  rw [hyS] at h2
  rw [hy'S] at h1
  constructor <;> linarith

/-- **`lem:welfare`** (Lemma D.6, appF-convex.tex:34-36, proof 38-50): `OPT ≤ W ≤ r̄`, and if
`W > 0`, then `OPT ≥ W/(2 ln(2r̄/W))`.

The proof. "We first prove the upper bounds": (U1) `W ≥ r(y) − c(y) = U_P(α) + V(α) ≥ U_P(α)` for
`y = x*(α)`, as `V(α) ≥ 0`, so `OPT ≤ W`; (U2) `W ≤ max_{x ∈ K} r(x) ≤ r̄` as `c ≥ 0`. "Now we
prove the lower bound": (L1) `eq:F-incr` (`incr`); (L2) `r(x*(α')) ≤ OPT/(1 − α')` for `α' < 1` and
`r(x*(1)) ≤ r̄`; (L3) with `a = 1 − W/(2r̄) ∈ [1/2, 1)` and `α_i = ia/N`, summing the right-hand
inequality of `eq:F-incr` over `[α_{i−1}, α_i]` and `[a, 1]` gives
`W = V(1) − V(0) ≤ OPT ∑_i (α_i − α_{i−1})/(1 − α_i) + (1 − a) r̄`;
(L4) the sum is a Riemann sum (`tendsto_riemannSum`) and tends to `∫_0^a dα/(1 − α) = ln(2r̄/W)`;
(L5) `W ≤ OPT ln(2r̄/W) + W/2`, and `ln(2r̄/W) ≥ ln 2 > 0`. (Indices from `0`: the term `i` of the
Lean sum is the paper's term `i + 1`.) The parenthetical remark after `eq:F-incr`,
`W = ∫_0^1 r(x*(α)) dα`, is not used ("but we need only the upper bound") and not formalised. -/
theorem welfare_lemma (h : Setting P m c rb) :
    OPT (profit P m c) ≤ welfare P m c ∧ welfare P m c ≤ rb ∧
      (0 < welfare P m c →
        welfare P m c / (2 * Real.log (2 * rb / welfare P m c)) ≤ OPT (profit P m c)) := by
  set W := welfare P m c with hWdef
  set OPT' := OPT (profit P m c) with hOPT
  -- `W` is the maximum `V(1)`
  have hWbdd : BddAbove ((fun x => reward m x - c x) '' P) := by
    refine ⟨V P m c 1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have := h.util_le_V (α := 1) hx
    simpa [util] using this
  -- "We first prove the upper bounds."
  -- (U1) "Let `α ∈ [0, 1]` and `y := x*(α)`. Then `W ≥ r(y) − c(y) = U_P(α) + V(α) ≥ U_P(α)`, as
  -- `V(α) ≥ 0`, so `OPT ≤ W`."
  have hU1 : OPT' ≤ W := by
    refine csSup_le ⟨_, mem_image_of_mem _ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
      ⟨le_rfl, zero_le_one⟩)⟩ ?_
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨y, hy, hyS⟩ := h.exists_favourable α
    have h1 : reward m y - c y ≤ W := le_csSup hWbdd (mem_image_of_mem _ hy.1)
    have h2 : reward m y - c y = profit P m c α + V P m c α := by
      rw [profit, ← hyS, hy.V_eq, util]
      ring
    have h3 := h.V_nonneg α
    linarith
  -- (U2) "And `W ≤ max_{x ∈ K} r(x) ≤ r̄` as `c ≥ 0`."
  have hU2 : W ≤ rb := by
    have hrbdd : BddAbove (reward m '' P) :=
      ⟨rb, by rintro _ ⟨x, hx, rfl⟩; exact h.reward_le x hx⟩
    have hWr : W ≤ sSup (reward m '' P) := by
      refine csSup_le ⟨_, mem_image_of_mem _ (h.zero_mem)⟩ ?_
      rintro _ ⟨x, hx, rfl⟩
      have := h.c_nonneg x hx
      exact (sub_le_self _ this).trans (le_csSup hrbdd (mem_image_of_mem _ hx))
    exact hWr.trans (csSup_le ⟨_, mem_image_of_mem _ (h.zero_mem)⟩
      (by rintro _ ⟨x, hx, rfl⟩; exact h.reward_le x hx))
  refine ⟨hU1, hU2, fun hW => ?_⟩
  -- "Now we prove the lower bound."
  -- (L1) "Let `0 ≤ α < α' ≤ 1`. The best response `x*(α')` is feasible at `α`, and `x*(α)` at `α'`,
  -- so `V(α) ≥ V(α') − (α' − α) r(x*(α'))` and `V(α') ≥ V(α) + (α' − α) r(x*(α))`, that is,
  -- (`eq:F-incr`) `(α' − α) r(x*(α)) ≤ V(α') − V(α) ≤ (α' − α) r(x*(α'))`." (`incr`)
  have hL1 : ∀ α α' : ℝ, 0 ≤ α → α < α' → α' ≤ 1 →
      (α' - α) * S P m c α ≤ V P m c α' - V P m c α ∧
        V P m c α' - V P m c α ≤ (α' - α) * S P m c α' :=
    fun _ _ hα hαα' hα' => incr h hα hαα' hα'
  -- (L2) "For `α' < 1` we have `r(x*(α')) ≤ OPT/(1 − α')`, as `(1 − α') r(x*(α')) = U_P(α') ≤ OPT`,
  -- and `r(x*(1)) ≤ r̄`."
  have hL2 : ∀ α' ∈ Ico (0 : ℝ) 1, S P m c α' ≤ OPT' / (1 - α') := fun α' hα' => by
    rw [le_div_iff₀ (by linarith [hα'.2]), mul_comm]
    exact h.profit_le_OPT ⟨hα'.1, hα'.2.le⟩
  have hL2' : S P m c 1 ≤ rb := h.S_le_rbar 1
  -- (L3) "Let `a := 1 − W/(2r̄)`, which lies in `[1/2, 1)` as `0 < W ≤ r̄`, let `N ≥ 1`, and let
  -- `α_i := ia/N` for `i = 0, …, N`."
  have hrb0 : 0 < rb := hW.trans_le hU2
  set a := 1 - W / (2 * rb) with ha
  have ha12 : 1 / 2 ≤ a := by
    rw [ha]
    have : W / (2 * rb) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have ha1 : a < 1 := by rw [ha]; linarith [div_pos hW (by positivity : (0 : ℝ) < 2 * rb)]
  have ha0 : 0 ≤ a := by linarith
  -- "Summing the right-hand inequality of `eq:F-incr` over the intervals `[α_{i−1}, α_i]` and
  -- `[a, 1]` gives `W = V(1) − V(0) ≤ OPT ∑_{i=1}^N (α_i − α_{i−1})/(1 − α_i) + (1 − a) r̄`."
  set s : ℕ → ℝ := fun N => ∑ i ∈ Finset.range N,
    ((i + 1 : ℕ) * a / N - i * a / N) / (1 - (i + 1 : ℕ) * a / N) with hs
  have hL3 : ∀ N : ℕ, 1 ≤ N → W ≤ OPT' * s N + (1 - a) * rb := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    set αi : ℕ → ℝ := fun i => i * a / N with hαi
    have hαi_mem : ∀ i ≤ N, αi i ∈ Icc 0 a := fun i hi => by
      refine ⟨by positivity, ?_⟩
      rw [hαi]
      simp only
      rw [div_le_iff₀ hNpos]
      have : (i : ℝ) ≤ N := by exact_mod_cast hi
      nlinarith
    have hαN : αi N = a := by simp only [hαi]; field_simp
    have hα0 : αi 0 = 0 := by simp [hαi]
    -- `W = V(1) − V(0)`
    have hW' : W = V P m c 1 - V P m c 0 := by rw [V_one, h.V_zero, sub_zero]
    -- the telescoping sum over `[α_i, α_{i+1}]`
    have htel : V P m c a - V P m c 0 =
        ∑ i ∈ Finset.range N, (V P m c (αi (i + 1)) - V P m c (αi i)) := by
      rw [Finset.sum_range_sub (fun i => V P m c (αi i)), hαN, hα0]
    -- termwise:
    -- `V(α_{i+1}) − V(α_i) ≤ (α_{i+1} − α_i) r(x*(α_{i+1})) ≤ OPT (α_{i+1} − α_i)/(1 − α_{i+1})`
    have hterm : ∀ i ∈ Finset.range N, V P m c (αi (i + 1)) - V P m c (αi i) ≤
        OPT' * ((αi (i + 1) - αi i) / (1 - αi (i + 1))) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hm1 := hαi_mem (i + 1) hi'
      have hm0 := hαi_mem i hi'.le
      have hlt : αi i < αi (i + 1) := by
        simp only [hαi]
        rw [div_lt_div_iff_of_pos_right hNpos]
        push_cast
        nlinarith
      have h1 := (hL1 _ _ hm0.1 hlt (hm1.2.trans ha1.le)).2
      have h2 := hL2 (αi (i + 1)) ⟨hm1.1, lt_of_le_of_lt hm1.2 ha1⟩
      have h1α : 0 < 1 - αi (i + 1) := by linarith [hm1.2]
      calc V P m c (αi (i + 1)) - V P m c (αi i) ≤ (αi (i + 1) - αi i) * S P m c (αi (i + 1)) := h1
        _ ≤ (αi (i + 1) - αi i) * (OPT' / (1 - αi (i + 1))) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = OPT' * ((αi (i + 1) - αi i) / (1 - αi (i + 1))) := by ring
    -- the interval `[a, 1]`: `V(1) − V(a) ≤ (1 − a) r(x*(1)) ≤ (1 − a) r̄`
    have hlast : V P m c 1 - V P m c a ≤ (1 - a) * rb := by
      have := (hL1 _ _ ha0 ha1 le_rfl).2
      exact this.trans (mul_le_mul_of_nonneg_left hL2' (by linarith))
    have hsN : s N = ∑ i ∈ Finset.range N, (αi (i + 1) - αi i) / (1 - αi (i + 1)) := by
      simp only [hs, hαi]
    calc W = (V P m c 1 - V P m c a) + (V P m c a - V P m c 0) := by rw [hW']; ring
      _ ≤ (1 - a) * rb + ∑ i ∈ Finset.range N, OPT' * ((αi (i + 1) - αi i) / (1 - αi (i + 1))) := by
          rw [htel]
          exact add_le_add hlast (Finset.sum_le_sum hterm)
      _ = OPT' * s N + (1 - a) * rb := by rw [hsN, Finset.mul_sum]; ring
  -- (L4) "The sum is a Riemann sum of the continuous function `α ↦ 1/(1 − α)` on `[0, a]`, so it
  -- tends to `∫_0^a dα/(1 − α) = ln(2r̄/W)` as `N → ∞`."
  have hcont : ContinuousOn (fun α : ℝ => 1 / (1 - α)) (Icc 0 a) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) fun α hα => by
      have := hα.2
      linarith
  have hriemann := tendsto_riemannSum ha0 hcont
  have hsR : ∀ N : ℕ, 1 ≤ N → s N = ∑ i ∈ Finset.range N, a / N * (1 / (1 - (i + 1) * a / N)) := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    simp only [hs]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    have e : ((i : ℝ) + 1) * a / N - i * a / N = a / N := by field_simp; ring
    rw [e]
    ring
  have hval : ∫ α in (0 : ℝ)..a, 1 / (1 - α) = Real.log (2 * rb / W) := by
    simp_rw [one_div]
    rw [intervalIntegral.integral_comp_sub_left (fun x => x⁻¹) 1, sub_zero,
      integral_inv_of_pos (by linarith) one_pos]
    congr 1
    rw [ha, sub_sub_cancel]
    field_simp
  rw [hval] at hriemann
  have hs_tendsto : Tendsto s atTop (𝓝 (Real.log (2 * rb / W))) :=
    hriemann.congr' (eventually_atTop.2 ⟨1, fun N hN => (hsR N hN).symm⟩)
  -- (L5) "Hence `W ≤ OPT ln(2r̄/W) + W/2`, …"
  have h1a : (1 - a) * rb = W / 2 := by rw [ha]; field_simp; ring
  have hL5 : W ≤ OPT' * Real.log (2 * rb / W) + W / 2 := by
    have hlim : Tendsto (fun N => OPT' * s N + (1 - a) * rb) atTop
        (𝓝 (OPT' * Real.log (2 * rb / W) + (1 - a) * rb)) :=
      (hs_tendsto.const_mul OPT').add_const _
    rw [← h1a]
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hL3⟩)
  -- "… and the claim follows as `ln(2r̄/W) ≥ ln 2 > 0`."
  have hlog : 0 < Real.log (2 * rb / W) := by
    have h2 : Real.log 2 ≤ Real.log (2 * rb / W) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hW]; linarith)
    exact (Real.log_pos (by norm_num)).trans_le h2
  rw [div_le_iff₀ (by positivity)]
  linarith

end Stoc.Convex
