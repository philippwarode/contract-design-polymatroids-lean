-- stamp r7 2026-11-02
import Stoc.Approximation.Scheme

/-!
# Homogeneous costs: the `1/p` rule

The STOC version's Section 5.1 (`sec:fptas-quadratic`, `stoc-sections/08-approximation.tex`:25-33)
with the proofs of Appendix D.1 (`sec:E-prule`, `stoc-sections/appE-halfrule.tex`:41-114): costs
homogeneous of degree `p > 1` on a compact convex action set `K ⊆ ℝ^E_{≥0}` containing zero, the
action sets to which Section 5 applies (08-approximation.tex:4) and those of `cor:fptashom`
(08-approximation.tex:37).

* `IsHomogeneous` (08-approximation.tex:27): costs homogeneous of degree `p`; "For `z ≥ 0` we write
  `‖z‖_c := c(z)^{1/p}`" (`cnorm`, appE-halfrule.tex:43), which `lem:segment`, `lem:foc` and the
  proof of `thm:prule` use (appE-halfrule.tex:48, 63, 79).
* `lem:segment` (`segment`, its case `‖z‖_c = 0` is `segment_left_zero`) and `lem:foc` (`foc`).
* `thm:prule` (`prule`): "For homogeneous costs of degree `p > 1`, `ᾱ = 1/p` is a share bound. This
  bound is tight." Its proof has four paragraphs. The first shows that the reward grows at most like
  `α^{1/(p−1)}` (steps (1)–(5): `reward_le_rpow_mul` with `cnorm_le_rpow_mul_of_lt`; step (6):
  `antitoneOn_ratio` for `R(α) = r(x*(α))/α^{1/(p−1)}`, `ratio`). The second shows that `U_P` is
  nonincreasing on `[1/p, 1]` (step (7): `profit_eq_shape_mul_ratio` with `shape` for
  `h(α) = (1 − α) α^{1/(p−1)}`, `shape_nonneg`, `hasDerivAt_shape`, `strictMonoOn_shape`,
  `strictAntiOn_shape`, `ratio_nonneg`; step (8), `eq:E-product`: `profit_antitoneOn`), which makes
  `1/p` a share bound (`isShareBound_of_antitoneOn`, not in the paper). The third shows that `U_P`
  is strictly decreasing on `[1/p, 1]` unless `r` vanishes on `K` (step (9): `reward_pos`,
  `profit_strictAntiOn`, `le_inv_of_isMaxOn`, and `profit_eq_zero` for `r = 0`). The fourth shows
  that the bound `1/p` on the share of an optimal contract is attained (step (10): `exCost`,
  `K = [0, 1]` (`Icc_eq_indepPoly_oneF`), `ex_isHomogeneous`, `ex_key`, `ex_isBR_iff`, `ex_isPBR`,
  `ex_profit_eq`, `ex_isMaxOn_iff`), which makes the bound tight (`ex_not_isShareBound`, not in the
  paper).
* The prose of Section 5.1 before `thm:prule` (08-approximation.tex:27-29). The unconstrained
  setting, "When `K = ℝ^E_{≥0}`, if the best response exists and is unique, then
  `x*(α) = α^{1/(p−1)} x*(1)` for `α > 0`", with its argument and "The principal's utility is
  therefore proportional to `(1 − α)α^{1/(p−1)}`, which is maximized at `α = 1/p`", is
  `unconstrained` (with `util_rpow_smul` and `shape_lt_inv`). "the optimal share may be smaller
  than `1/p`": for `p = 2` (the quadratic cost `x²/2`), one element with the capacity
  `f({e}) = u < 1/2` has the optimal share `u` (`Stoc.Lower.optimal_oneF`,
  `Stoc/Approximation/LowerBounds.lean`). "Nevertheless, convexity and homogeneity imply that
  `r(x*(α))/α^{1/(p−1)}` is nonincreasing for `α > 0`" is step (6) (`antitoneOn_ratio`), and "Since
  `(1 − α)α^{1/(p−1)}` is decreasing beyond `1/p`, so is the principal's utility there" is steps
  (7) and (8) (`strictAntiOn_shape`, `profit_antitoneOn`).
* `isHomogeneous_quadCost`: quadratic costs are homogeneous of degree `2` (not in the paper: the
  proof of `cor:fptasquad` applies `cor:fptashom` with `p = 2` to them).

The model's reward of success `r̄` (02-preliminaries.tex:12) is not used by these results and is
not a parameter of their Lean statements (see `Stoc/Approximation/Agent.lean`).

Taken over on 2026-10-20 from `Research/S14/Homogeneous.lean` (series 14, `thm:cvxpstar` and
`cor:cvxalphap`) for the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc.PRule

open Set Filter Topology Stoc.Convex

variable {E : Type*}

/-- Costs **homogeneous of degree `p`** (08-approximation.tex:27): "`c : ℝ^E_{≥0} → ℝ_{≥0}` is
continuous and convex and `c(tx) = t^p c(x)` for `t > 0`", for all `x ≥ 0`; `c(0) = 0`, as in the
model (`IsCost`, 02-preliminaries.tex:12). -/
structure IsHomogeneous (p : ℝ) (c : (E → ℝ) → ℝ) : Prop extends IsCost c where
  convexOn : ConvexOn ℝ (Ici 0) c
  continuousOn : ContinuousOn c (Ici 0)
  hom : ∀ z : E → ℝ, 0 ≤ z → ∀ t : ℝ, 0 < t → c (t • z) = t ^ p * c z

/-- "For `z ≥ 0` we write `‖z‖_c := c(z)^{1/p}`" (appE-halfrule.tex:43, at the start of
`sec:E-prule`), which `lem:segment`, `lem:foc` and the proof of `thm:prule` use
(appE-halfrule.tex:48, 63, 79). -/
noncomputable def cnorm (p : ℝ) (c : (E → ℝ) → ℝ) (z : E → ℝ) : ℝ := c z ^ (1 / p)

lemma smul_nonneg' {t : ℝ} (ht : 0 ≤ t) {x : E → ℝ} (hx : 0 ≤ x) : 0 ≤ t • x := fun e => by
  show 0 ≤ t * x e
  exact mul_nonneg ht (hx e)

variable {p : ℝ} {c : (E → ℝ) → ℝ}

lemma cnorm_nonneg (hc : IsHomogeneous p c) {z : E → ℝ} (hz : 0 ≤ z) : 0 ≤ cnorm p c z :=
  Real.rpow_nonneg (hc.nonneg z hz) _

/-- `‖z‖_c^p = c(z)`. -/
lemma cnorm_rpow (hc : IsHomogeneous p c) (hp : 1 < p) {z : E → ℝ} (hz : 0 ≤ z) :
    cnorm p c z ^ p = c z := by
  rw [cnorm, ← Real.rpow_mul (hc.nonneg z hz), one_div_mul_cancel (by linarith), Real.rpow_one]

/-! ### `lem:segment` -/

/-- **`lem:segment`**, step (3) of its proof: the case `Z = ‖z‖_c = 0`, `σ ∈ (0, 1)`.
"If `Z = 0`, then `c(tz) = t^p c(z) = 0` for every `t > 0`, and for every `λ ∈ (0, 1)` convexity and
homogeneity give `c((1 − σ)z + σw) ≤ (1 − λ) c((1−σ)/(1−λ) z) + λ c(σ/λ w) = λ^{1−p} σ^p c(w)`.
Letting `λ → 1` gives `c((1 − σ)z + σw) ≤ (σW)^p`, which is the claim." -/
theorem segment_left_zero (hc : IsHomogeneous p c) (hp : 1 < p) {z w : E → ℝ} (hz : 0 ≤ z)
    (hw : 0 ≤ w) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hZ : cnorm p c z = 0) :
    c ((1 - σ) • z + σ • w) ≤ ((1 - σ) * cnorm p c z + σ * cnorm p c w) ^ p := by
  set W := cnorm p c w with hWdef
  have hW0 : 0 ≤ W := cnorm_nonneg hc hw
  -- `c(z) = Z^p = 0`, so `c(tz) = t^p c(z) = 0` for every `t > 0`
  have hcz : c z = 0 := by rw [← cnorm_rpow hc hp hz, hZ, Real.zero_rpow (by linarith)]
  have hctz : ∀ t : ℝ, 0 < t → c (t • z) = 0 := fun t ht => by rw [hc.hom z hz t ht, hcz, mul_zero]
  -- for every `λ ∈ (0, 1)` (`l` below): `c((1 − σ)z + σw) ≤ λ^{1−p} σ^p c(w)`
  have hlam : ∀ l ∈ Ioo (0 : ℝ) 1, c ((1 - σ) • z + σ • w) ≤ l ^ (1 - p) * σ ^ p * c w := by
    intro l hl
    have h1l : 0 < 1 - l := by linarith [hl.2]
    have hpt : 0 < (1 - σ) / (1 - l) := div_pos (by linarith) h1l
    have hqt : 0 < σ / l := div_pos hσ0 hl.1
    have hid : (1 - σ) • z + σ • w = (1 - l) • (((1 - σ) / (1 - l)) • z) + l • ((σ / l) • w) := by
      rw [smul_smul, smul_smul, mul_div_cancel₀ _ h1l.ne', mul_div_cancel₀ _ hl.1.ne']
    have hconv := hc.convexOn.2 (mem_Ici.2 (smul_nonneg' hpt.le hz))
      (mem_Ici.2 (smul_nonneg' hqt.le hw)) h1l.le hl.1.le (by ring)
    rw [← hid, smul_eq_mul, smul_eq_mul, hctz _ hpt, hc.hom w hw _ hqt, mul_zero, zero_add] at hconv
    calc c ((1 - σ) • z + σ • w) ≤ l * ((σ / l) ^ p * c w) := hconv
      _ = l ^ (1 - p) * σ ^ p * c w := by
          rw [Real.div_rpow hσ0.le hl.1.le, Real.rpow_sub hl.1, Real.rpow_one]
          field_simp
  -- `λ → 1`
  have hlim : Tendsto (fun l : ℝ => l ^ (1 - p) * σ ^ p * c w) (𝓝[<] 1) (𝓝 (σ ^ p * c w)) := by
    have hcont : ContinuousAt (fun l : ℝ => l ^ (1 - p) * σ ^ p * c w) 1 :=
      ((continuousAt_id.rpow_const (Or.inl one_ne_zero)).mul continuousAt_const).mul
        continuousAt_const
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hle := ge_of_tendsto hlim
    (Filter.mem_of_superset (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)) fun l hl => hlam l hl)
  -- `σ^p c(w) = (σW)^p = ((1 − σ)·0 + σW)^p`
  calc c ((1 - σ) • z + σ • w) ≤ σ ^ p * c w := hle
    _ = ((1 - σ) * cnorm p c z + σ * W) ^ p := by
        rw [hZ, mul_zero, zero_add, Real.mul_rpow hσ0.le hW0, hWdef, cnorm_rpow hc hp hw]

/-- **`lem:segment`** (Lemma D.1, appE-halfrule.tex:45-50, proof 52-58): for all `z, w ∈ ℝ^E_{≥0}`
and `σ ∈ [0, 1]`, `c((1 − σ)z + σw) ≤ ((1 − σ)‖z‖_c + σ‖w‖_c)^p` (displayed in the STOC version).
For costs homogeneous of degree `p > 1`, those of `thm:prule`, for whose proof `sec:E-prule` holds
the lemma (the final version no longer states this assumption in `sec:E-prule`; its proof uses the
homogeneity and the convexity of `c`).

The proof: (1) `Z = ‖z‖_c`, `W = ‖w‖_c`; for `σ ∈ {0, 1}` the claim is an equality, so let
`σ ∈ (0, 1)`; (2) if `Z, W > 0`, the point is `H = (1 − σ)Z + σW` times a convex combination of
`z/Z` and `w/W`, at which `c ≤ 1`; (3) the case `Z = 0` (`segment_left_zero`, with `λ → 1`);
(4) the case `W = 0` is symmetric. -/
theorem segment (hc : IsHomogeneous p c) (hp : 1 < p) {z w : E → ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    c ((1 - σ) • z + σ • w) ≤ ((1 - σ) * cnorm p c z + σ * cnorm p c w) ^ p := by
  -- (1) "Let `Z := ‖z‖_c` and `W := ‖w‖_c`. For `σ ∈ {0, 1}` the claim is an equality, so let
  -- `σ ∈ (0, 1)`."
  set Z := cnorm p c z with hZdef
  set W := cnorm p c w with hWdef
  have hZ0 : 0 ≤ Z := cnorm_nonneg hc hz
  have hW0 : 0 ≤ W := cnorm_nonneg hc hw
  rcases hσ0.eq_or_lt with rfl | hσ0'
  · rw [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul, add_zero, hZdef,
      cnorm_rpow hc hp hz]
  rcases hσ1.eq_or_lt with rfl | hσ1'
  · rw [sub_self, zero_smul, zero_add, one_smul, zero_mul, zero_add, one_mul, hWdef,
      cnorm_rpow hc hp hw]
  by_cases hZW : 0 < Z ∧ 0 < W
  · -- (2) "If `Z, W > 0`, then `c(z/Z) = c(w/W) = 1` by homogeneity. With `H := (1 − σ)Z + σW > 0`,
    -- the point `(1 − σ)z + σw` is `H` times the convex combination of `z/Z` and `w/W` with the
    -- weights `(1 − σ)Z/H` and `σW/H`, at which `c` is at most `1` by convexity. So homogeneity
    -- gives `c((1 − σ)z + σw) ≤ H^p`."
    obtain ⟨hZp, hWp⟩ := hZW
    have hcz1 : c (Z⁻¹ • z) = 1 := by
      rw [hc.hom z hz _ (inv_pos.2 hZp), ← cnorm_rpow hc hp hz, ← hZdef, Real.inv_rpow hZ0,
        inv_mul_cancel₀ (Real.rpow_pos_of_pos hZp p).ne']
    have hcw1 : c (W⁻¹ • w) = 1 := by
      rw [hc.hom w hw _ (inv_pos.2 hWp), ← cnorm_rpow hc hp hw, ← hWdef, Real.inv_rpow hW0,
        inv_mul_cancel₀ (Real.rpow_pos_of_pos hWp p).ne']
    obtain ⟨H, hHdef⟩ : ∃ H, H = (1 - σ) * Z + σ * W := ⟨_, rfl⟩
    have hH : 0 < H := by
      rw [hHdef]
      have : 0 ≤ (1 - σ) * Z := mul_nonneg (by linarith) hZ0
      have : 0 < σ * W := mul_pos hσ0' hWp
      linarith
    have hθ0 : 0 ≤ (1 - σ) * Z / H := div_nonneg (mul_nonneg (by linarith) hZ0) hH.le
    have hθ1 : 0 ≤ σ * W / H := div_nonneg (mul_nonneg hσ0 hW0) hH.le
    have hθsum : (1 - σ) * Z / H + σ * W / H = 1 := by
      rw [← add_div, ← hHdef, div_self hH.ne']
    have hzZ : 0 ≤ Z⁻¹ • z := smul_nonneg' (inv_nonneg.2 hZ0) hz
    have hwW : 0 ≤ W⁻¹ • w := smul_nonneg' (inv_nonneg.2 hW0) hw
    have hle1 : c (((1 - σ) * Z / H) • (Z⁻¹ • z) + (σ * W / H) • (W⁻¹ • w)) ≤ 1 := by
      refine (hc.convexOn.2 (mem_Ici.2 hzZ) (mem_Ici.2 hwW) hθ0 hθ1 hθsum).trans ?_
      rw [smul_eq_mul, smul_eq_mul, hcz1, hcw1, mul_one, mul_one, hθsum]
    have hcomb : 0 ≤ ((1 - σ) * Z / H) • (Z⁻¹ • z) + (σ * W / H) • (W⁻¹ • w) :=
      add_nonneg (smul_nonneg' hθ0 hzZ) (smul_nonneg' hθ1 hwW)
    have hid : (1 - σ) • z + σ • w =
        H • (((1 - σ) * Z / H) • (Z⁻¹ • z) + (σ * W / H) • (W⁻¹ • w)) := by
      ext e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hid, hc.hom _ hcomb H hH, ← hHdef]
    calc H ^ p * c (((1 - σ) * Z / H) • (Z⁻¹ • z) + (σ * W / H) • (W⁻¹ • w)) ≤ H ^ p * 1 :=
          mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg hH.le p)
      _ = H ^ p := mul_one _
  · rcases not_and_or.1 hZW with hZ | hW
    · -- (3) "If `Z = 0`, …"
      exact segment_left_zero hc hp hz hw hσ0' hσ1' (le_antisymm (not_lt.1 hZ) hZ0)
    · -- (4) "The case `W = 0` is symmetric."
      have h := segment_left_zero hc hp hw hz (σ := 1 - σ) (by linarith) (by linarith)
        (le_antisymm (not_lt.1 hW) hW0)
      rw [sub_sub_cancel, add_comm, ← hZdef, ← hWdef, le_antisymm (not_lt.1 hW) hW0, mul_zero,
        zero_add] at h
      rw [le_antisymm (not_lt.1 hW) hW0, mul_zero, add_zero]
      exact h

/-! ### `lem:foc` -/

/-- `X^{p−1} X = X^p` for `X ≥ 0`. -/
lemma rpow_sub_one_mul_self {X : ℝ} (hX : 0 ≤ X) (hp : 1 < p) : X ^ (p - 1) * X = X ^ p := by
  conv_rhs => rw [show p = (p - 1) + 1 by ring]
  rw [Real.rpow_add' hX (by linarith), Real.rpow_one]

variable [Fintype E]

lemma reward_zero (m : E → ℝ) : reward m 0 = 0 := by
  simp [reward]

/-- `r(x + σ(z − x)) = r(x) + σ (r(z) − r(x))`: the reward is linear. -/
lemma reward_add_smul_sub (m x z : E → ℝ) (σ : ℝ) :
    reward m (x + σ • (z - x)) = reward m x + σ * (reward m z - reward m x) := by
  unfold reward
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- `lem:foc` without the model's `m ≥ 0`, which its proof does not use: the form that the proof
of `thm:prule` (`reward_le_rpow_mul`) takes, as it is stated for every `m`. The paper's statement,
with the proof's steps, is `foc` below. -/
theorem foc_aux (hc : IsHomogeneous p c) (hp : 1 < p) {K : Set (E → ℝ)} (_hKc : IsCompact K)
    (hK : Convex ℝ K) (hKnn : ∀ x ∈ K, 0 ≤ x) (_h0 : (0 : E → ℝ) ∈ K) {m : E → ℝ} {α : ℝ}
    (_hα : 0 < α) {x z : E → ℝ} (hx : IsBR K m c α x) (hz : z ∈ K) :
    α * (reward m z - reward m x) ≤ p * cnorm p c x ^ (p - 1) * (cnorm p c z - cnorm p c x) := by
  -- "Let `X := ‖x‖_c` and `Z := ‖z‖_c`."
  set X := cnorm p c x with hXdef
  set Z := cnorm p c z with hZdef
  have hxX : c x = X ^ p := (cnorm_rpow hc hp (hKnn x hx.1)).symm
  -- (1) "For `σ ∈ (0, 1]`, the point `x + σ(z − x)` lies in the convex set `K`."
  have h1 : ∀ σ ∈ Ioc (0 : ℝ) 1, x + σ • (z - x) ∈ K := fun σ hσ =>
    hK.add_smul_sub_mem hx.1 hz ⟨hσ.1.le, hσ.2⟩
  -- (2) "By the optimality of `x`, the linearity of `r` and `lem:segment`,
  -- `α r(x) − X^p ≥ α r(x) + σα (r(z) − r(x)) − (X + σ(Z − X))^p`."
  have h2 : ∀ σ ∈ Ioc (0 : ℝ) 1, α * reward m x + σ * α * (reward m z - reward m x) -
      (X + σ * (Z - X)) ^ p ≤ α * reward m x - X ^ p := by
    intro σ hσ
    have hopt := hx.2 _ (h1 σ hσ)
    have hseg := segment hc hp (hKnn x hx.1) (hKnn z hz) hσ.1.le hσ.2
    have e1 : (1 - σ) • x + σ • z = x + σ • (z - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have e2 : (1 - σ) * X + σ * Z = X + σ * (Z - X) := by ring
    rw [e1, ← hXdef, ← hZdef, e2] at hseg
    simp only [util] at hopt
    rw [reward_add_smul_sub, hxX] at hopt
    nlinarith
  -- (3) "Dividing by `σ` and letting `σ ↓ 0` gives the claim, since the right derivative of
  -- `σ ↦ (X + σ(Z − X))^p` at `0` is `p X^{p−1}(Z − X)`."
  have hderiv : Tendsto (fun s : ℝ => s⁻¹ * ((X + s * (Z - X)) ^ p - X ^ p)) (𝓝[>] 0)
      (𝓝 (p * X ^ (p - 1) * (Z - X))) := by
    rcases (cnorm_nonneg hc (hKnn x hx.1)).lt_or_eq with hXpos | hX0
    · -- `X > 0`: the chain rule
      have hf : HasDerivAt (fun s : ℝ => X + s * (Z - X)) (Z - X) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Z - X)).const_add X
      have hg :=
        (hf.rpow_const (p := p) (Or.inl (by simpa using hXpos.ne'))).tendsto_slope_zero_right
      simp only [zero_add, zero_mul, add_zero, smul_eq_mul] at hg
      convert hg using 2
      ring
    · -- "This also holds for `X = 0`, where the derivative is `lim_{σ↓0} σ^{p−1} Z^p = 0`, as
      -- `p > 1`."
      have hX : X = 0 := by rw [hXdef]; exact hX0.symm
      have hZ0 : 0 ≤ Z := cnorm_nonneg hc (hKnn z hz)
      have hp1 : p - 1 ≠ 0 := by linarith
      have hlim : Tendsto (fun s : ℝ => s ^ (p - 1) * Z ^ p) (𝓝[>] 0) (𝓝 0) := by
        have hcont : ContinuousAt (fun s : ℝ => s ^ (p - 1) * Z ^ p) 0 :=
          (continuousAt_id.rpow_const (Or.inr (by linarith))).mul continuousAt_const
        have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        rwa [Real.zero_rpow hp1, zero_mul] at this
      have hval : p * X ^ (p - 1) * (Z - X) = 0 := by
        rw [hX, Real.zero_rpow hp1, mul_zero, zero_mul]
      rw [hval]
      refine hlim.congr' (eventually_nhdsWithin_of_forall fun s (hs : 0 < s) => ?_)
      simp only [hX, Real.zero_rpow (by linarith : p ≠ 0), sub_zero, zero_add]
      rw [Real.mul_rpow hs.le hZ0, Real.rpow_sub_one hs.ne']
      ring
  have hle : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      α * (reward m z - reward m x) ≤ s⁻¹ * ((X + s * (Z - X)) ^ p - X ^ p) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have := h2 s hs
    rw [le_inv_mul_iff₀ hs.1]
    nlinarith
  exact ge_of_tendsto hderiv hle

/-- **`lem:foc`** (Lemma D.2, appE-halfrule.tex:60-65, proof 67-73): let `α > 0`, let `x` maximize
`U_A(· | α)` over `K`, and let `z ∈ K`. Then `α (r(z) − r(x)) ≤ p ‖x‖_c^{p−1} (‖z‖_c − ‖x‖_c)`. In
the setting of `thm:prule`, for whose proof `sec:E-prule` holds the lemma: the action set
`K ⊆ ℝ^E_{≥0}` is compact and convex and contains zero (08-approximation.tex:4, 37), and the costs
are homogeneous of degree `p > 1` (the final version no longer states these assumptions in
`sec:E-prule`). The rewards satisfy `m ≥ 0`, as in the model (02-preliminaries.tex:12). The proof
uses only that `K ⊆ ℝ^E_{≥0}` is convex; compactness, `0 ∈ K`, `α > 0` and `m ≥ 0` are not used, and
the steps are in `foc_aux`, the form without `m ≥ 0`.

The proof (appE-halfrule.tex:67-73): (1) `x + σ(z − x) ∈ K` for `σ ∈ (0, 1]`; (2) by the optimality
of `x`, the linearity of `r` and `lem:segment`,
`α r(x) − X^p ≥ α r(x) + σα (r(z) − r(x)) − (X + σ(Z − X))^p`; (3) dividing by `σ` and letting
`σ ↓ 0` gives the claim, since the right derivative of `σ ↦ (X + σ(Z − X))^p` at `0` is
`p X^{p−1}(Z − X)`, which "also holds for `X = 0`, where the derivative is
`lim_{σ↓0} σ^{p−1} Z^p = 0`, as `p > 1`". -/
theorem foc (hc : IsHomogeneous p c) (hp : 1 < p) {K : Set (E → ℝ)} (hKc : IsCompact K)
    (hK : Convex ℝ K) (hKnn : ∀ x ∈ K, 0 ≤ x) (h0 : (0 : E → ℝ) ∈ K) {m : E → ℝ}
    (_hm : ∀ e, 0 ≤ m e) {α : ℝ} (hα : 0 < α) {x z : E → ℝ} (hx : IsBR K m c α x) (hz : z ∈ K) :
    α * (reward m z - reward m x) ≤ p * cnorm p c x ^ (p - 1) * (cnorm p c z - cnorm p c x) :=
  foc_aux hc hp hKc hK hKnn h0 hα hx hz

/-! ### `thm:prule`: the reward grows at most like `α^{1/(p−1)}`

The first paragraph of the proof of `thm:prule` (appE-halfrule.tex:79-91): "We first show that the
reward grows at most like `α^{1/(p−1)}`." The steps of the proof are stated for the action set `K`
of `thm:prule`, with the assumptions on it that each step uses. -/

section Reward

variable (hc : IsHomogeneous p c) (hp : 1 < p) {K : Set (E → ℝ)} (hKc : IsCompact K)
  (hK : Convex ℝ K) (hKnn : ∀ x ∈ K, 0 ≤ x) (h0 : (0 : E → ℝ) ∈ K) {m : E → ℝ}
include hc hp hK hKnn

omit hK in
/-- `thm:prule`, step (4) of its proof: for `0 < α < α'`, maximizers `x` at `α` and `y` at `α'`,
`X = ‖x‖_c` and `Y = ‖y‖_c`, and the second and the third inequality of step (1),
`α (r(y) − r(x)) ≤ p X^{p−1}(Y − X)` and `α' (r(x) − r(y)) ≤ p Y^{p−1}(X − Y)`: "If `Y > X`, the
second and the third give `(p/α') Y^{p−1}(Y − X) ≤ r(y) − r(x) ≤ (p/α) X^{p−1}(Y − X)`, so `X > 0`
and `(Y/X)^{p−1} ≤ α'/α`, that is, `Y ≤ ϱ X`." For the action set `K` of `thm:prule`. -/
lemma cnorm_le_rpow_mul_of_lt {α α' : ℝ} (hα : 0 < α) (hαα' : α < α') {x y : E → ℝ}
    (hx : IsBR K m c α x) (hy : IsBR K m c α' y)
    (i2 : α * (reward m y - reward m x) ≤
      p * cnorm p c x ^ (p - 1) * (cnorm p c y - cnorm p c x))
    (i3 : α' * (reward m x - reward m y) ≤
      p * cnorm p c y ^ (p - 1) * (cnorm p c x - cnorm p c y))
    (hXY : cnorm p c x < cnorm p c y) :
    0 < cnorm p c x ∧ cnorm p c y ≤ (α' / α) ^ (1 / (p - 1)) * cnorm p c x := by
  set X := cnorm p c x with hXdef
  set Y := cnorm p c y with hYdef
  have hX0 : 0 ≤ X := cnorm_nonneg hc (hKnn x hx.1)
  have hY0 : 0 ≤ Y := cnorm_nonneg hc (hKnn y hy.1)
  have hα' : 0 < α' := hα.trans hαα'
  have hp0 : 0 < p := by linarith
  -- `(p/α') Y^{p−1}(Y − X) ≤ r(y) − r(x) ≤ (p/α) X^{p−1}(Y − X)`
  have hlo : p / α' * Y ^ (p - 1) * (Y - X) ≤ reward m y - reward m x := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hα']
    linarith
  have hhi : reward m y - reward m x ≤ p / α * X ^ (p - 1) * (Y - X) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hα]
    linarith
  -- dividing by `p (Y − X) > 0`: `Y^{p−1}/α' ≤ X^{p−1}/α`
  have hYX : Y ^ (p - 1) / α' ≤ X ^ (p - 1) / α := by
    have h := hlo.trans hhi
    have hpos : 0 < p * (Y - X) := mul_pos hp0 (by linarith)
    have e1 : p / α' * Y ^ (p - 1) * (Y - X) = Y ^ (p - 1) / α' * (p * (Y - X)) := by ring
    have e2 : p / α * X ^ (p - 1) * (Y - X) = X ^ (p - 1) / α * (p * (Y - X)) := by ring
    rw [e1, e2] at h
    exact le_of_mul_le_mul_right h hpos
  -- "so `X > 0`"
  have hXpos : 0 < X := by
    rcases hX0.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, Real.zero_rpow (by linarith), zero_div] at hYX
      have : 0 < Y ^ (p - 1) / α' := div_pos (Real.rpow_pos_of_pos (by linarith) _) hα'
      linarith
  refine ⟨hXpos, ?_⟩
  -- "and `(Y/X)^{p−1} ≤ α'/α`"
  have hpow : (Y / X) ^ (p - 1) ≤ α' / α := by
    rw [Real.div_rpow hY0 hX0, div_le_div_iff₀ (Real.rpow_pos_of_pos hXpos _) hα]
    rw [div_le_div_iff₀ hα' hα] at hYX
    linarith
  -- "that is, `Y ≤ ϱ X`"
  have hq : 0 < 1 / (p - 1) := by apply div_pos one_pos; linarith
  have := Real.rpow_le_rpow (Real.rpow_nonneg (div_nonneg hY0 hX0) _) hpow hq.le
  rw [← Real.rpow_mul (div_nonneg hY0 hX0), mul_one_div_cancel (by linarith), Real.rpow_one]
    at this
  rwa [div_le_iff₀ hXpos] at this

include hKc h0

/-- **`thm:prule`**, steps (1)–(5) of its proof (appE-halfrule.tex:79-90), "We first show that the
reward grows at most like `α^{1/(p−1)}`": for `0 < α < α'`, a maximizer `x` of `U_A(· | α)` and a
maximizer `y` of `U_A(· | α')`, `r(y) ≤ ϱ r(x)` with `ϱ = (α'/α)^{1/(p−1)}`, for the action set `K`
of `thm:prule`. -/
theorem reward_le_rpow_mul {α α' : ℝ} (hα : 0 < α) (hαα' : α < α') {x y : E → ℝ}
    (hx : IsBR K m c α x) (hy : IsBR K m c α' y) :
    reward m y ≤ (α' / α) ^ (1 / (p - 1)) * reward m x := by
  -- "let `X := ‖x‖_c` and `Y := ‖y‖_c`, and let `ϱ := (α'/α)^{1/(p−1)} > 1`"
  set X := cnorm p c x with hXdef
  set Y := cnorm p c y with hYdef
  set ρ := (α' / α) ^ (1 / (p - 1)) with hρdef
  have hX0 : 0 ≤ X := cnorm_nonneg hc (hKnn x hx.1)
  have hq : 0 < 1 / (p - 1) := by apply div_pos one_pos; linarith
  have hρ1 : 1 < ρ := Real.one_lt_rpow (by rw [lt_div_iff₀ hα]; linarith) hq
  -- (1) "`lem:foc` with `z = 0` and with `z = y` for `x`, and with `z = x` for `y`, gives
  -- `α r(x) ≥ p X^p`, `α (r(y) − r(x)) ≤ p X^{p−1}(Y − X)`, `α' (r(x) − r(y)) ≤ p Y^{p−1}(X − Y)`."
  have i1 : p * X ^ p ≤ α * reward m x := by
    have h := foc_aux hc hp hKc hK hKnn h0 hα hx h0
    have hc0 : cnorm p c 0 = 0 := by
      rw [cnorm, hc.zero, Real.zero_rpow (by apply one_div_ne_zero; linarith)]
    rw [hc0, reward_zero] at h
    have := rpow_sub_one_mul_self hX0 hp
    nlinarith
  have i2 : α * (reward m y - reward m x) ≤ p * X ^ (p - 1) * (Y - X) :=
    foc_aux hc hp hKc hK hKnn h0 hα hx hy.1
  have i3 : α' * (reward m x - reward m y) ≤ p * Y ^ (p - 1) * (X - Y) :=
    foc_aux hc hp hKc hK hKnn h0 (hα.trans hαα') hy hx.1
  -- (2) "In particular, `r(x) ≥ 0`."
  have hrx : 0 ≤ reward m x := by
    have := Real.rpow_nonneg hX0 p
    nlinarith
  have hXp1 : 0 ≤ X ^ (p - 1) := Real.rpow_nonneg hX0 _
  rcases le_or_gt Y X with hYX | hXY
  · -- (3) "If `Y ≤ X`, the second inequality gives `r(y) ≤ r(x) ≤ ϱ r(x)`."
    have : reward m y ≤ reward m x := by
      have : p * X ^ (p - 1) * (Y - X) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hXp1) (by linarith)
      nlinarith
    nlinarith
  · -- (4) "If `Y > X`, the second and the third give
    -- `(p/α') Y^{p−1}(Y − X) ≤ r(y) − r(x) ≤ (p/α) X^{p−1}(Y − X)`, so `X > 0` and
    -- `(Y/X)^{p−1} ≤ α'/α`, that is, `Y ≤ ϱ X`." (`cnorm_le_rpow_mul_of_lt`)
    obtain ⟨-, hYle⟩ := cnorm_le_rpow_mul_of_lt hc hp hKnn hα hαα' hx hy i2 i3 hXY
    -- (5) "Then the second and the first inequality give
    -- `r(y) ≤ r(x) + (p/α) X^{p−1}(ϱX − X) = r(x) + (ϱ − 1) p X^p/α ≤ ϱ r(x)`."
    have hXp : X ^ (p - 1) * X = X ^ p := rpow_sub_one_mul_self hX0 hp
    calc reward m y ≤ reward m x + p / α * X ^ (p - 1) * (ρ * X - X) := by
          have h4 : α * (reward m y - reward m x) ≤ p * X ^ (p - 1) * (ρ * X - X) :=
            i2.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hXp1))
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_le_iff_le_add', le_div_iff₀ hα]
          linarith
      _ = reward m x + (ρ - 1) * (p * X ^ p) / α := by rw [← hXp]; ring
      _ ≤ ρ * reward m x := by
          have : (ρ - 1) * (p * X ^ p) / α ≤ (ρ - 1) * reward m x := by
            rw [div_le_iff₀ hα]
            have h6 : (ρ - 1) * (p * X ^ p) ≤ (ρ - 1) * (α * reward m x) :=
              mul_le_mul_of_nonneg_left i1 (by linarith)
            linarith
          linarith

end Reward

/-! ### `thm:prule`: `R(α) = r(x*(α))/α^{1/(p−1)}` and `h(α) = (1 − α) α^{1/(p−1)}` -/

/-- `R(α) = r(x*(α))/α^{1/(p−1)}` for a choice `xs` of best responses (appE-halfrule.tex:91). -/
noncomputable def ratio (p : ℝ) (m : E → ℝ) (xs : ℝ → E → ℝ) (α : ℝ) : ℝ :=
  reward m (xs α) / α ^ (1 / (p - 1))

/-- `h(α) = (1 − α) α^{1/(p−1)}` (appE-halfrule.tex:95). -/
noncomputable def shape (p : ℝ) (α : ℝ) : ℝ := (1 - α) * α ^ (1 / (p - 1))

/-- **`thm:prule`**, step (6), for two shares: "Applied to the best responses at two shares, this
shows that `R(α) := r(x*(α))/α^{1/(p−1)}` is nonincreasing": for `0 < α < α'`, the bound
`r(xs(α')) ≤ ϱ r(xs(α))` of steps (1)–(5) (`reward_le_rpow_mul`) gives `R(α') ≤ R(α)`. -/
lemma ratio_le {m : E → ℝ} {xs : ℝ → E → ℝ} {α α' : ℝ} (hα : 0 < α) (hαα' : α < α')
    (h : reward m (xs α') ≤ (α' / α) ^ (1 / (p - 1)) * reward m (xs α)) :
    ratio p m xs α' ≤ ratio p m xs α := by
  have hapos : 0 < α ^ (1 / (p - 1)) := Real.rpow_pos_of_pos hα _
  have hbpos : 0 < α' ^ (1 / (p - 1)) := Real.rpow_pos_of_pos (lt_trans hα hαα') _
  rw [Real.div_rpow (le_of_lt (lt_trans hα hαα')) (le_of_lt hα)] at h
  unfold ratio
  rw [div_le_div_iff₀ hbpos hapos]
  rw [div_mul_eq_mul_div, le_div_iff₀ hapos] at h
  linarith

/-- **`thm:prule`**, step (6): "Applied to the best responses at two shares, this shows that
`R(α) := r(x*(α))/α^{1/(p−1)}` is nonincreasing on `(0, ∞)`", for a choice `xs` of best responses
at the shares `α > 0` that satisfies the bound of steps (1)–(5) at any two shares
(`reward_le_rpow_mul`). -/
theorem antitoneOn_ratio {m : E → ℝ} {xs : ℝ → E → ℝ}
    (hgrowth : ∀ α α', 0 < α → α < α' →
      reward m (xs α') ≤ (α' / α) ^ (1 / (p - 1)) * reward m (xs α)) :
    AntitoneOn (ratio p m xs) (Ioi 0) := by
  intro a ha b hb hab
  rcases hab.lt_or_eq with hlt | rfl
  · exact ratio_le ha hlt (hgrowth a b ha hlt)
  · exact le_rfl

/-- **`thm:prule`**, step (7): "its derivative `h'(α) = α^{1/(p−1)−1} (1/(p−1) − p/(p−1) α)`", for
`α > 0`. -/
lemma hasDerivAt_shape (hp : 1 < p) {α : ℝ} (hα : 0 < α) :
    HasDerivAt (shape p) (α ^ (1 / (p - 1) - 1) * (1 / (p - 1) - p / (p - 1) * α)) α := by
  have h1 : HasDerivAt (fun α : ℝ => 1 - α) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub 1
  have h2 : HasDerivAt (fun α : ℝ => α ^ (1 / (p - 1))) (1 / (p - 1) * α ^ (1 / (p - 1) - 1)) α :=
    Real.hasDerivAt_rpow_const (Or.inl hα.ne')
  show HasDerivAt (fun α => (1 - α) * α ^ (1 / (p - 1))) _ α
  convert h1.mul h2 using 1
  have hαq : α ^ (1 / (p - 1)) = α ^ (1 / (p - 1) - 1) * α := by
    rw [← Real.rpow_add_one hα.ne']; ring_nf
  rw [hαq]
  have hp1 : p - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `thm:prule`, step (7): the derivative "shows that `h` is … strictly decreasing on `[1/p, 1]`",
as `h' < 0` on `(1/p, 1)`. -/
lemma strictAntiOn_shape (hp : 1 < p) : StrictAntiOn (shape p) (Icc (1 / p) 1) := by
  have hp0 : 0 < 1 / p := by apply div_pos one_pos; linarith
  have hq0 : 0 < 1 / (p - 1) := by apply div_pos one_pos; linarith
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
      (ContinuousOn.rpow_const continuousOn_id fun x _ => Or.inr hq0.le)
  · intro α hα
    rw [interior_Icc] at hα
    have hα0 : 0 < α := lt_trans hp0 hα.1
    rw [(hasDerivAt_shape hp hα0).deriv]
    have hpos : 0 < α ^ (1 / (p - 1) - 1) := Real.rpow_pos_of_pos hα0 _
    have hlt : 1 / (p - 1) - p / (p - 1) * α < 0 := by
      have hp1 : 0 < p - 1 := by linarith
      rw [div_mul_eq_mul_div, ← sub_div, div_neg_iff]
      right
      refine ⟨?_, hp1⟩
      have := hα.1
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    exact mul_neg_of_pos_of_neg hpos hlt

/-- `thm:prule`, step (7): the derivative "shows that `h` is increasing on `[0, 1/p]`", as `h' > 0`
on `(0, 1/p)`. -/
lemma strictMonoOn_shape (hp : 1 < p) : StrictMonoOn (shape p) (Icc 0 (1 / p)) := by
  have hq0 : 0 < 1 / (p - 1) := by apply div_pos one_pos; linarith
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
      (ContinuousOn.rpow_const continuousOn_id fun x _ => Or.inr hq0.le)
  · intro α hα
    rw [interior_Icc] at hα
    rw [(hasDerivAt_shape hp hα.1).deriv]
    have hpos : 0 < α ^ (1 / (p - 1) - 1) := Real.rpow_pos_of_pos hα.1 _
    have hgt : 0 < 1 / (p - 1) - p / (p - 1) * α := by
      have hp1 : 0 < p - 1 := by linarith
      rw [div_mul_eq_mul_div, ← sub_div]
      refine div_pos ?_ hp1
      have := hα.2
      rw [lt_div_iff₀ (by linarith)] at this
      linarith
    exact mul_pos hpos hgt

/-- `thm:prule`, step (7): "The function `h` is nonnegative on `[0, 1]`". -/
lemma shape_nonneg {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) : 0 ≤ shape p α :=
  mul_nonneg (by linarith [hα.2]) (Real.rpow_nonneg hα.1 _)

lemma inv_mem_Icc (hp : 1 < p) : 1 / p ∈ Icc (0 : ℝ) 1 :=
  ⟨by apply div_nonneg zero_le_one; linarith, by rw [div_le_one (by linarith)]; linarith⟩

/-- `thm:prule`, step (10): `h` "is maximal exactly at `α = 1/p`" on `[0, 1]`, as it is increasing
on `[0, 1/p]` and strictly decreasing on `[1/p, 1]` (step (7)): `h(β) < h(1/p)` for every other
`β ∈ [0, 1]`. -/
lemma shape_lt_inv (hp : 1 < p) {β : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1) (hne : β ≠ 1 / p) :
    shape p β < shape p (1 / p) := by
  have hp1 := inv_mem_Icc hp
  rcases lt_or_gt_of_ne hne with h | h
  · exact strictMonoOn_shape hp ⟨hβ.1, h.le⟩ ⟨hp1.1, le_rfl⟩ h
  · exact strictAntiOn_shape hp ⟨le_rfl, hp1.2⟩ ⟨h.le, hβ.2⟩ h

/-! ### `thm:prule`: `U_P` is nonincreasing on `[1/p, 1]`, and strictly decreasing unless `r ≡ 0`

The second and third paragraphs of the proof of `thm:prule` (appE-halfrule.tex:93-111): "Next we
show that `U_P` is nonincreasing on `[1/p, 1]`." and "Now we show that `U_P` is strictly decreasing
on `[1/p, 1]` unless `r` vanishes on `K`." Like the first paragraph, they are stated for the action
set `K` of `thm:prule`, with the assumptions on it that each step uses. -/

section Profit

variable {K : Set (E → ℝ)} {m : E → ℝ} (xs : ℝ → E → ℝ)

/-- `thm:prule`, step (7): "For `α ∈ (0, 1]`, `U_P(α) = (1 − α) r(x*(α)) = h(α)R(α)`, where
`h(α) := (1 − α) α^{1/(p−1)}`" (here for every `α > 0`). -/
lemma profit_eq_shape_mul_ratio {α : ℝ} (hα : 0 < α) :
    profit (fun α => reward m (xs α)) α = shape p α * ratio p m xs α := by
  have hpos : 0 < α ^ (1 / (p - 1)) := Real.rpow_pos_of_pos hα _
  unfold profit shape ratio
  field_simp

/-- `thm:prule`, step (7): "`R ≥ 0`, as `m ≥ 0` and `x*(α) ≥ 0`", for the action set `K` of
`thm:prule`. -/
lemma ratio_nonneg (hKnn : ∀ x ∈ K, 0 ≤ x) (hm : ∀ e, 0 ≤ m e) {α : ℝ} (hα : 0 < α)
    (hxα : xs α ∈ K) : 0 ≤ ratio p m xs α :=
  div_nonneg (Finset.sum_nonneg fun e _ => mul_nonneg (hm e) (hKnn _ hxα e))
    (Real.rpow_nonneg hα.le _)

/-- **`thm:prule`**, step (8), `eq:E-product`: "So, for `1/p ≤ α < α' ≤ 1`,
`U_P(α) = h(α)R(α) ≥ h(α')R(α) ≥ h(α')R(α') = U_P(α')`, and `U_P` is nonincreasing on `[1/p, 1]`",
as `R` is nonincreasing (step (6)), `R ≥ 0` and `h` is decreasing on `[1/p, 1]` (step (7)). -/
theorem profit_antitoneOn (hp : 1 < p) (hR : AntitoneOn (ratio p m xs) (Ioi 0))
    (hR0 : ∀ α, 0 < α → 0 ≤ ratio p m xs α) :
    AntitoneOn (profit fun α => reward m (xs α)) (Icc (1 / p) 1) := by
  intro α hα α' hα' hle
  have hp0 : 0 < 1 / p := by apply div_pos one_pos; linarith
  have hα0 : 0 < α := hp0.trans_le hα.1
  have hα'0 : 0 < α' := hα0.trans_le hle
  rw [profit_eq_shape_mul_ratio xs hα0, profit_eq_shape_mul_ratio xs hα'0]
  have hRle : ratio p m xs α' ≤ ratio p m xs α := hR hα0 hα'0 hle
  have hh : shape p α' ≤ shape p α := (strictAntiOn_shape hp).antitoneOn hα hα' hle
  have hh0 : 0 ≤ shape p α' := shape_nonneg ⟨hα'0.le, hα'.2⟩
  -- `eq:E-product`: "`U_P(α) = h(α)R(α) ≥ h(α')R(α) ≥ h(α')R(α') = U_P(α')`"
  calc shape p α * ratio p m xs α ≥ shape p α' * ratio p m xs α :=
        mul_le_mul_of_nonneg_right hh (hR0 α hα0)
    _ ≥ shape p α' * ratio p m xs α' := mul_le_mul_of_nonneg_left hRle hh0

variable (hc : IsHomogeneous p c) (hp : 1 < p) (hK : Convex ℝ K) (hKnn : ∀ x ∈ K, 0 ≤ x)
  (h0 : (0 : E → ℝ) ∈ K)

include hc hp hK hKnn h0 in
/-- **`thm:prule`**, step (9) (appE-halfrule.tex:107-110): "Suppose that `r(z) > 0` for some
`z ∈ K`, and let `α > 0`. For `t ∈ (0, 1]`, the point `tz` lies in `K` by convexity and `0 ∈ K`, and
`U_A(tz | α) = tα r(z) − t^p c(z) > 0` for small `t`, as `p > 1`. As `c ≥ 0`,
`α r(x*(α)) ≥ U_A(x*(α) | α) ≥ U_A(tz | α) > 0`." For the action set `K` of `thm:prule`. -/
theorem reward_pos {z : E → ℝ} (hz : z ∈ K) (hrz : 0 < reward m z) {α : ℝ} (hα : 0 < α)
    {x : E → ℝ} (hx : IsBR K m c α x) : 0 < reward m x := by
  have hA : 0 < α * reward m z := mul_pos hα hrz
  -- "`U_A(tz | α) = tα r(z) − t^p c(z) > 0` for small `t`, as `p > 1`": some `t ∈ (0, 1]` with
  -- `t^{p−1} c(z) < α r(z)`
  have hlim : Tendsto (fun t : ℝ => t ^ (p - 1) * c z) (𝓝[>] 0)
      (𝓝 ((0 : ℝ) ^ (p - 1) * c z)) := by
    have : ContinuousAt (fun t : ℝ => t ^ (p - 1) * c z) 0 :=
      (continuousAt_id.rpow_const (Or.inr (by linarith))).mul continuousAt_const
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  rw [Real.zero_rpow (by linarith), zero_mul] at hlim
  obtain ⟨t, ht, ht1⟩ := ((hlim.eventually (gt_mem_nhds hA)).and
    (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  -- "the point `tz` lies in `K` by convexity and `0 ∈ K`"
  have htK : t • z ∈ K := hK.smul_mem_of_zero_mem h0 hz ⟨ht1.1.le, ht1.2⟩
  have hUtz : util m c α (t • z) = t * (α * reward m z - t ^ (p - 1) * c z) := by
    have hct : c (t • z) = t ^ p * c z := hc.hom z (hKnn z hz) t ht1.1
    have hrt : reward m (t • z) = t * reward m z := by
      simp only [reward, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    have htp : t ^ p = t * t ^ (p - 1) := by
      rw [mul_comm, rpow_sub_one_mul_self ht1.1.le hp]
    rw [util, hct, hrt, htp]
    ring
  have hpos : 0 < util m c α (t • z) := by
    rw [hUtz]
    exact mul_pos ht1.1 (by linarith)
  -- "As `c ≥ 0`, `α r(x*(α)) ≥ U_A(x*(α) | α) ≥ U_A(tz | α) > 0`."
  have hcx := hc.nonneg x (hKnn x hx.1)
  have : 0 < α * reward m x := by
    calc 0 < util m c α (t • z) := hpos
      _ ≤ util m c α x := hx.2 _ htK
      _ ≤ α * reward m x := by unfold util; linarith
  exact pos_of_mul_pos_right this hα.le

include hc hp hK hKnn h0 in
/-- **`thm:prule`**, step (9): if `r(z) > 0` for some `z ∈ K`, then "`R > 0` on `(0, ∞)`, and the
first inequality in `eq:E-product` is strict. Hence `U_P` is strictly decreasing on `[1/p, 1]`", for
a choice `xs` of maximizers on `[1/p, 1]` with `R` nonincreasing (step (6)), for the action set `K`
of `thm:prule`. -/
theorem profit_strictAntiOn (hxs : ∀ α ∈ Icc (1 / p) 1, IsBR K m c α (xs α))
    (hR : AntitoneOn (ratio p m xs) (Ioi 0)) {z : E → ℝ} (hz : z ∈ K) (hrz : 0 < reward m z) :
    StrictAntiOn (profit fun α => reward m (xs α)) (Icc (1 / p) 1) := by
  intro α hα α' hα' hlt
  have hp0 : 0 < 1 / p := by apply div_pos one_pos; linarith
  have hα0 : 0 < α := hp0.trans_le hα.1
  have hα'0 : 0 < α' := hα0.trans hlt
  rw [profit_eq_shape_mul_ratio xs hα0, profit_eq_shape_mul_ratio xs hα'0]
  have hRle : ratio p m xs α' ≤ ratio p m xs α := hR hα0 hα'0 hlt.le
  -- "So `R > 0` on `(0, ∞)`"
  have hR0 : 0 < ratio p m xs α :=
    div_pos (reward_pos hc hp hK hKnn h0 hz hrz hα0 (hxs α hα)) (Real.rpow_pos_of_pos hα0 _)
  have hh : shape p α' < shape p α := strictAntiOn_shape hp hα hα' hlt
  have hh0 : 0 ≤ shape p α' := shape_nonneg ⟨hα'0.le, hα'.2⟩
  -- "and the first inequality in `eq:E-product` is strict"
  calc shape p α * ratio p m xs α > shape p α' * ratio p m xs α := mul_lt_mul_of_pos_right hh hR0
    _ ≥ shape p α' * ratio p m xs α' := mul_le_mul_of_nonneg_left hRle hh0

include hc hp hK hKnn h0 in
/-- **`thm:prule`**, step (9): "so `U_P(α) < U_P(1/p)` for `α ∈ (1/p, 1]`, and every optimal
contract has a share in `[0, 1/p]`", for the action set `K` of `thm:prule`. -/
theorem le_inv_of_isMaxOn (hxs : ∀ α ∈ Icc (1 / p) 1, IsBR K m c α (xs α))
    (hR : AntitoneOn (ratio p m xs) (Ioi 0)) {z : E → ℝ} (hz : z ∈ K) (hrz : 0 < reward m z)
    {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1)
    (hmax : IsMaxOn (profit fun α => reward m (xs α)) (Icc 0 1) α) : α ≤ 1 / p := by
  by_contra hgt
  push Not at hgt
  have hp1 := inv_mem_Icc hp
  have hlt := profit_strictAntiOn xs hc hp hK hKnn h0 hxs hR hz hrz ⟨le_rfl, hp1.2⟩
    ⟨hgt.le, hα.2⟩ hgt
  exact absurd (isMaxOn_iff.1 hmax (1 / p) hp1) (not_le.2 hlt)

/-- `thm:prule`, step (9), its last sentence: "If, in contrast, `r` vanishes on `K`, then `U_P ≡ 0`
and every share is optimal." (Not part of the statement of `thm:prule`; `prule` records it in a
`have`.) For the action set `K` of `thm:prule`. -/
theorem profit_eq_zero (hxK : ∀ α ∈ Icc (0 : ℝ) 1, xs α ∈ K) (hr : ∀ z ∈ K, reward m z = 0) :
    ∀ α ∈ Icc (0 : ℝ) 1, profit (fun α => reward m (xs α)) α = 0 ∧
      IsMaxOn (profit fun α => reward m (xs α)) (Icc 0 1) α := by
  have h0 : ∀ α ∈ Icc (0 : ℝ) 1, profit (fun α => reward m (xs α)) α = 0 := fun α hα => by
    simp only [profit, hr _ (hxK α hα), mul_zero]
  exact fun α hα => ⟨h0 α hα, isMaxOn_iff.2 fun β hβ => by rw [h0 α hα, h0 β hβ]⟩

end Profit

/-! ### `thm:prule`: the bound `1/p` is attained

The last paragraph of the proof of `thm:prule` (appE-halfrule.tex:113): "Finally, we show that the
bound `1/p` on the share of an optimal contract is attained." -/

section Example

/-- The cost `c(x) = x^p/p` of one element. -/
noncomputable def exCost (p : ℝ) (x : Unit → ℝ) : ℝ := x () ^ p / p

/-- `thm:prule`, step (10): the cost `c(x) = x^p/p` of the example is homogeneous of degree `p`
(not in the paper: the last paragraph of the proof of `thm:prule` takes the example as an instance
of the theorem without saying so). -/
lemma ex_isHomogeneous (hp : 1 < p) : IsHomogeneous p (exCost p) where
  nonneg x hx := div_nonneg (Real.rpow_nonneg (hx ()) _) (by linarith)
  zero := by simp [exCost, Real.zero_rpow (by linarith : p ≠ 0)]
  convexOn := by
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have h := (convexOn_rpow hp.le).2 (mem_Ici.2 ((mem_Ici.1 hx) ()))
      (mem_Ici.2 ((mem_Ici.1 hy) ())) ha hb hab
    simp only [smul_eq_mul] at h
    simp only [exCost, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hp0 : 0 < p := by linarith
    calc (a * x () + b * y ()) ^ p / p ≤ (a * x () ^ p + b * y () ^ p) / p :=
          div_le_div_of_nonneg_right h hp0.le
      _ = a * (x () ^ p / p) + b * (y () ^ p / p) := by ring
  continuousOn := by
    refine Continuous.continuousOn ?_
    unfold exCost
    exact ((continuous_apply ()).rpow_const fun _ => Or.inr (by linarith)).div_const _
  hom := by
    intro x hx t ht
    simp only [exCost, Pi.smul_apply, smul_eq_mul]
    rw [Real.mul_rpow ht.le (hx ())]
    ring

/-- The agent's problem `max α u − u^p/p` over `u ≥ 0`: `u = α^{1/(p−1)}` is the unique
maximizer, by Bernoulli's inequality (not in the paper: the last paragraph of the proof of
`thm:prule`, appE-halfrule.tex:113, asserts `x*(α) = α^{1/(p−1)}` without proof; this is the core of
`ex_isBR_iff`). -/
lemma ex_key (hp : 1 < p) {α u : ℝ} (hα : 0 ≤ α) (hu : 0 ≤ u) :
    α * u - u ^ p / p ≤ α * α ^ (1 / (p - 1)) - (α ^ (1 / (p - 1))) ^ p / p ∧
      (α * u - u ^ p / p = α * α ^ (1 / (p - 1)) - (α ^ (1 / (p - 1))) ^ p / p →
        u = α ^ (1 / (p - 1))) := by
  have hp0 : 0 < p := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  set x0 := α ^ (1 / (p - 1)) with hx0def
  have hx00 : 0 ≤ x0 := Real.rpow_nonneg hα _
  have hx0p : x0 ^ (p - 1) = α := by
    rw [hx0def, one_div, Real.rpow_inv_rpow hα hp1]
  rcases hα.lt_or_eq with hαpos | hα0
  · -- `α > 0`: Bernoulli with `s = u/x0 − 1`.
    have hx0 : 0 < x0 := Real.rpow_pos_of_pos hαpos _
    have hs : -1 ≤ u / x0 - 1 := by have := div_nonneg hu hx0.le; linarith
    have e1 : (1 + (u / x0 - 1)) ^ p = u ^ p / x0 ^ p := by
      rw [show 1 + (u / x0 - 1) = u / x0 by ring, Real.div_rpow hu hx0.le]
    have hx0pp : x0 ^ p = α * x0 := by
      rw [← rpow_sub_one_mul_self hx00 hp, hx0p]
    have hx0ppos : 0 < x0 ^ p := Real.rpow_pos_of_pos hx0 _
    -- `u^p ≥ x0^p + p α (u − x0)`, strictly if `u ≠ x0`
    have e2 : (1 + p * (u / x0 - 1)) * x0 ^ p = x0 ^ p + p * α * (u - x0) := by
      rw [hx0pp]; field_simp
    have hdiff : (α * x0 - x0 ^ p / p) - (α * u - u ^ p / p) =
        (u ^ p - (x0 ^ p + p * α * (u - x0))) / p := by
      field_simp
      ring
    have hle : x0 ^ p + p * α * (u - x0) ≤ u ^ p := by
      have h := one_add_mul_self_le_rpow_one_add hs hp.le
      rw [e1, le_div_iff₀ hx0ppos, e2] at h
      exact h
    refine ⟨?_, fun heq => ?_⟩
    · have := div_nonneg (sub_nonneg.2 hle) hp0.le
      rw [← hdiff] at this
      linarith
    · by_contra hne
      have hs0 : u / x0 - 1 ≠ 0 := by
        intro h
        apply hne
        have : u / x0 = 1 := by linarith
        rwa [div_eq_one_iff_eq hx0.ne'] at this
      have hlt := one_add_mul_self_lt_rpow_one_add hs hs0 hp
      rw [e1, lt_div_iff₀ hx0ppos, e2] at hlt
      have := div_pos (sub_pos.2 hlt) hp0
      rw [← hdiff] at this
      linarith
  · -- `α = 0`: `x0 = 0` and `−u^p/p ≤ 0`, with equality only at `u = 0`.
    subst hα0
    have hx0z : x0 = 0 := by
      rw [hx0def, Real.zero_rpow (by apply one_div_ne_zero; exact hp1)]
    rw [hx0z, Real.zero_rpow hp0.ne']
    simp only [zero_mul, zero_div, sub_zero, zero_sub]
    have hup : 0 ≤ u ^ p / p := div_nonneg (Real.rpow_nonneg hu _) hp0.le
    refine ⟨by linarith, fun heq => ?_⟩
    have : u ^ p = 0 := by
      have : u ^ p / p = 0 := by linarith
      rcases div_eq_zero_iff.1 this with h | h
      · exact h
      · exact absurd h hp0.ne'
    exact (Real.rpow_eq_zero hu hp0.ne').1 this

lemma ex_util (α : ℝ) (z : Unit → ℝ) : util 1 (exCost p) α z = α * z () - z () ^ p / p := by
  simp [util, reward, exCost]

/-- `thm:prule`, step (10): "the agent maximizes `αx − x^p/p` over `[0, 1]`, so
`x*(α) = α^{1/(p−1)}` for `α ∈ [0, 1]`" (not in the paper: it asserts this; here with
uniqueness, by Bernoulli's inequality, `ex_key`). -/
theorem ex_isBR_iff (hp : 1 < p) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) {x : Unit → ℝ} :
    IsBR (indepPoly (oneF 1)) 1 (exCost p) α x ↔ x = fun _ => α ^ (1 / (p - 1)) := by
  have hq : 0 ≤ 1 / (p - 1) := by apply div_nonneg zero_le_one; linarith
  have hx0mem : (fun _ => α ^ (1 / (p - 1)) : Unit → ℝ) ∈ indepPoly (oneF 1) :=
    mem_indepPoly_oneF.2 ⟨Real.rpow_nonneg hα.1 _, Real.rpow_le_one hα.1 hα.2 hq⟩
  constructor
  · intro hx
    have hle := hx.2 _ hx0mem
    rw [ex_util, ex_util] at hle
    have key := ex_key hp hα.1 (mem_indepPoly_oneF.1 hx.1).1
    funext u
    exact key.2 (le_antisymm key.1 hle)
  · rintro rfl
    refine ⟨hx0mem, fun z hz => ?_⟩
    rw [ex_util, ex_util]
    exact (ex_key hp hα.1 (mem_indepPoly_oneF.1 hz).1).1

/-- `thm:prule`, step (10): in the example, "`U_P = h` on `[0, 1]`", as `x*(α) = α^{1/(p−1)}` there
(`ex_isBR_iff`), for every choice of best responses. -/
lemma ex_profit_eq (hp : 1 < p) (xs : ℝ → Unit → ℝ)
    (hxs : ∀ α ∈ Icc (0 : ℝ) 1, IsBR (indepPoly (oneF 1)) 1 (exCost p) α (xs α)) {β : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) : profit (fun α => reward 1 (xs α)) β = shape p β := by
  rw [profit, (ex_isBR_iff hp hβ).1 (hxs β hβ)]
  simp [reward, shape]

/-- **`thm:prule`**, step (10) (appE-halfrule.tex:113): in the example, "`U_P = h` on `[0, 1]`,
which is maximal exactly at `α = 1/p`", for every choice of best responses. -/
theorem ex_isMaxOn_iff (hp : 1 < p) (xs : ℝ → Unit → ℝ)
    (hxs : ∀ α ∈ Icc (0 : ℝ) 1, IsBR (indepPoly (oneF 1)) 1 (exCost p) α (xs α)) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) :
    IsMaxOn (profit fun α => reward 1 (xs α)) (Icc 0 1) α ↔ α = 1 / p := by
  -- "`U_P = h` on `[0, 1]`"
  have hU : ∀ β ∈ Icc (0 : ℝ) 1, profit (fun α => reward 1 (xs α)) β = shape p β :=
    fun β hβ => ex_profit_eq hp xs hxs hβ
  -- "which is maximal exactly at `α = 1/p`": `h` increases on `[0, 1/p]` and decreases on
  -- `[1/p, 1]`
  have hp1 := inv_mem_Icc hp
  have hlt : ∀ β ∈ Icc (0 : ℝ) 1, β ≠ 1 / p → shape p β < shape p (1 / p) :=
    fun β hβ hne => shape_lt_inv hp hβ hne
  constructor
  · intro hmax
    by_contra hne
    have h1 := isMaxOn_iff.1 hmax (1 / p) hp1
    rw [hU _ hp1, hU _ hα] at h1
    exact absurd h1 (not_le.2 (hlt α hα hne))
  · rintro rfl
    refine isMaxOn_iff.2 fun β hβ => ?_
    rw [hU _ hβ, hU _ hp1]
    rcases eq_or_ne β (1 / p) with h | h
    · rw [h]
    · exact (hlt β hβ h).le

/-- The action set `K = [0, 1]` of the example (appE-halfrule.tex:113) is `P₊(f)` for one element
with `f({e}) = 1`. -/
lemma Icc_eq_indepPoly_oneF : Icc (0 : Unit → ℝ) 1 = indepPoly (oneF 1) := by
  ext x
  rw [mem_indepPoly_oneF, mem_Icc]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨h0 (), h1 ()⟩
  · rintro ⟨h0, h1⟩
    exact ⟨fun _ => h0, fun _ => h1⟩

/-- `thm:prule`, step (10): in the example, `x*(α) = α^{1/(p−1)}` is the best response of the model
at every share `α ∈ [0, 1]` on `K = [0, 1]`, as it is the only maximizer (`ex_isBR_iff`), so that
the tie-breaking does not matter. -/
lemma ex_isPBR (hp : 1 < p) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    IsPBR (Icc 0 1) 1 (exCost p) α (fun _ => α ^ (1 / (p - 1))) := by
  rw [Icc_eq_indepPoly_oneF]
  refine ⟨(ex_isBR_iff hp hα).2 rfl, fun y hy => ?_⟩
  rw [(ex_isBR_iff hp hα).1 hy]

/-- `thm:prule`, "This bound is tight": in the example, no `ᾱ ∈ [0, 1/p)` is a share bound, for
every choice of best responses (not in the paper: the last paragraph of its proof shows that the
bound `1/p` on the share of an optimal contract is attained, as `U_P = h` is maximal exactly at
`1/p` (`ex_isMaxOn_iff`), and leaves implicit that a smaller `ᾱ` is then no share bound: `U_P = h`
is increasing on `[0, 1/p]`, so `sup_{α ∈ [0, ᾱ]} U_P(α) = h(ᾱ) < h(1/p) = OPT`). -/
theorem ex_not_isShareBound (hp : 1 < p) (xs : ℝ → Unit → ℝ)
    (hxs : ∀ α ∈ Icc (0 : ℝ) 1, IsBR (indepPoly (oneF 1)) 1 (exCost p) α (xs α)) {ᾱ : ℝ}
    (hᾱ : ᾱ ∈ Ico (0 : ℝ) (1 / p)) :
    ¬ IsShareBound (profit fun α => reward 1 (xs α)) ᾱ := by
  intro hsb
  have hp1 := inv_mem_Icc hp
  have hmem : ᾱ ∈ Icc (0 : ℝ) (1 / p) := ⟨hᾱ.1, hᾱ.2.le⟩
  -- `OPT = U_P(1/p)`, as `1/p` is optimal
  have hmax := (ex_isMaxOn_iff hp xs hxs hp1).2 rfl
  have hopt : OPT (profit fun α => reward 1 (xs α)) =
      profit (fun α => reward 1 (xs α)) (1 / p) :=
    IsGreatest.csSup_eq ⟨mem_image_of_mem _ hp1, by
      rintro _ ⟨β, hβ, rfl⟩
      exact isMaxOn_iff.1 hmax β hβ⟩
  -- on `[0, ᾱ] ⊆ [0, 1/p]`, `U_P = h` is at most `h(ᾱ) < h(1/p)`
  have hsup : sSup ((profit fun α => reward 1 (xs α)) '' Icc 0 ᾱ) ≤ shape p ᾱ := by
    refine csSup_le ⟨_, mem_image_of_mem _ (show (0 : ℝ) ∈ Icc 0 ᾱ from ⟨le_rfl, hᾱ.1⟩)⟩ ?_
    rintro _ ⟨β, hβ, rfl⟩
    rw [ex_profit_eq hp xs hxs ⟨hβ.1, hβ.2.trans (hmem.2.trans hp1.2)⟩]
    exact (strictMonoOn_shape hp).monotoneOn ⟨hβ.1, hβ.2.trans hmem.2⟩ hmem hβ.2
  have hh := strictMonoOn_shape hp hmem ⟨hp1.1, le_rfl⟩ hᾱ.2
  rw [← ex_profit_eq hp xs hxs hp1, ← hopt, ← hsb.2.2] at hh
  linarith

end Example

/-! ### The unconstrained setting -/

/-- The reward is linear: `r(t x) = t r(x)`. -/
lemma reward_smul (m x : E → ℝ) (t : ℝ) : reward m (t • x) = t * reward m x := by
  simp only [reward, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- 08-approximation.tex:27: "substituting `x = α^{1/(p−1)} y` in the agent's objective gives
`α r(x) − c(x) = α^{p/(p−1)}(r(y) − c(y))`", for `α > 0` and `y ≥ 0`, with costs homogeneous of
degree `p > 1`. -/
lemma util_rpow_smul (hc : IsHomogeneous p c) (hp : 1 < p) (m : E → ℝ) {α : ℝ} (hα : 0 < α)
    {y : E → ℝ} (hy : 0 ≤ y) :
    util m c α (α ^ (1 / (p - 1)) • y) = α ^ (p / (p - 1)) * util m c 1 y := by
  have ht : 0 < α ^ (1 / (p - 1)) := Real.rpow_pos_of_pos hα _
  have hp1 : p - 1 ≠ 0 := by linarith
  -- `α α^{1/(p−1)} = α^{p/(p−1)}` and `(α^{1/(p−1)})^p = α^{p/(p−1)}`
  have e1 : α * α ^ (1 / (p - 1)) = α ^ (p / (p - 1)) := by
    have e : p / (p - 1) = 1 + 1 / (p - 1) := by
      field_simp
      ring
    rw [e, Real.rpow_add hα, Real.rpow_one]
  have e2 : (α ^ (1 / (p - 1))) ^ p = α ^ (p / (p - 1)) := by
    rw [← Real.rpow_mul hα.le]
    congr 1
    field_simp
  rw [util, util, hc.hom y hy _ ht, reward_smul, ← mul_assoc, e1, e2]
  ring

/-- 08-approximation.tex:27, the unconstrained setting: "When `K = ℝ^E_{≥0}`, if the best
response exists and is unique, then `x*(α) = α^{1/(p−1)} x*(1)` for `α > 0`. Indeed, substituting
`x = α^{1/(p−1)} y` in the agent's objective gives `α r(x) − c(x) = α^{p/(p−1)}(r(y) − c(y))`. The
principal's utility is therefore proportional to `(1 − α)α^{1/(p−1)}`, which is maximized at
`α = 1/p`." For costs homogeneous of degree `p > 1` on `K = ℝ^E_{≥0}` (`Ici 0`) whose best responses
`x*(α) = xs α` exist and are unique at every share `α > 0`: `x*(α) = α^{1/(p−1)} x*(1)` and
`U_P(α) = h(α) r(x*(1))` with `h(α) = (1 − α)α^{1/(p−1)}` (`shape`) for `α > 0`, and `h` is maximal
on `[0, 1]` exactly at `1/p` (`shape_lt_inv`). The substitution is `util_rpow_smul`; that it maps
the maximizers at `1` to maximizers at `α`, as `y ↦ α^{1/(p−1)} y` maps `ℝ^E_{≥0}` onto itself, is
left implicit. -/
theorem unconstrained (hc : IsHomogeneous p c) (hp : 1 < p) {m : E → ℝ} {xs : ℝ → E → ℝ}
    (hxs : ∀ α, 0 < α → ∀ y, IsBR (Ici 0) m c α y ↔ y = xs α) :
    (∀ α, 0 < α → xs α = α ^ (1 / (p - 1)) • xs 1) ∧
    (∀ α, 0 < α → profit (fun α => reward m (xs α)) α = shape p α * reward m (xs 1)) ∧
    IsMaxOn (shape p) (Icc 0 1) (1 / p) ∧
    ∀ α ∈ Icc (0 : ℝ) 1, α ≠ 1 / p → shape p α < shape p (1 / p) := by
  have hx1 : IsBR (Ici 0) m c 1 (xs 1) := (hxs 1 one_pos _).2 rfl
  -- "if the best response exists and is unique, then `x*(α) = α^{1/(p−1)} x*(1)` for `α > 0`.
  -- Indeed, substituting `x = α^{1/(p−1)} y` in the agent's objective gives
  -- `α r(x) − c(x) = α^{p/(p−1)}(r(y) − c(y))`": so `α^{1/(p−1)} x*(1)` maximizes `U_A(· | α)`
  have hscale : ∀ α, 0 < α → xs α = α ^ (1 / (p - 1)) • xs 1 := by
    intro α hα
    have ht : 0 < α ^ (1 / (p - 1)) := Real.rpow_pos_of_pos hα _
    have hk : 0 < α ^ (p / (p - 1)) := Real.rpow_pos_of_pos hα _
    refine ((hxs α hα _).1 ⟨mem_Ici.2 (smul_nonneg' ht.le (mem_Ici.1 hx1.1)), fun z hz => ?_⟩).symm
    -- `z = α^{1/(p−1)} (α^{−1/(p−1)} z)`
    have hz' : 0 ≤ (α ^ (1 / (p - 1)))⁻¹ • z := smul_nonneg' (inv_nonneg.2 ht.le) (mem_Ici.1 hz)
    have hzeq : z = α ^ (1 / (p - 1)) • ((α ^ (1 / (p - 1)))⁻¹ • z) := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    rw [hzeq, util_rpow_smul hc hp m hα hz', util_rpow_smul hc hp m hα (mem_Ici.1 hx1.1)]
    exact mul_le_mul_of_nonneg_left (hx1.2 _ (mem_Ici.2 hz')) hk.le
  -- "The principal's utility is therefore proportional to `(1 − α)α^{1/(p−1)}`, …"
  have hprofit : ∀ α, 0 < α →
      profit (fun α => reward m (xs α)) α = shape p α * reward m (xs 1) := by
    intro α hα
    rw [profit, hscale α hα, reward_smul, shape]
    ring
  -- "… which is maximized at `α = 1/p`"
  refine ⟨hscale, hprofit, isMaxOn_iff.2 fun β hβ => ?_, fun α hα hne => shape_lt_inv hp hα hne⟩
  rcases eq_or_ne β (1 / p) with h | h
  · rw [h]
  · exact (shape_lt_inv hp hβ h).le

/-! ### `thm:prule` -/

/-- `ᾱ ∈ [0, 1)` is a share bound if `U_P = (1 − α) S(α)` is nonincreasing on `[ᾱ, 1]`, for a reward
curve `S` that is nonnegative and nondecreasing on `[0, 1]` (not in the paper: the proof of
`thm:prule` shows that `U_P` is nonincreasing on `[1/p, 1]` and leaves implicit that `1/p` is then a
share bound; the prose before the theorem: "Since `(1 − α)α^{1/(p−1)}` is decreasing beyond `1/p`,
so is the principal's utility there. Thus the unconstrained optimal share remains a tight upper
bound on the shares that need to be searched", 08-approximation.tex:29). -/
lemma isShareBound_of_antitoneOn {S : ℝ → ℝ} (hmono : MonotoneOn S (Icc 0 1))
    (hnn : ∀ α ∈ Icc (0 : ℝ) 1, 0 ≤ S α) {ᾱ : ℝ} (hᾱ : ᾱ ∈ Ico (0 : ℝ) 1)
    (hanti : AntitoneOn (profit S) (Icc ᾱ 1)) : IsShareBound (profit S) ᾱ := by
  have hsub : Icc (0 : ℝ) ᾱ ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hᾱ.2.le
  have hmem : ᾱ ∈ Icc (0 : ℝ) ᾱ := ⟨hᾱ.1, le_rfl⟩
  have hbdd := bddAbove_profit hmono hnn _ hsub
  refine ⟨hᾱ.1, hᾱ.2, le_antisymm ?_ ?_⟩
  · exact csSup_le_csSup (bddAbove_profit hmono hnn _ le_rfl) ⟨_, mem_image_of_mem _ hmem⟩
      (image_mono hsub)
  · refine csSup_le ⟨_, mem_image_of_mem _ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
      ⟨le_rfl, zero_le_one⟩)⟩ ?_
    rintro _ ⟨α, hα, rfl⟩
    rcases le_or_gt α ᾱ with h | h
    · exact le_csSup hbdd (mem_image_of_mem _ ⟨hα.1, h⟩)
    · exact (hanti ⟨le_rfl, hᾱ.2.le⟩ ⟨h.le, hα.2⟩ h.le).trans
        (le_csSup hbdd (mem_image_of_mem _ hmem))

/-- **`thm:prule`** (Theorem 5.3, 08-approximation.tex:31-33, proof appE-halfrule.tex:78-114): "For
homogeneous costs of degree `p > 1`, `ᾱ = 1/p` is a share bound. This bound is tight."

Here, on a compact convex action set `K ⊆ ℝ^E_{≥0}` with `0 ∈ K` (08-approximation.tex:4), with
rewards `m ≥ 0` and costs homogeneous of degree `p > 1`:
(a) for every choice of the best responses `x*(α)` of the model at the shares `α ∈ [0, 1]`
(`IsPBR`), `1/p` is a share bound of `U_P(α) = (1 − α) r(x*(α))`;
(b) the bound is tight: the instance of the last paragraph of the proof, one element with
`K = [0, 1]`, `m_e = 1` and `c(x) = x^p/p` (`exCost`), whose cost is homogeneous of degree `p` and
whose best responses exist, has for every choice of them the optimal share `1/p` ("the bound `1/p`
on the share of an optimal contract is attained"), and no `ᾱ ∈ [0, 1/p)` is a share bound for it.
The theorem does not state its assumptions on `K`; its proof uses them ("the point `tz` lies in `K`
by convexity and `0 ∈ K`", appE-halfrule.tex:107, and the maximizers over `K`), and Section 5 states
them (08-approximation.tex:4, and `cor:fptashom`, 08-approximation.tex:37).

The proof, paragraph by paragraph. It takes the best responses `x*(α)` at all shares `α > 0` ("on
`(0, ∞)`"): beyond `1`, maximizers of `U_A(· | α)` exist as `c` is continuous on the compact set `K`
("Both hold when `c` is continuous on the compact set", 02-preliminaries.tex:17; `exists_isBR`).
"We first show that the reward grows at most like `α^{1/(p−1)}`": steps (1)–(5)
(`reward_le_rpow_mul`, which cites `lem:foc` in the form `foc_aux`, with step (4)
`cnorm_le_rpow_mul_of_lt`) and step (6) (`antitoneOn_ratio`, `ratio_le`).
"Next we show that `U_P` is nonincreasing on `[1/p, 1]`": step (7) (`profit_eq_shape_mul_ratio`,
`shape_nonneg`, `hasDerivAt_shape`, `strictMonoOn_shape`, `strictAntiOn_shape`, `ratio_nonneg`) and
step (8), `eq:E-product` (`profit_antitoneOn`); so `1/p` is a share bound
(`isShareBound_of_antitoneOn`, not in the paper), which is (a).
"Now we show that `U_P` is strictly decreasing on `[1/p, 1]` unless `r` vanishes on `K`": step (9)
(`reward_pos`, `profit_strictAntiOn`, `le_inv_of_isMaxOn`, `profit_eq_zero`), which (a) and (b) do
not use; `prule` records it in `have`s.
"Finally, we show that the bound `1/p` on the share of an optimal contract is attained": step (10)
(`ex_isHomogeneous`, `ex_isBR_iff` with `ex_key`, `ex_isPBR`, `ex_isMaxOn_iff` with `ex_profit_eq`,
on `[0, 1] = P₊(oneF 1)`, `Icc_eq_indepPoly_oneF`); so no smaller number is a share bound
(`ex_not_isShareBound`, not in the paper), which is (b). -/
theorem prule {K : Set (E → ℝ)} (hKc : IsCompact K) (hK : Convex ℝ K) (hKnn : ∀ x ∈ K, 0 ≤ x)
    (h0 : (0 : E → ℝ) ∈ K) {m : E → ℝ} (hm : ∀ e, 0 ≤ m e) (hc : IsHomogeneous p c)
    (hp : 1 < p) :
    (∀ xs : ℝ → E → ℝ, (∀ α ∈ Icc (0 : ℝ) 1, IsPBR K m c α (xs α)) →
      IsShareBound (profit fun α => reward m (xs α)) (1 / p)) ∧
    ∃ (m' : Unit → ℝ) (c' : (Unit → ℝ) → ℝ), (∀ e, 0 ≤ m' e) ∧ IsHomogeneous p c' ∧
      (∃ xs : ℝ → Unit → ℝ, ∀ α ∈ Icc (0 : ℝ) 1, IsPBR (Icc 0 1) m' c' α (xs α)) ∧
      ∀ xs : ℝ → Unit → ℝ, (∀ α ∈ Icc (0 : ℝ) 1, IsPBR (Icc 0 1) m' c' α (xs α)) →
        IsMaxOn (profit fun α => reward m' (xs α)) (Icc 0 1) (1 / p) ∧
        ∀ ᾱ ∈ Ico (0 : ℝ) (1 / p), ¬ IsShareBound (profit fun α => reward m' (xs α)) ᾱ := by
  have hp1 := inv_mem_Icc hp
  have hp0 : 0 < 1 / p := by apply div_pos one_pos; linarith
  have hplt : 1 / p < 1 := by rw [div_lt_one (by linarith)]; exact hp
  refine ⟨fun xs hxs => ?_, ?_⟩
  · -- the best responses `x*(α)` at the shares `α > 1`, which the proof takes on `(0, ∞)`:
    -- maximizers exist, as `c` is continuous on the compact set `K`
    classical
    have hex : ∀ α, ∃ x, IsBR K m c α x := fun α =>
      exists_isBR hKc ⟨0, h0⟩ (hc.continuousOn.mono fun x hx => mem_Ici.2 (hKnn x hx)) α
    set xs' : ℝ → E → ℝ := fun α => if α ≤ 1 then xs α else (hex α).choose with hxs'def
    have heq : ∀ α, α ≤ 1 → xs' α = xs α := fun α hα => by
      simp only [hxs'def, hα, ↓reduceIte]
    have hxs' : ∀ α, 0 < α → IsBR K m c α (xs' α) := fun α hα => by
      by_cases h : α ≤ 1
      · rw [heq α h]
        exact (hxs α ⟨hα.le, h⟩).isBR
      · simp only [hxs'def, h, ↓reduceIte]
        exact (hex α).choose_spec
    -- (1)–(5) "We first show that the reward grows at most like `α^{1/(p−1)}`. Let `0 < α < α'`,
    -- let `x` and `y` maximize `U_A(· | α)` and `U_A(· | α')` over `K`, … `r(y) ≤ ϱ r(x)`."
    have h15 : ∀ α α', 0 < α → α < α' →
        reward m (xs' α') ≤ (α' / α) ^ (1 / (p - 1)) * reward m (xs' α) :=
      fun α α' hα hαα' => reward_le_rpow_mul hc hp hKc hK hKnn h0 hα hαα' (hxs' α hα)
        (hxs' α' (hα.trans hαα'))
    -- (6) "Applied to the best responses at two shares, this shows that
    -- `R(α) := r(x*(α))/α^{1/(p−1)}` is nonincreasing on `(0, ∞)`."
    have hR : AntitoneOn (ratio p m xs') (Ioi 0) := antitoneOn_ratio h15
    -- (7) "Next we show that `U_P` is nonincreasing on `[1/p, 1]`. For `α ∈ (0, 1]`,
    -- `U_P(α) = (1 − α) r(x*(α)) = h(α)R(α)`, where `h(α) := (1 − α) α^{1/(p−1)}`." … "Moreover,
    -- `R ≥ 0`, as `m ≥ 0` and `x*(α) ≥ 0`."
    have hR0 : ∀ α, 0 < α → 0 ≤ ratio p m xs' α := fun α hα =>
      ratio_nonneg xs' hKnn hm hα (hxs' α hα).1
    -- (8) "So, for `1/p ≤ α < α' ≤ 1`, `U_P(α) = h(α)R(α) ≥ h(α')R(α) ≥ h(α')R(α') = U_P(α')`,
    -- and `U_P` is nonincreasing on `[1/p, 1]`."
    have hU' := profit_antitoneOn xs' hp hR hR0
    have hU : AntitoneOn (profit fun α => reward m (xs α)) (Icc (1 / p) 1) := by
      intro α hα α' hα' hle
      have h := hU' hα hα' hle
      simp only [profit] at h ⊢
      rwa [heq α hα.2, heq α' hα'.2] at h
    -- (9) "Now we show that `U_P` is strictly decreasing on `[1/p, 1]` unless `r` vanishes on `K`.
    -- … Hence `U_P` is strictly decreasing on `[1/p, 1]`, so `U_P(α) < U_P(1/p)` for
    -- `α ∈ (1/p, 1]`, and every optimal contract has a share in `[0, 1/p]`. If, in contrast, `r`
    -- vanishes on `K`, then `U_P ≡ 0` and every share is optimal." ((a) does not use it.)
    have hxsI : ∀ α ∈ Icc (1 / p) 1, IsBR K m c α (xs' α) := fun α hα =>
      hxs' α (hp0.trans_le hα.1)
    have _h9 : (∃ z ∈ K, 0 < reward m z) →
        StrictAntiOn (profit fun α => reward m (xs' α)) (Icc (1 / p) 1) ∧
        ∀ αs ∈ Icc (0 : ℝ) 1, IsMaxOn (profit fun α => reward m (xs' α)) (Icc 0 1) αs →
          αs ≤ 1 / p := fun ⟨z, hz, hrz⟩ =>
      ⟨profit_strictAntiOn xs' hc hp hK hKnn h0 hxsI hR hz hrz,
        fun αs hαs hmax => le_inv_of_isMaxOn xs' hc hp hK hKnn h0 hxsI hR hz hrz hαs hmax⟩
    have _h9' := profit_eq_zero (m := m) xs' fun α hα => by
      rw [heq α hα.2]
      exact (hxs α hα).isBR.1
    -- (a): `1/p` is a share bound, as `U_P` is nonincreasing on `[1/p, 1]` (not in the paper)
    exact isShareBound_of_antitoneOn (monotoneOn_reward_of_isBR fun α hα => (hxs α hα).isBR)
      (fun α hα => reward_nonneg_of_nonneg hm (hKnn _ (hxs α hα).isBR.1)) ⟨hp1.1, hplt⟩ hU
  · -- (10) "Finally, we show that the bound `1/p` on the share of an optimal contract is attained.
    -- For one element with `K = [0, 1]`, `m_e = 1` and `c(x) = x^p/p`" (which is homogeneous of
    -- degree `p`), "the agent maximizes `αx − x^p/p` over `[0, 1]`, so `x*(α) = α^{1/(p−1)}` for
    -- `α ∈ [0, 1]`."
    refine ⟨1, exCost p, fun _ => zero_le_one, ex_isHomogeneous hp,
      ⟨fun α _ => α ^ (1 / (p - 1)), fun α hα => ex_isPBR hp hα⟩, fun xs hxs => ?_⟩
    have hxs1 : ∀ α ∈ Icc (0 : ℝ) 1, IsBR (indepPoly (oneF 1)) 1 (exCost p) α (xs α) := by
      intro α hα
      rw [← Icc_eq_indepPoly_oneF]
      exact (hxs α hα).isBR
    -- "Then `U_P = h` on `[0, 1]`, which is maximal exactly at `α = 1/p`."
    refine ⟨(ex_isMaxOn_iff hp xs hxs1 hp1).2 rfl, fun ᾱ hᾱ => ?_⟩
    -- (b): "This bound is tight", as no smaller number is a share bound (not in the paper)
    exact ex_not_isShareBound hp xs hxs1 hᾱ

/-! ### Quadratic costs -/

/-- Quadratic costs `∑_e β_e/2 x_e²` with `β ≥ 0` are homogeneous of degree `2` (not in the paper:
the proof of `cor:fptasquad` applies `cor:fptashom` with `p = 2` to quadratic costs, "Taking `p = 2`
therefore gives the following runtime guarantees", 08-approximation.tex:40, and leaves implicit that
they are homogeneous of degree `2`). -/
lemma isHomogeneous_quadCost {β : E → ℝ} (hβ : ∀ e, 0 ≤ β e) :
    IsHomogeneous 2 (quadCost β) where
  nonneg x _ := Finset.sum_nonneg fun e _ => mul_nonneg (div_nonneg (hβ e) zero_le_two)
    (sq_nonneg _)
  zero := by simp [quadCost]
  convexOn := by
    refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [quadCost, smul_eq_mul, Pi.add_apply, Pi.smul_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have hb' : b = 1 - a := by linarith
    subst hb'
    have := hβ e
    nlinarith [mul_nonneg (mul_nonneg ha hb) (mul_nonneg this (sq_nonneg (x e - y e)))]
  continuousOn := by
    refine Continuous.continuousOn ?_
    unfold quadCost
    fun_prop
  hom := by
    intro x _ t _
    simp only [quadCost, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring

end Stoc.PRule
