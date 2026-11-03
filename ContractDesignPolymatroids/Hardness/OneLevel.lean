-- stamp r9 2026-11-03
import ContractDesignPolymatroids.Hardness.ClosedForms

/-!
# One level: `lem:fast`, `lem:onelevel` and `lem:leftwindows`

The STOC version's `lem:fast`, `lem:onelevel` and `lem:leftwindows` (Appendix C.6,
`sec:D-onelevel`, "One level", `stoc-sections/appD-hardness.tex:790-986`), for the step
`k → k + 1` of the levels of `def:tower` built by the parameter rule:

* `cfast`, `IsConfig`, `IsWeakConfigT`, `OneLevelHyp`, `ατ₂`: the rate `t_b/β⁻¹(E ∪ {b})` of
  (W6), the configuration and the weak configurations of level `k + 1` at a share (Appendix B.6,
  "Configurations" and `lem:windows`: `configU`, `configW`, `IsWeakConfig` of the step), the
  hypotheses (W1)–(W6) of `lem:onelevel`, and the zero `α_{τ_2}` of `u_2 − w`, the share at which
  `b` reaches the top of the band of `τ_2`;
* `isConfig_of_windows`, `IsConfig.θb_eq`: `lem:windows`(b) and (a) at the step;
* `fast`: `lem:fast`;
* `onelevel_step1`, `onelevel_step2`, `onelevel_step3`: the three parts of the proof of
  `lem:onelevel`(a), steps (1)–(3) in our numbering ("We first show that `b` is merged with `τ_1` on
  the first window", "Next we show that `b` is merged with `τ_2` on the second window", "To complete
  (a), we follow `b` to the right of the second window"); `onelevel_a`, `onelevel_b`,
  `onelevel_c`: `lem:onelevel`(a)–(c); `onelevel`: the statement of `lem:onelevel`, their
  conjunction;
* `leftwindows_a`, `leftwindows_b`, `leftwindows_c`: `lem:leftwindows`(a)–(c); `leftwindows`: the
  statement of `lem:leftwindows`, their conjunction.

The proof of `lem:onelevel`(b) puts the step in the setting of `lem:dmt` (`dmtSetting_stepD`) and
applies `lem:dmt`(c) (`gapT_config_τ₁`, `gapT_config_τ₂`), which `lem:twosides` and
`thm:transition` use as well ("as in the proof of `lem:onelevel`(b)").

The exact statements `fast`, `onelevel` and `leftwindows` and the parts `onelevel_a`, `onelevel_b`,
`onelevel_c`, `leftwindows_a`, `leftwindows_b` and `leftwindows_c` are for an input `μ^in ∈ 𝔉` of
length at least `k + 2` (`def:tower`), which `onelevel` and `leftwindows` take once for their three
parts. `fast` and the parts are derived from `fast_aux`, `onelevel_a_aux`, `onelevel_b_aux`,
`onelevel_c_aux`, `leftwindows_a_aux`, `leftwindows_b_aux` and `leftwindows_c_aux`, which carry the
paper's proofs without the hypothesis `μ^in ∈ 𝔉` (`μ = μ_{k+1} > 0` then follows from (W1),
`OneLevelHyp.μ_pos`) and which the proofs of `lem:twosides` and `thm:transition` use.

Taken over on 2026-10-20 from `Paper/Hardness/OneLevel.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

section Tower

variable (μin : ℕ → ℕ)

/-- `t_b/β⁻¹(E ∪ {b})`, the rate of (W6), with `t_b = m_b/β_b` (`b = none` in level `k + 1`). -/
def cfast (k : ℕ) : ℝ :=
  mT μin (k + 1) none / βT μin (k + 1) none / ∑ o, 1 / βT μin (k + 1) o

/-- The configuration of level `k + 1` at `α` is `(U, W)` (Appendix B.6, "Configurations",
`stoc-sections/appB-tools.tex:398`): `U = {e ∈ E : ρ^f_e(α) > θ_b(α)}` and
`W = {e ∈ E : ρ^h_e(α) ≥ θ_b(α)}`, the sets `configU` and `configW` of the step. -/
def IsConfig (k : ℕ) (α : ℝ) (U W : Finset (Option (Option (Gr k)))) : Prop :=
  configU ((stepD μin k).fStep (gT μin k)) ((stepD μin k).dStep (mT μin k) (βT μin k))
      (stepD μin k).K (mT μin (k + 1)) (βT μin (k + 1)) α = U ∧
    configW ((stepD μin k).fStep (gT μin k)) ((stepD μin k).dStep (mT μin k) (βT μin k))
      (stepD μin k).K (mT μin (k + 1)) (βT μin (k + 1)) α = W

/-- `(U, W)` is a weak configuration of level `k + 1` at `α` (`lem:windows`, the `IsWeakConfig` of
the step). -/
abbrev IsWeakConfigT (k : ℕ) (α : ℝ) (U W : Finset (Option (Option (Gr k)))) : Prop :=
  IsWeakConfig ((stepD μin k).fStep (gT μin k)) ((stepD μin k).dStep (mT μin k) (βT μin k))
    (stepD μin k).K (mT μin (k + 1)) (βT μin (k + 1)) α U W

/-- The hypotheses (W1)–(W6) of `lem:onelevel` at the step `k → k + 1`
(`stoc-sections/appD-hardness.tex:820-830`), with `𝓡 = [R_0, R_1]` and `𝓡 + μ`. In words (the
paragraph after `lem:onelevel`, lines 852-855): (W1) and (W2) keep `b` inside the band of `τ_1` on
the first window and inside the band of `τ_2` on the second; (W3) and (W4) keep the old elements
above `b` on the first window and below `b` on the second; (W5) puts the band of `τ_1` below that of
`τ_2`, and (W6) makes `b` faster than every other element. -/
structure OneLevelHyp (k : ℕ) : Prop where
  /-- (W1), left: `sι < u_1(R_0)` -/
  W1a : (lvl μin k).s * ι < u1 μin k R0
  /-- (W1), right: `u_1(R_1) < w` -/
  W1b : u1 μin k (R1T μin k) < (lvl μin k).w (μT μin (k + 1))
  /-- (W2), left: `0 < u_2(R_0 + μ)` -/
  W2a : 0 < u2 μin k (R0 + μT μin (k + 1))
  /-- (W2), right: `u_2(R_1 + μ) < w` -/
  W2b : u2 μin k (R1T μin k + μT μin (k + 1)) < (lvl μin k).w (μT μin (k + 1))
  /-- (W3): `ρ^{(k)}_e(α) > ρ^h_{τ_1}(α)` for `e ∈ E_k` and `α ∈ 𝓡` -/
  W3 : ∀ c, ∀ α ∈ Set.Icc R0 (R1T μin k), ρh μin k α (some none) < ρT μin k α c
  /-- (W4): `ρ^h_e(α) < θ_2(α)` for `e ∈ E_k` and `α ∈ 𝓡 + μ` -/
  W4 : ∀ c, ∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (R1T μin k + μT μin (k + 1)),
    ρh μin k α (some (some c)) < θ2 μin k α
  /-- (W5): `φ > 1` -/
  W5 : 1 < φ μin k
  /-- (W6): `t_b/β⁻¹(E ∪ {b}) > M` -/
  W6 : (lvl μin k).M < cfast μin k

/-- `α_{τ_2}`, the zero of `u_2 − w`, the share at which `b` reaches the top of the band of `τ_2`
(`lem:onelevel`); `u_2` has slope `s > 0` (`u2_slope`), so the zero exists and is unique
(`ατ₂_spec`, `u2_sub_w`). -/
def ατ₂ (k : ℕ) : ℝ := Classical.epsilon fun α => u2 μin k α = (lvl μin k).w (μT μin (k + 1))

variable {μin}

/-! ### The setting of the step -/

/-- The rewards of level `k` are positive (`lem:weights`(b)). -/
lemma mT_pos (k : ℕ) (e : Gr k) : 0 < mT μin k e := by
  obtain ⟨n, hn, hv, -⟩ := (weights_b (μin := μin)).1 k e
  rw [hv]
  exact_mod_cast hn

/-- `M_k` is the largest reward of `E_k` (`lem:weights`(b)). -/
lemma mT_le_M (k : ℕ) (e : Gr k) : mT μin k e ≤ (lvl μin k).M := by
  obtain ⟨n, -, hv, hle⟩ := (weights_b (μin := μin)).1 k e
  rw [hv]
  exact hle

/-- (P4): `m_b > m_δ`, as `Δ_b = (415/2)M > 0`. -/
lemma mδ_lt_mb (k : ℕ) : (stepD μin k).mδ < (stepD μin k).mb := by
  have := M_pos (μin := μin) k
  show (lvl μin k).mδ < (lvl μin k).mδ + (lvl μin k).Δb
  unfold Level.Δb
  linarith

/-- `m_δ = M/2 < M`. -/
lemma mδ_lt_M (k : ℕ) : (lvl μin k).mδ < (lvl μin k).M := by
  have := M_pos (μin := μin) k
  unfold Level.mδ
  linarith

lemma mδ_pos (k : ℕ) : 0 < (lvl μin k).mδ := by
  have := M_pos (μin := μin) k
  unfold Level.mδ
  linarith

/-- `R_0 < R_1^{(k)}`, as `R_1^{(k)} − R_0 = ∑_{i ≤ k} μ_i + 2ε_0`. -/
lemma R0_lt_R1T (k : ℕ) : R0 < R1T μin k := by
  have := sum_nonneg fun i (_ : i ∈ range (k + 1)) => μT_nonneg (μin := μin) i
  have := ε₀_pos
  unfold R1T R0
  linarith

/-- The proof of `lem:onelevel`(b), its first sentence
(`stoc-sections/appD-hardness.tex:904-908`): the setting of `lem:dmt` holds at the step with
`f_C := g_k` and `C := E_k`, as `g_k` is submodular with `g_k(∅) = 0` and positive curvatures
(`fpHyp_gT`), the rewards of `E_k` are positive (`lem:weights`(b), `mT_pos`),
`m_* ≥ max_{e ∈ E} m_e` (the paragraph after `def:ruleP`, `stepD_hyp`), `β_b = β_δ/12` by (P2) (the
curvature of `b` in `StepData.βNew`, `βT_succ_none`) and `m_b > m_δ` by (P4); `μ > 0` is the
hypothesis `hμ`. -/
lemma dmtSetting_stepD (k : ℕ) (hμ : 0 < μT μin (k + 1)) :
    (stepD μin k).DmtSetting (gT μin k) (mT μin k) (βT μin k) where
  submod := (fpHyp_gT k).submod
  empty := (fpHyp_gT k).empty
  mC_pos := mT_pos k
  βC_pos := (fpHyp_gT k).pos
  mδ_pos := mδ_pos k
  βδ_pos := (lvl μin k).βδ_pos
  μ_pos := hμ
  mstar_ge := fun e => by
    rcases e with _ | _ | c
    · exact (stepD_hyp k).mδ_le
    · exact (stepD_hyp k).mδ_le
    · exact (stepD_hyp k).mstar_ge c
  mb_gt := mδ_lt_mb k

/-- (P5) is the hypothesis of `lem:dmt`(c) on `ΔF` at the step (with `q_C = q_k`). -/
lemma P5_stepD (k : ℕ) : (stepD μin k).Fτ₁ - (stepD μin k).Fτ₂ =
    (stepD μin k).w / (stepD μin k).βδ + (stepD μin k).dC (mT μin k) (βT μin k) -
      ((lvl μin k).q * (stepD μin k).μ - ∑ c, ((stepD μin k).mδ - mT μin k c) *
        (stepD μin k).dStep (mT μin k) (βT μin k) (some (some c))) / (stepD μin k).s := by
  rw [stepD_w, stepD_s]
  show ((lvl μin k).Fτ₂ _ _ + (lvl μin k).ΔF (μT μin (k + 1))) - (lvl μin k).Fτ₂ _ _ =
    (lvl μin k).w (μT μin (k + 1)) / (lvl μin k).βδ + (lvl μin k).dEk (μT μin (k + 1)) -
      ((lvl μin k).q * μT μin (k + 1) - (lvl μin k).Pcal (μT μin (k + 1))) / (lvl μin k).s
  unfold Level.ΔF
  ring

/-- (P8): the gap of level `k + 1` is `L(α) − r(ξ^{(k+1)}(α))` for the line
`L(α) = L_k(α) + ψ_{k+1}α + Δ_p` of `lem:dmt`(c) with `L_C = L_k`. -/
lemma gapT_succ_eq (k : ℕ) (α : ℝ) :
    gapT μin (k + 1) α = ((lvl μin k).p + (lvl μin k).q * α + (stepD μin k).ψ * α +
        (stepD μin k).Δp (mT μin k) (βT μin k)) -
      reward ((stepD μin k).mNew (mT μin k))
        (xi ((stepD μin k).gNew (gT μin k) (mT μin k) (βT μin k)) ((stepD μin k).mNew (mT μin k))
          ((stepD μin k).βNew (βT μin k)) α) := by
  rw [stepD_Δp, stepD_ψ]
  show (lvl μin k).p + (lvl μin k).Δp _ _ + ((lvl μin k).q + (lvl μin k).ψ) * α -
      reward ((stepD μin k).mNew (mT μin k))
        (xi ((stepD μin k).gNew (gT μin k) (mT μin k) (βT μin k)) ((stepD μin k).mNew (mT μin k))
          ((stepD μin k).βNew (βT μin k)) α) = _
  ring

/-- `thm:splice`(a) at the step: `ρ^f ≤ ρ^h`. -/
lemma ρf_le_ρh (k : ℕ) (α : ℝ) (e : Option (Option (Gr k))) : ρf μin k α e ≤ ρh μin k α e :=
  rho_le_rho_subMod (stepD_hyp k).fHyp (stepD_hyp k).d_nonneg α e

/-- `thm:splice`(b) at the step: `ρ^{(k+1)}_e = med(ρ^f_e, θ_b, ρ^h_e)` for `e ∈ E`. -/
lemma ρT_succ_med (k : ℕ) (α : ℝ) (e : Option (Option (Gr k))) :
    ρT μin (k + 1) α (some e) = med (ρf μin k α e) (θb μin k α) (ρh μin k α e) :=
  (splice_aux (f := (stepD μin k).fStep (gT μin k)) (d := (stepD μin k).dStep (mT μin k) (βT μin k))
    (K := (stepD μin k).K) (m' := mT μin (k + 1)) (β' := βT μin (k + 1)) (stepD_hyp k).fHyp
    (stepD_hyp k).d_nonneg (StepData.βb_pos (stepD_hyp k)) α).2.1 e

/-! ### Configurations of the step -/

/-- The configuration of level `k + 1` at `α` is `(U, W)` exactly if `U = {e : ρ^f_e > θ_b}` and
`W = {e : ρ^h_e ≥ θ_b}` at `α` (the definition, `configU`, `configW`). -/
lemma isConfig_iff {k : ℕ} {α : ℝ} {U W : Finset (Option (Option (Gr k)))} :
    IsConfig μin k α U W ↔
      ∀ e, (e ∈ U ↔ θb μin k α < ρf μin k α e) ∧ (e ∈ W ↔ θb μin k α ≤ ρh μin k α e) := by
  unfold IsConfig
  constructor
  · rintro ⟨rfl, rfl⟩ e
    simp only [configU, configW, mem_filter, mem_univ, true_and]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · intro h
    constructor <;> ext e <;> simp only [configU, configW, mem_filter, mem_univ, true_and]
    · exact (h e).1.symm
    · exact (h e).2.symm

/-- The paragraph "Configurations" (`stoc-sections/appB-tools.tex:397-400`, `config_spec`) at the
step: if the configuration of level `k + 1` at `α` is `(U, W)`, then `U ⊆ W`,
`ρ' = ρ^f > θ_b` on `U`, `ρ' = θ_b` on `W ∖ U`, `ρ' = ρ^h < θ_b` on `E ∖ W`, and the block of `b`,
the set of elements of `E ∪ {b}` with the marginal `θ_b`, is `D = (W ∖ U) ∪ {b}`. -/
lemma IsConfig.spec {k : ℕ} {α : ℝ} {U W : Finset (Option (Option (Gr k)))}
    (h : IsConfig μin k α U W) :
    U ⊆ W ∧ (∀ e ∈ U, ρT μin (k + 1) α (some e) = ρf μin k α e ∧ θb μin k α < ρf μin k α e) ∧
      (∀ e ∈ W \ U, ρT μin (k + 1) α (some e) = θb μin k α) ∧
      (∀ e ∉ W, ρT μin (k + 1) α (some e) = ρh μin k α e ∧ ρh μin k α e < θb μin k α) ∧
      univ.filter (fun o => ρT μin (k + 1) α o = θb μin k α) = insertNone (W \ U) := by
  obtain ⟨rfl, rfl⟩ := h
  exact config_spec (stepD_hyp k).fHyp.submod (stepD_hyp k).fHyp.empty (mT_pos (k + 1))
    (fpHyp_gT (k + 1)).pos (stepD_hyp k).d_nonneg α

/-- `lem:windows`, before (a) (`stoc-sections/appB-tools.tex:410`, `isWeakConfig_config`): the
configuration at `α` is a weak configuration. -/
lemma IsConfig.weak {k : ℕ} {α : ℝ} {U W : Finset (Option (Option (Gr k)))}
    (h : IsConfig μin k α U W) : IsWeakConfigT μin k α U W := by
  obtain ⟨rfl, rfl⟩ := h
  exact isWeakConfig_config (stepD_hyp k).fHyp.submod (stepD_hyp k).fHyp.empty (mT_pos (k + 1))
    (fpHyp_gT (k + 1)).pos (stepD_hyp k).d_nonneg α

/-- `lem:windows`(b) at the step (`windows_b`, `stoc-sections/appB-tools.tex:417`): for
`U ⊆ W ⊆ E`, if `ρ^f_e > θ_{U,W}` for `e ∈ U`, `ρ^f_e ≤ θ_{U,W}` for `e ∈ E ∖ U`,
`ρ^h_e ≥ θ_{U,W}` for `e ∈ W`, and `ρ^h_e < θ_{U,W}` for `e ∈ E ∖ W` at `α`, then `(U, W)` is the
configuration of level `k + 1` at `α`. -/
lemma isConfig_of_windows {k : ℕ} {α : ℝ} {U W : Finset (Option (Option (Gr k)))} (hUW : U ⊆ W)
    (hU : ∀ e ∈ U, θUW μin k α U W < ρf μin k α e)
    (hUc : ∀ e ∉ U, ρf μin k α e ≤ θUW μin k α U W)
    (hW : ∀ e ∈ W, θUW μin k α U W ≤ ρh μin k α e)
    (hWc : ∀ e ∉ W, ρh μin k α e < θUW μin k α U W) : IsConfig μin k α U W := by
  obtain ⟨h1, h2⟩ := windows_b (stepD_hyp k).fHyp.submod (stepD_hyp k).fHyp.empty
    (mT_pos (k + 1)) (fpHyp_gT (k + 1)).pos (stepD_hyp k).d_nonneg hUW hU hUc hW hWc
  exact ⟨h1.symm, h2.symm⟩

/-- `lem:windows`(a) at the step (`windows_a`, `stoc-sections/appB-tools.tex:413`), for the
configuration, which is a weak configuration (`IsConfig.weak`): if the configuration of level
`k + 1` at `α` is `(U, W)`, then `θ_b(α) = θ_{U,W}`. -/
lemma IsConfig.θb_eq {k : ℕ} {α : ℝ} {U W : Finset (Option (Option (Gr k)))}
    (h : IsConfig μin k α U W) : θb μin k α = θUW μin k α U W :=
  (windows_a (stepD_hyp k).fHyp.submod (stepD_hyp k).fHyp.empty (mT_pos (k + 1))
    (fpHyp_gT (k + 1)).pos (stepD_hyp k).d_nonneg h.spec.1 h.weak).1

/-! ### Rates -/

/-- `lem:fullplane`(c) for level `k`: its marginals are continuous and grow at most at the rate
`max_{e ∈ E_k} m_e = M_k` (`lem:weights`(b)). -/
lemma ρT_rate (k : ℕ) (c : Gr k) :
    Continuous (fun α => ρT μin k α c) ∧ GrowsAtMost (fun α => ρT μin k α c) (lvl μin k).M := by
  have H := fpHyp_gT (μin := μin) k
  -- (the first claim of `lem:fullplane`(c), for `c = 0`, is not used)
  obtain ⟨-, hup, -, hcont, -, -, -⟩ := fullplane_c H.submod H.empty (mT_pos (μin := μin) k)
    H.pos c 0 fun S _ => by
      rw [zero_mul]
      exact sum_nonneg fun o _ => div_nonneg (mT_pos (μin := μin) k o).le (H.pos o).le
  have hsup : univ.sup' ⟨c, mem_univ c⟩ (mT μin k) ≤ (lvl μin k).M :=
    sup'_le _ _ fun e _ => mT_le_M k e
  refine ⟨(continuous_apply c).comp hcont, fun α Δ hΔ => ?_⟩
  have h1 := hup c α Δ hΔ
  have h2 := mul_le_mul_of_nonneg_right hsup hΔ
  simp only at h1 ⊢
  unfold ρT
  linarith

/-- The step (3) of the proof of `lem:fast` for `f`: the marginals `ρ^f_e`, `e ∈ E_k`, are those
of level `k` (`eq:D-bands`), continuous and growing at most at the rate `M` (`ρT_rate`), and the
marginals of `τ_1` and `τ_2` are affine with slope `m_δ < M`. -/
lemma ρf_rate (k : ℕ) (e : Option (Option (Gr k))) :
    Continuous (fun α => ρf μin k α e) ∧ GrowsAtMost (fun α => ρf μin k α e) (lvl μin k).M := by
  have hm := mδ_lt_M (μin := μin) k
  rcases e with _ | _ | c
  · have hf : (fun α => ρf μin k α none) = fun α => α * (lvl μin k).mδ -
        (lvl μin k).βδ * (lvl μin k).Fτ₂ (μT μin (k + 1)) (R1T μin k) :=
      funext fun α => (D_bands k α).2.2.2.1
    rw [hf]
    refine ⟨by fun_prop, fun α Δ hΔ => ?_⟩
    nlinarith
  · have hf : (fun α => ρf μin k α (some none)) = fun α => α * (lvl μin k).mδ -
        (lvl μin k).βδ * (lvl μin k).Fτ₁ (μT μin (k + 1)) (R1T μin k) :=
      funext fun α => (D_bands k α).2.2.1
    rw [hf]
    refine ⟨by fun_prop, fun α Δ hΔ => ?_⟩
    nlinarith
  · have hf : (fun α => ρf μin k α (some (some c))) = fun α => ρT μin k α c :=
      funext fun α => (D_bands k α).1 c
    rw [hf]
    exact ρT_rate k c

/-- The step (3) of the proof of `lem:fast` for `h`: `ρ^h_e(α) = ρ^{(k)}_e(α − μ) + m_*μ` for
`e ∈ E_k` (`eq:D-bands`), so it is continuous and grows at most at the rate `M` (`ρT_rate`), and
`ρ^h_{τ_1} = ρ^f_{τ_1} + w`, `ρ^h_{τ_2} = ρ^f_{τ_2} + w` are affine with slope `m_δ < M`
(`ρf_rate`). -/
lemma ρh_rate (k : ℕ) (e : Option (Option (Gr k))) :
    Continuous (fun α => ρh μin k α e) ∧ GrowsAtMost (fun α => ρh μin k α e) (lvl μin k).M := by
  rcases e with _ | _ | c
  · have hf : (fun α => ρh μin k α none) = fun α => ρf μin k α none +
        (lvl μin k).w (μT μin (k + 1)) := funext fun α => (D_bands k α).2.2.2.2.2
    obtain ⟨h1, h2⟩ := ρf_rate (μin := μin) k none
    rw [hf]
    refine ⟨h1.add continuous_const, fun α Δ hΔ => ?_⟩
    have := h2 α Δ hΔ
    simp only at this ⊢
    linarith
  · have hf : (fun α => ρh μin k α (some none)) = fun α => ρf μin k α (some none) +
        (lvl μin k).w (μT μin (k + 1)) := funext fun α => (D_bands k α).2.2.2.2.1
    obtain ⟨h1, h2⟩ := ρf_rate (μin := μin) k (some none)
    rw [hf]
    refine ⟨h1.add continuous_const, fun α Δ hΔ => ?_⟩
    have := h2 α Δ hΔ
    simp only at this ⊢
    linarith
  · have hf : (fun α => ρh μin k α (some (some c))) = fun α => ρT μin k (α - μT μin (k + 1)) c +
        (lvl μin k).mstar * μT μin (k + 1) := funext fun α => (D_bands k α).2.1 c
    obtain ⟨h1, h2⟩ := ρT_rate (μin := μin) k c
    rw [hf]
    refine ⟨(h1.comp (continuous_id.sub continuous_const)).add continuous_const,
      fun α Δ hΔ => ?_⟩
    have := h2 (α - μT μin (k + 1)) Δ hΔ
    simp only at this ⊢
    rw [show α + Δ - μT μin (k + 1) = α - μT μin (k + 1) + Δ by ring]
    linarith

/-! ### `lem:fast` -/

/-- `lem:fast` without the hypothesis `μ^in ∈ 𝔉` (which its proof does not use), the form the
proofs below use (`stoc-sections/appD-hardness.tex:796-800`, proof lines 802-814): at the step
`k → k + 1`, if `t_b/β⁻¹(E ∪ {b}) > M`, then `m̄ > M`, and `θ_b − ρ^f_e` and `θ_b − ρ^h_e` are
continuous and strictly increasing for every `e ∈ E`.

The proof's steps: (1) as `β⁻¹(E ∪ {b}) ≥ β⁻¹({b, τ_1}) = 13/β_δ` and `t_b = 12m_b/β_δ`,
`M < t_b/β⁻¹(E ∪ {b}) ≤ (12/13)m_b ≤ (12/13)m_b + (1/13)m_δ = m̄`, the last step by (P4);
(2) by `lem:fullplane`(c), applied to `g_{k+1}` on
`E ∪ {b}`, `θ_b` is continuous and grows at least at the rate `c := t_b/β⁻¹(E ∪ {b})`; (3) for
`e ∈ E_k`, `ρ^f_e` and `ρ^h_e` grow at most at the rate `max_{e'∈E_k} m_{e'} = M`, by
(`eq:D-bands`) and `lem:fullplane`(c), and the marginals of `τ_1` and `τ_2` are affine with slope
`m_δ < M` (`ρf_rate`, `ρh_rate`, with `max_{e'∈E_k} m_{e'} ≤ M`, `mT_le_M`); (4) as `c > M`,
every difference is continuous and grows at least at the rate `c − M > 0`. -/
theorem fast_aux (k : ℕ) (h6 : (lvl μin k).M < cfast μin k) :
    (lvl μin k).M < (lvl μin k).mbar ∧
    ∀ e, (Continuous fun α => θb μin k α - ρf μin k α e) ∧
      StrictMono (fun α => θb μin k α - ρf μin k α e) ∧
      (Continuous fun α => θb μin k α - ρh μin k α e) ∧
      StrictMono (fun α => θb μin k α - ρh μin k α e) := by
  have H := stepD_hyp (μin := μin) k
  have H1 := fpHyp_gT (μin := μin) (k + 1)
  have hM := M_pos (μin := μin) k
  have hβ := (lvl μin k).βδ_pos
  -- (1) "As `β⁻¹(E ∪ {b}) ≥ β⁻¹({b, τ_1}) = 13/β_δ` and `t_b = 12m_b/β_δ`, we have
  -- `M < t_b/β⁻¹(E ∪ {b}) ≤ (12/13)m_b ≤ (12/13)m_b + (1/13)m_δ = m̄`, the last step by (P4)."
  have hB : 13 / (lvl μin k).βδ ≤ ∑ o, 1 / βT μin (k + 1) o := by
    have h1 : ∑ o ∈ ({none, some (some none)} : Finset (Gr (k + 1))), 1 / βT μin (k + 1) o =
        13 / (lvl μin k).βδ := (StepData.block_τ₁_sums H).1
    rw [← h1]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun o _ _ => (one_div_pos.2 (H1.pos o)).le
  have htb : (lvl μin k).mb / (lvl μin k).βb = 12 * (lvl μin k).mb / (lvl μin k).βδ := by
    unfold Level.βb
    field_simp
  have hmb : 0 < (lvl μin k).mb := by
    have := mδ_lt_mb (μin := μin) k
    have := mδ_pos (μin := μin) k
    simp only [stepD_mb, stepD_mδ] at *
    linarith
  have hcle : cfast μin k ≤ 12 / 13 * (lvl μin k).mb := by
    show (lvl μin k).mb / (lvl μin k).βb / ∑ o, 1 / βT μin (k + 1) o ≤ _
    rw [htb]
    calc 12 * (lvl μin k).mb / (lvl μin k).βδ / ∑ o, 1 / βT μin (k + 1) o
        ≤ 12 * (lvl μin k).mb / (lvl μin k).βδ / (13 / (lvl μin k).βδ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hB
      _ = 12 / 13 * (lvl μin k).mb := by field_simp
  have hm : (lvl μin k).M < (lvl μin k).mbar := by
    have := mδ_pos (μin := μin) k
    -- "the last step by (P4)": `m̄ = m_δ + s` with `s = (12/13)Δ_b` and `m_b = m_δ + Δ_b`
    have hP4 : 12 / 13 * (lvl μin k).mb + 1 / 13 * (lvl μin k).mδ = (lvl μin k).mbar := by
      simp only [Level.mbar, Level.s, Level.mb]
      ring
    calc (lvl μin k).M < cfast μin k := h6
      _ ≤ 12 / 13 * (lvl μin k).mb := hcle
      _ ≤ 12 / 13 * (lvl μin k).mb + 1 / 13 * (lvl μin k).mδ := by linarith
      _ = (lvl μin k).mbar := hP4
  refine ⟨hm, fun e => ?_⟩
  -- (2) "By `lem:fullplane`(c), applied to `g_{k+1}` on `E ∪ {b}`, `θ_b` is continuous and grows
  -- at least at the rate `c := t_b/β⁻¹(E ∪ {b})`." (its first claim, for `c = 0`, is not used)
  obtain ⟨-, -, -, hcont, -, -, hθrate⟩ := fullplane_c H1.submod H1.empty
    (mT_pos (μin := μin) (k + 1)) H1.pos none 0 fun S _ => by
      rw [zero_mul]
      exact sum_nonneg fun o _ => div_nonneg (mT_pos (μin := μin) (k + 1) o).le (H1.pos o).le
  have hθc : Continuous fun α => θb μin k α := (continuous_apply none).comp hcont
  -- (3) "For `e ∈ E_k`, `ρ^f_e` and `ρ^h_e` grow at most at the rate `max_{e'∈E_k} m_{e'} = M`,
  -- by (`eq:D-bands`) and `lem:fullplane`(c), and the marginals of `τ_1` and `τ_2` are affine
  -- with slope `m_δ < M`."
  -- The Lean uses `max_{e'∈E_k} m_{e'} ≤ M` (`mT_le_M`), which suffices.
  obtain ⟨hfc, hfr⟩ := ρf_rate (μin := μin) k e
  obtain ⟨hhc, hhr⟩ := ρh_rate (μin := μin) k e
  -- (4) "As `c > M`, every difference `θ_b − ρ^f_e` and `θ_b − ρ^h_e` is continuous and grows at
  -- least at the rate `c − M > 0`."
  refine ⟨hθc.sub hfc, fun α α' hαα => ?_, hθc.sub hhc, fun α α' hαα => ?_⟩
  · have hδ : 0 < α' - α := sub_pos.2 hαα
    have h1 := hθrate α (α' - α) hδ.le
    have h2 := hfr α (α' - α) hδ.le
    simp only [add_sub_cancel] at h1 h2
    have := mul_lt_mul_of_pos_right h6 hδ
    show θb μin k α - ρf μin k α e < θb μin k α' - ρf μin k α' e
    have h1' : θb μin k α + cfast μin k * (α' - α) ≤ θb μin k α' := h1
    linarith
  · have hδ : 0 < α' - α := sub_pos.2 hαα
    have h1 := hθrate α (α' - α) hδ.le
    have h2 := hhr α (α' - α) hδ.le
    simp only [add_sub_cancel] at h1 h2
    have := mul_lt_mul_of_pos_right h6 hδ
    show θb μin k α - ρh μin k α e < θb μin k α' - ρh μin k α' e
    have h1' : θb μin k α + cfast μin k * (α' - α) ≤ θb μin k α' := h1
    linarith

/-- **`lem:fast`** (Lemma C.14, `stoc-sections/appD-hardness.tex:796-800`, proof lines 802-814): let
`μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). Consider the step `k → k + 1`, and suppose
that `t_b/β⁻¹(E ∪ {b}) > M`. Then `m̄ > M`, and `θ_b − ρ^f_e` and `θ_b − ρ^h_e` are continuous and
strictly increasing for every `e ∈ E`. The proof (steps (1)–(4)) is that of `fast_aux`, which does
not use the hypothesis on the input. -/
theorem fast {K : ℕ} (k : ℕ) (_hF : InF μin K) (_hK : k + 2 ≤ K)
    (h6 : (lvl μin k).M < cfast μin k) :
    (lvl μin k).M < (lvl μin k).mbar ∧
    ∀ e, (Continuous fun α => θb μin k α - ρf μin k α e) ∧
      StrictMono (fun α => θb μin k α - ρf μin k α e) ∧
      (Continuous fun α => θb μin k α - ρh μin k α e) ∧
      StrictMono (fun α => θb μin k α - ρh μin k α e) :=
  fast_aux k h6

/-! ### `α_{τ_2}` -/

/-- (W1) gives `w > u_1(R_1) > u_1(R_0) > sι > 0`, so `μ > 0` (not in the paper: there the input
`μ^in ∈ 𝔉` gives `μ = μ_{k+1} > 0`; the auxiliary forms below, which do not assume `μ^in ∈ 𝔉`,
take `μ > 0` from (W1)). -/
lemma OneLevelHyp.μ_pos {k : ℕ} (h : OneLevelHyp μin k) : 0 < μT μin (k + 1) := by
  have h1 := u1_slope (μin := μin) k R0 (R1T μin k)
  have h2 := mul_pos (s_pos (μin := μin) k) (sub_pos.2 (R0_lt_R1T (μin := μin) k))
  have h3 := mul_pos (s_pos (μin := μin) k) (show (0 : ℝ) < ι by unfold ι; norm_num)
  have hw : 0 < (lvl μin k).w (μT μin (k + 1)) := by linarith [h.W1a, h.W1b]
  have hM := M_pos (μin := μin) k
  unfold Level.w at hw
  by_contra hcon
  have : 64 * (lvl μin k).M * μT μin (k + 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hcon)
  linarith

/-- `u_2(α_{τ_2}) = w`: the zero exists, as `u_2` is affine with slope `s > 0` (`u2_slope`) (not in
the paper: `lem:onelevel` presupposes it in "Let `α_{τ_2}` be the zero of `u_2 − w`"). -/
lemma ατ₂_spec (k : ℕ) : u2 μin k (ατ₂ μin k) = (lvl μin k).w (μT μin (k + 1)) := by
  have hs := (s_pos (μin := μin) k).ne'
  refine Classical.epsilon_spec (p := fun α => u2 μin k α = (lvl μin k).w (μT μin (k + 1)))
    ⟨0 + ((lvl μin k).w (μT μin (k + 1)) - u2 μin k 0) / (lvl μin k).s, ?_⟩
  have := u2_slope (μin := μin) k 0 (0 + ((lvl μin k).w (μT μin (k + 1)) - u2 μin k 0) /
    (lvl μin k).s)
  rw [add_sub_cancel_left, mul_div_cancel₀ _ hs] at this
  show u2 μin k _ = _
  linarith

/-- `u_2 − w` is affine with slope `s` and vanishes at `α_{τ_2}`. -/
lemma u2_sub_w (k : ℕ) (α : ℝ) :
    u2 μin k α - (lvl μin k).w (μT μin (k + 1)) = (lvl μin k).s * (α - ατ₂ μin k) := by
  have := u2_slope (μin := μin) k (ατ₂ μin k) α
  rw [ατ₂_spec] at this
  linarith

/-! ### The proof of `lem:onelevel`(b): `lem:dmt`(c) at the step -/

/-- The proof of `lem:onelevel`(b) (`stoc-sections/appD-hardness.tex:908-911`), case (a):
`lem:dmt`(c), applied with `L_C := L_k` (its hypothesis on `ΔF` is (P5), `P5_stepD`, and its line
`L` is `L_{k+1}` by (P8), `gapT_succ_eq`): if `(E ∖ {τ_1}, E)` is a weak configuration of level
`k + 1` at `α`, the gap of level `k + 1` at `α` is the gap of level `k` at `α`. -/
theorem gapT_config_τ₁ (k : ℕ) (hμ : 0 < μT μin (k + 1)) {α : ℝ}
    (hconf : IsWeakConfigT μin k α (univ.erase (some none)) univ) :
    gapT μin (k + 1) α = gapT μin k α := by
  rw [gapT_succ_eq]
  exact (StepData.dmt_c (dmtSetting_stepD k hμ) (lvl μin k).p (lvl μin k).q (P5_stepD k) α).1
    hconf

/-- The proof of `lem:onelevel`(b), case (b) of `lem:dmt`(c): if `(∅, {τ_2})` is a weak
configuration of level `k + 1` at `α`, the gap of level `k + 1` at `α` is the gap of level `k` at
`α − μ` (`lem:dmt`(c) with `L_C := L_k`, as in `gapT_config_τ₁`). -/
theorem gapT_config_τ₂ (k : ℕ) (hμ : 0 < μT μin (k + 1)) {α : ℝ}
    (hconf : IsWeakConfigT μin k α ∅ {none}) :
    gapT μin (k + 1) α = gapT μin k (α - μT μin (k + 1)) := by
  rw [gapT_succ_eq]
  exact (StepData.dmt_c (dmtSetting_stepD k hμ) (lvl μin k).p (lvl μin k).q (P5_stepD k) α).2
    hconf

/-- The proof of `lem:onelevel`(b) on `[α_{τ_2}, ∞)` (`stoc-sections/appD-hardness.tex:911-922`):
if `(∅, ∅)` is a weak configuration at `α` and at `α'`, that is, `ρ^h_e ≤ θ_b` for every `e ∈ E`
(the tightness of `∅` is trivial), then
(`eq:windows`), with `lem:fullplane`(f) and `lem:translation`(c) (`config_empty` of
`ContractDesignPolymatroids/Hardness/Step.lean`), gives
`r(ξ^{(k+1)}(α)) = r(ξ^{(k)}(α − μ)) + m_δ(F_{τ_1} + F_{τ_2}) − ∑_{e∈E} m_ed_e + Km_b` at both;
hence the difference of the gap of level `k + 1` at `α` and that of level `k` at `α − μ` changes by
`(q_{k+1} − q_k)(α' − α) = ψ_{k+1}(α' − α)`, that is, it is affine with slope `ψ_{k+1}`. -/
theorem gapT_config_empty (k : ℕ) {α α' : ℝ}
    (hlow : ∀ e, ρh μin k α e ≤ θb μin k α) (hlow' : ∀ e, ρh μin k α' e ≤ θb μin k α') :
    (gapT μin (k + 1) α' - gapT μin k (α' - μT μin (k + 1))) -
        (gapT μin (k + 1) α - gapT μin k (α - μT μin (k + 1))) =
      (lvl μin k).ψ * (α' - α) := by
  have H := stepD_hyp (μin := μin) k
  have e1 := (StepData.config_empty H hlow).2
  have e2 := (StepData.config_empty H hlow').2
  simp only [gapT, gap]
  rw [q_succ]
  have hc1 : curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) α =
      curve ((stepD μin k).gNew (gT μin k) (mT μin k) (βT μin k)) ((stepD μin k).mNew (mT μin k))
        ((stepD μin k).βNew (βT μin k)) α := rfl
  have hc2 : curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) α' =
      curve ((stepD μin k).gNew (gT μin k) (mT μin k) (βT μin k)) ((stepD μin k).mNew (mT μin k))
        ((stepD μin k).βNew (βT μin k)) α' := rfl
  rw [hc1, hc2, e1, e2, stepD_μ]
  ring

/-! ### `lem:onelevel` -/

/-- **Step (1) of the proof of `lem:onelevel`** (our numbering;
`stoc-sections/appD-hardness.tex:861-870`), "We first show that `b` is merged with `τ_1` on the
first window `𝓡`": on `𝓡`, the configuration of level `k + 1` is `(E ∖ {τ_1}, E)` and `θ_b = θ_1`.

The step's sentences: (1) as `u_1` is affine and `sι > 0`, (W1) gives `0 < u_1(α) < w`, that is,
`ρ^f_{τ_1} < θ_1 < ρ^h_{τ_1}` at `α`; (2) we apply `lem:windows`(b) with `U = E ∖ {τ_1}` and
`W = E`, where `D = {b, τ_1}`, `X_{U,W} = K − d(E) + F_{τ_1}`, and `θ_{U,W} = θ_1` (`θ1_θUW`), and
its conditions hold, for `τ_1` by (1); (3) for `e ∈ E_k`, (W3) and `thm:splice`(a) give
`ρ^h_e ≥ ρ^f_e = ρ^{(k)}_e > ρ^h_{τ_1} > θ_1`; (4) for `τ_2`, (W5) gives
`ρ^h_{τ_2} ≥ ρ^f_{τ_2} = ρ^f_{τ_1} + φw > ρ^h_{τ_1} > θ_1`; (5) so the configuration is
`(E ∖ {τ_1}, E)` (`lem:windows`(b), `isConfig_of_windows`), and `θ_b = θ_1` (`θ_b = θ_{U,W}` for the
configuration by `lem:windows`(a), `IsConfig.θb_eq`, as in the paragraph before
`lem:closedforms`). -/
theorem onelevel_step1 {k : ℕ} (h : OneLevelHyp μin k) {α : ℝ}
    (hα : α ∈ Set.Icc R0 (R1T μin k)) :
    IsConfig μin k α (univ.erase (some none)) univ ∧ θb μin k α = θ1 μin k α := by
  have hμ := h.μ_pos
  have hs := s_pos (μin := μin) k
  obtain ⟨hof, -, -, -, hhτ₁, -⟩ := D_bands (μin := μin) k α
  -- (1) "As `u_1` is affine and `sι > 0`, (W1) gives `0 < u_1(α) < w`, that is,
  -- `ρ^f_{τ_1} < θ_1 < ρ^h_{τ_1}` at `α`."
  have hu0 : 0 < u1 μin k α := by
    have h1 := u1_slope (μin := μin) k R0 α
    have h2 := mul_nonneg hs.le (sub_nonneg.2 hα.1)
    have h3 := mul_pos hs (show (0 : ℝ) < ι by unfold ι; norm_num)
    linarith [h.W1a]
  have hu1 : u1 μin k α < (lvl μin k).w (μT μin (k + 1)) := by
    have h1 := u1_slope (μin := μin) k α (R1T μin k)
    have h2 := mul_nonneg hs.le (sub_nonneg.2 hα.2)
    linarith [h.W1b]
  have hτ₁_1 : ρf μin k α (some none) < θ1 μin k α := by unfold u1 at hu0; linarith
  have hτ₁_2 : θ1 μin k α < ρh μin k α (some none) := by rw [hhτ₁]; unfold u1 at hu1; linarith
  -- (2) "We apply `lem:windows`(b) with `U = E ∖ {τ_1}` and `W = E`. Then `D = {b, τ_1}`,
  -- `X_{U,W} = K − d(E) + F_{τ_1}`, and `θ_{U,W} = θ_1`. The conditions of the lemma hold. For
  -- `τ_1`, we have just seen it."
  have hθ : θUW μin k α (univ.erase (some none)) univ = θ1 μin k α := (θ1_θUW k α).symm
  -- (3) "For `e ∈ E_k`, (W3) and `thm:splice`(a) give
  -- `ρ^h_e ≥ ρ^f_e = ρ^{(k)}_e > ρ^h_{τ_1} > θ_1`."
  have hold : ∀ c, θ1 μin k α < ρf μin k α (some (some c)) ∧
      ρf μin k α (some (some c)) ≤ ρh μin k α (some (some c)) := fun c => by
    refine ⟨?_, ρf_le_ρh k α _⟩
    rw [hof c]
    exact hτ₁_2.trans (h.W3 c α hα)
  -- (4) "For `τ_2`, (W5) gives `ρ^h_{τ_2} ≥ ρ^f_{τ_2} = ρ^f_{τ_1} + φw > ρ^h_{τ_1} > θ_1`."
  have hτ₂ : θ1 μin k α < ρf μin k α none ∧ ρf μin k α none ≤ ρh μin k α none := by
    refine ⟨?_, ρf_le_ρh k α none⟩
    have := mul_lt_mul_of_pos_right h.W5 (w_pos hμ)
    rw [ρf_τ₂_eq hμ]
    rw [hhτ₁] at hτ₁_2
    linarith
  -- (5) "So the configuration is `(E ∖ {τ_1}, E)`, and `θ_b = θ_1`."
  have hc : IsConfig μin k α (univ.erase (some none)) univ := by
    refine isConfig_of_windows (erase_subset _ _) (fun e he => ?_) (fun e he => ?_)
      (fun e _ => ?_) (fun e he => absurd (mem_univ e) he) <;> rw [hθ]
    · rcases e with _ | _ | c
      · exact hτ₂.1
      · exact absurd rfl (mem_erase.1 he).1
      · exact (hold c).1
    · rcases e with _ | _ | c
      · exact absurd (mem_erase.2 ⟨by simp, mem_univ _⟩) he
      · exact hτ₁_1.le
      · exact absurd (mem_erase.2 ⟨by simp, mem_univ _⟩) he
    · rcases e with _ | _ | c
      · exact hτ₂.1.le.trans hτ₂.2
      · exact hτ₁_2.le
      · exact (hold c).1.le.trans (hold c).2
  exact ⟨hc, hc.θb_eq.trans hθ⟩

/-- **Step (2) of the proof of `lem:onelevel`** (our numbering;
`stoc-sections/appD-hardness.tex:872-879`), "Next we show that `b` is merged with `τ_2` on the
second window `𝓡 + μ`": on `𝓡 + μ`, the configuration of level `k + 1` is `(∅, {τ_2})` and
`θ_b = θ_2`.

The step's sentences: (1) by (W2), `ρ^f_{τ_2} < θ_2 < ρ^h_{τ_2}`; (2) we apply `lem:windows`(b) with
`U = ∅` and `W = {τ_2}`, where `D = {b, τ_2}`, `X_{U,W} = K + F_{τ_2} − w/β_δ`, and `θ_{U,W} = θ_2`
(`θ2_θUW`); (3) for `e ∈ E_k`, `ρ^f_e ≤ ρ^h_e < θ_2` by (W4); (4) for `τ_1`,
`ρ^f_{τ_1} ≤ ρ^h_{τ_1} < ρ^f_{τ_2} < θ_2` by (W5); (5) so the configuration is `(∅, {τ_2})`
(`lem:windows`(b), `isConfig_of_windows`), and `θ_b = θ_2` (`lem:windows`(a), `IsConfig.θb_eq`). -/
theorem onelevel_step2 {k : ℕ} (h : OneLevelHyp μin k) {α : ℝ}
    (hα : α ∈ Set.Icc (R0 + μT μin (k + 1)) (R1T μin k + μT μin (k + 1))) :
    IsConfig μin k α ∅ {none} ∧ θb μin k α = θ2 μin k α := by
  have hμ := h.μ_pos
  have hs := s_pos (μin := μin) k
  obtain ⟨-, -, -, -, hhτ₁, hhτ₂⟩ := D_bands (μin := μin) k α
  -- (1) "By (W2), `ρ^f_{τ_2} < θ_2 < ρ^h_{τ_2}`."
  have hu0 : 0 < u2 μin k α := by
    have h1 := u2_slope (μin := μin) k (R0 + μT μin (k + 1)) α
    have h2 := mul_nonneg hs.le (sub_nonneg.2 hα.1)
    linarith [h.W2a]
  have hu1 : u2 μin k α < (lvl μin k).w (μT μin (k + 1)) := by
    have h1 := u2_slope (μin := μin) k α (R1T μin k + μT μin (k + 1))
    have h2 := mul_nonneg hs.le (sub_nonneg.2 hα.2)
    linarith [h.W2b]
  have hτ₂_1 : ρf μin k α none < θ2 μin k α := by unfold u2 at hu0; linarith
  have hτ₂_2 : θ2 μin k α < ρh μin k α none := by rw [hhτ₂]; unfold u2 at hu1; linarith
  -- (2) "We apply `lem:windows`(b) with `U = ∅` and `W = {τ_2}`. Then `D = {b, τ_2}`,
  -- `X_{U,W} = K + F_{τ_2} − w/β_δ`, and `θ_{U,W} = θ_2`."
  have hθ : θUW μin k α ∅ {none} = θ2 μin k α := (θ2_θUW k α).symm
  -- (3) "For `e ∈ E_k`, `ρ^f_e ≤ ρ^h_e < θ_2` by (W4)."
  have hold : ∀ c, ρf μin k α (some (some c)) ≤ ρh μin k α (some (some c)) ∧
      ρh μin k α (some (some c)) < θ2 μin k α := fun c => ⟨ρf_le_ρh k α _, h.W4 c α hα⟩
  -- (4) "For `τ_1`, `ρ^f_{τ_1} ≤ ρ^h_{τ_1} < ρ^f_{τ_2} < θ_2` by (W5)."
  have hτ₁ : ρf μin k α (some none) ≤ ρh μin k α (some none) ∧
      ρh μin k α (some none) < θ2 μin k α := by
    refine ⟨ρf_le_ρh k α _, ?_⟩
    rw [hhτ₁]
    have e := ρf_τ₂_eq hμ (μin := μin) α
    have := mul_lt_mul_of_pos_right h.W5 (w_pos hμ)
    linarith
  -- (5) "So the configuration is `(∅, {τ_2})`, and `θ_b = θ_2`."
  have hc : IsConfig μin k α ∅ {none} := by
    refine isConfig_of_windows (empty_subset _) (fun e he => absurd he (notMem_empty e))
      (fun e _ => ?_) (fun e he => ?_) (fun e he => ?_) <;> rw [hθ]
    · rcases e with _ | _ | c
      · exact hτ₂_1.le
      · exact hτ₁.1.trans hτ₁.2.le
      · exact (hold c).1.trans (hold c).2.le
    · rw [mem_singleton.1 he]
      exact hτ₂_2.le
    · rcases e with _ | _ | c
      · exact absurd (mem_singleton_self _) he
      · exact hτ₁.2
      · exact (hold c).2
  exact ⟨hc, hc.θb_eq.trans hθ⟩

/-- **Step (3) of the proof of `lem:onelevel`** (our numbering;
`stoc-sections/appD-hardness.tex:881-902`), "To complete (a), we follow `b` to the right of the
second window": `α_{τ_2} > R_1 + μ`; on `[R_1 + μ, α_{τ_2}]` the configuration of level `k + 1` is
`(∅, {τ_2})` with `θ_b = θ_2`, and on `(α_{τ_2}, ∞)` it is `(∅, ∅)`.

The step's sentences: (1) by (W2) and as `u_2` increases, `α_{τ_2} > R_1 + μ` and `u_2 > 0` on
`[R_1 + μ, ∞)`; (2) for `e ∈ E_k`, `θ_2 − ρ^h_e` is positive at `R_1 + μ` by (W4), and it increases,
as `θ_2` has slope `m̄ > M` (by (W6) and `lem:fast`) while `ρ^h_e` grows at most at the rate `M`;
(3) `ρ^h_{τ_1} < ρ^f_{τ_2} < θ_2` by (W5) and as `u_2 > 0`; (4) so every `e ∈ E_k ∪ {τ_1}` has
`ρ^f_e ≤ ρ^h_e < θ_2` on `[R_1 + μ, ∞)`; (5) on `[R_1 + μ, α_{τ_2}]`, where `0 < u_2 ≤ w`, also
`ρ^f_{τ_2} < θ_2 ≤ ρ^h_{τ_2}`, and `lem:windows`(b) with `U = ∅` and `W = {τ_2}` gives `(∅, {τ_2})`
and `θ_b = θ_2`; (6) `θ_out := αm_b − β_bK` (`θout` of `ContractDesignPolymatroids/Hardness/Step.lean`), the marginal that
`b` would have on its own, is `θ_{U,W}` for `U = W = ∅`, and from the definitions
`13θ_2 = α(12m_b + m_δ) − β_δ(K + F_{τ_2}) + w = 12θ_out + ρ^h_{τ_2}`, as `β_δ = 12β_b` and
`ρ^h_{τ_2}(α) = αm_δ − β_δF_{τ_2} + w`, so `12(θ_out − θ_2) = u_2 − w` and
`12(θ_out − ρ^h_{τ_2}) = 13(u_2 − w)`; (7) on `(α_{τ_2}, ∞)`, where `u_2 > w`, every `e ∈ E` has
`ρ^f_e ≤ ρ^h_e < θ_out`, and `lem:windows`(b) with `U = W = ∅` gives `(∅, ∅)`. -/
theorem onelevel_step3 {k : ℕ} (h : OneLevelHyp μin k) :
    R1T μin k + μT μin (k + 1) < ατ₂ μin k ∧
    (∀ α, R1T μin k + μT μin (k + 1) ≤ α → α ≤ ατ₂ μin k →
      IsConfig μin k α ∅ {none} ∧ θb μin k α = θ2 μin k α) ∧
    (∀ α, ατ₂ μin k < α → IsConfig μin k α ∅ ∅) := by
  have H := stepD_hyp (μin := μin) k
  have hμ := h.μ_pos
  have hs := s_pos (μin := μin) k
  have hβ := (lvl μin k).βδ_pos
  set R1 := R1T μin k
  set μ := μT μin (k + 1)
  -- (1) "By (W2) and as `u_2` increases, `α_{τ_2} > R_1 + μ` and `u_2 > 0` on `[R_1 + μ, ∞)`."
  have hατ₂ : R1 + μ < ατ₂ μin k := by
    have := u2_sub_w (μin := μin) k (R1 + μ)
    have := h.W2b
    by_contra hcon
    have : 0 ≤ (lvl μin k).s * (R1 + μ - ατ₂ μin k) := mul_nonneg hs.le (by linarith)
    linarith
  have hu0 : ∀ α, R1 + μ ≤ α → 0 < u2 μin k α := by
    intro α hα
    have h1 := u2_slope (μin := μin) k (R0 + μ) α
    have h2 := mul_nonneg hs.le (show 0 ≤ α - (R0 + μ) by linarith [R0_lt_R1T (μin := μin) k])
    linarith [h.W2a]
  -- (2) "For `e ∈ E_k`, `θ_2 − ρ^h_e` is positive at `R_1 + μ` by (W4), and it increases, as
  -- `θ_2` has slope `m̄ > M` (by (W6) and `lem:fast`) while `ρ^h_e` grows at most at the rate
  -- `M`."
  have hm := (fast_aux k h.W6).1
  have hθ2 : ∀ α δ, θ2 μin k (α + δ) = θ2 μin k α + δ * (lvl μin k).mbar := by
    intro α δ
    rw [θ2_eq, θ2_eq]
    ring
  have hold : ∀ c α, R1 + μ ≤ α → ρh μin k α (some (some c)) < θ2 μin k α := by
    intro c α hα
    have h0 := h.W4 c (R1 + μ) ⟨by linarith [R0_lt_R1T (μin := μin) k], le_rfl⟩
    have h1 := (ρh_rate (μin := μin) k (some (some c))).2 (R1 + μ) (α - (R1 + μ))
      (sub_nonneg.2 hα)
    have h2 := hθ2 (R1 + μ) (α - (R1 + μ))
    simp only [add_sub_cancel] at h1 h2
    have := mul_le_mul_of_nonneg_left hm.le (sub_nonneg.2 hα)
    linarith
  -- (3) "Moreover, `ρ^h_{τ_1} < ρ^f_{τ_2} < θ_2` by (W5) and as `u_2 > 0`."
  have hτ₁ : ∀ α, R1 + μ ≤ α → ρh μin k α (some none) < ρf μin k α none ∧
      ρf μin k α none < θ2 μin k α := by
    intro α hα
    obtain ⟨-, -, -, -, hhτ₁, -⟩ := D_bands (μin := μin) k α
    have e := ρf_τ₂_eq hμ (μin := μin) α
    have := mul_lt_mul_of_pos_right h.W5 (w_pos hμ)
    have := hu0 α hα
    unfold u2 at this
    constructor <;> linarith
  -- (4) "So every `e ∈ E_k ∪ {τ_1}` has `ρ^f_e ≤ ρ^h_e < θ_2` on `[R_1 + μ, ∞)`."
  have hlow : ∀ α, R1 + μ ≤ α → ∀ e, e ≠ none → ρf μin k α e ≤ ρh μin k α e ∧
      ρh μin k α e < θ2 μin k α := by
    intro α hα e he
    refine ⟨ρf_le_ρh k α e, ?_⟩
    rcases e with _ | _ | c
    · exact absurd rfl he
    · exact (hτ₁ α hα).1.trans (hτ₁ α hα).2
    · exact hold c α hα
  -- (5) "On `[R_1 + μ, α_{τ_2}]`, where `0 < u_2 ≤ w`, also `ρ^f_{τ_2} < θ_2 ≤ ρ^h_{τ_2}`, and
  -- `lem:windows`(b) with `U = ∅` and `W = {τ_2}` shows that the configuration is `(∅, {τ_2})`,
  -- with `θ_b = θ_2`."
  have h5 : ∀ α, R1 + μ ≤ α → α ≤ ατ₂ μin k →
      IsConfig μin k α ∅ {none} ∧ θb μin k α = θ2 μin k α := by
    intro α hα1 hα2
    have hτ₂_2 : θ2 μin k α ≤ ρh μin k α none := by
      have := u2_sub_w (μin := μin) k α
      have := mul_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.2 hα2)
      rw [(D_bands (μin := μin) k α).2.2.2.2.2]
      unfold u2 at *
      linarith
    have hθ : θUW μin k α ∅ {none} = θ2 μin k α := (θ2_θUW k α).symm
    have hc : IsConfig μin k α ∅ {none} := by
      refine isConfig_of_windows (empty_subset _) (fun e he => absurd he (notMem_empty e))
        (fun e _ => ?_) (fun e he => ?_) (fun e he => ?_) <;> rw [hθ]
      · rcases e with _ | e
        · exact (hτ₁ α hα1).2.le
        · exact (hlow α hα1 _ (by simp)).1.trans (hlow α hα1 _ (by simp)).2.le
      · rw [mem_singleton.1 he]
        exact hτ₂_2
      · rcases e with _ | e
        · exact absurd (mem_singleton_self _) he
        · exact (hlow α hα1 _ (by simp)).2
    exact ⟨hc, hc.θb_eq.trans hθ⟩
  -- (6) "Let `θ_out := αm_b − β_bK`, the marginal that `b` would have on its own, which is
  -- `θ_{U,W}` for `U = W = ∅`."
  have hout : ∀ α, (stepD μin k).θout α =
      α * (lvl μin k).mb - (lvl μin k).βb * (lvl μin k).K μ R1 := fun α => rfl
  have hθout : ∀ α, θUW μin k α ∅ ∅ = (stepD μin k).θout α := by
    intro α
    have hD : insertNone ((∅ : Finset (Option (Option (Gr k)))) \ ∅) = {none} := by
      ext o
      rcases o with _ | _ | _ | c <;> simp [mem_insertNone]
    have hX : bigX ((stepD μin k).fStep (gT μin k)) ((stepD μin k).dStep (mT μin k) (βT μin k))
        (stepD μin k).K ∅ ∅ = (stepD μin k).K := by
      simp [bigX, subMod, StepData.fStep_empty H.old.empty]
    have hb : (lvl μin k).βb ≠ 0 := by
      unfold Level.βb
      positivity
    unfold θUW thetaUW blockUW
    rw [hD, sum_singleton, sum_singleton, hX, hout]
    show (α * ((lvl μin k).mb / (lvl μin k).βb) - (lvl μin k).K μ R1) / (1 / (lvl μin k).βb) = _
    field_simp
  -- "From the definitions, `13θ_2 = α(12m_b + m_δ) − β_δ(K + F_{τ_2}) + w = 12θ_out + ρ^h_{τ_2}`,
  -- as `β_δ = 12β_b` and `ρ^h_{τ_2}(α) = αm_δ − β_δF_{τ_2} + w`."
  have h12 : (lvl μin k).βδ = 12 * (lvl μin k).βb := by
    unfold Level.βb
    ring
  have hρτ₂ : ∀ α, ρh μin k α none = α * (lvl μin k).mδ -
      (lvl μin k).βδ * (lvl μin k).Fτ₂ μ R1 + (lvl μin k).w μ := fun α => by
    rw [(D_bands (μin := μin) k α).2.2.2.2.2, (D_bands (μin := μin) k α).2.2.2.1]
  have h13' : ∀ α, 13 * θ2 μin k α = α * (12 * (lvl μin k).mb + (lvl μin k).mδ) -
      (lvl μin k).βδ * ((lvl μin k).K μ R1 + (lvl μin k).Fτ₂ μ R1) + (lvl μin k).w μ := fun α => by
    rw [θ2_eq]
    simp only [Level.mbar, Level.s, Level.mb]
    field_simp
    ring
  have h13 : ∀ α, 13 * θ2 μin k α = 12 * (stepD μin k).θout α + ρh μin k α none := fun α => by
    rw [h13', hout, hρτ₂, h12]
    ring
  -- "So `12(θ_out − θ_2) = u_2 − w` and `12(θ_out − ρ^h_{τ_2}) = 13(u_2 − w)`."
  have hout1 : ∀ α, 12 * ((stepD μin k).θout α - θ2 μin k α) =
      u2 μin k α - (lvl μin k).w μ := by
    intro α
    have := h13 α
    rw [u2, (D_bands (μin := μin) k α).2.2.2.2.2] at *
    linarith
  have hout2 : ∀ α, 12 * ((stepD μin k).θout α - ρh μin k α none) =
      13 * (u2 μin k α - (lvl μin k).w μ) := by
    intro α
    have := h13 α
    rw [u2, (D_bands (μin := μin) k α).2.2.2.2.2] at *
    linarith
  -- (7) "On `(α_{τ_2}, ∞)`, where `u_2 > w`, every `e ∈ E` therefore has `ρ^f_e ≤ ρ^h_e < θ_out`,
  -- and `lem:windows`(b) with `U = W = ∅` shows that the configuration is `(∅, ∅)`."
  have h7 : ∀ α, ατ₂ μin k < α → IsConfig μin k α ∅ ∅ := by
    intro α hα
    have hα1 : R1 + μ ≤ α := by linarith
    have hpos : 0 < u2 μin k α - (lvl μin k).w μ := by
      rw [u2_sub_w]
      exact mul_pos hs (sub_pos.2 hα)
    have h1 := hout1 α
    have h2 := hout2 α
    have hall : ∀ e, ρf μin k α e ≤ ρh μin k α e ∧ ρh μin k α e < (stepD μin k).θout α := by
      intro e
      refine ⟨ρf_le_ρh k α e, ?_⟩
      rcases e with _ | e
      · linarith
      · have := (hlow α hα1 (some e) (by simp)).2
        linarith
    refine isConfig_of_windows (empty_subset _) (fun e he => absurd he (notMem_empty e))
      (fun e _ => ?_) (fun e he => absurd he (notMem_empty e)) (fun e _ => ?_) <;> rw [hθout]
    · exact (hall e).1.trans (hall e).2.le
    · exact (hall e).2
  exact ⟨hατ₂, h5, h7⟩

/-- `lem:onelevel`(a) without the hypothesis `μ^in ∈ 𝔉` (`μ > 0` from (W1)), the form the proofs
below use (`stoc-sections/appD-hardness.tex:831-837`, proof lines 861-902): under (W1)–(W6) at the
step `k → k + 1`, `α_{τ_2} > R_1 + μ`, and the configuration of level `k + 1` is `(E ∖ {τ_1}, E)`,
with `θ_b = θ_1`, on `𝓡`; it is `(∅, {τ_2})`, with `θ_b = θ_2`, on `[R_0 + μ, α_{τ_2}]`; and it is
`(∅, ∅)` on `(α_{τ_2}, ∞)`.

The proof, steps (1)–(3) in our numbering: (1) the first window (`onelevel_step1`); (2) the
second window (`onelevel_step2`); (3) to the right of the second window (`onelevel_step3`); "With
the two windows, this proves (a)." -/
theorem onelevel_a_aux {k : ℕ} (h : OneLevelHyp μin k) :
    R1T μin k + μT μin (k + 1) < ατ₂ μin k ∧
    (∀ α ∈ Set.Icc R0 (R1T μin k),
      IsConfig μin k α (univ.erase (some none)) univ ∧ θb μin k α = θ1 μin k α) ∧
    (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (ατ₂ μin k),
      IsConfig μin k α ∅ {none} ∧ θb μin k α = θ2 μin k α) ∧
    (∀ α, ατ₂ μin k < α → IsConfig μin k α ∅ ∅) := by
  obtain ⟨hατ₂, h3, h3'⟩ := onelevel_step3 h
  refine ⟨hατ₂, fun α hα => onelevel_step1 h hα, fun α hα => ?_, h3'⟩
  -- "With the two windows, this proves (a)."
  by_cases h1 : α ≤ R1T μin k + μT μin (k + 1)
  · exact onelevel_step2 h ⟨hα.1, h1⟩
  · exact h3 α (not_le.1 h1).le hα.2

/-- `lem:onelevel`(b) without the hypothesis `μ^in ∈ 𝔉` (`μ > 0` from (W1)), the form the proofs
below use (`stoc-sections/appD-hardness.tex:838-845`, proof lines 904-922, "Now we prove (b)"):
under (W1)–(W6) at the step `k → k + 1`, the gap of level `k + 1` is the gap of level `k` at `α`
for `α ∈ 𝓡`, the gap of level `k` at `α − μ` for `α ∈ [R_0 + μ, α_{τ_2}]`, and that plus
`ψ_{k+1}(α − α_{τ_2})` for `α ∈ [α_{τ_2}, ∞)`.

The proof's sentences: (1) the setting of `lem:dmt` holds with `f_C := g_k` and `C := E_k`
(`dmtSetting_stepD`); on `𝓡` and on `[R_0 + μ, α_{τ_2}]` the claim is `lem:dmt`(c), applied with
`L_C := L_k`, whose cases (a) and (b) hold there by (a) (`gapT_config_τ₁`, `gapT_config_τ₂`; the
configuration is a weak configuration, `IsConfig.weak`); (2) on `[α_{τ_2}, ∞)`, `(∅, ∅)` is a weak
configuration, also at `α_{τ_2}`, where `ρ^h_{τ_2} = θ_2 = θ_b`; (3) so (`eq:windows`) gives
`r(ξ^{(k+1)}(α)) = r(ξ^{(k)}(α − μ)) + m_δ(F_{τ_1} + F_{τ_2}) − ∑_{e∈E} m_ed_e + Km_b`, and the
difference of the gaps is affine on `[α_{τ_2}, ∞)` with slope `q_{k+1} − q_k = ψ_{k+1}`
(`gapT_config_empty`); (4) it vanishes at `α_{τ_2}` by the case of `[R_0 + μ, α_{τ_2}]`. -/
theorem onelevel_b_aux {k : ℕ} (h : OneLevelHyp μin k) :
    (∀ α ∈ Set.Icc R0 (R1T μin k), gapT μin (k + 1) α = gapT μin k α) ∧
    (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (ατ₂ μin k),
      gapT μin (k + 1) α = gapT μin k (α - μT μin (k + 1))) ∧
    (∀ α, ατ₂ μin k ≤ α → gapT μin (k + 1) α =
      gapT μin k (α - μT μin (k + 1)) + (lvl μin k).ψ * (α - ατ₂ μin k)) := by
  have hμ := h.μ_pos
  obtain ⟨hατ₂, ha1, ha2, ha3⟩ := onelevel_a_aux h
  -- (1) "Now we prove (b). The setting of `lem:dmt` holds with `f_C := g_k` and `C := E_k`, as
  -- `m_* ≥ max_{e∈E} m_e` (see the paragraph after `def:ruleP`), `β_b = β_δ/12` by (P2) and
  -- `m_b > m_δ` by (P4), and its numbers `w`, `m̄`, `s`, and `ψ` are those of the parameter rule,
  -- with `ψ = ψ_{k+1}`. On `𝓡` and on `[R_0 + μ, α_{τ_2}]`, the claim is `lem:dmt`(c), applied
  -- with `L_C := L_k`, whose cases (a) and (b) hold there by (a). Its hypothesis on `ΔF` is (P5),
  -- and its line `L` is `L_{k+1}` by (P8)." (`dmtSetting_stepD`, `P5_stepD` and `gapT_succ_eq`,
  -- in `gapT_config_τ₁` and `gapT_config_τ₂`)
  have hb2 : ∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (ατ₂ μin k),
      gapT μin (k + 1) α = gapT μin k (α - μT μin (k + 1)) :=
    fun α hα => gapT_config_τ₂ k hμ (ha2 α hα).1.weak
  refine ⟨fun α hα => gapT_config_τ₁ k hμ (ha1 α hα).1.weak, hb2, fun α hα => ?_⟩
  -- (2) "On `[α_{τ_2}, ∞)`, the pair `(∅, ∅)` is a weak configuration, also at `α_{τ_2}`, where
  -- `ρ^h_{τ_2} = θ_2 = θ_b`."
  have hlow : ∀ α', ατ₂ μin k ≤ α' → ∀ e, ρh μin k α' e ≤ θb μin k α' := by
    intro α' hα' e
    rcases hα'.lt_or_eq with hlt | heq
    · exact (((ha3 α' hlt).spec).2.2.2.1 e (notMem_empty e)).2.le
    · subst heq
      obtain ⟨hc, hθ⟩ := ha2 (ατ₂ μin k) ⟨by linarith [R0_lt_R1T (μin := μin) k], le_rfl⟩
      rcases e with _ | e
      · -- at `α_{τ_2}`, `ρ^h_{τ_2} = θ_2 = θ_b`
        rw [hθ, (D_bands (μin := μin) k _).2.2.2.2.2]
        have := ατ₂_spec (μin := μin) k
        unfold u2 at this
        linarith
      · exact (hc.spec.2.2.2.1 (some e) (by simp)).2.le
  -- (3), (4) "So (`eq:windows`), with `lem:fullplane`(f) and `lem:translation`(c) (translation
  -- vector `(μ, m_*μ)`), gives
  -- `r(ξ^{(k+1)}(α)) = r(ξ^{(k)}(α − μ)) + m_δ(F_{τ_1} + F_{τ_2}) − ∑_{e∈E} m_ed_e + Km_b`.
  -- Hence `L_{k+1}(α) − r(ξ^{(k+1)}(α)) − (L_k(α − μ) − r(ξ^{(k)}(α − μ)))` is affine in `α` on
  -- `[α_{τ_2}, ∞)`, with slope `q_{k+1} − q_k = ψ_{k+1}`, and it vanishes at `α_{τ_2}` by the
  -- case of `[R_0 + μ, α_{τ_2}]`." (`gapT_config_empty`)
  have h0 := hb2 (ατ₂ μin k) ⟨by linarith [R0_lt_R1T (μin := μin) k], le_rfl⟩
  have := gapT_config_empty (μin := μin) k (hlow _ le_rfl) (hlow α hα)
  linarith

/-- `lem:onelevel`(c) without the hypothesis `μ^in ∈ 𝔉` (`μ > 0` from (W1)), the form the proofs
below use (`stoc-sections/appD-hardness.tex:846-848`, proof lines 924-941, "Finally, we prove
(c)"): under (W1)–(W6) at the step `k → k + 1`, on `𝓡` the smallest marginal of level `k + 1` is
`θ_1` (that of `b`) and the largest is `ρ^f_{τ_2}` (that of `τ_2`); on `𝓡 + μ`, the largest is `θ_2`
(that of `b`) and the smallest is `ρ^h_{τ_1}` (that of `τ_1`).

The proof's sentences: (1) on `𝓡`, `b` and `τ_1` have the marginal `θ_1`, and all other elements
have `ρ' = ρ^f > θ_1` (as shown for the first window, `onelevel_step1`, with the paragraph
"Configurations", `IsConfig.spec`); (2) for `α ∈ 𝓡`
and `e ∈ E_k`, (W4) at `α + μ` with (`eq:D-bands`), then (W2) and the slope `m_δ` of `ρ^f_{τ_2}`
give `ρ^{(k)}_e(α) + m_*μ = ρ^h_e(α + μ) < θ_2(α + μ) = ρ^f_{τ_2}(α + μ) + u_2(α + μ)
≤ ρ^f_{τ_2}(α) + μm_δ + w = ρ^f_{τ_2}(α) + m_*μ`, so `ρ^f_{τ_2}` is the largest; (3) on
`𝓡 + μ`, `b` and `τ_2` have the marginal `θ_2`, and all other elements have `ρ' = ρ^h < θ_2` (as
shown for the second window, `onelevel_step2`); (4) for
`α ∈ 𝓡 + μ` and `e ∈ E_k`, (W3) at `α − μ` and the slope `m_δ` of `ρ^h_{τ_1}` give
`ρ^h_e(α) = ρ^{(k)}_e(α − μ) + m_*μ > ρ^h_{τ_1}(α − μ) + m_*μ = ρ^h_{τ_1}(α) + w`, so, with
`ρ^h_{τ_1} < θ_2` from (3), `ρ^h_{τ_1}` is the smallest. -/
theorem onelevel_c_aux {k : ℕ} (h : OneLevelHyp μin k) :
    (∀ α ∈ Set.Icc R0 (R1T μin k),
      (∀ o, θ1 μin k α ≤ ρT μin (k + 1) α o ∧ ρT μin (k + 1) α o ≤ ρf μin k α none) ∧
      ρT μin (k + 1) α none = θ1 μin k α ∧ ρT μin (k + 1) α (some none) = ρf μin k α none) ∧
    (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (R1T μin k + μT μin (k + 1)),
      (∀ o, ρh μin k α (some none) ≤ ρT μin (k + 1) α o ∧ ρT μin (k + 1) α o ≤ θ2 μin k α) ∧
      ρT μin (k + 1) α none = θ2 μin k α ∧
      ρT μin (k + 1) α (some (some none)) = ρh μin k α (some none)) := by
  have hμ := h.μ_pos
  have hs := s_pos (μin := μin) k
  have he : (lvl μin k).w (μT μin (k + 1)) =
      μT μin (k + 1) * ((lvl μin k).mstar - (lvl μin k).mδ) := by
    rw [← stepD_w]
    rfl
  constructor
  · intro α hα
    obtain ⟨hc, hθ⟩ := onelevel_step1 h hα
    obtain ⟨-, hU, hWU, -, -⟩ := hc.spec
    -- (1) "Finally, we prove (c). On `𝓡`, `b` and `τ_1` have the marginal `θ_1`, and all other
    -- elements have `ρ' = ρ^f > θ_1` (as shown for the first window)."
    have hρ : ∀ e, e ≠ some none → ρT μin (k + 1) α (some e) = ρf μin k α e ∧
        θ1 μin k α < ρf μin k α e := fun e he => by
      rw [← hθ]
      exact hU e (mem_erase.2 ⟨he, mem_univ e⟩)
    have hρτ₁ : ρT μin (k + 1) α (some (some none)) = θ1 μin k α := by
      rw [← hθ]
      exact hWU (some none) (by simp)
    -- (2) "For `α ∈ 𝓡` and `e ∈ E_k`, (W4) at `α + μ` with (`eq:D-bands`), then (W2) and the slope
    -- `m_δ` of `ρ^f_{τ_2}` give `ρ^{(k)}_e(α) + m_*μ = ρ^h_e(α + μ) < θ_2(α + μ) =
    -- ρ^f_{τ_2}(α + μ) + u_2(α + μ) ≤ ρ^f_{τ_2}(α) + μm_δ + w = ρ^f_{τ_2}(α) + m_*μ`, so
    -- `ρ^f_{τ_2}` is the largest marginal."
    have hold : ∀ c, ρf μin k α (some (some c)) < ρf μin k α none := by
      intro c
      have hα' : α + μT μin (k + 1) ∈
          Set.Icc (R0 + μT μin (k + 1)) (R1T μin k + μT μin (k + 1)) :=
        ⟨by linarith [hα.1], by linarith [hα.2]⟩
      have h4 := h.W4 c _ hα'
      rw [(D_bands (μin := μin) k _).2.1, add_sub_cancel_right] at h4
      have hu2 : u2 μin k (α + μT μin (k + 1)) ≤ (lvl μin k).w (μT μin (k + 1)) := by
        have h1 := u2_slope (μin := μin) k (α + μT μin (k + 1))
          (R1T μin k + μT μin (k + 1))
        have h2 := mul_nonneg hs.le (show 0 ≤ R1T μin k + μT μin (k + 1) -
          (α + μT μin (k + 1)) by linarith [hα.2])
        linarith [h.W2b]
      unfold u2 at hu2
      rw [(D_bands (μin := μin) k _).1]
      rw [(D_bands (μin := μin) k _).2.2.2.1] at hu2 ⊢
      rw [he] at hu2
      nlinarith
    have hτ₂ : θ1 μin k α ≤ ρf μin k α none := (hρ none (by simp)).2.le
    refine ⟨fun o => ?_, hθ, (hρ none (by simp)).1⟩
    rcases o with _ | e
    · rw [show ρT μin (k + 1) α none = θb μin k α from rfl, hθ]
      exact ⟨le_rfl, hτ₂⟩
    · by_cases heτ₁ : e = some none
      · subst heτ₁
        rw [hρτ₁]
        exact ⟨le_rfl, hτ₂⟩
      · rw [(hρ e heτ₁).1]
        refine ⟨(hρ e heτ₁).2.le, ?_⟩
        rcases e with _ | _ | c
        · exact le_rfl
        · exact absurd rfl heτ₁
        · exact (hold c).le
  · intro α hα
    obtain ⟨hc, hθ⟩ := onelevel_step2 h hα
    obtain ⟨-, -, hWU, hW, -⟩ := hc.spec
    -- (3) "On `𝓡 + μ`, `b` and `τ_2` have the marginal `θ_2`, and all other elements have
    -- `ρ' = ρ^h < θ_2` (as shown for the second window)."
    have hρ : ∀ e, e ≠ none → ρT μin (k + 1) α (some e) = ρh μin k α e ∧
        ρh μin k α e < θ2 μin k α := fun e he => by
      rw [← hθ]
      exact hW e (by simpa using he)
    have hρτ₂ : ρT μin (k + 1) α (some none) = θ2 μin k α := by
      rw [← hθ]
      exact hWU none (by simp)
    -- (4) "For `α ∈ 𝓡 + μ` and `e ∈ E_k`, (W3) at `α − μ` and the slope `m_δ` of `ρ^h_{τ_1}` give
    -- `ρ^h_e(α) = ρ^{(k)}_e(α − μ) + m_*μ > ρ^h_{τ_1}(α − μ) + m_*μ = ρ^h_{τ_1}(α) + w`, so
    -- `ρ^h_{τ_1}` is the smallest marginal." The marginal `θ_2` of `b` and `τ_2` exceeds
    -- `ρ^h_{τ_1}` by (3) ("all other elements have `ρ' = ρ^h < θ_2`"), as at
    -- appD-hardness.tex:877-878.
    have hold : ∀ c, ρh μin k α (some none) < ρh μin k α (some (some c)) := by
      intro c
      have hα' : α - μT μin (k + 1) ∈ Set.Icc R0 (R1T μin k) :=
        ⟨by linarith [hα.1], by linarith [hα.2]⟩
      have h3 := h.W3 c _ hα'
      rw [(D_bands (μin := μin) k α).2.1]
      rw [(D_bands (μin := μin) k _).2.2.2.2.1, (D_bands (μin := μin) k _).2.2.1] at h3
      rw [(D_bands (μin := μin) k α).2.2.2.2.1, (D_bands (μin := μin) k α).2.2.1]
      rw [he] at h3 ⊢
      have := mul_pos hμ (show 0 < (lvl μin k).mstar - (lvl μin k).mδ by
        have := M_pos (μin := μin) k
        unfold Level.mstar
        linarith)
      nlinarith
    have hτ₁τ₂ : ρh μin k α (some none) ≤ θ2 μin k α := (hρ (some none) (by simp)).2.le
    refine ⟨fun o => ?_, hθ, (hρ (some none) (by simp)).1⟩
    rcases o with _ | e
    · rw [show ρT μin (k + 1) α none = θb μin k α from rfl, hθ]
      exact ⟨hτ₁τ₂, le_rfl⟩
    · by_cases heτ₂ : e = none
      · subst heτ₂
        rw [hρτ₂]
        exact ⟨hτ₁τ₂, le_rfl⟩
      · rw [(hρ e heτ₂).1]
        refine ⟨?_, (hρ e heτ₂).2.le⟩
        rcases e with _ | _ | c
        · exact absurd rfl heτ₂
        · exact le_rfl
        · exact (hold c).le

/-- **`lem:onelevel`(a)** (Lemma C.15, `stoc-sections/appD-hardness.tex:819-837`, proof lines
861-902): let `μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). Consider the step
`k → k + 1`, and assume (W1)–(W6) (`OneLevelHyp`); let `α_{τ_2}` be the zero of `u_2 − w`, the share
at which `b` reaches the top of the band of `τ_2`. Then `α_{τ_2} > R_1 + μ`, and the configuration
of level `k + 1` is `(E ∖ {τ_1}, E)`, with `θ_b = θ_1`, on `𝓡`; it is `(∅, {τ_2})`, with
`θ_b = θ_2`, on `[R_0 + μ, α_{τ_2}]`; and it is `(∅, ∅)` on `(α_{τ_2}, ∞)`. The proof (steps
(1)–(3)) is that of `onelevel_a_aux`, which takes `μ > 0` from (W1) instead of from `μ^in ∈ 𝔉`. -/
theorem onelevel_a {K k : ℕ} (_hF : InF μin K) (_hK : k + 2 ≤ K) (h : OneLevelHyp μin k) :
    R1T μin k + μT μin (k + 1) < ατ₂ μin k ∧
    (∀ α ∈ Set.Icc R0 (R1T μin k),
      IsConfig μin k α (univ.erase (some none)) univ ∧ θb μin k α = θ1 μin k α) ∧
    (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (ατ₂ μin k),
      IsConfig μin k α ∅ {none} ∧ θb μin k α = θ2 μin k α) ∧
    (∀ α, ατ₂ μin k < α → IsConfig μin k α ∅ ∅) :=
  onelevel_a_aux h

/-- **`lem:onelevel`(b)** (`stoc-sections/appD-hardness.tex:819-832, 838-845`, proof lines
904-922): let `μ^in ∈ 𝔉` have length at least `k + 2`. Under (W1)–(W6) at the step `k → k + 1`,
the gap `L_{k+1}(α) − r(ξ^{(k+1)}(α))` of level `k + 1` is the gap of level `k` at `α` for
`α ∈ 𝓡`, the gap of level `k` at `α − μ` for `α ∈ [R_0 + μ, α_{τ_2}]`, and that plus
`ψ_{k+1}(α − α_{τ_2})` for `α ∈ [α_{τ_2}, ∞)`. The proof is that of `onelevel_b_aux`. -/
theorem onelevel_b {K k : ℕ} (_hF : InF μin K) (_hK : k + 2 ≤ K) (h : OneLevelHyp μin k) :
    (∀ α ∈ Set.Icc R0 (R1T μin k), gapT μin (k + 1) α = gapT μin k α) ∧
    (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (ατ₂ μin k),
      gapT μin (k + 1) α = gapT μin k (α - μT μin (k + 1))) ∧
    (∀ α, ατ₂ μin k ≤ α → gapT μin (k + 1) α =
      gapT μin k (α - μT μin (k + 1)) + (lvl μin k).ψ * (α - ατ₂ μin k)) :=
  onelevel_b_aux h

/-- **`lem:onelevel`(c)** (`stoc-sections/appD-hardness.tex:819-832, 846-848`, proof lines
924-941): let `μ^in ∈ 𝔉` have length at least `k + 2`. Under (W1)–(W6) at the step `k → k + 1`,
on `𝓡` the smallest marginal of level `k + 1` is `θ_1` (that of `b`) and the largest is `ρ^f_{τ_2}`
(that of `τ_2`); on `𝓡 + μ`, the largest is `θ_2` (that of `b`) and the smallest is `ρ^h_{τ_1}`
(that of `τ_1`). The proof is that of `onelevel_c_aux`. -/
theorem onelevel_c {K k : ℕ} (_hF : InF μin K) (_hK : k + 2 ≤ K) (h : OneLevelHyp μin k) :
    (∀ α ∈ Set.Icc R0 (R1T μin k),
      (∀ o, θ1 μin k α ≤ ρT μin (k + 1) α o ∧ ρT μin (k + 1) α o ≤ ρf μin k α none) ∧
      ρT μin (k + 1) α none = θ1 μin k α ∧ ρT μin (k + 1) α (some none) = ρf μin k α none) ∧
    (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (R1T μin k + μT μin (k + 1)),
      (∀ o, ρh μin k α (some none) ≤ ρT μin (k + 1) α o ∧ ρT μin (k + 1) α o ≤ θ2 μin k α) ∧
      ρT μin (k + 1) α none = θ2 μin k α ∧
      ρT μin (k + 1) α (some (some none)) = ρh μin k α (some none)) :=
  onelevel_c_aux h

/-- **`lem:onelevel`** (Lemma C.15, `stoc-sections/appD-hardness.tex:819-850`): let
`μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). Consider the step `k → k + 1`, and assume
(W1)–(W6) (`OneLevelHyp`): (W1) `sι < u_1(R_0)` and `u_1(R_1) < w`; (W2) `0 < u_2(R_0 + μ)` and
`u_2(R_1 + μ) < w`; (W3) `ρ^{(k)}_e(α) > ρ^h_{τ_1}(α)` for all `e ∈ E_k` and `α ∈ 𝓡`; (W4)
`ρ^h_e(α) < θ_2(α)` for all `e ∈ E_k` and `α ∈ 𝓡 + μ`; (W5) `φ > 1`; (W6) `t_b/β⁻¹(E ∪ {b}) > M`.
Let `α_{τ_2}` (`ατ₂`) be the zero of `u_2 − w`, the share at which `b` reaches the top of the band
of `τ_2`. Then `α_{τ_2} > R_1 + μ`, and the following hold. (a) The configuration of level `k + 1`
is `(E ∖ {τ_1}, E)`, with `θ_b = θ_1`, on `𝓡`. It is `(∅, {τ_2})`, with `θ_b = θ_2`, on
`[R_0 + μ, α_{τ_2}]`, and it is `(∅, ∅)` on `(α_{τ_2}, ∞)`. (b) The gap
`L_{k+1}(α) − r(ξ^{(k+1)}(α))` of level `k + 1` (`gapT`) equals `L_k(α) − r(ξ^{(k)}(α))` for
`α ∈ 𝓡`, `L_k(α − μ) − r(ξ^{(k)}(α − μ))` for `α ∈ [R_0 + μ, α_{τ_2}]`, and
`L_k(α − μ) − r(ξ^{(k)}(α − μ)) + ψ_{k+1}(α − α_{τ_2})` for `α ∈ [α_{τ_2}, ∞)`. (c) On `𝓡`, the
smallest marginal of level `k + 1` is `θ_1` and the largest is `ρ^f_{τ_2}`. On `𝓡 + μ`, the largest
is `θ_2` and the smallest is `ρ^h_{τ_1}`.

The input `μ^in` of `def:tower` comes from the family `𝔉`, as in the paper, and is taken once for
the three parts; the claim `α_{τ_2} > R_1 + μ` is the first conjunct of (a). Its parts are
`onelevel_a`, `onelevel_b` and `onelevel_c`; their docstrings give the paper's steps. -/
theorem onelevel {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) (h : OneLevelHyp μin k) :
    -- `α_{τ_2} > R_1 + μ`, and (a)
    (R1T μin k + μT μin (k + 1) < ατ₂ μin k ∧
      (∀ α ∈ Set.Icc R0 (R1T μin k),
        IsConfig μin k α (univ.erase (some none)) univ ∧ θb μin k α = θ1 μin k α) ∧
      (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (ατ₂ μin k),
        IsConfig μin k α ∅ {none} ∧ θb μin k α = θ2 μin k α) ∧
      (∀ α, ατ₂ μin k < α → IsConfig μin k α ∅ ∅)) ∧
    -- (b)
    ((∀ α ∈ Set.Icc R0 (R1T μin k), gapT μin (k + 1) α = gapT μin k α) ∧
      (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (ατ₂ μin k),
        gapT μin (k + 1) α = gapT μin k (α - μT μin (k + 1))) ∧
      (∀ α, ατ₂ μin k ≤ α → gapT μin (k + 1) α =
        gapT μin k (α - μT μin (k + 1)) + (lvl μin k).ψ * (α - ατ₂ μin k))) ∧
    -- (c)
    ((∀ α ∈ Set.Icc R0 (R1T μin k),
        (∀ o, θ1 μin k α ≤ ρT μin (k + 1) α o ∧ ρT μin (k + 1) α o ≤ ρf μin k α none) ∧
        ρT μin (k + 1) α none = θ1 μin k α ∧ ρT μin (k + 1) α (some none) = ρf μin k α none) ∧
      (∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (R1T μin k + μT μin (k + 1)),
        (∀ o, ρh μin k α (some none) ≤ ρT μin (k + 1) α o ∧ ρT μin (k + 1) α o ≤ θ2 μin k α) ∧
        ρT μin (k + 1) α none = θ2 μin k α ∧
        ρT μin (k + 1) α (some (some none)) = ρh μin k α (some none))) :=
  ⟨onelevel_a hF hK h, onelevel_b hF hK h, onelevel_c hF hK h⟩

/-! ### `lem:leftwindows` -/

/-- `lem:leftwindows`(a) without the hypothesis `μ^in ∈ 𝔉`, the form the proofs below use
(`stoc-sections/appD-hardness.tex:953-954`, proof lines 965-970), for level `j = k + 1`:
assume the hypotheses of `lem:onelevel` at the step `k → k + 1`. Then for every `α ≤ R_0`, every
`e ∈ E_k ∪ {τ_2}` has `ρ^f_e(α) > θ_b(α)`, and `θ_b(α) ≤ ρ^h_{τ_1}(α)`.

The proof's steps: (1) by `lem:onelevel`(a), the configuration at `R_0` is `(E ∖ {τ_1}, E)` with
`θ_b = θ_1`, so `ρ^f_e > θ_b` at `R_0` for `e ∈ E_k ∪ {τ_2}`, and `θ_b < ρ^h_{τ_1}` at `R_0` by
(W1); (2) by (W6) and `lem:fast`, the differences `ρ^f_e − θ_b` and `ρ^h_{τ_1} − θ_b` decrease, so
these inequalities hold on `(−∞, R_0]`, "This proves (a)". -/
theorem leftwindows_a_aux {k : ℕ} (h : OneLevelHyp μin k) :
    ∀ α, α ≤ R0 → (∀ e, e ≠ some none → θb μin k α < ρf μin k α e) ∧
      θb μin k α ≤ ρh μin k α (some none) := by
  have hs := s_pos (μin := μin) k
  have hR0 : R0 ∈ Set.Icc R0 (R1T μin k) := ⟨le_rfl, (R0_lt_R1T (μin := μin) k).le⟩
  -- (1) "By `lem:onelevel`(a), the configuration at `R_0` is `(E ∖ {τ_1}, E)`, with `θ_b = θ_1`. So
  -- `ρ^f_e > θ_b` at `R_0` for `e ∈ E_{j−1} ∪ {τ_2}`, and `θ_b < ρ^h_{τ_1}` at `R_0` by (W1)."
  obtain ⟨hc0, hθ0⟩ := (onelevel_a_aux h).2.1 R0 hR0
  have h0f : ∀ e, e ≠ some none → θb μin k R0 < ρf μin k R0 e := fun e he =>
    ((isConfig_iff.1 hc0) e).1.1 (mem_erase.2 ⟨he, mem_univ e⟩)
  have h0h : θb μin k R0 < ρh μin k R0 (some none) := by
    have hu1 : u1 μin k R0 < (lvl μin k).w (μT μin (k + 1)) := by
      have h1 := u1_slope (μin := μin) k R0 (R1T μin k)
      have h2 := mul_pos hs (sub_pos.2 (R0_lt_R1T (μin := μin) k))
      linarith [h.W1b]
    rw [hθ0, (D_bands (μin := μin) k R0).2.2.2.2.1]
    unfold u1 at hu1
    linarith
  -- (2) "By (W6) and `lem:fast`, the differences `ρ^f_e − θ_b` and `ρ^h_{τ_1} − θ_b` decrease, so
  -- these inequalities hold on `(−∞, R_0]`. This proves (a)."
  have hfast := (fast_aux k h.W6).2
  intro α hα
  rcases hα.lt_or_eq with hlt | heq
  · refine ⟨fun e he => ?_, ?_⟩
    · have := (hfast e).2.1 hlt
      have := h0f e he
      simp only at *
      linarith
    · have := (hfast (some none)).2.2.2 hlt
      simp only at *
      linarith
  · subst heq
    exact ⟨h0f, h0h.le⟩

/-- `lem:leftwindows`(b) without the hypothesis `μ^in ∈ 𝔉`, the form the proofs below use
(`stoc-sections/appD-hardness.tex:955-957`, proof lines 970-976), for level `j = k + 1`:
assume the hypotheses of `lem:onelevel` at the step `k → k + 1`. Then for every `α ≤ R_0`,
`ρ^{(k+1)}_e(α) = ρ^{(k)}_e(α)` for `e ∈ E_k`, `ρ^{(k+1)}_{τ_2}(α) = ρ^f_{τ_2}(α)`, and `b` has the
smallest marginal of level `k + 1`.

The proof's step: (3) as `ρ^f ≤ ρ^h` (`thm:splice`(a)), `thm:splice`(b) then gives, with (a),
`ρ^{(k+1)}_e = med(ρ^f_e, θ_b, ρ^h_e) = ρ^f_e` for `e ∈ E_k ∪ {τ_2}`, which is `ρ^{(k)}_e` for
`e ∈ E_k` by `lem:fullplane`(f) (`eq:D-bands`), and
`ρ^{(k+1)}_{τ_1} = med(ρ^f_{τ_1}, θ_b, ρ^h_{τ_1}) ≥ θ_b`; so `b` has the smallest marginal, "which
proves (b)". -/
theorem leftwindows_b_aux {k : ℕ} (h : OneLevelHyp μin k) :
    ∀ α, α ≤ R0 → (∀ c, ρT μin (k + 1) α (some (some (some c))) = ρT μin k α c) ∧
      ρT μin (k + 1) α (some none) = ρf μin k α none ∧
      ∀ o, θb μin k α ≤ ρT μin (k + 1) α o := by
  intro α hα
  have ha := leftwindows_a_aux h α hα
  -- (3) "As `ρ^f ≤ ρ^h` (`thm:splice`(a)), `thm:splice`(b) then gives
  -- `ρ^{(j)}_e = med(ρ^f_e, θ_b, ρ^h_e) = ρ^f_e` for `e ∈ E_{j−1} ∪ {τ_2}`, which is `ρ^{(j−1)}_e`
  -- for `e ∈ E_{j−1}` by `lem:fullplane`(f), and
  -- `ρ^{(j)}_{τ_1} = med(ρ^f_{τ_1}, θ_b, ρ^h_{τ_1}) ≥ θ_b`. So `b` has the smallest marginal, which
  -- proves (b)."
  have hρ : ∀ e, e ≠ some none → ρT μin (k + 1) α (some e) = ρf μin k α e := fun e he => by
    rw [ρT_succ_med, med_eq_left (ρf_le_ρh k α e) (ha.1 e he).le]
  refine ⟨fun c => ?_, hρ none (by simp), fun o => ?_⟩
  · rw [hρ _ (by simp), (D_bands (μin := μin) k α).1]
  · rcases o with _ | e
    · exact le_rfl
    · by_cases he : e = some none
      · subst he
        rw [ρT_succ_med]
        exact (le_med_iff_of_le (ρf_le_ρh k α _) le_rfl).2 ha.2
      · rw [hρ e he]
        exact (ha.1 e he).le

/-- `lem:leftwindows`(c) without the hypothesis `μ^in ∈ 𝔉`, the form the proofs below use
(`stoc-sections/appD-hardness.tex:958-960`, proof lines 978-985), for level `j = k + 1`:
assume the hypotheses of `lem:onelevel` at the step `k → k + 1`. If `α ≤ R_0` and `u_1(α) ≥ 0`,
then level `k + 1` has the configuration `(E ∖ {τ_1}, E)`, so the block of `b` (the elements of
`E ∪ {b}` with the marginal `θ_b`) is `{b, τ_1}`, and `θ_b(α) = θ_1(α)`.

The proof's steps: (4) as `u_1` increases and `u_1(R_1) < w` by (W1), `ρ^f_{τ_1} ≤ θ_1 < ρ^h_{τ_1}`
at `α`; (5) `θ_1` has slope `m̄ > M`, so `ρ^f_e − θ_1` decreases for `e ∈ E_k ∪ {τ_2}`, and it is
positive at `R_0`, where `θ_1 = θ_b` (by (a) at `R_0` and `lem:onelevel`(a)), so
`ρ^h_e ≥ ρ^f_e > θ_1` at `α` for these `e`; (6) by `lem:windows`(b) with `U = E ∖ {τ_1}` and
`W = E` (`isConfig_of_windows`), the configuration at `α` is `(E ∖ {τ_1}, E)` and `θ_b = θ_1`
(`IsConfig.θb_eq`), so the block of `b` is `(W ∖ U) ∪ {b} = {b, τ_1}` (`IsConfig.spec`). -/
theorem leftwindows_c_aux {k : ℕ} (h : OneLevelHyp μin k) :
    ∀ α, α ≤ R0 → 0 ≤ u1 μin k α →
      IsConfig μin k α (univ.erase (some none)) univ ∧
      univ.filter (fun o => ρT μin (k + 1) α o = θb μin k α) = {none, some (some none)} ∧
      θb μin k α = θ1 μin k α := by
  intro α hα hu
  have hs := s_pos (μin := μin) k
  -- (4) "For (c), let `α ≤ R_0` with `u_1(α) ≥ 0`. As `u_1` increases and `u_1(R_1) < w` by (W1),
  -- `ρ^f_{τ_1} ≤ θ_1 < ρ^h_{τ_1}` at `α`."
  have hu1 : u1 μin k α < (lvl μin k).w (μT μin (k + 1)) := by
    have h1 := u1_slope (μin := μin) k α (R1T μin k)
    have h2 := mul_nonneg hs.le (show 0 ≤ R1T μin k - α by
      linarith [R0_lt_R1T (μin := μin) k])
    linarith [h.W1b]
  have hτ₁_1 : ρf μin k α (some none) ≤ θ1 μin k α := by unfold u1 at hu; linarith
  have hτ₁_2 : θ1 μin k α < ρh μin k α (some none) := by
    rw [(D_bands (μin := μin) k α).2.2.2.2.1]
    unfold u1 at hu1
    linarith
  -- (5) "The function `θ_1` has slope `m̄ > M`, so `ρ^f_e − θ_1` decreases for
  -- `e ∈ E_{j−1} ∪ {τ_2}`, and it is positive at `R_0`, where `θ_1 = θ_b`. So `ρ^h_e ≥ ρ^f_e > θ_1`
  -- at `α` for these `e`."
  have hm := (fast_aux k h.W6).1
  have hθ0 : θb μin k R0 = θ1 μin k R0 :=
    ((onelevel_a_aux h).2.1 R0 ⟨le_rfl, (R0_lt_R1T (μin := μin) k).le⟩).2
  have hθ1 : θ1 μin k R0 = θ1 μin k α + (R0 - α) * (lvl μin k).mbar := by
    rw [θ1_eq, θ1_eq]
    ring
  have hU : ∀ e, e ≠ some none → θ1 μin k α < ρf μin k α e ∧ ρf μin k α e ≤ ρh μin k α e := by
    intro e he
    refine ⟨?_, ρf_le_ρh k α e⟩
    have h1 := (leftwindows_a_aux h R0 le_rfl).1 e he
    rw [hθ0] at h1
    have h2 := (ρf_rate (μin := μin) k e).2 α (R0 - α) (sub_nonneg.2 hα)
    simp only [add_sub_cancel] at h2
    have := mul_le_mul_of_nonneg_left hm.le (sub_nonneg.2 hα)
    linarith
  -- (6) "By `lem:windows`(b) with `U = E ∖ {τ_1}` and `W = E`, the configuration at `α` is
  -- `(E ∖ {τ_1}, E)`, and `θ_b = θ_1`. So the block of `b` is `(W ∖ U) ∪ {b} = {b, τ_1}`."
  have hθ : θUW μin k α (univ.erase (some none)) univ = θ1 μin k α := (θ1_θUW k α).symm
  have hc : IsConfig μin k α (univ.erase (some none)) univ := by
    refine isConfig_of_windows (erase_subset _ _) (fun e he => ?_) (fun e he => ?_)
      (fun e _ => ?_) (fun e he => absurd (mem_univ e) he) <;> rw [hθ]
    · exact (hU e (mem_erase.1 he).1).1
    · have : e = some none := by
        by_contra hne
        exact he (mem_erase.2 ⟨hne, mem_univ e⟩)
      subst this
      exact hτ₁_1
    · by_cases he : e = some none
      · subst he
        exact hτ₁_2.le
      · exact (hU e he).1.le.trans (hU e he).2
  have hb : θb μin k α = θ1 μin k α := hc.θb_eq.trans hθ
  refine ⟨hc, ?_, hb⟩
  rw [hc.spec.2.2.2.2]
  exact StepData.insertNone_τ₁

/-- **`lem:leftwindows`(a)** (Lemma C.16, `stoc-sections/appD-hardness.tex:947-954`, proof lines
965-970), for level `j = k + 1`: let `μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`), and
assume the hypotheses of `lem:onelevel` at the step `k → k + 1` (`OneLevelHyp`); `f`, `h`, `τ_1`,
`τ_2`, `b`, `u_1`, `θ_1`, and `θ_b` are the quantities of this step, and `E = E_k ∪ {τ_1, τ_2}`.
Then for every `α ≤ R_0`, every `e ∈ E_k ∪ {τ_2}` has `ρ^f_e(α) > θ_b(α)`, and
`θ_b(α) ≤ ρ^h_{τ_1}(α)`. The proof (steps (1), (2)) is that of `leftwindows_a_aux`, which does not
use the hypothesis on the input. -/
theorem leftwindows_a {K k : ℕ} (_hF : InF μin K) (_hK : k + 2 ≤ K) (h : OneLevelHyp μin k) :
    ∀ α, α ≤ R0 → (∀ e, e ≠ some none → θb μin k α < ρf μin k α e) ∧
      θb μin k α ≤ ρh μin k α (some none) :=
  leftwindows_a_aux h

/-- **`lem:leftwindows`(b)** (`stoc-sections/appD-hardness.tex:947-952, 955-957`, proof lines
970-976), for level `j = k + 1`: let `μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`), and
assume the hypotheses of `lem:onelevel` at the step `k → k + 1`. Then for every `α ≤ R_0`,
`ρ^{(k+1)}_e(α) = ρ^{(k)}_e(α)` for `e ∈ E_k`, `ρ^{(k+1)}_{τ_2}(α) = ρ^f_{τ_2}(α)`, and `b` has the
smallest marginal of level `k + 1`. The proof (step (3)) is that of `leftwindows_b_aux`, which does
not use the hypothesis on the input. -/
theorem leftwindows_b {K k : ℕ} (_hF : InF μin K) (_hK : k + 2 ≤ K) (h : OneLevelHyp μin k) :
    ∀ α, α ≤ R0 → (∀ c, ρT μin (k + 1) α (some (some (some c))) = ρT μin k α c) ∧
      ρT μin (k + 1) α (some none) = ρf μin k α none ∧
      ∀ o, θb μin k α ≤ ρT μin (k + 1) α o :=
  leftwindows_b_aux h

/-- **`lem:leftwindows`(c)** (`stoc-sections/appD-hardness.tex:947-952, 958-960`, proof lines
978-985), for level `j = k + 1`: let `μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`), and
assume the hypotheses of `lem:onelevel` at the step `k → k + 1`. If `α ≤ R_0` and `u_1(α) ≥ 0`,
then level `k + 1` has the configuration `(E ∖ {τ_1}, E)`, so the block of `b` is `{b, τ_1}`, and
`θ_b(α) = θ_1(α)`. The proof (steps (4)–(6)) is that of `leftwindows_c_aux`, which does not use
the hypothesis on the input. -/
theorem leftwindows_c {K k : ℕ} (_hF : InF μin K) (_hK : k + 2 ≤ K) (h : OneLevelHyp μin k) :
    ∀ α, α ≤ R0 → 0 ≤ u1 μin k α →
      IsConfig μin k α (univ.erase (some none)) univ ∧
      univ.filter (fun o => ρT μin (k + 1) α o = θb μin k α) = {none, some (some none)} ∧
      θb μin k α = θ1 μin k α :=
  leftwindows_c_aux h

/-- **`lem:leftwindows`** (Lemma C.16, `stoc-sections/appD-hardness.tex:947-962`), for level
`j = k + 1`: let `μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). Let `j ≥ 1`, and assume the
hypotheses of `lem:onelevel` at the step `j − 1 → j` (`OneLevelHyp`). In this lemma, `f`, `h`,
`τ_1`, `τ_2`, `b`, `u_1`, `θ_1`, and `θ_b` are the quantities of this step, written without the
index `j`, and `E := E_{j−1} ∪ {τ_1, τ_2}`. Then the following hold for every `α ≤ R_0`. (a) Every
`e ∈ E_{j−1} ∪ {τ_2}` has `ρ^f_e(α) > θ_b(α)`, and `θ_b(α) ≤ ρ^h_{τ_1}(α)`. (b)
`ρ^{(j)}_e(α) = ρ^{(j−1)}_e(α)` for `e ∈ E_{j−1}`, `ρ^{(j)}_{τ_2}(α) = ρ^f_{τ_2}(α)`, and `b` has
the smallest marginal of level `j`. (c) If `u_1(α) ≥ 0`, then level `j` has the configuration
`(E ∖ {τ_1}, E)`, so the block of `b` is `{b, τ_1}`, and `θ_b(α) = θ_1(α)`.

The input `μ^in` of `def:tower` comes from the family `𝔉`, as in the paper, and is taken once for
the three parts, and so is the share `α ≤ R_0`. Its parts are `leftwindows_a`, `leftwindows_b` and
`leftwindows_c`; their docstrings give the paper's steps. -/
theorem leftwindows {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) (h : OneLevelHyp μin k) (α : ℝ)
    (hα : α ≤ R0) :
    -- (a)
    ((∀ e, e ≠ some none → θb μin k α < ρf μin k α e) ∧
      θb μin k α ≤ ρh μin k α (some none)) ∧
    -- (b)
    ((∀ c, ρT μin (k + 1) α (some (some (some c))) = ρT μin k α c) ∧
      ρT μin (k + 1) α (some none) = ρf μin k α none ∧
      ∀ o, θb μin k α ≤ ρT μin (k + 1) α o) ∧
    -- (c)
    (0 ≤ u1 μin k α →
      IsConfig μin k α (univ.erase (some none)) univ ∧
      univ.filter (fun o => ρT μin (k + 1) α o = θb μin k α) = {none, some (some none)} ∧
      θb μin k α = θ1 μin k α) :=
  ⟨leftwindows_a hF hK h α hα, leftwindows_b hF hK h α hα, leftwindows_c hF hK h α hα⟩

end Tower

end

end Hardness

end Stoc
