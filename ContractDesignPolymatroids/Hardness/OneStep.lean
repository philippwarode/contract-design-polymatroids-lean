-- stamp r9 2026-11-03
import ContractDesignPolymatroids.Hardness.Transition

/-!
# One step, and level 1: `lem:weights`(d), `prop:level1` and `thm:onestep`

The STOC version's `lem:weights`(d) (Appendix C.7, `sec:D-alllevels`, "Every level works",
`stoc-sections/appD-hardness.tex:1235-1242`, proof lines 1269-1285), `thm:onestep` (lines
1288-1418) and `prop:level1` (lines 1420-1490), for the levels of `def:tower` built by the parameter
rule.

* `υ0`, `shat`, `Awt`: `υ^0 = u^0/w`, `ŝ = s/(64M)` and `A` at a step (before `lem:weights` and in
  `lem:weights`(d)); `weights_d`: `lem:weights`(d);
* `weights`: the statement of `lem:weights`, the conjunction of (a)–(c) (`weights_a`, `weights_b`,
  `weights_c` in `ContractDesignPolymatroids/Hardness/Tower.lean`) and (d);
* the steps of the proof of `thm:onestep` that `prop:level1` uses as well ("as in the proof of
  `thm:onestep`"): `θ2_R0μ` (the value `θ_2(R_0 + μ) = ρ̄_k + m_*μ + sι`), `onestep_Q1`,
  `onestep_Q2` ((Q1), (Q2)), and the derivations `onestep_W3T2`, `onestep_T2'`, `onestep_W4`,
  `onestep_T3` of (W3) and the inequalities `ρ^h_{τ_1} < ρ^f_e < ρ^f_{τ_2}` of (T2), of the
  inequality `ρ^f_{τ_2} < ρ^h_{e'}` of (T2), of (W4) and of (T3) from them. The spread and the
  slope bound of the old marginals at `R_0` are parameters: `thm:onestep` takes them from
  `lem:onelevel`(c) and `lem:fullplane`(c), `prop:level1` from the first table of `prop:base` and
  (B3);
* `level1`: `prop:level1` (with `level1_data`, `level1_numbers`, `level1_spread`, the number `c` of
  its proof, `cLevel1`, and the D3 lemma `base_slopes`, the slope bound `12` of the base marginals
  read off the table); `onestep`: `thm:onestep` (with `Mhat`, `cτ₂`, `cw` and the lemmas
  `onestep_*` for the first paragraph of its proof, which writes the numbers of a step in terms of
  `M`, `ϖ` and `w`, and for its bullets).

The quantities of a step are those of the step `k → k + 1`: `φ μin k`, `υ0 μin k` and `Awt μin k`
are the paper's `φ`, `υ^0`, `A` at that step, so `φ μin (j - 1)` is the paper's `φ_j` of level `j`.

Taken over on 2026-10-20 from `Paper/Hardness/OneStep.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

section Tower

variable (μin : ℕ → ℕ)

/-- `υ^0 = u^0/w` at the step `k → k + 1` (the paper's `υ^0_{k+1}` of level `k + 1`). -/
def υ0 (k : ℕ) : ℝ :=
  (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) / (lvl μin k).w (μT μin (k + 1))

/-- `ŝ = s/(64M)` at the step `k → k + 1` (before `lem:weights`). -/
def shat (k : ℕ) : ℝ := (lvl μin k).s / (64 * (lvl μin k).M)

/-- `A = 1245/416 − 1/2 − d̄ + a_0/(Δ_b w)` at the step `k → k + 1` (`lem:weights`(d)). -/
def Awt (k : ℕ) : ℝ :=
  1245 / 416 - 1 / 2 - (lvl μin k).dbar (μT μin (k + 1)) +
    (lvl μin k).a0 (μT μin (k + 1)) / ((lvl μin k).Δb * (lvl μin k).w (μT μin (k + 1)))

variable {μin}

/-- `ϖ_{k+1} = 8ϖ_k` for `k ≥ 1`, and `1/β_δ = ϖ_{k+1}` at the step `k → k + 1` (`lem:weights`,
(P2)). -/
lemma inv_βδ_eq (j : ℕ) : 1 / (lvl μin (j + 1)).βδ = 8 * ϖ μin (j + 1) := by
  show ϖ μin (j + 2) = _
  rw [ϖ_succ, ϖ_succ, pow_succ]
  ring

/-- Before `lem:weights` (`stoc-sections/appD-hardness.tex:1220-1221`): by (P4),
`s = (12/13)Δ_b = (2490/13)M` at every step, so `ŝ := s/(64M) = 1245/416` does not depend on the
step. -/
lemma shat_eq (k : ℕ) : shat μin k = 1245 / 416 := by
  have hM := (M_pos (μin := μin) k).ne'
  have hs : (lvl μin k).s = 2490 / 13 * (lvl μin k).M := by
    simp only [Level.s, Level.Δb]
    ring
  rw [shat, hs]
  field_simp
  ring

/-! ### `lem:weights`(d) -/

/-- **`lem:weights`(d)** (`stoc-sections/appD-hardness.tex:1235-1242`, proof lines 1269-1285): let
`k ≥ 1` (here `k = j + 1`) and let `μ^in ∈ 𝔉` have length at least `k + 2`. At the step
`k → k + 1`, `d̄ ∈ [127/64, 129/64)`, `|a_0|/(Δ_b w) ≤ 517/106240 < 0.00487`, and
`φ ∈ (2.9791, 3.0209)`. Moreover, `u^0/w = A − (1245/832)ℓ̂_k` with
`A := 1245/416 − 1/2 − d̄ + a_0/(Δ_b w) ∈ (0.4722, 0.5133)`, and `u^0/w ∈ (0.2354, 0.5133)`.

The proof's steps: (1) with `M := M_k` and `ϖ := ϖ_k`, `1/β_δ = ϖ_{k+1} = 8ϖ`, `m_* = (129/2)M`,
and `w = 64Mμ`, and `β⁻¹(E_k) = 16ϖ` by (a); (2) by (b), `m_* − m_e ∈ [127M/2, 129M/2)` for
`e ∈ E_k`, and as `d_e = μ(m_* − m_e)/β_e` and `d_{τ_1} = w/β_δ = 512ϖMμ`, (P3) gives
`d̄ = ∑_{e∈E_k} (m_* − m_e)/(512ϖMβ_e) ∈ [127/64, 129/64)`; (3) as `|m_δ − m_e| ≤ M/2`,
`|Π| ≤ (M/2)d(E_k) < (M/2)(129/2)Mμβ⁻¹(E_k) = 516ϖμM²`; (4) with `0 < q_kμ ≤ ϖμM²` by (c) and
`a_0 = (q_kμ − Π)/(8ϖ)`, `|a_0| ≤ (517/8)μM²`, and as `Δ_bw = 13280μM²`,
`|a_0|/(Δ_bw) ≤ 517/106240`; (5) by `lem:closedforms`(a), `φ = 1 + d̄ − a_0/(sw)`, where
`a_0/(sw) = (13/12)a_0/(Δ_bw)`, which gives the range of `φ`; (6) `a_2Δ_b = s(μ − |𝓡|/2)`, so
`a_2Δ_b/w = ŝ(1 − ℓ̂_k/2)`, as `|𝓡|/μ = ℓ̂_k`, and (P6) gives
`u^0/w = ŝ(1 − ℓ̂_k/2) − 1/2 − d̄ + a_0/(Δ_bw) = A − (1/2)ŝℓ̂_k` (`ŝ = 1245/416`, `shat_eq`);
(7) the range of `A` follows from those of `d̄` and `a_0/(Δ_bw)`, and `0 < (1/2)ŝℓ̂_k < 0.2367` by
`lem:inputs` gives the range of `u^0/w`. -/
theorem weights_d {j : ℕ} {K : ℕ} (hF : InF μin K) (hK : j + 1 + 2 ≤ K) :
    (lvl μin (j + 1)).dbar (μT μin (j + 2)) ∈ Set.Ico (127 / 64) (129 / 64) ∧
    |(lvl μin (j + 1)).a0 (μT μin (j + 2))| /
        ((lvl μin (j + 1)).Δb * (lvl μin (j + 1)).w (μT μin (j + 2))) ≤ 517 / 106240 ∧
    (517 / 106240 : ℝ) < 0.00487 ∧
    φ μin (j + 1) ∈ Set.Ioo 2.9791 3.0209 ∧
    υ0 μin (j + 1) = Awt μin (j + 1) - 1245 / 832 * ℓhat μin (j + 1) ∧
    Awt μin (j + 1) ∈ Set.Ioo 0.4722 0.5133 ∧
    υ0 μin (j + 1) ∈ Set.Ioo 0.2354 0.5133 := by
  set L := lvl μin (j + 1) with hL
  set μ := μT μin (j + 2) with hμdef
  set M := L.M with hMdef
  set ϖk := ϖ μin (j + 1) with hϖdef
  have hμ : 0 < μ := μT_pos hF (by omega)
  have hM : 0 < M := M_pos (j + 1)
  have hϖ : 0 < ϖk := ϖ_pos (j + 1)
  -- (1) "Write `M := M_k` and `ϖ := ϖ_k`, so that `1/β_δ = ϖ_{k+1} = 8ϖ`, `m_* = (129/2)M`, and
  -- `w = 64Mμ`, and `β⁻¹(E_k) = 16ϖ` by (a)."
  have hβ : 1 / L.βδ = 8 * ϖk := inv_βδ_eq j
  have hβ' : L.βδ = 1 / (8 * ϖk) := by rw [← hβ, one_div_one_div]
  have hmstar : L.mstar = 129 / 2 * M := by simp only [Level.mstar, Level.mδ, hMdef]; ring
  have hw : L.w μ = 64 * M * μ := rfl
  have hS : ∑ c, 1 / L.β c = 16 * ϖk := (weights_a (μin := μin)).2.2.1 j
  have hβpos : ∀ c, 0 < L.β c := (fpHyp_gT (μin := μin) (j + 1)).pos
  have hmpos : ∀ c, 0 < L.m c := mT_pos (j + 1)
  have hmle : ∀ c, L.m c ≤ M := mT_le_M (j + 1)
  have hne : (univ : Finset (Gr (j + 1))).Nonempty := ⟨none, mem_univ _⟩
  -- (2) "By (b), `m_* − m_e ∈ [(127/2)M, (129/2)M)` for `e ∈ E_k`. As `d_e = μ(m_* − m_e)/β_e`
  -- and `d_{τ_1} = w/β_δ = 512ϖMμ`, (P3) gives
  -- `d̄ = ∑_{e∈E_k} (m_* − m_e)/(512ϖMβ_e) ∈ [127/64, 129/64)`."
  have hdbar : L.dbar μ = ∑ c, (L.mstar - L.m c) / (512 * ϖk * M * L.β c) := by
    simp only [Level.dbar, Level.dEk, Level.d, sum_div]
    refine sum_congr rfl fun c _ => ?_
    rw [hw, hβ']
    have := (hβpos c).ne'
    field_simp
    ring
  have hlow : ∀ c, 127 / 2 * M / (512 * ϖk * M) * (1 / L.β c) ≤
      (L.mstar - L.m c) / (512 * ϖk * M * L.β c) := fun c => by
    have := hβpos c
    rw [hmstar, show 127 / 2 * M / (512 * ϖk * M) * (1 / L.β c) =
      127 / 2 * M / (512 * ϖk * M * L.β c) by field_simp]
    exact div_le_div_of_nonneg_right (by linarith [hmle c]) (by positivity)
  have hupp : ∀ c, (L.mstar - L.m c) / (512 * ϖk * M * L.β c) <
      129 / 2 * M / (512 * ϖk * M) * (1 / L.β c) := fun c => by
    have := hβpos c
    rw [hmstar, show 129 / 2 * M / (512 * ϖk * M) * (1 / L.β c) =
      129 / 2 * M / (512 * ϖk * M * L.β c) by field_simp]
    exact div_lt_div_of_pos_right (by linarith [hmpos c]) (by positivity)
  have hd1 : 127 / 64 ≤ L.dbar μ := by
    rw [hdbar]
    calc (127 / 64 : ℝ) = ∑ c, 127 / 2 * M / (512 * ϖk * M) * (1 / L.β c) := by
          rw [← mul_sum, hS]; field_simp; ring
      _ ≤ _ := sum_le_sum fun c _ => hlow c
  have hd2 : L.dbar μ < 129 / 64 := by
    rw [hdbar]
    calc ∑ c, (L.mstar - L.m c) / (512 * ϖk * M * L.β c) <
          ∑ c, 129 / 2 * M / (512 * ϖk * M) * (1 / L.β c) :=
          sum_lt_sum_of_nonempty hne fun c _ => hupp c
      _ = 129 / 64 := by rw [← mul_sum, hS]; field_simp; ring
  -- (3) "As `|m_δ − m_e| ≤ M/2` for `e ∈ E_k`, we get
  -- `|Π| ≤ (M/2)d(E_k) < (M/2)·(129/2)Mμβ⁻¹(E_k) = 516ϖμM²`."
  have hdnn : ∀ c, 0 ≤ L.d μ c := fun c => by
    have := hβpos c
    unfold Level.d
    rw [hmstar]
    have := hmle c
    have : 0 ≤ 129 / 2 * M - L.m c := by linarith
    positivity
  have hdE : L.dEk μ < 129 / 2 * M * μ * ∑ c, 1 / L.β c := by
    unfold Level.dEk
    rw [mul_sum]
    refine sum_lt_sum_of_nonempty hne fun c _ => ?_
    have := hβpos c
    unfold Level.d
    rw [hmstar, show 129 / 2 * M * μ * (1 / L.β c) = μ * (129 / 2 * M) / L.β c by ring]
    exact div_lt_div_of_pos_right (by nlinarith [hmpos c]) this
  have hPi : |L.Pcal μ| < 516 * ϖk * μ * M ^ 2 := by
    have h1 : |L.Pcal μ| ≤ M / 2 * L.dEk μ := by
      unfold Level.Pcal Level.dEk
      rw [mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ => ?_)
      rw [abs_mul, abs_of_nonneg (hdnn c)]
      refine mul_le_mul_of_nonneg_right ?_ (hdnn c)
      rw [abs_le]
      have := hmpos c
      have := hmle c
      simp only [Level.mδ, hMdef] at *
      constructor <;> linarith
    rw [hS] at hdE
    nlinarith
  -- (4) "With `0 < q_kμ ≤ ϖμM²` by (c) and `a_0 = β_δ(q_kμ − Π) = (q_kμ − Π)/(8ϖ)`, this gives
  -- `|a_0| ≤ (517/8)μM²`, and as `Δ_bw = 13280μM²`, `|a_0|/(Δ_bw) ≤ 517/106240`."
  obtain ⟨hq1, hq2⟩ := (weights_c (μin := μin)).2 j
  have hqpos : 0 < L.q := lt_of_le_of_lt (by positivity) hq1
  have ha0 : |L.a0 μ| ≤ 517 / 8 * μ * M ^ 2 := by
    have e : L.a0 μ = (L.q * μ - L.Pcal μ) / (8 * ϖk) := by
      simp only [Level.a0, hβ']
      field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * ϖk), div_le_iff₀ (by positivity)]
    have hqμ : L.q * μ ≤ ϖk * M ^ 2 * μ := mul_le_mul_of_nonneg_right hq2 hμ.le
    calc |L.q * μ - L.Pcal μ| ≤ |L.q * μ| + |L.Pcal μ| := abs_sub _ _
      _ ≤ 517 / 8 * μ * M ^ 2 * (8 * ϖk) := by
        rw [abs_of_pos (by positivity)]
        nlinarith
  have hΔw : L.Δb * L.w μ = 13280 * μ * M ^ 2 := by
    rw [hw]; simp only [Level.Δb, hMdef]; ring
  have hΔwpos : 0 < L.Δb * L.w μ := by rw [hΔw]; positivity
  have ha0r : |L.a0 μ| / (L.Δb * L.w μ) ≤ 517 / 106240 := by
    rw [div_le_iff₀ hΔwpos, hΔw]
    linarith
  have ha0r' : |L.a0 μ / (L.Δb * L.w μ)| ≤ 517 / 106240 := by
    rwa [abs_div, abs_of_pos hΔwpos]
  obtain ⟨ha0l, ha0u⟩ := abs_le.1 ha0r'
  -- (5) "By `lem:closedforms`(a), `φ = 1 + d̄ − a_0/(sw)`, where `a_0/(sw) = (13/12)a_0/(Δ_bw)`,
  -- which gives the range of `φ`."
  have hφ := (closedforms_a (j + 1) hF hK).2
  have hsw : L.a0 μ / (L.s * L.w μ) = 13 / 12 * (L.a0 μ / (L.Δb * L.w μ)) := by
    have := (w_pos (μin := μin) (k := j + 1) hμ).ne'
    have : L.Δb ≠ 0 := by unfold Level.Δb; positivity
    simp only [Level.s]
    field_simp
  rw [hsw] at hφ
  -- (6) "Next, `a_2Δ_b = s(μ − |𝓡|/2)`, so `a_2Δ_b/w = ŝ(1 − ℓ̂_k/2)`, as `|𝓡|/μ = ℓ̂_k`, and (P6)
  -- gives `u^0/w = ŝ(1 − ℓ̂_k/2) − 1/2 − d̄ + a_0/(Δ_bw) = A − (1/2)ŝℓ̂_k`."
  have hw0 := (w_pos (μin := μin) (k := j + 1) hμ).ne'
  have ha2 : Level.a2 μ (R1T μin (j + 1)) * L.Δb = L.s * (μ - lenR μin (j + 1) / 2) := by
    simp only [Level.a2, Level.s, lenR]
    ring
  have ha2w : Level.a2 μ (R1T μin (j + 1)) * L.Δb / L.w μ =
      shat μin (j + 1) * (1 - ℓhat μin (j + 1) / 2) := by
    rw [ha2, shat, ← hL, ← hMdef, show ℓhat μin (j + 1) = lenR μin (j + 1) / μ from rfl, hw]
    have := hμ.ne'
    have := hM.ne'
    field_simp
  have hυ' : υ0 μin (j + 1) = shat μin (j + 1) * (1 - ℓhat μin (j + 1) / 2) - 1 / 2 - L.dbar μ +
      L.a0 μ / (L.Δb * L.w μ) := by
    rw [← ha2w]
    simp only [υ0, Level.u0]
    rw [← hL, ← hμdef]
    have : L.Δb ≠ 0 := by unfold Level.Δb; positivity
    have : L.w μ ≠ 0 := by rw [hw]; positivity
    field_simp
    ring
  have hυ2 : υ0 μin (j + 1) = Awt μin (j + 1) - 1 / 2 * shat μin (j + 1) * ℓhat μin (j + 1) := by
    rw [hυ', shat_eq]
    simp only [Awt]
    rw [← hL, ← hμdef]
    ring
  have hυ : υ0 μin (j + 1) = Awt μin (j + 1) - 1245 / 832 * ℓhat μin (j + 1) := by
    rw [hυ2, shat_eq]
    ring
  -- (7) "The range of `A` follows from those of `d̄` and `a_0/(Δ_bw)`, and
  -- `0 < (1/2)ŝℓ̂_k < 0.2367` by `lem:inputs` gives the range of `u^0/w`."
  have hA : Awt μin (j + 1) ∈ Set.Ioo 0.4722 0.5133 := by
    simp only [Awt]
    rw [← hL, ← hμdef]
    constructor <;> norm_num <;> linarith
  have hℓ : ℓhat μin (j + 1) < 253 / 1600 :=
    ((inputs hF (by omega)).2.1 (j + 1) (by omega) (by omega)).2.1
  have hℓ0 : 0 < ℓhat μin (j + 1) := by
    simp only [ℓhat, lenR_eq]
    have := sum_nonneg fun i (_ : i ∈ range (j + 1 + 1)) => μT_nonneg (μin := μin) i
    positivity
  have hsℓ : 0 < 1 / 2 * shat μin (j + 1) * ℓhat μin (j + 1) ∧
      1 / 2 * shat μin (j + 1) * ℓhat μin (j + 1) < 0.2367 := by
    rw [shat_eq]
    constructor <;> linarith
  refine ⟨⟨hd1, hd2⟩, ha0r, by norm_num, ⟨?_, ?_⟩, hυ, hA, ?_⟩
  · rw [hφ]; norm_num; linarith
  · rw [hφ]; norm_num; linarith
  · rw [hυ2]
    constructor <;> linarith [hA.1, hA.2, hsℓ.1, hsℓ.2]

/-- **`lem:weights`** (Lemma C.20, `stoc-sections/appD-hardness.tex:1226-1244`): (a)
`β⁻¹(E_k) = 2ϖ_{k+1}` for every `k ≥ 0`. Hence `β⁻¹({τ_{1,k+1}, τ_{2,k+1}}) = β⁻¹(E_k)` and
`β⁻¹(E_k ∪ {τ_{1,k+1}, τ_{2,k+1}, b_{k+1}}) = 16ϖ_{k+1}` for `k ≥ 0`, and `β⁻¹(E_k ∖ {b_k}) = 4ϖ_k`
for `k ≥ 1` (here at level `k + 1`). (b) For every `k ≥ 0`, all rewards of `E_k` are integers in
`(0, M_k]`, and `M_k = 12 · 208^k` is the reward of `C_1` if `k = 0` and of `b_k` if `k ≥ 1`. (c)
`q_0 = 7`, and `(9/10)ϖ_k M_k² < q_k ≤ ϖ_k M_k²` for `k ≥ 1` (here for `k + 1`). (d) Let `k ≥ 1`
(here `k = j + 1`), and let `μ^in ∈ 𝔉` have length at least `k + 2`. At the step `k → k + 1`,
`d̄ ∈ [127/64, 129/64)`, `|a_0|/(Δ_b w) ≤ 517/106240 < 0.00487`, and `φ ∈ (2.9791, 3.0209)`.
Moreover, `u^0/w = A − (1245/832)ℓ̂_k` with
`A := 1245/416 − 1/2 − d̄ + a_0/(Δ_b w) ∈ (0.4722, 0.5133)`, and `u^0/w ∈ (0.2354, 0.5133)`.

Parts (a)–(c) concern the levels for any input `μ^in` and have no hypothesis on it; (d) has its own.
Its parts are `weights_a`, `weights_b` and `weights_c` (`ContractDesignPolymatroids/Hardness/Tower.lean`) and `weights_d`;
their docstrings give the paper's steps. -/
theorem weights :
    -- (a)
    ((∀ k, ∑ e, 1 / βT μin k e = 2 * ϖ μin (k + 1)) ∧
      (∀ k, 1 / (stepD μin k).βδ + 1 / (stepD μin k).βδ = ∑ e, 1 / βT μin k e) ∧
      (∀ k, ∑ e, 1 / βT μin (k + 1) e = 16 * ϖ μin (k + 1)) ∧
      (∀ k, ∑ e : Option (Option (Gr k)), 1 / βT μin (k + 1) (some e) = 4 * ϖ μin (k + 1))) ∧
    -- (b)
    ((∀ k (e : Gr k), ∃ n : ℕ, 0 < n ∧ mT μin k e = n ∧ (n : ℝ) ≤ (lvl μin k).M) ∧
      (∀ k, (lvl μin k).M = 12 * 208 ^ k) ∧
      mT μin 0 (show Gr 0 from (1 : Fin 3)) = (lvl μin 0).M ∧
      (∀ k, mT μin (k + 1) none = (lvl μin (k + 1)).M)) ∧
    -- (c)
    ((lvl μin 0).q = 7 ∧
      ∀ k, 9 / 10 * ϖ μin (k + 1) * (lvl μin (k + 1)).M ^ 2 < (lvl μin (k + 1)).q ∧
        (lvl μin (k + 1)).q ≤ ϖ μin (k + 1) * (lvl μin (k + 1)).M ^ 2) ∧
    -- (d)
    ∀ {j K : ℕ}, InF μin K → j + 1 + 2 ≤ K →
      (lvl μin (j + 1)).dbar (μT μin (j + 2)) ∈ Set.Ico (127 / 64) (129 / 64) ∧
      |(lvl μin (j + 1)).a0 (μT μin (j + 2))| /
          ((lvl μin (j + 1)).Δb * (lvl μin (j + 1)).w (μT μin (j + 2))) ≤ 517 / 106240 ∧
      (517 / 106240 : ℝ) < 0.00487 ∧
      φ μin (j + 1) ∈ Set.Ioo 2.9791 3.0209 ∧
      υ0 μin (j + 1) = Awt μin (j + 1) - 1245 / 832 * ℓhat μin (j + 1) ∧
      Awt μin (j + 1) ∈ Set.Ioo 0.4722 0.5133 ∧
      υ0 μin (j + 1) ∈ Set.Ioo 0.2354 0.5133 :=
  ⟨weights_a, weights_b, weights_c, weights_d⟩

/-! ### The steps of the proof of `thm:onestep` that `prop:level1` uses -/

/-- `lem:fullplane`(c) for level `k`: its marginals are nondecreasing. -/
lemma ρT_mono (k : ℕ) (c : Gr k) : Monotone fun α => ρT μin k α c := by
  have H := fpHyp_gT (μin := μin) k
  exact ((fullplane_c H.submod H.empty (mT_pos (μin := μin) k) H.pos c 0 fun S _ => by
    rw [zero_mul]
    exact sum_nonneg fun o _ => div_nonneg (mT_pos (μin := μin) k o).le (H.pos o).le).2.2.1
      c).2.2.2

/-- `w = (m_* − m_δ)μ` and `m_*μ = m_δμ + w` (`tab:ruleP`). -/
lemma mstar_μ (k : ℕ) (μ : ℝ) : (lvl μin k).mstar * μ = (lvl μin k).mδ * μ + (lvl μin k).w μ := by
  simp only [Level.mstar, Level.w]
  ring

/-- The value `θ_2(R_0 + μ) = ρ̄_k + m_*μ + sι` that the proofs of (W4) and (T3) in `thm:onestep`
use, for `μ^in ∈ 𝔉` of length at least `k + 2`: `θ_2(R_0 + μ) = ρ^f_{τ_2}(R_0 + μ) + u_2(R_0 + μ)`
with `u_2(R_0 + μ) = u^0` (`lem:closedforms`(b)) and
`ρ^f_{τ_2}(R_0 + μ) = μm_δ + ρ̄_k + w − u^0 + sι` (`lem:closedforms`(c)), and `m_δμ + w = m_*μ`. -/
lemma θ2_R0μ {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) :
    θ2 μin k (R0 + μT μin (k + 1)) =
      (lvl μin k).ρbar + (lvl μin k).mstar * μT μin (k + 1) + (lvl μin k).s * ι := by
  have hb := (closedforms_b k hF hK).2.2.1
  have hc := (closedforms_c k hF hK).1 (R0 + μT μin (k + 1))
  have hm := mstar_μ (μin := μin) k (μT μin (k + 1))
  unfold u2 at hb
  rw [hm]
  linarith

/-- **(Q1)** of the proof of `thm:onestep` (`stoc-sections/appD-hardness.tex:1324-1325`), for
`μ^in ∈ 𝔉` of length at least `k + 2`: by `lem:closedforms`(c),
`ρ^f_{τ_2}(α) = ρ̄_k + m_δ(α − R_0) + (1 − υ^0 + c_{τ_2})w` with `c_{τ_2} = sι/w`, and
`ρ^h_{τ_1} = ρ^f_{τ_2} − (φ − 1)w` (`ρ^f_{τ_2} = ρ^f_{τ_1} + φw` and
`ρ^h_{τ_1} = ρ^f_{τ_1} + w`). -/
lemma onestep_Q1 {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) (α : ℝ) :
    ρf μin k α none = (lvl μin k).ρbar + (lvl μin k).mδ * (α - R0) +
      (1 - υ0 μin k + (lvl μin k).s * ι / (lvl μin k).w (μT μin (k + 1))) *
        (lvl μin k).w (μT μin (k + 1)) ∧
    ρh μin k α (some none) = ρf μin k α none - (φ μin k - 1) * (lvl μin k).w (μT μin (k + 1)) := by
  have hμ : 0 < μT μin (k + 1) := μT_pos hF (by omega)
  have hw := (w_pos (μin := μin) hμ).ne'
  refine ⟨?_, ?_⟩
  · rw [(closedforms_c k hF hK).1 α, υ0]
    field_simp
    ring
  · rw [(D_bands (μin := μin) k α).2.2.2.2.1, ρf_τ₂_eq hμ]
    ring

/-- **(Q2)** of the proof of `thm:onestep` (`stoc-sections/appD-hardness.tex:1326-1331`): if the
marginals of level `k` at `R_0` lie in `[ρ̄_k − c, ρ̄_k]` (`c` the spread, `c_ww` in the paper) and
grow at most at the rate `L` (the slope bound, `M` in the paper), then, as they are nondecreasing
(`lem:fullplane`(c)), every `e ∈ E_k` has `ρ^{(k)}_e(α) ∈ [ρ̄_k − c, ρ̄_k + L(α − R_0)]` for
`α ≥ R_0` and `ρ^{(k)}_e(α) ∈ [ρ̄_k − c − L(R_0 − α), ρ̄_k]` for `α ≤ R_0`.

The spread and the slope bound are parameters, as the proof of `prop:level1` replaces them: "That
derivation uses the assumption `k ≥ 1` only through the spread and the slopes of the old marginals
at `R_0`, which these bounds replace." `thm:onestep` takes `L = M` by `lem:fullplane`(c)
(`ρT_rate`), `prop:level1` takes `L = 12` from the first table of `prop:base` (`base_slopes`). -/
lemma onestep_Q2 {k : ℕ} {c L : ℝ}
    (hR0 : ∀ e, (lvl μin k).ρbar - c ≤ ρT μin k R0 e ∧ ρT μin k R0 e ≤ (lvl μin k).ρbar)
    (hL : ∀ e, GrowsAtMost (fun α => ρT μin k α e) L) (e : Gr k) (α : ℝ) :
    (R0 ≤ α → (lvl μin k).ρbar - c ≤ ρT μin k α e ∧
      ρT μin k α e ≤ (lvl μin k).ρbar + L * (α - R0)) ∧
    (α ≤ R0 → (lvl μin k).ρbar - c - L * (R0 - α) ≤ ρT μin k α e ∧
      ρT μin k α e ≤ (lvl μin k).ρbar) := by
  have hmono := ρT_mono (μin := μin) k e
  obtain ⟨h1, h2⟩ := hR0 e
  refine ⟨fun hα => ⟨h1.trans (hmono hα), ?_⟩, fun hα => ⟨?_, (hmono hα).trans h2⟩⟩
  · have := hL e R0 (α - R0) (sub_nonneg.2 hα)
    simp only [add_sub_cancel] at this
    linarith
  · have := hL e α (R0 - α) (sub_nonneg.2 hα)
    simp only [add_sub_cancel] at this
    linarith

/-- (W3) and the inequalities `ρ^h_{τ_1} < ρ^f_e < ρ^f_{τ_2}` of (T2) in the proof of `thm:onestep`
(`stoc-sections/appD-hardness.tex:1365-1373`), before the numbers, for `μ^in ∈ 𝔉` of length at
least `k + 2`, with the spread `c` and the slope bound `L ≥ m_δ` of (Q2): for `e ∈ E_k` and
`α ∈ [R_0, R_0 + μ]`, (Q1) and (Q2) give `ρ^{(k)}_e − ρ^h_{τ_1} ≥ (φ + υ^0 − 2)w − sι − c − m_δμ`
(the paper's `(φ + υ^0 − 2 − c_{τ_2} − c_w)w − m_δμ`) and
`ρ^f_{τ_2} − ρ^{(k)}_e ≥ (1 − υ^0)w − (L − m_δ)μ` (the paper's `(1 − υ^0)w − (M − m_δ)μ`). -/
lemma onestep_W3T2 {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) {c L : ℝ}
    (hR0 : ∀ e, (lvl μin k).ρbar - c ≤ ρT μin k R0 e ∧ ρT μin k R0 e ≤ (lvl μin k).ρbar)
    (hL : ∀ e, GrowsAtMost (fun α => ρT μin k α e) L) (hLm : (lvl μin k).mδ ≤ L)
    {α : ℝ} (hα : α ∈ Set.Icc R0 (R0 + μT μin (k + 1))) (e : Gr k) :
    (φ μin k + υ0 μin k - 2) * (lvl μin k).w (μT μin (k + 1)) - (lvl μin k).s * ι - c -
        (lvl μin k).mδ * μT μin (k + 1) ≤ ρT μin k α e - ρh μin k α (some none) ∧
      (1 - υ0 μin k) * (lvl μin k).w (μT μin (k + 1)) - (L - (lvl μin k).mδ) * μT μin (k + 1) ≤
        ρf μin k α none - ρT μin k α e := by
  have hμ : 0 < μT μin (k + 1) := μT_pos hF (by omega)
  obtain ⟨q1, q1'⟩ := onestep_Q1 hF hK α
  obtain ⟨q2l, q2u⟩ := (onestep_Q2 (μin := μin) hR0 hL e α).1 hα.1
  have hw := (w_pos (μin := μin) hμ)
  have hs := (s_pos (μin := μin) k)
  have hι : (0 : ℝ) ≤ ι := by unfold ι; norm_num
  have hmδ := mδ_pos (μin := μin) k
  have hcτ₂ : (lvl μin k).s * ι / (lvl μin k).w (μT μin (k + 1)) *
      (lvl μin k).w (μT μin (k + 1)) = (lvl μin k).s * ι := div_mul_cancel₀ _ hw.ne'
  have h1 : (lvl μin k).mδ * (α - R0) ≤ (lvl μin k).mδ * μT μin (k + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hα.2]) hmδ.le
  have h2 : (L - (lvl μin k).mδ) * (α - R0) ≤ (L - (lvl μin k).mδ) * μT μin (k + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hα.2]) (by linarith)
  have hsι : 0 ≤ (lvl μin k).s * ι := mul_nonneg hs.le hι
  constructor <;> nlinarith

/-- The inequality `ρ^f_{τ_2} < ρ^h_{e'}` of (T2) in the proof of `thm:onestep`
(`stoc-sections/appD-hardness.tex:1374-1384`), before the numbers, for `μ^in ∈ 𝔉` of length at
least `k + 2`, with the spread `c` and the slope bound `L ≥ m_δ` of (Q2): for `e' ∈ E_k` and `α`
in the transition, `0 ≤ R_0 + μ − α ≤ μ − |𝓡|`, and (Q1) at `α` and (Q2) at `α − μ ≤ R_0` give
`ρ^h_{e'}(α) − ρ^f_{τ_2}(α) ≥ υ^0 w − sι − c − (L − m_δ)(μ − |𝓡|)` (the paper's
`(υ^0 − c_{τ_2} − c_w)w − (M − m_δ)(μ − |𝓡|)`). -/
lemma onestep_T2' {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) {c L : ℝ}
    (hR0 : ∀ e, (lvl μin k).ρbar - c ≤ ρT μin k R0 e ∧ ρT μin k R0 e ≤ (lvl μin k).ρbar)
    (hL : ∀ e, GrowsAtMost (fun α => ρT μin k α e) L) (hLm : (lvl μin k).mδ ≤ L)
    {α : ℝ} (hα : α ∈ Set.Icc (R1T μin k) (R0 + μT μin (k + 1))) (e : Gr k) :
    υ0 μin k * (lvl μin k).w (μT μin (k + 1)) - (lvl μin k).s * ι - c -
        (L - (lvl μin k).mδ) * (μT μin (k + 1) - lenR μin k) ≤
      ρh μin k α (some (some e)) - ρf μin k α none := by
  have hμ : 0 < μT μin (k + 1) := μT_pos hF (by omega)
  obtain ⟨q1, -⟩ := onestep_Q1 hF hK α
  obtain ⟨q2l, -⟩ :=
    (onestep_Q2 (μin := μin) hR0 hL e (α - μT μin (k + 1))).2 (by linarith [hα.2])
  have hh := (D_bands (μin := μin) k α).2.1 e
  have hm := mstar_μ (μin := μin) k (μT μin (k + 1))
  have hw := (w_pos (μin := μin) hμ)
  have hcτ₂ : (lvl μin k).s * ι / (lvl μin k).w (μT μin (k + 1)) *
      (lvl μin k).w (μT μin (k + 1)) = (lvl μin k).s * ι := div_mul_cancel₀ _ hw.ne'
  have hlen : R0 + μT μin (k + 1) - α ≤ μT μin (k + 1) - lenR μin k := by
    unfold lenR
    linarith [hα.1]
  have h2 : (L - (lvl μin k).mδ) * (R0 + μT μin (k + 1) - α) ≤
      (L - (lvl μin k).mδ) * (μT μin (k + 1) - lenR μin k) :=
    mul_le_mul_of_nonneg_left hlen (by linarith)
  rw [hh]
  nlinarith

/-- (W4) in the proof of `thm:onestep` (`stoc-sections/appD-hardness.tex:1402-1405`), before the
numbers, for `μ^in ∈ 𝔉` of length at least `k + 2`: if the marginals of level `k` at `R_0` are at
most `ρ̄_k` and grow at most at the rate `L` (the slope bound of (Q2), `M` in the paper), and
`m̄ > L`, then for `e ∈ E_k`, `θ_2 − ρ^h_e` increases, as `θ_2` has slope `m̄` and
`ρ^h_e(α) = ρ^{(k)}_e(α − μ) + m_*μ` grows at most at the rate `L`; at `R_0 + μ` it is at least
`ρ^f_{τ_2}(R_0 + μ) + u_2(R_0 + μ) − ρ̄_k − m_*μ = sι > 0`, by (Q1), (Q2), and
`u_2(R_0 + μ) = u^0` (`θ2_R0μ`). So (W4) holds. -/
lemma onestep_W4 {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) {L : ℝ}
    (hL : ∀ e, GrowsAtMost (fun α => ρT μin k α e) L) (hm : L < (lvl μin k).mbar)
    (hR0 : ∀ e, ρT μin k R0 e ≤ (lvl μin k).ρbar) :
    ∀ e, ∀ α ∈ Set.Icc (R0 + μT μin (k + 1)) (R1T μin k + μT μin (k + 1)),
      ρh μin k α (some (some e)) < θ2 μin k α := by
  intro e α hα
  have hs := (s_pos (μin := μin) k)
  have hι : (0 : ℝ) < ι := by unfold ι; norm_num
  -- "At `R_0 + μ` it is at least `ρ^f_{τ_2}(R_0 + μ) + u_2(R_0 + μ) − ρ̄_k − m_*μ = sι > 0`, by
  -- (Q1), (Q2), and `u_2(R_0 + μ) = u^0`." (`θ2_R0μ`)
  have h0 : ρh μin k (R0 + μT μin (k + 1)) (some (some e)) + (lvl μin k).s * ι ≤
      θ2 μin k (R0 + μT μin (k + 1)) := by
    rw [(D_bands (μin := μin) k _).2.1 e, add_sub_cancel_right, θ2_R0μ hF hK]
    linarith [hR0 e]
  -- "for `e ∈ E_k`, `θ_2 − ρ^h_e` increases, as `m̄ > M`."
  -- The Lean: `ρ^h_e(α) = ρ^{(k)}_e(α − μ) + m_*μ` grows at most at the rate `L < m̄`.
  have h1 : ρh μin k α (some (some e)) ≤ ρh μin k (R0 + μT μin (k + 1)) (some (some e)) +
      L * (α - (R0 + μT μin (k + 1))) := by
    have := hL e R0 (α - (R0 + μT μin (k + 1))) (sub_nonneg.2 hα.1)
    rw [show R0 + (α - (R0 + μT μin (k + 1))) = α - μT μin (k + 1) by ring] at this
    rw [(D_bands (μin := μin) k α).2.1 e, (D_bands (μin := μin) k _).2.1 e,
      add_sub_cancel_right]
    linarith
  have h2 : θ2 μin k α = θ2 μin k (R0 + μT μin (k + 1)) +
      (α - (R0 + μT μin (k + 1))) * (lvl μin k).mbar := by
    rw [θ2_eq, θ2_eq]
    ring
  have h3 := mul_le_mul_of_nonneg_left hm.le (sub_nonneg.2 hα.1)
  nlinarith [mul_pos hs hι]

/-- (T3) in the proof of `thm:onestep` (`stoc-sections/appD-hardness.tex:1406-1411`), before the
specific element, for `μ^in ∈ 𝔉` of length at least `k + 2`: if `ρ^{(k)}_{e_l}(R_0) = ρ̄_k` and
`ρ^h_{e_l}` has slope at most `m_δ` on `[R_0 + μ − ι, R_0 + μ]`, then `θ_2 − ρ^h_{e_l}` has slope at
least `s = m̄ − m_δ` there, it is `sι` at `R_0 + μ` (as for (W4)), so it is at most `0` at
`R_0 + μ − ι`. -/
lemma onestep_T3 {K k : ℕ} (hF : InF μin K) (hK : k + 2 ≤ K) {el : Gr k}
    (hR0 : ρT μin k R0 el = (lvl μin k).ρbar)
    (hslope : ρh μin k (R0 + μT μin (k + 1)) (some (some el)) -
        ρh μin k (R0 + μT μin (k + 1) - ι) (some (some el)) ≤ (lvl μin k).mδ * ι) :
    θ2 μin k (R0 + μT μin (k + 1) - ι) ≤ ρh μin k (R0 + μT μin (k + 1) - ι) (some (some el)) := by
  -- "At `R_0 + μ` it is `sι`, as for (W4) and since `ρ^{f_k}_{τ_{2,k}}(R_0) = ρ̄_k`."
  -- The Lean: for `e_l` with `ρ^{(k)}_{e_l}(R_0) = ρ̄_k` (`hR0`) in place of `τ_{2,k}`.
  have h0 : θ2 μin k (R0 + μT μin (k + 1)) - ρh μin k (R0 + μT μin (k + 1)) (some (some el)) =
      (lvl μin k).s * ι := by
    rw [(D_bands (μin := μin) k _).2.1 el, add_sub_cancel_right, θ2_R0μ hF hK, hR0]
    ring
  -- "… so `θ_2 − ρ^h_{τ_{2,k}}` has slope at least `s`."
  -- The Lean: `θ_2 − ρ^h_{e_l}`, with the slope of `ρ^h_{e_l}` at most `m_δ` (`hslope`).
  have h1 : θ2 μin k (R0 + μT μin (k + 1)) - θ2 μin k (R0 + μT μin (k + 1) - ι) =
      (lvl μin k).mbar * ι := by
    rw [θ2_eq, θ2_eq]
    ring
  have hsm : (lvl μin k).mbar * ι = (lvl μin k).mδ * ι + (lvl μin k).s * ι := by
    rw [show (lvl μin k).mbar = (lvl μin k).mδ + (lvl μin k).s from rfl]
    ring
  -- "So it is at most `0` at `R_0 + μ − ι`."
  linarith

/-! ### `prop:level1` -/

/-- The data of the step `0 → 1`, the first paragraph of the proof of `prop:level1`
(`stoc-sections/appD-hardness.tex:1428-1434`): `M = 12`, `m_δ = 6`, `m_* = 774`, `1/β_δ = 3/4`,
`1/β_b = 9`, `Δ_b = 2490`, `m_b = 2496`, and `s = 29880/13 ∈ (2298.46, 2298.47)`, and
`∑_{e∈E_0} (m_* − m_e)/β_e = 769 + 762/4 + 770/4 = 1152`; so `d̄ = 2`, `w = 768μ`,
`m_*μ = 774μ`, `Π = μ(769 − 1143 + 385) = 11μ`, and `a_0 = (4/3)(q_0 − 11)μ = −(16/3)μ`; and
`|𝓡_0| = 2/5`. -/
lemma level1_data (h0 : 0 < μin 0) (hμ : 0 < μT μin 1) :
    (lvl μin 0).M = 12 ∧ (lvl μin 0).mδ = 6 ∧ (lvl μin 0).mstar = 774 ∧
    1 / (lvl μin 0).βδ = 3 / 4 ∧ 1 / (lvl μin 0).βb = 9 ∧ (lvl μin 0).Δb = 2490 ∧
    (lvl μin 0).mb = 2496 ∧ (lvl μin 0).s = 29880 / 13 ∧
    (lvl μin 0).s ∈ Set.Ioo 2298.46 2298.47 ∧
    ∑ c, ((lvl μin 0).mstar - (lvl μin 0).m c) / (lvl μin 0).β c = 1152 ∧
    (lvl μin 0).dbar (μT μin 1) = 2 ∧ (lvl μin 0).w (μT μin 1) = 768 * μT μin 1 ∧
    (lvl μin 0).mstar * μT μin 1 = 774 * μT μin 1 ∧
    (lvl μin 0).Pcal (μT μin 1) = 11 * μT μin 1 ∧ (lvl μin 0).a0 (μT μin 1) = -(16 / 3) * μT μin 1 ∧
    lenR μin 0 = 2 / 5 := by
  have hM : (lvl μin 0).M = 12 := rfl
  have hmδ : (lvl μin 0).mδ = 6 := by simp only [Level.mδ, hM]; norm_num
  have hms : (lvl μin 0).mstar = 774 := by simp only [Level.mstar, hmδ, hM]; norm_num
  have hβ : (lvl μin 0).βδ = 4 / 3 := by
    simp only [Level.βδ, lvl_k]
    norm_num
  have hΔ : (lvl μin 0).Δb = 2490 := by simp only [Level.Δb, hM]; norm_num
  have hs : (lvl μin 0).s = 29880 / 13 := by simp only [Level.s, hΔ]; norm_num
  have hm : ∀ c, (lvl μin 0).m c = Base.m c := fun c => rfl
  have hβc : ∀ c, (lvl μin 0).β c = Base.β c := fun c => rfl
  have hsum : ∑ c, ((lvl μin 0).mstar - (lvl μin 0).m c) / (lvl μin 0).β c = 1152 := by
    simp only [hms, hm, hβc]
    show ∑ c : Fin 3, (774 - Base.m c) / Base.β c = 1152
    rw [Fin.sum_univ_three]
    simp [Base.m, Base.β]
    norm_num
  have hw : (lvl μin 0).w (μT μin 1) = 768 * μT μin 1 := by
    simp only [Level.w, hM]; ring
  have hdE : (lvl μin 0).dEk (μT μin 1) = 1152 * μT μin 1 := by
    simp only [Level.dEk, Level.d]
    rw [← hsum, sum_mul]
    exact sum_congr rfl fun c _ => by ring
  have hPi : (lvl μin 0).Pcal (μT μin 1) = 11 * μT μin 1 := by
    simp only [Level.Pcal, Level.d, hmδ, hms, hm, hβc]
    show ∑ c : Fin 3, (6 - Base.m c) * (μT μin 1 * (774 - Base.m c) / Base.β c) = _
    rw [Fin.sum_univ_three]
    simp [Base.m, Base.β]
    ring
  refine ⟨hM, hmδ, hms, by rw [hβ]; norm_num, by unfold Level.βb; rw [hβ]; norm_num, hΔ,
    by simp only [Level.mb, hmδ, hΔ]; norm_num, hs, by rw [hs]; constructor <;> norm_num, hsum,
    ?_, hw, by rw [hms], hPi, ?_, ?_⟩
  · simp only [Level.dbar, hdE, hw, hβ]
    field_simp
    norm_num
  · simp only [Level.a0, hPi, hβ]
    show 4 / 3 * (q₀ * μT μin 1 - 11 * μT μin 1) = _
    unfold q₀
    ring
  · rw [lenR_eq, sum_range_one, μT_zero h0]
    norm_num

variable (μin) in
/-- The number `c := s − 1920 − 8/3735` of the proof of `prop:level1`, with `s` of the step
`0 → 1`. -/
def cLevel1 : ℝ := (lvl μin 0).s - 1920 - 8 / 3735

/-- The numbers of the step `0 → 1`, the rest of the first paragraph of the proof of
`prop:level1` (`stoc-sections/appD-hardness.tex:1434-1442`): (d2) by `lem:inputs`,
`μ ∈ (80/33, 44/15)`, so `w > 1861`; (d3) by (P6) and `lem:closedforms`(a),
`u^0 = s(μ − 1/5) − (5/2)w − 16μ/(3·2490) = cμ − s/5`, where `c := s − 1920 − 8/3735 ∈
(378.45, 378.46)` (`cLevel1`), and `φ_1 = 3 + (16μ/3)/(sw) = 3 + 1/(144s)`; (d4) so
`φ_1 ∈ (3, 3.000004)`, and `υ^0_1 = u^0/w = c/768 − s/(3840μ)` increases with `μ` and lies in
`(0.2458, 0.2888)`. -/
lemma level1_numbers {K : ℕ} (hF : InF μin K) (hK : 2 ≤ K) :
    μT μin 1 ∈ Set.Ioo (80 / 33) (44 / 15) ∧ 1861 < (lvl μin 0).w (μT μin 1) ∧
    (lvl μin 0).u0 (μT μin 1) (R1T μin 0) = (lvl μin 0).s * (μT μin 1 - 1 / 5) -
      5 / 2 * (lvl μin 0).w (μT μin 1) - 16 * μT μin 1 / (3 * 2490) ∧
    (lvl μin 0).u0 (μT μin 1) (R1T μin 0) = cLevel1 μin * μT μin 1 - (lvl μin 0).s / 5 ∧
    cLevel1 μin ∈ Set.Ioo 378.45 378.46 ∧
    φ μin 0 = 3 + 16 * μT μin 1 / 3 / ((lvl μin 0).s * (lvl μin 0).w (μT μin 1)) ∧
    φ μin 0 = 3 + 1 / (144 * (lvl μin 0).s) ∧
    υ0 μin 0 = cLevel1 μin / 768 - (lvl μin 0).s / (3840 * μT μin 1) ∧
    φ μin 0 ∈ Set.Ioo 3 3.000004 ∧ υ0 μin 0 ∈ Set.Ioo 0.2458 0.2888 := by
  have h0 := μin0_pos hF
  have hμ : 0 < μT μin 1 := μT_pos hF (by omega)
  obtain ⟨-, -, -, -, -, hΔ, -, hs, -, -, hdbar, hw, -, -, ha0, hlen⟩ := level1_data h0 hμ
  have hcL : cLevel1 μin = 29880 / 13 - 1920 - 8 / 3735 := by rw [cLevel1, hs]
  -- (d2) "By `lem:inputs`, `μ ∈ (80/33, 44/15)`, so `w > 1861`, and `|𝓡_0| = 2/5`."
  -- (`|𝓡_0| = 2/5` is `level1_data`.)
  have hμr := (inputs hF hK).1
  have hw1861 : 1861 < (lvl μin 0).w (μT μin 1) := by
    rw [hw]
    linarith [hμr.1]
  -- (d3) "By (P6) and `lem:closedforms`(a), `u^0 = s(μ − 1/5) − (5/2)w − 16μ/(3·2490) = cμ − s/5`,
  -- where `c := s − 1920 − 8/3735 ∈ (378.45, 378.46)`, and
  -- `φ_1 = 3 + (16μ/3)/(sw) = 3 + 1/(144s)`."
  have hR1 : R1T μin 0 - R0 = 2 / 5 := hlen
  have hu0' : (lvl μin 0).u0 (μT μin 1) (R1T μin 0) = (lvl μin 0).s * (μT μin 1 - 1 / 5) -
      5 / 2 * (lvl μin 0).w (μT μin 1) - 16 * μT μin 1 / (3 * 2490) := by
    simp only [Level.u0, Level.a2, hdbar, ha0, hR1, Level.s, hΔ]
    ring
  have hu0 : (lvl μin 0).u0 (μT μin 1) (R1T μin 0) =
      cLevel1 μin * μT μin 1 - (lvl μin 0).s / 5 := by
    rw [hu0', hcL, hw, hs]
    ring
  have hc : cLevel1 μin ∈ Set.Ioo 378.45 378.46 := by
    rw [hcL]
    constructor <;> norm_num
  have hφ' : φ μin 0 = 3 + 16 * μT μin 1 / 3 / ((lvl μin 0).s * (lvl μin 0).w (μT μin 1)) := by
    rw [(closedforms_a 0 hF (by omega)).2, hdbar, ha0]
    ring
  have hφ : φ μin 0 = 3 + 1 / (144 * (lvl μin 0).s) := by
    rw [hφ', hw]
    have := hμ.ne'
    have : (lvl μin 0).s ≠ 0 := by rw [hs]; norm_num
    field_simp
    ring
  -- (d4) "So `φ_1 ∈ (3, 3.000004)`, and `υ^0_1 = u^0/w = c/768 − s/(3840μ)` increases with `μ`
  -- and lies in `(0.2458, 0.2888)`."
  have hυ : υ0 μin 0 = cLevel1 μin / 768 - (lvl μin 0).s / (3840 * μT μin 1) := by
    rw [υ0, hu0, hw]
    field_simp
    ring
  have hυmono : ∀ μ₁ μ₂ : ℝ, 0 < μ₁ → μ₁ < μ₂ →
      cLevel1 μin / 768 - (lvl μin 0).s / (3840 * μ₁) <
        cLevel1 μin / 768 - (lvl μin 0).s / (3840 * μ₂) := by
    intro μ₁ μ₂ h1 h12
    have : (lvl μin 0).s / (3840 * μ₂) < (lvl μin 0).s / (3840 * μ₁) :=
      div_lt_div_of_pos_left (by rw [hs]; norm_num) (by positivity) (by linarith)
    linarith
  refine ⟨hμr, hw1861, hu0', hu0, hc, hφ', hφ, hυ, ?_, ?_⟩
  · rw [hφ, hs]
    constructor <;> norm_num
  · rw [hυ]
    constructor
    · refine lt_trans ?_ (hυmono (80 / 33) _ (by norm_num) hμr.1)
      rw [hcL, hs]
      norm_num
    · refine lt_trans (hυmono _ (44 / 15) hμ hμr.2) ?_
      rw [hcL, hs]
      norm_num

/-- The base marginals grow at most at the rate `12` (not in the paper: the proof of `prop:level1`
reads "their slopes are at most `12`" off the first table of `prop:base`). On each of the five
pieces of the table, the marginals are the row there (`Base.base`), affine with the slopes
`(5, 12, 4)`, `(5, 8, 8)`, `(5, 12, 4)`, `(32/5, 32/5, 4)` and `(5, 12, 4)`, so `α ↦ 12α − ρ_e(α)`
is nondecreasing on each piece; the pieces cover `ℝ` and meet at their end points. -/
lemma base_slopes (e : Fin 3) : GrowsAtMost (fun α => rho Base.f₀ Base.m Base.β α e) 12 := by
  obtain ⟨-, -, ⟨r₁, r₂, r₃, r₄, r₅⟩, -⟩ := Base.base
  have hz₁ : ζ₁ = 1 / 3 := rfl
  have hz₂ : ζ₂ = 2 / 3 := rfl
  -- the slopes of the five rows are at most `12`
  have s₁ : ∀ x y : ℝ, x ≤ y → Base.row₁ y e - Base.row₁ x e ≤ 12 * (y - x) := by
    intro x y h
    fin_cases e <;> simp [Base.row₁] <;> linarith
  have s₂ : ∀ x y : ℝ, x ≤ y → Base.row₂ y e - Base.row₂ x e ≤ 12 * (y - x) := by
    intro x y h
    fin_cases e <;> simp [Base.row₂] <;> linarith
  have s₃ : ∀ x y : ℝ, x ≤ y → Base.row₃ y e - Base.row₃ x e ≤ 12 * (y - x) := by
    intro x y h
    fin_cases e <;> simp [Base.row₃] <;> linarith
  have s₄ : ∀ x y : ℝ, x ≤ y → Base.row₄ y e - Base.row₄ x e ≤ 12 * (y - x) := by
    intro x y h
    fin_cases e <;> simp [Base.row₄] <;> linarith
  have s₅ : ∀ x y : ℝ, x ≤ y → Base.row₅ y e - Base.row₅ x e ≤ 12 * (y - x) := by
    intro x y h
    fin_cases e <;> simp [Base.row₅] <;> linarith
  -- so `α ↦ 12α − ρ_e(α)` is nondecreasing on each piece
  have hpiece : ∀ (ρ : ℝ → Fin 3 → ℝ) (s : Set ℝ),
      (∀ α ∈ s, rho Base.f₀ Base.m Base.β α e = ρ α e) →
      (∀ x y : ℝ, x ≤ y → ρ y e - ρ x e ≤ 12 * (y - x)) →
      MonotoneOn (fun α => 12 * α - rho Base.f₀ Base.m Base.β α e) s :=
    fun ρ s hs hρ x hx y hy hxy => by
      simp only [hs x hx, hs y hy]
      linarith [hρ x y hxy]
  have p₁ := hpiece Base.row₁ (Set.Iic (-1 / 6)) (fun α h => (r₁ α h).1 e) s₁
  have p₂ := hpiece Base.row₂ (Set.Icc (-1 / 6) ζ₁) (fun α h => (r₂ α h.1 h.2).1 e) s₂
  have p₃ := hpiece Base.row₃ (Set.Icc ζ₁ (3 / 7)) (fun α h => (r₃ α h.1 h.2).1 e) s₃
  have p₄ := hpiece Base.row₄ (Set.Icc (3 / 7) ζ₂) (fun α h => (r₄ α h.1 h.2).1 e) s₄
  have p₅ := hpiece Base.row₅ (Set.Ici ζ₂) (fun α h => (r₅ α h).1 e) s₅
  -- the pieces cover `ℝ` and meet at their end points
  have p₄₅ := p₄.union_right p₅ (isGreatest_Icc (by rw [hz₂]; norm_num)) isLeast_Ici
  rw [Set.Icc_union_Ici_eq_Ici (by rw [hz₂]; norm_num)] at p₄₅
  have p₃₅ := p₃.union_right p₄₅ (isGreatest_Icc (by rw [hz₁]; norm_num)) isLeast_Ici
  rw [Set.Icc_union_Ici_eq_Ici (by rw [hz₁]; norm_num)] at p₃₅
  have p₂₅ := p₂.union_right p₃₅ (isGreatest_Icc (by rw [hz₁]; norm_num)) isLeast_Ici
  rw [Set.Icc_union_Ici_eq_Ici (by rw [hz₁]; norm_num)] at p₂₅
  have hmono := p₁.Iic_union_Ici p₂₅
  intro α Δ hΔ
  have := hmono (show α ≤ α + Δ by linarith)
  simp only at this
  linarith

/-- The second paragraph of the proof of `prop:level1`, before the bullets
(`stoc-sections/appD-hardness.tex:1444-1451`): (h0) "To check the hypotheses, we use `sι < 22.99`,
`R_0 = 3/10`, `R_1 = 7/10`, `s|𝓡_0| < 919.4`, `s/5 < 459.70`, and `m_δμ = (M − m_δ)μ = w/128`"; (h1)
"By the first table of `prop:base` and (B3), the base marginals at `R_0` lie in
`[2/5, 7/6] = [ρ̄_0 − 23/30, ρ̄_0]`, and their slopes are at most `12`" (`base_slopes`), so (Q1) and
(Q2) of the proof of `thm:onestep` hold with `k = 0`, `c_ww = 23/30`, `c_{τ_2}w = sι` and the slope
bound `12` (`onestep_Q2`): "That derivation uses the assumption `k ≥ 1` only through the
spread and the slopes of the old marginals at `R_0`, which these bounds replace." -/
lemma level1_spread (h0 : 0 < μin 0) :
    (lvl μin 0).s * ι < 22.99 ∧ R0 = 3 / 10 ∧ R1T μin 0 = 7 / 10 ∧
    (lvl μin 0).s * lenR μin 0 < 919.4 ∧ (lvl μin 0).s / 5 < 459.70 ∧
    (∀ μ, (lvl μin 0).mδ * μ = (lvl μin 0).w μ / 128 ∧
      ((lvl μin 0).M - (lvl μin 0).mδ) * μ = (lvl μin 0).w μ / 128) ∧
    (∀ e, (lvl μin 0).ρbar - 23 / 30 ≤ ρT μin 0 R0 e ∧ ρT μin 0 R0 e ≤ (lvl μin 0).ρbar) ∧
    ∀ e, GrowsAtMost (fun α => ρT μin 0 α e) 12 := by
  obtain ⟨-, -, -, -, -, ⟨-, ⟨hC0, hC1, hC2⟩, -⟩⟩ := Base.base
  have hs : (lvl μin 0).s = 29880 / 13 := by
    show 12 / 13 * (415 / 2 * 12) = _
    norm_num
  have hlen : lenR μin 0 = 2 / 5 := by
    rw [lenR_eq, sum_range_one, μT_zero h0]
    norm_num
  have hR1 : R1T μin 0 = 7 / 10 := by
    have := R0_eq
    unfold lenR at hlen
    linarith
  refine ⟨?_, R0_eq, hR1, ?_, ?_, fun μ => ⟨?_, ?_⟩, fun e => ?_, fun e => base_slopes e⟩
  · rw [hs]
    unfold ι
    norm_num
  · rw [hs, hlen]
    norm_num
  · rw [hs]
    norm_num
  · show 12 / 2 * μ = 64 * 12 * μ / 128
    ring
  · show (12 - 12 / 2) * μ = 64 * 12 * μ / 128
    ring
  · show 7 / 6 - 23 / 30 ≤ rho Base.f₀ Base.m Base.β R0 e ∧
      rho Base.f₀ Base.m Base.β R0 e ≤ 7 / 6
    change Fin 3 at e
    fin_cases e
    · rw [show ((⟨0, by norm_num⟩ : Fin 3)) = 0 from rfl, hC0]; norm_num
    · rw [show ((⟨1, by norm_num⟩ : Fin 3)) = 1 from rfl, hC1]; norm_num
    · rw [show ((⟨2, by norm_num⟩ : Fin 3)) = 2 from rfl, hC2]; norm_num

/-- **`prop:level1`** (Proposition C.22, `stoc-sections/appD-hardness.tex:1420-1425`, proof lines
1427-1490): let `μ^in ∈ 𝔉` have length at least `2`. Then `φ_1 ∈ (3, 3.000004)` and
`υ^0_1 ∈ (0.2458, 0.2888)`, and the hypotheses of `lem:onelevel` and those of `thm:transition` with
`(e_t, e_l) = (C_0, C_0)` hold at the step `0 → 1` (`φ_1 = φ μin 0`, `υ^0_1 = υ0 μin 0`, `C_0 = 0`).

The proof's steps, in the paper's two paragraphs and its bullets: the first paragraph, "We have
`M = 12`, …" (`level1_data`, `level1_numbers`): the numbers of the step, `u^0 = cμ − s/5`,
`φ_1 = 3 + 1/(144s)` and the ranges of `φ_1` and `υ^0_1`; the second paragraph, "To check the
hypotheses, we use …" (`level1_spread`): by the first table of `prop:base` and (B3), the spread
`23/30` of the base marginals at `R_0` and their slope bound `12` (`base_slopes`), so (Q1) and (Q2)
with `k = 0`, `c_ww = 23/30`, `c_{τ_2}w = sι` and the slope bound `12`; then the bullets in the
paper's order: (T1); (W1); (W2); (W3) and (T2), with the bounds `> 2200`, `> 0.7w` and `> 421` (by
`onestep_W3T2` and `onestep_T2'`, "as in the proof of `thm:onestep`") and (B3); (W4) and (T3)
(`onestep_W4`, `onestep_T3`); (W5) and (W6). -/
theorem level1 {K : ℕ} (hF : InF μin K) (hK : 2 ≤ K) :
    φ μin 0 ∈ Set.Ioo 3 3.000004 ∧ υ0 μin 0 ∈ Set.Ioo 0.2458 0.2888 ∧
    OneLevelHyp μin 0 ∧ TransitionHyp μin 0 (0 : Fin 3) (0 : Fin 3) := by
  have h0 := μin0_pos hF
  have hμ : 0 < μT μin 1 := μT_pos hF (by omega)
  have hwpos := w_pos (μin := μin) hμ
  -- "We have `M = 12`, `m_δ = 6`, `m_* = 774`, …" (the first paragraph)
  obtain ⟨hM, hmδ, -, hβ, hβb, hΔ, hmb, hs, -, -, -, hw, -, -, -, hlen⟩ := level1_data h0 hμ
  obtain ⟨⟨hμ1, hμ2⟩, hw1861, -, hu0, hc, -, -, -, hφr, hυr⟩ := level1_numbers hF hK
  -- "To check the hypotheses, we use `sι < 22.99`, …" (the second paragraph: the spread
  -- `hspread` and the slope bound `12` of the base marginals, `hslope`, for (Q1) and (Q2))
  obtain ⟨hsι, hR0, hR1, hsR, hs5, hdrift, hspread, hslope⟩ := level1_spread (μin := μin) h0
  have h12 : (lvl μin 0).mδ ≤ 12 := by rw [hmδ]; norm_num
  have hcb := closedforms_b 0 hF (by omega)
  have hu0w : (lvl μin 0).u0 (μT μin 1) (R1T μin 0) = υ0 μin 0 * (lvl μin 0).w (μT μin 1) := by
    rw [υ0, div_mul_cancel₀ _ hwpos.ne']
  obtain ⟨-, -, ⟨-, r₂, -, -, -⟩, -, -, ⟨hB3, ⟨hC0, -, -⟩, -⟩⟩ := Base.base
  have hρT : ∀ α (e : Gr 0), ρT μin 0 α e = rho Base.f₀ Base.m Base.β α e := fun α e => rfl
  -- (T1) "`ψ_1 = (9/13)·2490²` and `q_1 = 7 + ψ_1 < 4.3·10^6`."
  have hβδ : (lvl μin 0).βδ = 4 / 3 := by
    rw [← one_div_one_div (lvl μin 0).βδ, hβ]
    norm_num
  have hβ1 : ∀ o : Option (Option (Option (Fin 3))), 0 < βT μin 1 o :=
    fun o => (fpHyp_gT (μin := μin) 1).pos o
  have hψ1 : (lvl μin 0).ψ = 9 / 13 * 2490 ^ 2 := by
    simp only [Level.ψ, hΔ, hβδ]
    norm_num
  have hq1 : (lvl μin 1).q < 4.3 * 10 ^ 6 := by
    rw [q_succ, hψ1]
    show q₀ + _ < _
    unfold q₀
    norm_num
  -- "Taking `v = m_b` in the minimum form of `S_2`,
  -- `S_2({b, C_1, C_2}) ≤ (1/4)(2484² + 2492²) < 3.1·10^6 < ψ_1`."
  have hT1a : SS (mT μin (0 + 1)) (βT μin (0 + 1))
      (insert none (((univ : Finset (Fin 3)).erase 0).image fun c => some (some (some c)))) ≤
        (lvl μin 0).ψ := by
    show SS (fun o : Option (Option (Option (Fin 3))) => mT μin 1 o) (fun o => βT μin 1 o)
      (insert none (((univ : Finset (Fin 3)).erase 0).image fun c => some (some (some c)))) ≤
        (lvl μin 0).ψ
    refine (SS_le hβ1 _ (lvl μin 0).mb).trans ?_
    have hsum : ∑ o ∈ insert none (((univ : Finset (Fin 3)).erase 0).image
        fun c => some (some (some c))), (mT μin 1 o - (lvl μin 0).mb) ^ 2 / βT μin 1 o =
          1 / 4 * (2484 ^ 2 + 2492 ^ 2) := by
      rw [sum_insert, sum_image]
      · have he : (univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
        show ((lvl μin 0).mb - (lvl μin 0).mb) ^ 2 / (lvl μin 0).βb +
          ∑ c ∈ (univ : Finset (Fin 3)).erase 0, (Base.m c - (lvl μin 0).mb) ^ 2 / Base.β c = _
        rw [he, sum_pair (by decide), hmb]
        simp [Base.m, Base.β]
        norm_num
      · intro a _ b _ h
        exact Option.some.inj (Option.some.inj (Option.some.inj h))
      · intro h
        obtain ⟨c, -, hc⟩ := mem_image.1 h
        exact Option.some_ne_none _ hc
    have h31 : 1 / 4 * (2484 ^ 2 + 2492 ^ 2 : ℝ) < 3.1 * 10 ^ 6 := by norm_num
    have hψ31 : (3.1 : ℝ) * 10 ^ 6 < (lvl μin 0).ψ := by
      rw [hψ1]
      norm_num
    rw [hsum]
    linarith
  -- "Moreover, `S_2({b, C_0}) = 2491²/(β_b + 1) = (9/10)·2491² > 5.58·10^6 > q_1`."
  have hT1b : (lvl μin (0 + 1)).q ≤
      SS (mT μin (0 + 1)) (βT μin (0 + 1)) {none, some (some (some (0 : Fin 3)))} := by
    show (lvl μin 1).q ≤ SS (fun o : Option (Option (Option (Fin 3))) => mT μin 1 o)
      (fun o => βT μin 1 o) {none, some (some (some 0))}
    rw [SS_pair hβ1 (by simp)]
    show (lvl μin 1).q ≤ ((lvl μin 0).mb - Base.m 0) ^ 2 / ((lvl μin 0).βb + Base.β 0)
    have hpair : ((lvl μin 0).mb - Base.m 0) ^ 2 / ((lvl μin 0).βb + Base.β 0) =
        9 / 10 * 2491 ^ 2 := by
      have : (lvl μin 0).βb = 1 / 9 := by rw [← one_div_one_div (lvl μin 0).βb, hβb]
      rw [hmb, this]
      simp [Base.m, Base.β]
      norm_num
    have h558 : (5.58 : ℝ) * 10 ^ 6 < 9 / 10 * 2491 ^ 2 := by norm_num
    have h43 : (4.3 : ℝ) * 10 ^ 6 < 5.58 * 10 ^ 6 := by norm_num
    rw [hpair]
    linarith
  -- (W1) "`u_1(R_0) = (1/2)(w − s|𝓡_0|) > (1/2)(1861 − 919.4) > 470 > sι`, and
  -- `w − u_1(R_1) = u_1(R_0) > 470`."
  have hu1R0 : u1 μin 0 R0 =
      ((lvl μin 0).w (μT μin 1) - (lvl μin 0).s * lenR μin 0) / 2 := by
    rw [hcb.1]
    unfold lenR
    ring
  have h470 : 470 < u1 μin 0 R0 := by
    rw [hu1R0]
    linarith
  have hW1a : (lvl μin 0).s * ι < u1 μin 0 R0 := by linarith
  have hW1b : u1 μin 0 (R1T μin 0) < (lvl μin 0).w (μT μin 1) := by
    have : (lvl μin 0).w (μT μin 1) - u1 μin 0 (R1T μin 0) = u1 μin 0 R0 := by
      rw [hcb.1, hcb.1]
      ring
    linarith
  -- (W2) "`u_2(R_0 + μ) = u^0 > 0.2458w > 0`"
  have hW2a : 0 < u2 μin 0 (R0 + μT μin 1) := by
    rw [hcb.2.2.1, hu0w]
    have := mul_lt_mul_of_pos_right hυr.1 hwpos
    have : (0 : ℝ) < 0.2458 * (lvl μin 0).w (μT μin 1) := by positivity
    linarith
  -- "and `w − u_2(R_1 + μ) = w − u^0 − s|𝓡_0| = (768 − c)μ − s/5 > 389.54·80/33 − 459.70 > 484`."
  have hW2b : u2 μin 0 (R1T μin 0 + μT μin 1) < (lvl μin 0).w (μT μin 1) := by
    have e1 : (lvl μin 0).w (μT μin 1) - u2 μin 0 (R1T μin 0 + μT μin 1) =
        (lvl μin 0).w (μT μin 1) - (lvl μin 0).u0 (μT μin 1) (R1T μin 0) -
          (lvl μin 0).s * lenR μin 0 := by
      have := hcb.2.2.2.2.2 (R0 + μT μin 1) (R1T μin 0 + μT μin 1)
      rw [hcb.2.2.1] at this
      unfold lenR
      linarith
    have e2 : (lvl μin 0).w (μT μin 1) - (lvl μin 0).u0 (μT μin 1) (R1T μin 0) -
        (lvl μin 0).s * lenR μin 0 = (768 - cLevel1 μin) * μT μin 1 - (lvl μin 0).s / 5 := by
      rw [hu0, hw, hlen]
      ring
    have h1 : 389.54 * (80 / 33) < (768 - cLevel1 μin) * μT μin 1 :=
      mul_lt_mul'' (by linarith [hc.2]) hμ1 (by norm_num) (by norm_num)
    have : (484 : ℝ) < (768 - cLevel1 μin) * μT μin 1 - (lvl μin 0).s / 5 := by
      linarith
    linarith
  -- (W3) and (T2) "as in the proof of `thm:onestep`, on `[R_0, R_0 + μ]`,
  -- `ρ^{(0)}_e − ρ^h_{τ_1} ≥ (φ_1 + υ^0_1 − 2 − 1/128)w − sι − 23/30 > 1.2379·1861 − 23.76 > 2200`,
  -- `ρ^f_{τ_2} − ρ^{(0)}_e ≥ (1 − υ^0_1 − 1/128)w > 0.7w`."
  have hfirst : ∀ c α, α ∈ Set.Icc R0 (R0 + μT μin 1) →
      2200 < ρT μin 0 α c - ρh μin 0 α (some none) ∧
        0.7 * (lvl μin 0).w (μT μin 1) < ρf μin 0 α none - ρT μin 0 α c := by
    intro c α hα
    -- (Q1) and (Q2) with the spread `23/30` and the slope bound `12 = M`
    obtain ⟨w1, w2⟩ := onestep_W3T2 hF (by omega) hspread hslope h12 hα c
    rw [(hdrift _).1] at w1
    rw [← hM, (hdrift _).2] at w2
    have h1 : 1.2379 * 1861 <
        (φ μin 0 + υ0 μin 0 - 2 - 1 / 128) * (lvl μin 0).w (μT μin 1) :=
      mul_lt_mul'' (by linarith [hφr.1, hυr.1]) hw1861 (by norm_num) (by norm_num)
    have h2 : 0.7 * (lvl μin 0).w (μT μin 1) <
        (1 - υ0 μin 0 - 1 / 128) * (lvl μin 0).w (μT μin 1) :=
      mul_lt_mul_of_pos_right (by linarith [hυr.2]) hwpos
    constructor <;> linarith
  -- "On the transition, where the drift is `(M − m_δ)(μ − |𝓡_0|) = 6μ − 12/5`,
  -- `ρ^h_{e'} − ρ^f_{τ_2} ≥ u^0 − sι − 23/30 − 6μ + 12/5 = (c − 6)μ − s/5 − sι − 23/30 + 12/5
  -- > 372.45·80/33 − 459.70 − 22.99 − 0.77 + 2.4 > 421`."
  have hsecond : ∀ c' α, α ∈ Set.Icc (R1T μin 0) (R0 + μT μin 1) →
      421 < ρh μin 0 α (some (some c')) - ρf μin 0 α none := by
    intro c' α hα
    have t2 := onestep_T2' hF (by omega) hspread hslope h12 hα c'
    have hd : ((lvl μin 0).M - (lvl μin 0).mδ) * (μT μin 1 - lenR μin 0) =
        6 * μT μin 1 - 12 / 5 := by
      rw [hM, hmδ, hlen]
      ring
    rw [← hM] at t2
    have e : υ0 μin 0 * (lvl μin 0).w (μT μin 1) - (lvl μin 0).s * ι - 23 / 30 -
        (6 * μT μin 1 - 12 / 5) = (cLevel1 μin - 6) * μT μin 1 - (lvl μin 0).s / 5 -
          (lvl μin 0).s * ι - 23 / 30 + 12 / 5 := by
      rw [← hu0w, hu0]
      ring
    have h1 : 372.45 * (80 / 33) < (cLevel1 μin - 6) * μT μin 1 :=
      mul_lt_mul'' (by linarith [hc.1]) hμ1 (by norm_num) (by norm_num)
    rw [hd] at t2
    linarith
  -- "By (B3), `C_0` has the largest of the marginals `ρ^h_e`, `e ∈ E_0`, on the transition, as
  -- `α − μ ≥ R_1 − μ > 7/10 − 44/15 = −67/30 > −7/3` there."
  have hthird : ∀ c' α, α ∈ Set.Icc (R1T μin 0) (R0 + μT μin 1) →
      ρh μin 0 α (some (some c')) ≤ ρh μin 0 α (some (some (0 : Fin 3))) := by
    intro c' α hα
    rw [(D_bands (μin := μin) 0 α).2.1 c', (D_bands (μin := μin) 0 α).2.1 (0 : Fin 3),
      hρT _ c', hρT _ (0 : Fin 3)]
    have hlt : -7 / 3 < α - μT μin 1 := by rw [hR1] at hα; linarith [hα.1]
    have hle : α - μT μin 1 ≤ ζ₁ := by
      have : R0 < ζ₁ := by rw [hR0]; unfold ζ₁; norm_num
      linarith [hα.2]
    change Fin 3 at c'
    by_cases hc' : c' = 0
    · rw [hc']
    · linarith [hB3 _ hlt hle c' hc']
  have hRμ : R1T μin 0 < R0 + μT μin 1 := by rw [hR1, hR0]; linarith
  have hW3 : ∀ c, ∀ α ∈ Set.Icc R0 (R1T μin 0), ρh μin 0 α (some none) < ρT μin 0 α c :=
    fun c α hα => by linarith [(hfirst c α ⟨hα.1, hα.2.trans hRμ.le⟩).1]
  have hT2 : ∀ α ∈ Set.Icc (R1T μin 0) (R0 + μT μin (0 + 1)), ∀ c c' : Gr 0,
      ρh μin 0 α (some none) < ρf μin 0 α (some (some c)) ∧
        ρf μin 0 α (some (some c)) < ρf μin 0 α none ∧
        ρf μin 0 α none < ρh μin 0 α (some (some c')) ∧
        ρh μin 0 α (some (some c')) ≤ ρh μin 0 α (some (some (0 : Fin 3))) := by
    intro α hα c c'
    have hα' : α ∈ Set.Icc R0 (R0 + μT μin 1) :=
      ⟨by linarith [hα.1, R0_lt_R1T (μin := μin) 0], hα.2⟩
    obtain ⟨n1, n2⟩ := hfirst c α hα'
    have n3 := hsecond c' α hα
    have hfc := (D_bands (μin := μin) 0 α).1 c
    refine ⟨by rw [hfc]; linarith, by rw [hfc]; linarith, by linarith, hthird c' α hα⟩
  -- (W4) and (T3) "as in the proof of `thm:onestep`. Here `ρ̄_0` is the largest base marginal at
  -- `R_0` by (B3), and the marginal `ρ^h_{C_0}(α) = 5(α − μ) − 1/3 + m_*μ` on `(−∞, R_0 + μ]` has
  -- slope `5 < m_δ`."
  -- (W4) with the slope bound `12 < m̄` of the base marginals (`hslope`) and (B3) (`hspread`)
  have hW4 := onestep_W4 hF (by omega) hslope (by simp only [Level.mbar, hmδ, hs]; norm_num)
    fun e => (hspread e).2
  have hT3 : θ2 μin 0 (R0 + μT μin 1 - ι) ≤
      ρh μin 0 (R0 + μT μin 1 - ι) (some (some (0 : Fin 3))) := by
    have hι : ι = 1 / 100 := rfl
    refine onestep_T3 hF (by omega) hC0 ?_
    rw [(D_bands (μin := μin) 0 _).2.1 (0 : Fin 3), (D_bands (μin := μin) 0 _).2.1 (0 : Fin 3),
      hρT _ (0 : Fin 3), hρT _ (0 : Fin 3), hmδ]
    have e1 : R0 + μT μin (0 + 1) - μT μin (0 + 1) = R0 := by ring
    have e2 : R0 + μT μin (0 + 1) - ι - μT μin (0 + 1) = R0 - ι := by ring
    rw [e1, e2]
    obtain ⟨h1, -⟩ := r₂ R0 (by rw [hR0]; norm_num) (by rw [hR0]; unfold ζ₁; norm_num)
    obtain ⟨h2, -⟩ := r₂ (R0 - ι) (by rw [hR0, hι]; norm_num)
      (by rw [hR0, hι]; unfold ζ₁; norm_num)
    rw [h1, h2]
    simp [Base.row₂]
    rw [hι]
    linarith
  -- (W5) "`φ_1 > 3`."
  have hW5 : 1 < φ μin 0 := by linarith [hφr.1]
  -- (W6) "`β⁻¹(E ∪ {b}) = 3/2 + 3/2 + 9 = 12`, so `t_b/β⁻¹(E ∪ {b}) = 9·2496/12 = 1872 > 12`."
  have hW6 : (lvl μin 0).M < cfast μin 0 := by
    have hE0 : ∑ c : Fin 3, 1 / βT μin 0 c = 3 / 2 := by
      show ∑ c : Fin 3, 1 / Base.β c = 3 / 2
      rw [Fin.sum_univ_three]
      simp [Base.β]
      norm_num
    have hτ₁τ₂ : 1 / βT μin 1 (some none) + 1 / βT μin 1 (some (some none)) = 3 / 2 := by
      show 1 / (lvl μin 0).βδ + 1 / (lvl μin 0).βδ = 3 / 2
      rw [hβ]
      norm_num
    have hS : ∑ o, 1 / βT μin 1 o = 3 / 2 + 3 / 2 + 9 := by
      change ∑ o : Option (Option (Option (Fin 3))), 1 / βT μin 1 o = _
      rw [sum_three]
      change 1 / (lvl μin 0).βb + 1 / βT μin 1 (some none) + 1 / βT μin 1 (some (some none)) +
        ∑ c : Fin 3, 1 / βT μin 0 c = _
      rw [hβb]
      linarith
    have ht : cfast μin 0 = 9 * 2496 / 12 := by
      show (lvl μin 0).mb / (lvl μin 0).βb / ∑ o, 1 / βT μin 1 o = _
      rw [hS, hmb, div_eq_mul_one_div _ (lvl μin 0).βb, hβb]
      norm_num
    rw [ht, hM]
    norm_num
  exact ⟨hφr, hυr, ⟨hW1a, hW1b, hW2a, hW2b, hW3, hW4, hW5, hW6⟩,
    ⟨hT1a, hT1b, fun h => absurd rfl h, hT2, hT3⟩⟩

/-! ### `thm:onestep` -/

variable (μin) in
/-- `M̂ = M_{k−1}/M` at level `k = j + 1` (the first paragraph of the proof of `thm:onestep`). -/
def Mhat (j : ℕ) : ℝ := (lvl μin j).M / (lvl μin (j + 1)).M

variable (μin) in
/-- `c_{τ_2} = sι/w`, the margin of (P6) relative to `w`, at the step `k → k + 1` (the proof of
`thm:onestep`). -/
def cτ₂ (k : ℕ) : ℝ := (lvl μin k).s * ι / (lvl μin k).w (μT μin (k + 1))

variable (μin) in
/-- `c_w = φ_k w_k/w`, the width of level `k = j + 1` at `R_0` relative to `w`, at the step
`k → k + 1` (the proof of `thm:onestep`). -/
def cw (j : ℕ) : ℝ :=
  φ μin j * (lvl μin j).w (μT μin (j + 1)) / (lvl μin (j + 1)).w (μT μin (j + 2))

/-- The numbers of a step in the first paragraph of the proof of `thm:onestep`
(`stoc-sections/appD-hardness.tex:1296-1301`), for `k = j + 1`: "The numbers of a step grow from
level to level. We first write them in terms of `M := M_k`, `ϖ := ϖ_k`, and the band width `w`, so
that the same computation works at every level `k ≥ 1`." With `m_o := m_δ^{(k)} = (1/2)M_{k−1}`,
let `M̂ := M_{k−1}/M = 1/208` (`lem:weights`(b)); by the parameter rule, `ϖ_{k+1} = 8ϖ`,
`m_δ = (1/2)M`, `m_* = (129/2)M`, `m_b = 208M`, `Δ_b = (415/2)M`, `s = (2490/13)M`, and
`m̄ = (4993/26)M`, so `m̄ − M = (4967/26)M > 191M`. -/
lemma onestep_rule (j : ℕ) :
    Mhat μin j = 1 / 208 ∧ (lvl μin j).mδ = (lvl μin j).M / 2 ∧
    1 / (lvl μin (j + 1)).βδ = 8 * ϖ μin (j + 1) ∧
    (lvl μin (j + 1)).mδ = (lvl μin (j + 1)).M / 2 ∧
    (lvl μin (j + 1)).mstar = 129 / 2 * (lvl μin (j + 1)).M ∧
    (lvl μin (j + 1)).mb = 208 * (lvl μin (j + 1)).M ∧
    (lvl μin (j + 1)).Δb = 415 / 2 * (lvl μin (j + 1)).M ∧
    (lvl μin (j + 1)).s = 2490 / 13 * (lvl μin (j + 1)).M ∧
    (lvl μin (j + 1)).mbar = 4993 / 26 * (lvl μin (j + 1)).M ∧
    (lvl μin (j + 1)).mbar - (lvl μin (j + 1)).M = 4967 / 26 * (lvl μin (j + 1)).M ∧
    191 * (lvl μin (j + 1)).M < (lvl μin (j + 1)).mbar - (lvl μin (j + 1)).M := by
  have hM := (weights_b (μin := μin)).2.1
  have hMpos := M_pos (μin := μin) (j + 1)
  have hmbar : (lvl μin (j + 1)).mbar = 4993 / 26 * (lvl μin (j + 1)).M := by
    simp only [Level.mbar, Level.mδ, Level.s, Level.Δb]
    ring
  -- "so `m̄ − M = (4967/26)M > 191M`"
  have h4967 : (lvl μin (j + 1)).mbar - (lvl μin (j + 1)).M =
      4967 / 26 * (lvl μin (j + 1)).M := by
    rw [hmbar]
    ring
  refine ⟨?_, rfl, inv_βδ_eq j, rfl, by simp only [Level.mstar, Level.mδ]; ring,
    by simp only [Level.mb, Level.mδ, Level.Δb]; ring, rfl,
    by simp only [Level.s, Level.Δb]; ring, hmbar, h4967, by rw [h4967]; linarith⟩
  -- "`M̂ := M_{k−1}/M = 1/208` (`lem:weights`(b))"
  rw [Mhat, hM, hM, pow_succ]
  field_simp

/-- The numbers of level `k = j + 1` that the proof of `thm:onestep` takes from the step
`k − 1 → k`: `φ_k ∈ (1, 3.0209)` and `υ^0_k < 0.5133`, by `prop:level1` for `k = 1` and by
`lem:weights`(d) at the step `k − 1 → k` for `k ≥ 2`. -/
lemma onestep_prev_numbers {j K : ℕ} (hF : InF μin K) (hK : j + 2 ≤ K) :
    1 < φ μin j ∧ φ μin j < 3.0209 ∧ υ0 μin j < 0.5133 := by
  rcases j with _ | j
  · obtain ⟨hφ, hυ, -, -⟩ := level1 hF hK
    exact ⟨by linarith [hφ.1], by linarith [hφ.2], by linarith [hυ.2]⟩
  · obtain ⟨-, -, -, hφ, -, -, hυ⟩ := weights_d hF hK
    exact ⟨by linarith [hφ.1], hφ.2, hυ.2⟩

/-- The quantities of the first paragraph of the proof of `thm:onestep`
(`stoc-sections/appD-hardness.tex:1301-1319`), for `k = j + 1`: the inputs enter through
`μ̂ = μ̂_k ∈ (5/44, 11/80)`, `ℓ̂ = ℓ̂_k < 0.158125`, and `1/μ < 33/640` (`lem:inputs`);
`w_k/w = M̂μ̂`; `ŝ = s/(64M) = 1245/416 ∈ (2.9927, 2.9928)`; and the three small quantities: the
margin of (P6) `c_{τ_2} = sι/w = ŝι/μ < 0.00155`, the width `c_w = φ_kw_k/w = φ_kM̂μ̂ < 0.00200`
(`onestep_prev_numbers`), and the drifts over one shift `m_δμ = (M − m_δ)μ = w/128`. -/
lemma onestep_small {j K : ℕ} (hF : InF μin K) (hK : j + 3 ≤ K) :
    μhat μin (j + 1) ∈ Set.Ioo (5 / 44) (11 / 80) ∧ ℓhat μin (j + 1) < 253 / 1600 ∧
    1 / μT μin (j + 2) < 33 / 640 ∧
    (lvl μin j).w (μT μin (j + 1)) / (lvl μin (j + 1)).w (μT μin (j + 2)) =
      Mhat μin j * μhat μin (j + 1) ∧
    shat μin (j + 1) ∈ Set.Ioo 2.9927 2.9928 ∧
    cτ₂ μin (j + 1) < 0.00155 ∧ cw μin j < 0.002 ∧
    (lvl μin (j + 1)).mδ * μT μin (j + 2) = (lvl μin (j + 1)).w (μT μin (j + 2)) / 128 ∧
    ((lvl μin (j + 1)).M - (lvl μin (j + 1)).mδ) * μT μin (j + 2) =
      (lvl μin (j + 1)).w (μT μin (j + 2)) / 128 := by
  obtain ⟨hMh, -, -, hmδ, -, -, -, -, -, -, -⟩ := onestep_rule (μin := μin) j
  -- "The inputs enter through `μ̂ := μ̂_k` and `ℓ̂ := ℓ̂_k` of `lem:inputs`, so
  -- `μ̂ ∈ (5/44, 11/80)`, `ℓ̂ < 0.158125`, and `1/μ < 33/640`."
  obtain ⟨-, hin, -, -, -⟩ := inputs hF (by omega)
  obtain ⟨hμh, hℓ, hμ⟩ := hin (j + 1) (by omega) (by omega)
  obtain ⟨-, hφ2, -⟩ := onestep_prev_numbers (μin := μin) (j := j) hF (by omega)
  have hμpos : 0 < μT μin (j + 2) := μT_pos hF (by omega)
  have hμk : 0 < μT μin (j + 1) := μT_pos hF (by omega)
  have hM := M_pos (μin := μin) (j + 1)
  have hw : (lvl μin (j + 1)).w (μT μin (j + 2)) = 64 * (lvl μin (j + 1)).M * μT μin (j + 2) :=
    rfl
  have hwk : (lvl μin j).w (μT μin (j + 1)) = 64 * (lvl μin j).M * μT μin (j + 1) := rfl
  -- "We use `w = 64Mμ` and `w_k = 64M̂Mμ_k`, so `w_k/w = M̂μ̂`."
  have hratio : (lvl μin j).w (μT μin (j + 1)) / (lvl μin (j + 1)).w (μT μin (j + 2)) =
      Mhat μin j * μhat μin (j + 1) := by
    rw [hw, hwk, Mhat, μhat]
    field_simp
  -- "recall that `ŝ = s/(64M) = 1245/416 ∈ (2.9927, 2.9928)`"
  have hshat : shat μin (j + 1) ∈ Set.Ioo 2.9927 2.9928 := by
    rw [shat_eq]
    constructor <;> norm_num
  refine ⟨hμh, hℓ, hμ, hratio, hshat, ?_, ?_, ?_, ?_⟩
  · -- "The margin of (P6): `c_{τ_2} := sι/w = ŝι/μ < 0.00155`."
    have e : cτ₂ μin (j + 1) = shat μin (j + 1) * ι * (1 / μT μin (j + 2)) := by
      rw [cτ₂, shat, hw]
      field_simp
    have h1 : shat μin (j + 1) * (1 / μT μin (j + 2)) < 2.9928 * (33 / 640) :=
      mul_lt_mul'' hshat.2 hμ (by linarith [hshat.1]) (by positivity)
    rw [e]
    unfold ι
    nlinarith [h1]
  · -- "The width `c_w := φ_kw_k/w = φ_kM̂μ̂ < 0.00200` of level `k` at `R_0`, as
    -- `φ_1 < 3.000004` (`prop:level1`) and `φ_k < 3.0209` for `k ≥ 2` (`lem:weights`(d) at the
    -- step `k − 1 → k`)."
    -- The Lean: `φ_k < 3.0209` for every `k ≥ 1` (`onestep_prev_numbers`, from both sources).
    rw [cw, mul_div_assoc, hratio, hMh]
    have h1 : φ μin j * (1 / 208 * μhat μin (j + 1)) ≤ 3.0209 * (1 / 208 * (11 / 80)) :=
      mul_le_mul hφ2.le (by linarith [hμh.2]) (by linarith [hμh.1]) (by norm_num)
    linarith
  · -- "The drifts over one shift, `m_δμ = (M − m_δ)μ = w/128`."
    rw [hmδ, hw]
    ring
  · rw [hmδ, hw]
    ring

/-- The width of level `k = j + 1` at `R_0` (`stoc-sections/appD-hardness.tex:1315-1317`), for
`μ^in ∈ 𝔉` of length at least `k + 2`: "By `lem:onelevel`(c) for level `k`, the largest marginal
of level `k` at `R_0` is `ρ^{f_k}_{τ_{2,k}}(R_0) = ρ̄_k`, and the smallest is `θ_1`, which exceeds
`ρ^{f_k}_{τ_{1,k}}(R_0) = ρ̄_k − c_ww`, as `u_1(R_0) > 0` by (W1) at the step `k − 1 → k`" (with
`u_1 = θ_1 − ρ^f_{τ_1}` and `ρ^{f_k}_{τ_{2,k}} = ρ^{f_k}_{τ_{1,k}} + φ_kw_k`, `ρf_τ₂_eq`). -/
lemma onestep_width {j K : ℕ} (hF : InF μin K) (hK : j + 3 ≤ K) (hj : OneLevelHyp μin j)
    (c : Gr (j + 1)) :
    (lvl μin (j + 1)).ρbar - cw μin j * (lvl μin (j + 1)).w (μT μin (j + 2)) <
        ρT μin (j + 1) R0 c ∧ ρT μin (j + 1) R0 c ≤ (lvl μin (j + 1)).ρbar := by
  have hμ : 0 < μT μin (j + 2) := μT_pos hF (by omega)
  have hμj : 0 < μT μin (j + 1) := μT_pos hF (by omega)
  -- "By `lem:onelevel`(c) for level `k`, the largest marginal of level `k` at `R_0` is
  -- `ρ^{f_k}_{τ_{2,k}}(R_0) = ρ̄_k`, and the smallest is `θ_1`,"
  obtain ⟨hc, -, -⟩ := (onelevel_c hF (by omega) hj).1 R0
    ⟨le_rfl, (R0_lt_R1T (μin := μin) j).le⟩
  have hρbar : (lvl μin (j + 1)).ρbar = ρf μin j R0 none := (closedforms_c j hF (by omega)).2.1
  have hcw : cw μin j * (lvl μin (j + 1)).w (μT μin (j + 2)) =
      φ μin j * (lvl μin j).w (μT μin (j + 1)) := by
    rw [cw, div_mul_cancel₀ _ (w_pos hμ).ne']
  -- "which exceeds `ρ^{f_k}_{τ_{1,k}}(R_0) = ρ̄_k − c_ww`, as `u_1(R_0) > 0` by (W1) at the step
  -- `k − 1 → k`"
  have hu : 0 < u1 μin j R0 := by
    have := mul_pos (s_pos (μin := μin) j) (show (0 : ℝ) < ι by unfold ι; norm_num)
    linarith [hj.W1a]
  have hτ₁ := ρf_τ₂_eq (μin := μin) hμj R0
  unfold u1 at hu
  refine ⟨?_, by rw [hρbar]; exact (hc c).2⟩
  rw [hcw, hρbar]
  linarith [(hc c).1]

/-- The largest marginal of level `k − 1 = j` at `R_0` is `ρ̄_{k−1}`, for `μ^in ∈ 𝔉` of length at
least `k + 2`: by `lem:onelevel`(c) at the step `k − 2 → k − 1` (with `lem:closedforms`(c)), or by
(B3) of `prop:base` for `k = 1`. -/
lemma onestep_prev_max {j K : ℕ} (hF : InF μin K) (hK : j + 2 ≤ K)
    (hyp : ∀ i < j, OneLevelHyp μin i) (c : Gr j) :
    ρT μin j R0 c ≤ (lvl μin j).ρbar := by
  rcases j with _ | j
  · exact ((level1_spread (μin := μin) (μin0_pos hF)).2.2.2.2.2.2.1 c).2
  · have hj := hyp j (Nat.lt_succ_self j)
    obtain ⟨hc, -, -⟩ := (onelevel_c hF (by omega) hj).1 R0
      ⟨le_rfl, (R0_lt_R1T (μin := μin) j).le⟩
    rw [(closedforms_c j hF (by omega)).2.1]
    exact (hc c).2

/-- `s|𝓡|/w = ŝℓ̂` at the step `k → k + 1`, `k = j + 1` (the bullet (W1), (W2) of the proof of
`thm:onestep`, `stoc-sections/appD-hardness.tex:1357`; as `|𝓡|/μ = ℓ̂`). -/
lemma onestep_sℓ (j : ℕ) (hμ : 0 < μT μin (j + 2)) :
    (lvl μin (j + 1)).s * lenR μin (j + 1) =
      shat μin (j + 1) * ℓhat μin (j + 1) * (lvl μin (j + 1)).w (μT μin (j + 2)) := by
  have hM := (M_pos (μin := μin) (j + 1)).ne'
  rw [shat, show ℓhat μin (j + 1) = lenR μin (j + 1) / μT μin (j + 2) from rfl]
  simp only [Level.w]
  field_simp

/-- (W3) and the inequalities `ρ^h_{τ_1} < ρ^f_e < ρ^f_{τ_2}` of (T2) in the proof of `thm:onestep`,
with the numbers (`stoc-sections/appD-hardness.tex:1365-1373`): for `e ∈ E_k` and
`α ∈ [R_0, R_0 + μ]`, (Q1) and (Q2) give
`ρ^{(k)}_e − ρ^h_{τ_1} ≥ (φ + υ^0 − 2 − c_{τ_2} − c_w)w − m_δμ
> (2.9791 + 0.2354 − 2 − 0.00155 − 0.002 − 1/128)w > 1.2w` and
`ρ^f_{τ_2} − ρ^{(k)}_e ≥ (1 − υ^0)w − (M − m_δ)μ > (1 − 0.5133 − 1/128)w > 0.47w` (`k = j + 1`). -/
lemma onestep_W3T2_num {j K : ℕ} (hF : InF μin K) (hK : j + 3 ≤ K)
    (hyp : ∀ i ≤ j, OneLevelHyp μin i) {α : ℝ} (hα : α ∈ Set.Icc R0 (R0 + μT μin (j + 2)))
    (c : Gr (j + 1)) :
    1.2 * (lvl μin (j + 1)).w (μT μin (j + 2)) <
        ρT μin (j + 1) α c - ρh μin (j + 1) α (some none) ∧
      0.47 * (lvl μin (j + 1)).w (μT μin (j + 2)) <
        ρf μin (j + 1) α none - ρT μin (j + 1) α c := by
  have hμ : 0 < μT μin (j + 2) := μT_pos hF (by omega)
  obtain ⟨-, -, -, -, -, hcτ₂, hcw, hd1, hd2⟩ := onestep_small hF hK
  obtain ⟨-, -, -, hφ, -, -, hυ⟩ := weights_d (j := j) hF (by omega)
  have hw := w_pos (μin := μin) (k := j + 1) hμ
  have hsι : (lvl μin (j + 1)).s * ι = cτ₂ μin (j + 1) * (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    rw [cτ₂, div_mul_cancel₀ _ hw.ne']
  -- (Q1) and (Q2) with the spread of `onestep_width` and the rate `M` of `lem:fullplane`(c)
  obtain ⟨w1, w2⟩ := onestep_W3T2 hF (by omega) (fun e => ⟨(onestep_width hF hK (hyp j le_rfl)
    e).1.le, (onestep_width hF hK (hyp j le_rfl) e).2⟩) (fun e => (ρT_rate (j + 1) e).2)
    (mδ_lt_M (j + 1)).le hα c
  have h1 := mul_le_mul_of_nonneg_right (show 2.9791 + 0.2354 - 2 ≤
    φ μin (j + 1) + υ0 μin (j + 1) - 2 by linarith [hφ.1, hυ.1]) hw.le
  have h2 := mul_le_mul_of_nonneg_right hcτ₂.le hw.le
  have h3 := mul_le_mul_of_nonneg_right hcw.le hw.le
  have h4 := mul_le_mul_of_nonneg_right (show 1 - 0.5133 ≤ 1 - υ0 μin (j + 1) by
    linarith [hυ.2]) hw.le
  constructor <;> linarith

/-- The inequality `ρ^f_{τ_2} < ρ^h_{e'}` of (T2) in the proof of `thm:onestep`, with the numbers
(`stoc-sections/appD-hardness.tex:1374-1384`): for `e' ∈ E_k` and `α` in the transition,
`ρ^h_{e'}(α) − ρ^f_{τ_2}(α) ≥ (υ^0 − c_{τ_2} − c_w)w − (M − m_δ)(μ − |𝓡|)
= (A − 1/128 − (2477/1664)ℓ̂ − c_{τ_2} − c_w)w > 0.225w` (`k = j + 1`). -/
lemma onestep_T2b {j K : ℕ} (hF : InF μin K) (hK : j + 3 ≤ K)
    (hyp : ∀ i ≤ j, OneLevelHyp μin i) {α : ℝ}
    (hα : α ∈ Set.Icc (R1T μin (j + 1)) (R0 + μT μin (j + 2))) (c' : Gr (j + 1)) :
    0.225 * (lvl μin (j + 1)).w (μT μin (j + 2)) <
      ρh μin (j + 1) α (some (some c')) - ρf μin (j + 1) α none := by
  have hμ : 0 < μT μin (j + 2) := μT_pos hF (by omega)
  obtain ⟨-, -, -, hmδ, -, -, -, -, -, -, -⟩ := onestep_rule (μin := μin) j
  obtain ⟨-, hℓ, -, -, -, hcτ₂, hcw, -, -⟩ := onestep_small hF hK
  obtain ⟨-, -, -, -, hυA, hA, -⟩ := weights_d (j := j) hF (by omega)
  have hw := w_pos (μin := μin) (k := j + 1) hμ
  have hsι : (lvl μin (j + 1)).s * ι = cτ₂ μin (j + 1) * (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    rw [cτ₂, div_mul_cancel₀ _ hw.ne']
  -- (Q1) and (Q2) with the spread of `onestep_width` and the rate `M` of `lem:fullplane`(c)
  have t2 := onestep_T2' hF (by omega) (fun e => ⟨(onestep_width hF hK (hyp j le_rfl) e).1.le,
    (onestep_width hF hK (hyp j le_rfl) e).2⟩) (fun e => (ρT_rate (j + 1) e).2)
    (mδ_lt_M (j + 1)).le hα c'
  -- "`= (A − 1/128 − (2477/1664)ℓ̂ − c_{τ_2} − c_w)w`"
  have e : υ0 μin (j + 1) * (lvl μin (j + 1)).w (μT μin (j + 2)) - (lvl μin (j + 1)).s * ι -
      cw μin j * (lvl μin (j + 1)).w (μT μin (j + 2)) -
      ((lvl μin (j + 1)).M - (lvl μin (j + 1)).mδ) * (μT μin (j + 2) - lenR μin (j + 1)) =
      (Awt μin (j + 1) - 1 / 128 - 2477 / 1664 * ℓhat μin (j + 1) - cτ₂ μin (j + 1) - cw μin j) *
        (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    rw [hsι, hυA, hmδ, show ℓhat μin (j + 1) = lenR μin (j + 1) / μT μin (j + 2) from rfl]
    simp only [Level.w]
    field_simp
    ring
  -- "`> (0.4722 − 1/128 − 0.2354 − 0.00155 − 0.002)w > 0.225w`"
  have h1 := mul_le_mul_of_nonneg_right hA.1.le hw.le
  have h2 := mul_le_mul_of_nonneg_right hℓ.le hw.le
  have h3 := mul_le_mul_of_nonneg_right hcτ₂.le hw.le
  have h4 := mul_le_mul_of_nonneg_right hcw.le hw.le
  linarith

/-- The inequality `ρ^h_{e'} ≤ ρ^h_{e_l}` of (T2) in the proof of `thm:onestep`
(`stoc-sections/appD-hardness.tex:1385-1401`): for `α` in the transition, `τ_{2,k}` has the largest
of the marginals `ρ^h_e(α)`, `e ∈ E_k` (`k = j + 1`, `τ_{2,k} = some none`).

The step's sentences: (1) let `α' := α − μ`, so that `0 ≤ R_0 − α' < μ`; by `lem:leftwindows`(b) for
level `k`, `b_k` has the smallest marginal of level `k` at `α'`, and
`ρ^{(k)}_{τ_{1,k}} ≤ ρ^{h_k}_{τ_{1,k}} = ρ^{f_k}_{τ_{2,k}} − (φ_k − 1)w_k
< ρ^{f_k}_{τ_{2,k}} = ρ^{(k)}_{τ_{2,k}}`;
(2) `ρ^{(k)}_e(α') = ρ^{(k−1)}_e(α') ≤ ρ̄_{k−1}` for `e ∈ E_{k−1}` (`onestep_prev_max`);
(3) by `lem:closedforms`(c) at level `k`, `ρ̄_k − ρ̄_{k−1} ≥ (1 − υ^0_k)w_k` with `υ^0_k < 0.5133`
(`onestep_prev_numbers`); (4) `ρ^{f_k}_{τ_{2,k}}` has slope `m_o = M_{k−1}/2`, where
`(1/2)M_{k−1}μ = w_k/(128μ̂) < (11/160)w_k`; so
`ρ^{(k)}_{τ_{2,k}}(α') − ρ̄_{k−1} > (1 − 0.5133 − 11/160)w_k > 0.41w_k`, and `τ_{2,k}` has the
largest of the marginals `ρ^h_e(α) = ρ^{(k)}_e(α') + m_*μ`. -/
lemma onestep_T2c {j K : ℕ} (hF : InF μin K) (hK : j + 3 ≤ K) (hyp : ∀ i ≤ j, OneLevelHyp μin i)
    {α : ℝ} (hα : α ∈ Set.Icc (R1T μin (j + 1)) (R0 + μT μin (j + 2))) (c' : Gr (j + 1)) :
    ρh μin (j + 1) α (some (some c')) ≤ ρh μin (j + 1) α (some (some (some none))) := by
  have hj := hyp j le_rfl
  have hμk : 0 < μT μin (j + 1) := μT_pos hF (by omega)
  have hwk := w_pos (μin := μin) (k := j) hμk
  obtain ⟨⟨hμh, -⟩, -, -, -, -, -, -, -, -⟩ := onestep_small hF hK
  obtain ⟨hφ1, -, hυk⟩ := onestep_prev_numbers (μin := μin) (j := j) hF (by omega)
  -- (1) "… let `α` lie in the transition, and let `α' := α − μ`, so that `0 ≤ R_0 − α' < μ`."
  have hα'1 : α - μT μin (j + 2) ≤ R0 := by linarith [hα.2]
  have hα'2 : R0 - (α - μT μin (j + 2)) < μT μin (j + 2) := by
    linarith [hα.1, R0_lt_R1T (μin := μin) (j + 1)]
  rw [(D_bands (μin := μin) (j + 1) α).2.1 c', (D_bands (μin := μin) (j + 1) α).2.1 (some none)]
  suffices h : ρT μin (j + 1) (α - μT μin (j + 2)) c' ≤
      ρT μin (j + 1) (α - μT μin (j + 2)) (some none) by linarith
  -- "By `lem:leftwindows`(b) for level `k`, `b_k` has the smallest marginal of level `k` at `α'`"
  obtain ⟨hold, hτ₂, hb⟩ := leftwindows_b hF (by omega) hj _ hα'1
  -- (1) "and `ρ^{(k)}_{τ_{1,k}} ≤ ρ^{h_k}_{τ_{1,k}} = ρ^{f_k}_{τ_{2,k}} − (φ_k − 1)w_k
  -- < ρ^{f_k}_{τ_{2,k}} = ρ^{(k)}_{τ_{2,k}}`"
  have hτ₁ : ρT μin (j + 1) (α - μT μin (j + 2)) (some (some none)) ≤
      ρT μin (j + 1) (α - μT μin (j + 2)) (some none) := by
    rw [hτ₂, ρT_succ_med j _ (some none), med_eq_min_max (ρf_le_ρh j _ (some none))]
    refine (min_le_right _ _).trans ?_
    rw [(onestep_Q1 hF (by omega) _).2]
    have := mul_pos (sub_pos.2 hφ1) hwk
    linarith
  -- (2) "Moreover, `ρ^{(k)}_e(α') = ρ^{(k−1)}_e(α') ≤ ρ̄_{k−1}` for `e ∈ E_{k−1}`, as `ρ̄_{k−1}`
  -- is the largest marginal of level `k − 1` at `R_0` (`lem:onelevel`(c), or (B3) of `prop:base`
  -- for `k = 1`)." (`onestep_prev_max`, and `ρT_mono` for `α' ≤ R_0`)
  have hprev : ∀ c : Gr j, ρT μin (j + 1) (α - μT μin (j + 2)) (some (some (some c))) ≤
      (lvl μin j).ρbar := fun c => by
    rw [hold c]
    have h1 := ρT_mono (μin := μin) j c hα'1
    have h2 := onestep_prev_max hF (by omega) (fun i hi => hyp i hi.le) c
    linarith
  -- (3) "By `lem:closedforms`(c) at level `k`, `ρ̄_k − ρ̄_{k−1} ≥ (1 − υ^0_k)w_k`, where
  -- `υ^0_k < 0.5133` (`prop:level1` for `k = 1`, and `lem:weights`(d) at the step `k − 1 → k` for
  -- `k ≥ 2`)." (`onestep_prev_numbers`)
  have hc := closedforms_c j hF (by omega)
  have hρ : (lvl μin j).ρbar + (1 - υ0 μin j) * (lvl μin j).w (μT μin (j + 1)) ≤
      ρf μin j R0 none := by
    have hu : (lvl μin j).u0 (μT μin (j + 1)) (R1T μin j) =
        υ0 μin j * (lvl μin j).w (μT μin (j + 1)) := by
      rw [υ0, div_mul_cancel₀ _ hwk.ne']
    have := mul_nonneg (s_pos (μin := μin) j).le (show (0 : ℝ) ≤ ι by unfold ι; norm_num)
    rw [hc.2.2, hu]
    linarith
  -- (4) "The marginal `ρ^{f_k}_{τ_{2,k}}` has slope `m_o = (1/2)M_{k−1}`, where
  -- `(1/2)M_{k−1}μ = w_k/(128μ̂) < (11/160)w_k`."
  have hslope : ρf μin j (α - μT μin (j + 2)) none =
      ρf μin j R0 none - (lvl μin j).mδ * (R0 - (α - μT μin (j + 2))) := by
    rw [hc.1, hc.1]
    ring
  have hmo : (lvl μin j).mδ * μT μin (j + 2) < 11 / 160 * (lvl μin j).w (μT μin (j + 1)) := by
    have e : (lvl μin j).mδ * μT μin (j + 2) =
        (lvl μin j).w (μT μin (j + 1)) / (128 * μhat μin (j + 1)) := by
      simp only [Level.mδ, Level.w, μhat]
      field_simp
      ring
    have hμh0 : 0 < μhat μin (j + 1) := lt_trans (by norm_num) hμh
    rw [e, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right hμh hwk]
  have hmo' : (lvl μin j).mδ * (R0 - (α - μT μin (j + 2))) ≤ (lvl μin j).mδ * μT μin (j + 2) :=
    mul_le_mul_of_nonneg_left hα'2.le (mδ_pos (μin := μin) j).le
  -- "So `ρ^{(k)}_{τ_{2,k}}(α') − ρ̄_{k−1} > (1 − 0.5133 − 11/160)w_k > 0.41w_k`, …"
  have hτ₂bar : (lvl μin j).ρbar + 0.41 * (lvl μin j).w (μT μin (j + 1)) <
      ρT μin (j + 1) (α - μT μin (j + 2)) (some none) := by
    have := mul_le_mul_of_nonneg_right (show 1 - 0.5133 ≤ 1 - υ0 μin j by linarith) hwk.le
    rw [hτ₂, hslope]
    linarith
  -- "… and `τ_{2,k}` has the largest of the marginals `ρ^h_e(α)`, `e ∈ E_k`." With
  -- `ρ^h_e(α) = ρ^{(k)}_e(α') + m_*μ`: `b_k` by (1) ("`b_k` has the smallest marginal of level `k`
  -- at `α'`"), `τ_{1,k}` by (1), the old elements by (2) and the last estimate.
  change Option (Option (Option (Gr j))) at c'
  rcases c' with _ | _ | _ | c
  · exact hb (some none)
  · exact le_rfl
  · exact hτ₁
  · linarith [hprev c]

/-- (T3) in the proof of `thm:onestep` (`stoc-sections/appD-hardness.tex:1406-1411`) with
`e_l = τ_{2,k}`: on `(−∞, R_0 + μ]`, `ρ^h_{τ_{2,k}}(α) = ρ^{f_k}_{τ_{2,k}}(α − μ) + m_*μ`
(`lem:leftwindows`(b)) has slope `m_o ≤ m_δ`, and `ρ^{f_k}_{τ_{2,k}}(R_0) = ρ̄_k`
(`lem:closedforms`(c)), so `onestep_T3` applies (`k = j + 1`). -/
lemma onestep_T3τ₂ {j K : ℕ} (hF : InF μin K) (hK : j + 3 ≤ K) (hyp : ∀ i ≤ j, OneLevelHyp μin i) :
    θ2 μin (j + 1) (R0 + μT μin (j + 2) - ι) ≤
      ρh μin (j + 1) (R0 + μT μin (j + 2) - ι) (some (some (some none))) := by
  have hj := hyp j le_rfl
  have hι : (0 : ℝ) < ι := by unfold ι; norm_num
  obtain ⟨hMh, hmδo, -, hmδ, -, -, -, -, -, -, -⟩ := onestep_rule (μin := μin) j
  have hM := M_pos (μin := μin) (j + 1)
  have hlw := leftwindows_b hF (by omega) hj
  refine onestep_T3 (k := j + 1) (el := some none) hF (by omega) ?_ ?_
  · -- "since `ρ^{f_k}_{τ_{2,k}}(R_0) = ρ̄_k`"
    rw [(hlw R0 le_rfl).2.1, (closedforms_c j hF (by omega)).2.1]
  · -- "`ρ^h_{τ_{2,k}}(α) = ρ^{f_k}_{τ_{2,k}}(α − μ) + m_*μ` (`lem:leftwindows`(b)) has slope
    -- `m_o ≤ m_δ`"
    rw [(D_bands (μin := μin) (j + 1) _).2.1 (some none),
      (D_bands (μin := μin) (j + 1) _).2.1 (some none)]
    have e1 : R0 + μT μin (j + 1 + 1) - μT μin (j + 1 + 1) = R0 := by ring
    have e2 : R0 + μT μin (j + 1 + 1) - ι - μT μin (j + 1 + 1) = R0 - ι := by ring
    rw [e1, e2, (hlw R0 le_rfl).2.1, (hlw (R0 - ι) (by linarith)).2.1,
      (closedforms_c j hF (by omega)).1, (closedforms_c j hF (by omega)).1]
    have hMj : (lvl μin j).M = (lvl μin (j + 1)).M / 208 := by
      have h := hMh
      rw [Mhat, div_eq_iff hM.ne'] at h
      linarith
    have h1 : (lvl μin j).mδ ≤ (lvl μin (j + 1)).mδ := by
      rw [hmδo, hmδ, hMj]
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hι.le
    linarith

/-- (T1) of the proof of `thm:onestep`, first part (`stoc-sections/appD-hardness.tex:1336-1342`):
`ψ_{k+1} = (12/13)Δ_b²/β_δ = (96/13)ϖΔ_b²`, and by `lem:weights`(a), `β⁻¹(E_k ∖ {b_k}) = 4ϖ`;
taking `v = m_b` in the minimum form of `S_2`, as all rewards of `E_k` lie in `(0, m_b)`,
`S_2((E_k ∖ {b_k}) ∪ {b}) ≤ β⁻¹(E_k ∖ {b_k})m_b² = 4ϖ((416/415)Δ_b)² < 4.02ϖΔ_b² < ψ_{k+1}`
(`k = j + 1`, `b_k = none`). -/
lemma onestep_T1a (j : ℕ) :
    SS (mT μin (j + 2)) (βT μin (j + 2))
      (insert none (((univ : Finset (Gr (j + 1))).erase none).image
        fun c => some (some (some c)))) ≤ (lvl μin (j + 1)).ψ := by
  obtain ⟨-, -, hβ, -, -, hmb, hΔ, -, -, -, -⟩ := onestep_rule (μin := μin) j
  have hβ2 : ∀ o : Option (Option (Option (Gr (j + 1)))), 0 < βT μin (j + 2) o :=
    fun o => (fpHyp_gT (μin := μin) (j + 2)).pos o
  have hβ1 : ∀ c, 0 < βT μin (j + 1) c := (fpHyp_gT (μin := μin) (j + 1)).pos
  have hM := M_pos (μin := μin) (j + 1)
  have hϖ := ϖ_pos (μin := μin) (j + 1)
  -- "`ψ_{k+1} = (12/13)Δ_b²/β_δ = (96/13)ϖΔ_b²`"
  have hψ : (lvl μin (j + 1)).ψ = 96 / 13 * ϖ μin (j + 1) * (lvl μin (j + 1)).Δb ^ 2 := by
    simp only [Level.ψ]
    rw [div_eq_mul_one_div _ (lvl μin (j + 1)).βδ, hβ]
    ring
  -- "By `lem:weights`(a), `β⁻¹(E_k ∖ {b_k}) = 4ϖ`."
  have hE : ∑ c ∈ (univ : Finset (Gr (j + 1))).erase none, 1 / βT μin (j + 1) c =
      4 * ϖ μin (j + 1) := by
    have h : ∑ c ∈ (univ : Finset (Option (Option (Option (Gr j))))).erase none,
        1 / βT μin (j + 1) c = ∑ e : Option (Option (Gr j)), 1 / βT μin (j + 1) (some e) := by
      rw [sum_erase_eq_sub (mem_univ _), Fintype.sum_option]
      ring
    exact h.trans ((weights_a (μin := μin)).2.2.2 j)
  -- "Taking `v = m_b` in the minimum form of `S_2`, as all rewards of `E_k` lie in
  -- `(0, m_b)`, `S_2((E_k ∖ {b_k}) ∪ {b}) ≤ β⁻¹(E_k ∖ {b_k})m_b²`"
  show SS (fun o : Option (Option (Option (Gr (j + 1)))) => mT μin (j + 2) o)
    (fun o => βT μin (j + 2) o) (insert none (((univ : Finset (Gr (j + 1))).erase none).image
      fun c => some (some (some c)))) ≤ _
  refine (SS_le hβ2 _ (lvl μin (j + 1)).mb).trans ?_
  rw [sum_insert, sum_image]
  · show ((lvl μin (j + 1)).mb - (lvl μin (j + 1)).mb) ^ 2 / (lvl μin (j + 1)).βb +
      ∑ c ∈ (univ : Finset (Gr (j + 1))).erase none,
        (mT μin (j + 1) c - (lvl μin (j + 1)).mb) ^ 2 / βT μin (j + 1) c ≤ _
    rw [sub_self, zero_pow two_ne_zero, zero_div, zero_add]
    have hterm : ∀ c ∈ (univ : Finset (Gr (j + 1))).erase none,
        (mT μin (j + 1) c - (lvl μin (j + 1)).mb) ^ 2 / βT μin (j + 1) c ≤
          (lvl μin (j + 1)).mb ^ 2 * (1 / βT μin (j + 1) c) := fun c _ => by
      have h1 := mT_pos (μin := μin) (j + 1) c
      have h2 := mT_le_M (μin := μin) (j + 1) c
      rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ (hβ1 c).le
      rw [hmb]
      nlinarith
    -- "`= 4ϖ((416/415)Δ_b)² < 4.02ϖΔ_b² < ψ_{k+1}`"
    have hmbΔ : (lvl μin (j + 1)).mb = 416 / 415 * (lvl μin (j + 1)).Δb := by
      rw [hmb, hΔ]
      ring
    have hΔ0 : 0 < (lvl μin (j + 1)).Δb := by rw [hΔ]; positivity
    refine le_of_lt ?_
    calc _ ≤ ∑ c ∈ (univ : Finset (Gr (j + 1))).erase none,
          (lvl μin (j + 1)).mb ^ 2 * (1 / βT μin (j + 1) c) := sum_le_sum hterm
      _ = 4 * ϖ μin (j + 1) * (416 / 415 * (lvl μin (j + 1)).Δb) ^ 2 := by
        rw [← mul_sum, hE, hmbΔ]
        ring
      _ < 4.02 * ϖ μin (j + 1) * (lvl μin (j + 1)).Δb ^ 2 := by
        have := mul_pos hϖ (pow_pos hΔ0 2)
        nlinarith
      _ ≤ (lvl μin (j + 1)).ψ := by
        rw [hψ]
        have := mul_pos hϖ (pow_pos hΔ0 2)
        nlinarith
  · intro a _ b _ h
    exact Option.some.inj (Option.some.inj (Option.some.inj h))
  · intro h
    obtain ⟨c, -, hc⟩ := mem_image.1 h
    exact Option.some_ne_none _ hc

/-- (T1) of the proof of `thm:onestep`, second part (`stoc-sections/appD-hardness.tex:1343-1349`):
by the formula for `S_2` of a pair (`eq:B-pair`) and by `lem:weights`(c),
`S_2({b, b_k}) = (m_b − M)²/(β_b + β_{b_k}) = (32/3)ϖ(207M)² = 457056ϖM²` and
`q_{k+1} = q_k + ψ_{k+1} ≤ ϖM² + (96/13)(415/2)²ϖM² < 317955ϖM²` (`k = j + 1`). -/
lemma onestep_T1b (j : ℕ) :
    (lvl μin (j + 2)).q ≤
      SS (mT μin (j + 2)) (βT μin (j + 2)) {none, some (some (some (none : Gr (j + 1))))} := by
  obtain ⟨-, -, hβ, -, -, hmb, hΔ, -, -, -, -⟩ := onestep_rule (μin := μin) j
  have hβ2 : ∀ o : Option (Option (Option (Gr (j + 1)))), 0 < βT μin (j + 2) o :=
    fun o => (fpHyp_gT (μin := μin) (j + 2)).pos o
  have hM := M_pos (μin := μin) (j + 1)
  have hϖ := ϖ_pos (μin := μin) (j + 1)
  obtain ⟨-, hq⟩ := (weights_c (μin := μin)).2 j
  have hβk1 : (lvl μin (j + 1)).βδ = 1 / (8 * ϖ μin (j + 1)) := by
    rw [← hβ, one_div_one_div]
  -- `β_b = β_δ/12 = 1/(96ϖ)` and `β_{b_k} = β_δ^{(k)}/12 = 1/(12ϖ)` (P2)
  have hβb : (lvl μin (j + 1)).βb = 1 / (96 * ϖ μin (j + 1)) := by
    rw [Level.βb, hβk1]
    field_simp
    ring
  have hβbk : (lvl μin j).βb = 1 / (12 * ϖ μin (j + 1)) := by
    have : (lvl μin j).βδ = 1 / ϖ μin (j + 1) := by
      show (lvl μin j).βδ = 1 / (1 / (lvl μin j).βδ)
      rw [one_div_one_div]
    rw [Level.βb, this]
    field_simp
  -- "Next, by the formula for `S_2` of a pair and by `lem:weights`(c), …" (`SS_pair`, `weights_c`)
  set x : Option (Option (Option (Gr (j + 1)))) := some (some (some none)) with hx
  show (lvl μin (j + 1)).q + (lvl μin (j + 1)).ψ ≤
    SS (fun o : Option (Option (Option (Gr (j + 1)))) => mT μin (j + 2) o)
      (fun o => βT μin (j + 2) o) {none, x}
  rw [SS_pair hβ2 (show none ≠ x by simp [hx])]
  -- "`S_2({b, b_k}) = (m_b − M)²/(β_b + β_{b_k}) = (32/3)ϖ(207M)² = 457056ϖM²`"
  show _ ≤ ((lvl μin (j + 1)).mb - mT μin (j + 1) none) ^ 2 /
    ((lvl μin (j + 1)).βb + (lvl μin j).βb)
  rw [(weights_b (μin := μin)).2.2.2 j]
  have hSS : ((lvl μin (j + 1)).mb - (lvl μin (j + 1)).M) ^ 2 /
      ((lvl μin (j + 1)).βb + (lvl μin j).βb) =
      457056 * ϖ μin (j + 1) * (lvl μin (j + 1)).M ^ 2 := by
    rw [hmb, hβb, hβbk]
    field_simp
    ring
  -- "`q_{k+1} = q_k + ψ_{k+1} ≤ ϖM² + (96/13)(415/2)²ϖM² < 317955ϖM²`"
  have hψ : (lvl μin (j + 1)).ψ = 96 / 13 * (415 / 2) ^ 2 * ϖ μin (j + 1) *
      (lvl μin (j + 1)).M ^ 2 := by
    simp only [Level.ψ]
    rw [hΔ, hβk1]
    field_simp
    ring
  rw [hSS, hψ]
  have := mul_pos hϖ (pow_pos hM 2)
  nlinarith

/-- (T1) of the proof of `thm:onestep`, third part (`stoc-sections/appD-hardness.tex:1350-1356`): we
decompose `S_2` into the groups `{b, τ_2}`, with `β⁻¹({b, τ_2}) = 104ϖ` and mean `m̄`, and
`{τ_{2,k}}`, with `β⁻¹({τ_{2,k}}) = ϖ` and mean `m_o` (the decomposition `eq:B-twogroups`,
`SS_union`, with `S_2({b, τ_2}) = ψ_{k+1}`); as `m̄ − m_o ≥ m̄ − M > 191M` (`m_o ≤ M` by
`lem:weights`(b), and `m̄ − M > 191M` from the first paragraph of the proof, `onestep_rule`) and
`q_k ≤ ϖM²`, `S_2({b, τ_2, τ_{2,k}}) = ψ_{k+1} + (104/105)ϖ(m̄ − m_o)² > ψ_{k+1} + ϖM² ≥ q_{k+1}`
(`k = j + 1`, `τ_{2,k} = some none`). -/
lemma onestep_T1c (j : ℕ) :
    (lvl μin (j + 2)).q ≤ SS (mT μin (j + 2)) (βT μin (j + 2))
      {none, some none, some (some (some (some none : Gr (j + 1))))} := by
  obtain ⟨-, -, hβ, -, -, -, -, -, -, -, h191⟩ := onestep_rule (μin := μin) j
  have H := stepD_hyp (μin := μin) (j + 1)
  have hβ2 : ∀ o : Option (Option (Option (Gr (j + 1)))), 0 < βT μin (j + 2) o :=
    fun o => (fpHyp_gT (μin := μin) (j + 2)).pos o
  have hM := M_pos (μin := μin) (j + 1)
  have hϖ := ϖ_pos (μin := μin) (j + 1)
  obtain ⟨-, hq⟩ := (weights_c (μin := μin)).2 j
  set x : Option (Option (Option (Gr (j + 1)))) := some (some (some (some none))) with hx
  have hU : ({none, some none, x} : Finset (Option (Option (Option (Gr (j + 1)))))) =
      {none, some none} ∪ {x} := by
    ext o
    simp only [mem_insert, mem_union, mem_singleton, or_assoc]
  -- "Finally, we decompose `S_2` into the groups `{b, τ_2}`, with `β⁻¹({b, τ_2}) = 104ϖ` and mean
  -- `m̄`, and `{τ_{2,k}}`, with `β⁻¹({τ_{2,k}}) = ϖ` and mean `m_o`."
  show (lvl μin (j + 1)).q + (lvl μin (j + 1)).ψ ≤
    SS (fun o : Option (Option (Option (Gr (j + 1)))) => mT μin (j + 2) o)
      (fun o => βT μin (j + 2) o) {none, some none, x}
  rw [hU, SS_union hβ2 (disjoint_singleton_right.2 (by simp [hx])) (insert_nonempty _ _)
    (singleton_nonempty _)]
  -- the group `{b, τ_2}`: `S_2({b, τ_2}) = ψ_{k+1}`, mean `m̄`, `β⁻¹({b, τ_2}) = 104ϖ`
  have h1 : SS (fun o : Option (Option (Option (Gr (j + 1)))) => mT μin (j + 2) o)
      (fun o => βT μin (j + 2) o) {none, some none} = (lvl μin (j + 1)).ψ := by
    rw [← stepD_ψ]
    exact StepData.SS_block_τ₂ H
  have h2 : mbar (fun o : Option (Option (Option (Gr (j + 1)))) => mT μin (j + 2) o)
      (fun o => βT μin (j + 2) o) {none, some none} = (lvl μin (j + 1)).mbar := by
    rw [← stepD_mbar]
    exact StepData.mbar_block_τ₂ H
  have h3 : ∑ o ∈ ({none, some none} : Finset (Option (Option (Option (Gr (j + 1)))))),
      1 / βT μin (j + 2) o = 104 * ϖ μin (j + 1) := by
    rw [show ∑ o ∈ ({none, some none} : Finset (Option (Option (Option (Gr (j + 1)))))),
      1 / βT μin (j + 2) o = 13 / (stepD μin (j + 1)).βδ from (StepData.block_τ₂_sums H).1,
      div_eq_mul_one_div, stepD_βδ, hβ]
    ring
  -- the group `{τ_{2,k}}`: `S_2({τ_{2,k}}) = 0`, mean `m_o`, `β⁻¹({τ_{2,k}}) = ϖ`
  have hbx := (hβ2 x).ne'
  have h4 : SS (fun o : Option (Option (Option (Gr (j + 1)))) => mT μin (j + 2) o)
      (fun o => βT μin (j + 2) o) {x} = 0 := by
    simp only [SS, mbar, sum_singleton]
    field_simp
    ring
  have h5 : mbar (fun o : Option (Option (Option (Gr (j + 1)))) => mT μin (j + 2) o)
      (fun o => βT μin (j + 2) o) {x} = (lvl μin j).mδ := by
    simp only [mbar, sum_singleton]
    field_simp
    rfl
  have h6 : ∑ o ∈ ({x} : Finset (Option (Option (Option (Gr (j + 1)))))),
      1 / βT μin (j + 2) o = ϖ μin (j + 1) := by
    rw [sum_singleton]
    rfl
  rw [h1, h4, h2, h5, h3, h6]
  -- "As `m̄ − m_o ≥ m̄ − M > 191M` and `q_k ≤ ϖM²`, this gives
  -- `S_2({b, τ_2, τ_{2,k}}) = ψ_{k+1} + (104/105)ϖ(m̄ − m_o)² > ψ_{k+1} + ϖM² ≥ q_{k+1}`."
  have e : ((lvl μin (j + 1)).mbar - (lvl μin j).mδ) ^ 2 /
      (1 / (104 * ϖ μin (j + 1)) + 1 / ϖ μin (j + 1)) =
      104 / 105 * ϖ μin (j + 1) * ((lvl μin (j + 1)).mbar - (lvl μin j).mδ) ^ 2 := by
    field_simp
    ring
  -- `m_o` is the reward of `τ_{2,k} ∈ E_k`, so `m_o ≤ M` (`lem:weights`(b))
  have hmo : (lvl μin j).mδ ≤ (lvl μin (j + 1)).M := mT_le_M (μin := μin) (j + 1) (some none)
  have hgap : 191 * (lvl μin (j + 1)).M < (lvl μin (j + 1)).mbar - (lvl μin j).mδ := by
    linarith
  have hsq : (191 * (lvl μin (j + 1)).M) ^ 2 < ((lvl μin (j + 1)).mbar - (lvl μin j).mδ) ^ 2 :=
    pow_lt_pow_left₀ hgap (by positivity) two_ne_zero
  rw [e]
  have := mul_lt_mul_of_pos_left hsq hϖ
  nlinarith

/-- **`thm:onestep`** (Theorem C.21, `stoc-sections/appD-hardness.tex:1288-1293`, proof lines
1295-1418): let `k ≥ 1` (here `k = j + 1`), and let `μ^in ∈ 𝔉` have length at least `k + 2`. Assume
that the hypotheses of `lem:onelevel` hold at the steps `0 → 1, …, k − 1 → k`. Then at the step
`k → k + 1`, the hypotheses of `lem:onelevel` and those of `thm:transition` with
`(e_t, e_l) = (b_k, τ_{2,k})` hold (`b_k = none`, `τ_{2,k} = some none`).

The proof's steps: the first paragraph, which writes the numbers of a step in terms of `M`, `ϖ`
and `w` ("The numbers of a step grow from level to level. We first write them in terms of
`M := M_k`, `ϖ := ϖ_k`, and the band width `w`, so that the same computation works at every level
`k ≥ 1`": `onestep_rule`, with `m̄ − M = (4967/26)M > 191M`; the inputs and the three small
quantities, `onestep_prev_numbers`, `onestep_small`; `d̄`, `φ`, `A`, and `υ^0` from
`lem:weights`(d); the width of level `k` at `R_0`, `onestep_width`), (Q1) and (Q2) (`onestep_Q1`,
`onestep_Q2`, with the spread `c_ww` of `onestep_width` and the rate `M` of `lem:fullplane`(c),
`ρT_rate`), and the bullets in the paper's order: (T1) (`onestep_T1a`, `onestep_T1b`,
`onestep_T1c`); (W1), (W2) (with `onestep_sℓ` and `lem:closedforms`(b)); (W3) and the inequalities
`ρ^h_{τ_1} < ρ^f_e < ρ^f_{τ_2}` of (T2) (`onestep_W3T2_num`); the inequality `ρ^f_{τ_2} < ρ^h_{e'}`
of (T2) (`onestep_T2b`); the inequality `ρ^h_{e'} ≤ ρ^h_{e_l}` of (T2) (`onestep_T2c`); (W4)
(`onestep_W4`); (T3) (`onestep_T3τ₂`); (W5); (W6). -/
theorem onestep {j K : ℕ} (hF : InF μin K) (hK : j + 3 ≤ K) (hyp : ∀ i ≤ j, OneLevelHyp μin i) :
    OneLevelHyp μin (j + 1) ∧ TransitionHyp μin (j + 1) none (some none) := by
  -- The first paragraph: "The numbers of a step grow from level to level. We first write them in
  -- terms of `M := M_k`, `ϖ := ϖ_k`, and the band width `w`, so that the same computation works at
  -- every level `k ≥ 1`. … By the parameter rule, … `m̄ = (4993/26)M`, so
  -- `m̄ − M = (4967/26)M > 191M`."
  have hμ : 0 < μT μin (j + 2) := μT_pos hF (by omega)
  have hw := w_pos (μin := μin) (k := j + 1) hμ
  have hM := M_pos (μin := μin) (j + 1)
  obtain ⟨-, -, hβ, -, -, hmb, -, -, -, -, h191⟩ := onestep_rule (μin := μin) j
  obtain ⟨-, hℓ, -, -, hshat, hcτ₂, -, -, -⟩ := onestep_small hF hK
  -- "We take `d̄`, `φ`, `A`, and `υ^0 := u^0/w` from `lem:weights`(d) at the step `k → k + 1`, …"
  -- (the rest of the sentence, on `ŝ`, is in `onestep_small`)
  obtain ⟨-, -, -, hφ, hυA, hA, hυ⟩ := weights_d (j := j) hF (by omega)
  have hR1 : R1T μin (j + 1) < R0 + μT μin (j + 2) :=
    (inputs hF (by omega)).2.2.2.2 (j + 1) (by omega)
  have hcb := closedforms_b (j + 1) hF (by omega)
  have hsι : (lvl μin (j + 1)).s * ι = cτ₂ μin (j + 1) * (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    rw [cτ₂, div_mul_cancel₀ _ hw.ne']
  have hu0 : (lvl μin (j + 1)).u0 (μT μin (j + 2)) (R1T μin (j + 1)) =
      υ0 μin (j + 1) * (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    rw [υ0, div_mul_cancel₀ _ hw.ne']
  -- "We now check the hypotheses one by one."
  -- (T1) (`onestep_T1a`, `onestep_T1b`, `onestep_T1c`, the last with `m̄ − M > 191M` of the first
  -- paragraph)
  have hT1a := onestep_T1a (μin := μin) j
  have hT1b := onestep_T1b (μin := μin) j
  have hT1c := onestep_T1c (μin := μin) j
  -- (W1), (W2) "`s|𝓡|/w = ŝℓ̂ < 0.4733`."
  have hcτ₂w := mul_le_mul_of_nonneg_right hcτ₂.le hw.le
  have hℓ0 : 0 < ℓhat μin (j + 1) := by
    simp only [ℓhat, lenR_eq]
    have := sum_nonneg fun i (_ : i ∈ range (j + 1 + 1)) => μT_nonneg (μin := μin) i
    positivity
  have hsℓ : (lvl μin (j + 1)).s * lenR μin (j + 1) <
      0.4733 * (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    rw [onestep_sℓ j hμ]
    have : shat μin (j + 1) * ℓhat μin (j + 1) < 0.4733 := by
      nlinarith [hshat.1, hshat.2]
    exact mul_lt_mul_of_pos_right this hw
  -- "So, by `lem:closedforms`(b), `u_1(R_0) = (1/2)(w − s|𝓡|) > 0.2633w > sι`,"
  have hW1a : (lvl μin (j + 1)).s * ι < u1 μin (j + 1) R0 := by
    have e : u1 μin (j + 1) R0 = ((lvl μin (j + 1)).w (μT μin (j + 2)) -
        (lvl μin (j + 1)).s * lenR μin (j + 1)) / 2 := by
      rw [hcb.1]
      unfold lenR
      ring
    have h1 : 0.2633 * (lvl μin (j + 1)).w (μT μin (j + 2)) < u1 μin (j + 1) R0 := by
      rw [e]
      linarith
    rw [hsι]
    linarith
  -- "`u_1(R_1) = (1/2)(w + s|𝓡|) < 0.7367w`,"
  have hW1b : u1 μin (j + 1) (R1T μin (j + 1)) < (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    have e : u1 μin (j + 1) (R1T μin (j + 1)) = ((lvl μin (j + 1)).w (μT μin (j + 2)) +
        (lvl μin (j + 1)).s * lenR μin (j + 1)) / 2 := by
      rw [hcb.1]
      unfold lenR
      ring
    have h1 : u1 μin (j + 1) (R1T μin (j + 1)) < 0.7367 * (lvl μin (j + 1)).w (μT μin (j + 2)) := by
      rw [e]
      linarith
    linarith
  -- "`u_2(R_0 + μ) = υ^0w > 0.2354w`,"
  have hW2a : 0 < u2 μin (j + 1) (R0 + μT μin (j + 2)) := by
    have h1 : 0.2354 * (lvl μin (j + 1)).w (μT μin (j + 2)) <
        u2 μin (j + 1) (R0 + μT μin (j + 2)) := by
      rw [hcb.2.2.1, hu0]
      exact mul_lt_mul_of_pos_right hυ.1 hw
    have : (0 : ℝ) < 0.2354 * (lvl μin (j + 1)).w (μT μin (j + 2)) := by positivity
    linarith
  -- "and `u_2(R_1 + μ) = (υ^0 + ŝℓ̂)w = (A + (1245/832)ℓ̂)w < 0.7501w`."
  have hW2b : u2 μin (j + 1) (R1T μin (j + 1) + μT μin (j + 2)) <
      (lvl μin (j + 1)).w (μT μin (j + 2)) := by
    have h1 := hcb.2.2.2.2.2 (R0 + μT μin (j + 1 + 1)) (R1T μin (j + 1) + μT μin (j + 1 + 1))
    have e : (lvl μin (j + 1)).s * (R1T μin (j + 1) + μT μin (j + 1 + 1) -
        (R0 + μT μin (j + 1 + 1))) = (lvl μin (j + 1)).s * lenR μin (j + 1) := by
      unfold lenR
      ring
    rw [hcb.2.2.1, hu0, e, onestep_sℓ j hμ] at h1
    have h2 : u2 μin (j + 1) (R1T μin (j + 1) + μT μin (j + 2)) =
        (υ0 μin (j + 1) + shat μin (j + 1) * ℓhat μin (j + 1)) *
          (lvl μin (j + 1)).w (μT μin (j + 2)) := by
      linarith
    have h3 : υ0 μin (j + 1) + shat μin (j + 1) * ℓhat μin (j + 1) =
        Awt μin (j + 1) + 1245 / 832 * ℓhat μin (j + 1) := by
      rw [hυA, shat_eq]
      ring
    have h4 : Awt μin (j + 1) + 1245 / 832 * ℓhat μin (j + 1) < 0.7501 := by
      linarith [hA.2]
    rw [h2, h3]
    nlinarith
  -- (W3) and the inequalities `ρ^h_{τ_1} < ρ^f_e < ρ^f_{τ_2}` of (T2) (`onestep_W3T2_num`):
  -- `ρ^{(k)}_e − ρ^h_{τ_1} > 1.2w` and `ρ^f_{τ_2} − ρ^{(k)}_e > 0.47w` on `[R_0, R_0 + μ]`.
  have hW3 : ∀ c, ∀ α ∈ Set.Icc R0 (R1T μin (j + 1)),
      ρh μin (j + 1) α (some none) < ρT μin (j + 1) α c := fun c α hα => by
    have := (onestep_W3T2_num hF hK hyp ⟨hα.1, hα.2.trans hR1.le⟩ c).1
    linarith
  have hT2 : ∀ α ∈ Set.Icc (R1T μin (j + 1)) (R0 + μT μin (j + 2)), ∀ c c' : Gr (j + 1),
      ρh μin (j + 1) α (some none) < ρf μin (j + 1) α (some (some c)) ∧
        ρf μin (j + 1) α (some (some c)) < ρf μin (j + 1) α none ∧
        ρf μin (j + 1) α none < ρh μin (j + 1) α (some (some c')) ∧
        ρh μin (j + 1) α (some (some c')) ≤ ρh μin (j + 1) α (some (some (some none))) := by
    intro α hα c c'
    have hα' : α ∈ Set.Icc R0 (R0 + μT μin (j + 2)) :=
      ⟨(R0_lt_R1T (μin := μin) (j + 1)).le.trans hα.1, hα.2⟩
    obtain ⟨n1, n2⟩ := onestep_W3T2_num hF hK hyp hα' c
    -- the inequality `ρ^f_{τ_2} < ρ^h_{e'}` of (T2) (`onestep_T2b`):
    -- `ρ^h_{e'} − ρ^f_{τ_2} > 0.225w` on the transition
    have n3 := onestep_T2b hF hK hyp hα c'
    have hfc := (D_bands (μin := μin) (j + 1) α).1 c
    -- the inequality `ρ^h_{e'} ≤ ρ^h_{e_l}` of (T2) (`onestep_T2c`): `τ_{2,k}` has the largest of
    -- the `ρ^h_e`, `e ∈ E_k`
    exact ⟨by rw [hfc]; linarith, by rw [hfc]; linarith, by linarith,
      onestep_T2c hF hK hyp hα c'⟩
  -- (W4) "for `e ∈ E_k`, `θ_2 − ρ^h_e` increases, as `m̄ > M`. At `R_0 + μ` it is at least
  -- `ρ^f_{τ_2}(R_0 + μ) + u_2(R_0 + μ) − ρ̄_k − m_*μ = sι > 0`, by (Q1), (Q2), and
  -- `u_2(R_0 + μ) = u^0`." (`onestep_W4`, with the rate `M` of `lem:fullplane`(c))
  have hW4 := onestep_W4 hF (by omega) (fun e => (ρT_rate (j + 1) e).2) (by linarith)
    fun e => (onestep_width hF hK (hyp j le_rfl) e).2
  -- (T3) (`onestep_T3τ₂`)
  have hT3 := onestep_T3τ₂ hF hK hyp
  -- (W5) "`φ > 2.9791`."
  have hW5 : 1 < φ μin (j + 1) := by linarith [hφ.1]
  -- (W6) "`β⁻¹(E ∪ {b}) = 16ϖ_{k+1} = 128ϖ` (`lem:weights`(a)) and
  -- `t_b = 12ϖ_{k+1}·208M = 96ϖ·208M`, so `t_b/β⁻¹(E ∪ {b}) = 156M > M`."
  have hW6 : (lvl μin (j + 1)).M < cfast μin (j + 1) := by
    have hϖ := ϖ_pos (μin := μin) (j + 1)
    have hS : ∑ o, 1 / βT μin (j + 2) o = 128 * ϖ μin (j + 1) := by
      rw [(weights_a (μin := μin)).2.2.1 (j + 1)]
      show 16 * (1 / (lvl μin (j + 1)).βδ) = _
      rw [hβ]
      ring
    have hb : 1 / (lvl μin (j + 1)).βb = 96 * ϖ μin (j + 1) := by
      rw [Level.βb, one_div_div, div_eq_mul_one_div 12, hβ]
      ring
    show (lvl μin (j + 1)).M <
      (lvl μin (j + 1)).mb / (lvl μin (j + 1)).βb / ∑ o, 1 / βT μin (j + 2) o
    rw [hS, hmb, div_eq_mul_one_div _ (lvl μin (j + 1)).βb, hb]
    rw [show 208 * (lvl μin (j + 1)).M * (96 * ϖ μin (j + 1)) / (128 * ϖ μin (j + 1)) =
      156 * (lvl μin (j + 1)).M by field_simp; ring]
    linarith
  -- "This proves all the hypotheses, and the theorem."
  exact ⟨⟨hW1a, hW1b, hW2a, hW2b, hW3, hW4, hW5, hW6⟩, ⟨hT1a, hT1b, fun _ => hT1c, hT2, hT3⟩⟩

end Tower

end

end Hardness

end Stoc
