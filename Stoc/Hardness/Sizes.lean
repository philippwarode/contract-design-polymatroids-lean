-- stamp r5 2026-11-02
import Stoc.Hardness.Encoding
import Stoc.Hardness.OneStep

/-!
# Sizes: `lem:sizes`

The STOC version's `lem:sizes` (Lemma C.24, Appendix C.7, `sec:D-alllevels`, "Every level works",
`stoc-sections/appD-hardness.tex:1547-1552`, proof lines 1554-1660): let
`μ^in ∈ 𝔉` have length `k`. Every number computed by the parameter rule for the levels
`1, …, k − 1`, and every value of `g_{k−1}`, is a rational with `O(k + log μ^in_k)` bits, and the
parameter rule runs in time polynomial in `k + log μ^in_k`.

The proof's first sentence fixes what `O(k + log μ^in_k)` bits means: "A rational number has
`O(k + log μ^in_k)` bits if its magnitude and its denominator are at most `2^{O(k + log μ^in_k)}`."
`Bits B x` says this for the bound `2^B` (its magnitude is at most `2^B`, and `n x` is an integer
for a positive integer `n ≤ 2^B`), and `sizes` gives it for `B = 100(k + ⌊log₂ μ^in_k⌋ + 1)`.

* `InZ N x`: `x ∈ (1/N)ℤ`, the notation of the proof (`x ∈ δℤ` is `InZ (1/δ) x`), with the rules
  for sums, products and coarser denominators that the proof uses without comment; `InZ` and
  `Bits` are in `Stoc/Hardness/Encoding.lean`, with the encoding lengths of `lem:exactbr`.
* The magnitudes (the first two paragraphs of the proof): `Ω_j = ϖ_j M_j (1 + μ_j)` (`Ω`), and the
  bounds of `sizes_dE`, `sizes_ρbar`, `sizes_F`, `sizes_K`, `sizes_p` and `sizes_g`.
* The denominators (the third paragraph): the common denominators `𝔇_j`, `𝔈_j`, `𝔗_j` and `𝔓`,
  the items of the list (`sizes_items`), the formula `(*)` for `F_{τ_2}` (`Fτ₂_star`), the formula
  `(†)` for `Δ_p` (`Δp_dagger`), and the memberships `sizes_Fτ₂_den`, `sizes_K_den`, `sizes_g_den`,
  `sizes_p_den` and `sizes_ρbar_den`.
* The bits (the end of the third paragraph): `𝔇_j`, `𝔗_j` and `𝔓` are at most
  `2^{O(j + log μ^in_1)}` (`sizes_pow`, `sizes_dens`, which bound them by `2^{O(j + log μ^in_k)}`,
  as `μ^in_1 ≤ μ^in_k`; that suffices), so the numbers above have
  `O(k + log μ^in_k)` bits (`sizes_prim`); so do the sums `d_j(E_{j−1})` and `Π`, in `(δ/4)ℤ`, and
  `a_2`, in `(δ/130)ℤ`, by their magnitudes, and `d̄`, `φ` and `a_0`, which take `O(1)` arithmetic
  operations more (`sizes_step`).
* `sizes`: the lemma. `RuleNumber μin j x` says that `x` is one of the numbers that the parameter
  rule computes at the step `j → j + 1` (`def:ruleP`, `tab:ruleP`): the numbers of (P1)–(P8), the
  rewards and curvatures of the new level, and `φ`.

Not formalised: the running time, the last paragraph of the proof ("Per level, the parameter rule
needs `O(|E_{k−1}|)` arithmetic operations on numbers of `O(k + log μ^in_k)` bits. Values of
`g_{k−1}` are computed recursively, by the formula above, in `O(k|E_{k−1}|)` operations."), as
Turing machines are not formalised and arithmetic operations are not counted; the formula for `g_j`
that it uses is `gT_succ_apply`.

Indices: the levels are numbered as in the paper (`lvl μin j` is level `j`, on `Gr j = E_j`), and
`μin i` is `μ^in_{i+1}`. The paper states the bounds for the step `j − 1 → j` to a level `j ≥ 1`;
the lemmas below state them for the step `j → j + 1`, whose numbers are those of `lvl μin j` with
`μ = μT μin (j + 1)` and `R_1 = R1T μin j`, as in `Stoc/Hardness/Tower.lean`. So the paper's
`Ω_j`, `M_j`, `ϖ_j` and `F_{τ_2}^{(j)}` appear as `Ω μin (j + 1)`, `(lvl μin (j + 1)).M`,
`ϖ μin (j + 1)` and `(lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)`.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### The inputs and two summation rules (not in the paper) -/

variable {μin : ℕ → ℕ}

/-- The inputs increase, `μ^in_i < μ^in_{i+1}` (not in the paper: by `def:family`, as in step (1) of
the proof of `lem:inputs`). -/
lemma μin_lt {k : ℕ} (hF : InF μin k) {i : ℕ} (hi : i + 1 < k) : μin i < μin (i + 1) := by
  obtain ⟨-, -, H, hH, hb⟩ := hF
  obtain ⟨-, a2⟩ := hb i (by omega)
  obtain ⟨b1, -⟩ := hb (i + 1) hi
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have h8 : (0 : ℝ) < 8 ^ i := by positivity
  have : (μin i : ℝ) < μin (i + 1) := by
    calc (μin i : ℝ) < 11 / 10 * H * 8 ^ i := a2
      _ ≤ H * 8 ^ (i + 1) := by rw [pow_succ]; nlinarith
      _ ≤ μin (i + 1) := b1
  exact_mod_cast this

/-- The inputs increase weakly, `μ^in_{i+1} ≤ μ^in_{j+1}` for `i ≤ j < k` (not in the paper: from
`μin_lt`). -/
lemma μin_mono {k : ℕ} (hF : InF μin k) {i j : ℕ} (hij : i ≤ j) (hj : j < k) : μin i ≤ μin j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (μin_lt hF (by omega)).le

/-- The translations increase weakly, `μ_i ≤ μ_j` for `i ≤ j < k` (not in the paper: from
`μin_mono`). -/
lemma μT_mono {k : ℕ} (hF : InF μin k) {i j : ℕ} (hij : i ≤ j) (hj : j < k) :
    μT μin i ≤ μT μin j := by
  have h := μin_mono hF hij hj
  have h0 : (0 : ℝ) < 3 * μin 0 := by have := μin0_pos hF; positivity
  unfold μT δT
  have : (μin i : ℝ) ≤ μin j := by exact_mod_cast h
  rw [one_div, inv_mul_eq_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right this h0.le

/-- `μ_j ≤ μ^in_k` (the proof of `lem:sizes`): `μ_j = μ^in_{j+1}/(3μ^in_1) ≤ μ^in_{j+1} ≤ μ^in_k`
for `j < k`. -/
lemma μT_le {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j < k) : μT μin j ≤ μin (k - 1) := by
  have h0 : (1 : ℝ) ≤ μin 0 := by exact_mod_cast μin0_pos hF
  have hm : (μin j : ℝ) ≤ μin (k - 1) := by
    exact_mod_cast μin_mono hF (by omega : j ≤ k - 1) (by omega)
  have hj0 : (0 : ℝ) ≤ μin j := Nat.cast_nonneg _
  unfold μT δT
  rw [one_div, inv_mul_eq_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- A sum of nonnegative numbers, each at least twice the one before, is at most twice the last
(not in the paper: the proof of `lem:sizes` uses it with "more than doubles from level to
level"). -/
lemma sum_le_two_mul {a : ℕ → ℝ} {j : ℕ} (h0 : ∀ i ≤ j, 0 ≤ a i)
    (h : ∀ i < j, 2 * a i ≤ a (i + 1)) : ∑ i ∈ range (j + 1), a i ≤ 2 * a j := by
  induction j with
  | zero =>
    simp only [zero_add, sum_range_one]
    linarith [h0 0 le_rfl]
  | succ j ih =>
    rw [sum_range_succ]
    have h1 := ih (fun i hi => h0 i (by omega)) (fun i hi => h i (by omega))
    have h2 := h j (by omega)
    linarith

/-! ### The magnitudes -/

variable (μin) in
/-- `Ω_j = ϖ_j M_j (1 + μ_j)` (the proof of `lem:sizes`). -/
def Ω (j : ℕ) : ℝ := ϖ μin j * (lvl μin j).M * (1 + μT μin j)

/-- `Ω_j > 0` (not in the paper). -/
lemma Ω_pos (j : ℕ) : 0 < Ω μin j := by
  have := ϖ_pos (μin := μin) j
  have := M_pos (μin := μin) j
  have := μT_nonneg (μin := μin) j
  unfold Ω
  positivity

/-- `M_{j+1} = 208M_j`: by (P1) and (P4), `M_{j+1} = m_b = M_j/2 + (415/2)M_j`, as in the proof of
`lem:weights`(b). -/
lemma M_succ_eq (j : ℕ) : (lvl μin (j + 1)).M = 208 * (lvl μin j).M := by
  rw [M_succ]
  simp only [Level.mb, Level.mδ, Level.Δb]
  ring

/-- The proof of `lem:sizes`: "`Ω_j := ϖ_j M_j (1 + μ_j)`, which more than doubles from level to
level", for the levels `j ≥ 1` for which `μ_{j+1}` is defined. -/
lemma Ω_double {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 < k) :
    2 * Ω μin (j + 1) ≤ Ω μin (j + 2) := by
  have hμ := μT_mono hF (Nat.le_succ (j + 1)) hj
  have h0 := μT_nonneg (μin := μin) (j + 1)
  have hM := M_pos (μin := μin) (j + 1)
  unfold Ω
  rw [ϖ_succ, ϖ_succ, M_succ_eq (j + 1), pow_succ]
  have : (0 : ℝ) < 3 / 4 * 8 ^ j := by positivity
  have h1 : 0 < 3 / 4 * 8 ^ j * (lvl μin (j + 1)).M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hμ h1.le]

/-- The proof of `lem:sizes`: "`w_j = 64 M_{j−1} μ_j = (4/13) M_j μ_j`" (at the step
`j → j + 1`). -/
lemma w_eq_M (j : ℕ) :
    (lvl μin j).w (μT μin (j + 1)) = 4 / 13 * (lvl μin (j + 1)).M * μT μin (j + 1) := by
  rw [M_succ_eq]
  simp only [Level.w]
  ring

/-- The proof of `lem:sizes`: "`d̄_j < 129/64` and `φ_j < 3.021` (`lem:weights`(d) at the step
`j − 1 → j` for `j ≥ 2`, and `d̄_1 = 2` and `φ_1 < 3.000004` by `prop:level1` and its proof)", and
"`0 < u^0_j < w_j` (`lem:weights`(d) and `prop:level1`)", here at the step `j → j + 1` with
`j + 2 ≤ k`; also `d̄ > 0` and `φ > 0`, which the bounds below use. -/
lemma sizes_dbar_φ {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    0 < (lvl μin j).dbar (μT μin (j + 1)) ∧ (lvl μin j).dbar (μT μin (j + 1)) < 129 / 64 ∧
    0 < φ μin j ∧ φ μin j < 3.021 ∧ 0 < υ0 μin j ∧ υ0 μin j < 1 := by
  rcases j with _ | j
  · -- "`d̄_1 = 2` and `φ_1 < 3.000004` by `prop:level1` and its proof"
    have h0 := μin0_pos hF
    have hμ : 0 < μT μin 1 := μT_pos hF (by omega)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hdbar, -⟩ := level1_data h0 hμ
    obtain ⟨⟨hφ1, hφ2⟩, ⟨hυ1, hυ2⟩, -⟩ := level1 hF (by omega)
    refine ⟨by rw [hdbar]; norm_num, by rw [hdbar]; norm_num, by linarith, by linarith,
      by linarith, by linarith⟩
  · -- "`lem:weights`(d) at the step `j − 1 → j` for `j ≥ 2`"
    obtain ⟨⟨hd1, hd2⟩, -, -, ⟨hφ1, hφ2⟩, -, -, ⟨hυ1, hυ2⟩⟩ := weights_d (j := j) hF (by omega)
    refine ⟨by linarith, hd2, by linarith, by linarith, by linarith, by linarith⟩

/-- `d_e ≥ 0` for `e ∈ E_j ∪ {τ_1, τ_2}` (the paragraph after `def:ruleP`: `m_* ≥ M ≥ m_e`, hence
`d ≥ 0`; `stepD_hyp`). -/
lemma dE'_nonneg (j : ℕ) (e : Option (Option (Gr j))) : 0 ≤ (lvl μin j).dE' (μT μin (j + 1)) e := by
  have hH := stepD_hyp (μin := μin) j
  rw [← Level.dStep_eq (lvl μin j) (μT μin (j + 1)) (R1T μin j)]
  exact hH.d_nonneg e

/-- `d_e ≥ 0` for `e ∈ E_j` (`dE'_nonneg`). -/
lemma d_nonneg (j : ℕ) (c : Gr j) : 0 ≤ (lvl μin j).d (μT μin (j + 1)) c :=
  dE'_nonneg j (some (some c))

/-- The proof of `lem:sizes`: "So `d_j(E_j ∖ {b_j}) = (2 + d̄_j)ϖ_j w_j ≤ 2Ω_j` and
`ΔF_j = φ_j ϖ_j w_j ≤ Ω_j`, and the number `Π` of (P5) at the step to level `j` satisfies
`|Π| ≤ M_j d_j(E_j ∖ {b_j})`", at the step `j → j + 1` (so `d(E)`, `ΔF` and `Π` of that step and
`Ω_{j+1}`, `M_{j+1}`); also `d(E_j) ≤ d(E)`, `d(E) ≥ 0` and `ΔF ≥ 0`, which the bounds below use. -/
lemma sizes_dE {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    (lvl μin j).dE (μT μin (j + 1)) =
        (2 + (lvl μin j).dbar (μT μin (j + 1))) * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) ∧
    0 ≤ (lvl μin j).dEk (μT μin (j + 1)) ∧
    (lvl μin j).dEk (μT μin (j + 1)) ≤ (lvl μin j).dE (μT μin (j + 1)) ∧
    (lvl μin j).dE (μT μin (j + 1)) ≤ 2 * Ω μin (j + 1) ∧
    (lvl μin j).ΔF (μT μin (j + 1)) =
        φ μin j * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) ∧
    0 ≤ (lvl μin j).ΔF (μT μin (j + 1)) ∧ (lvl μin j).ΔF (μT μin (j + 1)) ≤ Ω μin (j + 1) ∧
    |(lvl μin j).Pcal (μT μin (j + 1))| ≤
      (lvl μin (j + 1)).M * (lvl μin j).dE (μT μin (j + 1)) := by
  obtain ⟨hd0, hd1, hφ0, hφ1, -, -⟩ := sizes_dbar_φ hF hj
  have hμ : 0 < μT μin (j + 1) := μT_pos hF (by omega)
  have hw := w_pos (μin := μin) hμ
  have hϖ : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
  have hϖ0 := ϖ_pos (μin := μin) (j + 1)
  have hM := M_pos (μin := μin) (j + 1)
  have hMj := M_pos (μin := μin) j
  -- "`d_j(E_j ∖ {b_j}) = (2 + d̄_j)ϖ_j w_j`" (`lem:closedforms`(a))
  have hdE : (lvl μin j).dE (μT μin (j + 1)) =
      (2 + (lvl μin j).dbar (μT μin (j + 1))) * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) := by
    rw [(closedforms_a j hF hj).1, hϖ]
    ring
  have hdEk0 : 0 ≤ (lvl μin j).dEk (μT μin (j + 1)) :=
    sum_nonneg fun c _ => d_nonneg (μin := μin) j c
  have hdEk : (lvl μin j).dEk (μT μin (j + 1)) ≤ (lvl μin j).dE (μT μin (j + 1)) := by
    rw [Level.dE_split]
    have : 0 ≤ (lvl μin j).w (μT μin (j + 1)) / (lvl μin j).βδ :=
      div_nonneg hw.le (lvl μin j).βδ_pos.le
    linarith
  -- "`ΔF_j = φ_j ϖ_j w_j`" (the definition of `φ` before `lem:closedforms`)
  have hΔF : (lvl μin j).ΔF (μT μin (j + 1)) =
      φ μin j * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) := by
    rw [φ, hϖ]
    have := (lvl μin j).βδ_pos.ne'
    field_simp
  have hwM := w_eq_M (μin := μin) j
  have hΩ : Ω μin (j + 1) = ϖ μin (j + 1) * (lvl μin (j + 1)).M * (1 + μT μin (j + 1)) := rfl
  have hϖw : ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) ≤ 4 / 13 * Ω μin (j + 1) := by
    rw [hwM, hΩ]
    have : 0 < ϖ μin (j + 1) * (lvl μin (j + 1)).M := by positivity
    nlinarith
  have hϖw0 : 0 < ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) := by positivity
  refine ⟨hdE, hdEk0, hdEk, ?_, hΔF, ?_, ?_, ?_⟩
  · -- "`≤ 2Ω_j`", as `(2 + 129/64)(4/13) < 2`
    rw [hdE, mul_assoc]
    nlinarith
  · rw [hΔF, mul_assoc]
    positivity
  · -- "`ΔF_j ≤ Ω_j`", as `3.021 · 4/13 < 1`
    rw [hΔF, mul_assoc]
    nlinarith
  · -- "`|Π| ≤ M_j d_j(E_j ∖ {b_j})`": `|m_δ − m_e| ≤ M_{j−1} ≤ M_j` and `d_e ≥ 0`
    have hterm : ∀ c, |((lvl μin j).mδ - (lvl μin j).m c) * (lvl μin j).d (μT μin (j + 1)) c| ≤
        (lvl μin j).M * (lvl μin j).d (μT μin (j + 1)) c := by
      intro c
      have hc0 := mT_pos (μin := μin) j c
      have hc1 := mT_le_M (μin := μin) j c
      have hdc := d_nonneg (μin := μin) j c
      change 0 < (lvl μin j).m c at hc0
      change (lvl μin j).m c ≤ (lvl μin j).M at hc1
      rw [abs_mul, abs_of_nonneg hdc]
      apply mul_le_mul_of_nonneg_right _ hdc
      rw [abs_le]
      simp only [Level.mδ]
      constructor <;> linarith
    calc |(lvl μin j).Pcal (μT μin (j + 1))|
        ≤ ∑ c, |((lvl μin j).mδ - (lvl μin j).m c) * (lvl μin j).d (μT μin (j + 1)) c| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, (lvl μin j).M * (lvl μin j).d (μT μin (j + 1)) c := sum_le_sum fun c _ => hterm c
      _ = (lvl μin j).M * (lvl μin j).dEk (μT μin (j + 1)) := by rw [Level.dEk, mul_sum]
      _ ≤ (lvl μin (j + 1)).M * (lvl μin j).dE (μT μin (j + 1)) := by
          rw [M_succ_eq]
          nlinarith

/-- `ρ̄_0 = 7/6` (P6). -/
lemma ρbar_zero : (lvl μin 0).ρbar = 7 / 6 := rfl

/-- The proof of `lem:sizes`: "By `lem:closedforms`(c), and as `0 < u^0_j < w_j` (`lem:weights`(d)
and `prop:level1`), `0 < ρ̄_j ≤ ρ̄_0 + ∑_{i≤j}(w_i + s_iι) ≤ 7/6 + 2w_j + M_j/50 ≤ M_j(1 + μ_j)`,
because `w_i` more than doubles from level to level, and `s_iι = (2490/1300)M_{i−1} < M_i/100`",
for the level `j + 1` with `j + 2 ≤ k` (the sum over the steps `i → i + 1`, `i ≤ j`). -/
lemma sizes_ρbar {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    0 < (lvl μin (j + 1)).ρbar ∧
    (lvl μin (j + 1)).ρbar ≤ 7 / 6 + ∑ i ∈ range (j + 1),
      ((lvl μin i).w (μT μin (i + 1)) + (lvl μin i).s * ι) ∧
    7 / 6 + ∑ i ∈ range (j + 1), ((lvl μin i).w (μT μin (i + 1)) + (lvl μin i).s * ι) ≤
      7 / 6 + 2 * (lvl μin j).w (μT μin (j + 1)) + (lvl μin (j + 1)).M / 50 ∧
    7 / 6 + 2 * (lvl μin j).w (μT μin (j + 1)) + (lvl μin (j + 1)).M / 50 ≤
      (lvl μin (j + 1)).M * (1 + μT μin (j + 1)) := by
  -- `ρ̄_{i+1} = ρ̄_i + w_{i+1} − u^0_{i+1} + s_{i+1}ι` (`lem:closedforms`(c)) and `0 < u^0 < w`
  have hstep : ∀ i, i + 2 ≤ k → (lvl μin i).ρbar + (lvl μin i).s * ι < (lvl μin (i + 1)).ρbar ∧
      (lvl μin (i + 1)).ρbar ≤ (lvl μin i).ρbar + (lvl μin i).w (μT μin (i + 1)) +
        (lvl μin i).s * ι := by
    intro i hi
    obtain ⟨-, h1, h2⟩ := closedforms_c_aux (μin := μin) i
    obtain ⟨-, -, -, -, hυ0, hυ1⟩ := sizes_dbar_φ hF hi
    have hw := w_pos (μin := μin) (μT_pos hF (by omega : i + 1 < k))
    have hu : (lvl μin i).u0 (μT μin (i + 1)) (R1T μin i) =
        υ0 μin i * (lvl μin i).w (μT μin (i + 1)) := by
      rw [υ0, div_mul_cancel₀ _ hw.ne']
    rw [h1, h2, hu]
    constructor <;> nlinarith
  have hρ : ∀ j, j + 2 ≤ k → 0 < (lvl μin (j + 1)).ρbar ∧
      (lvl μin (j + 1)).ρbar ≤ 7 / 6 + ∑ i ∈ range (j + 1),
        ((lvl μin i).w (μT μin (i + 1)) + (lvl μin i).s * ι) := by
    intro j hj
    induction j with
    | zero =>
      obtain ⟨h1, h2⟩ := hstep 0 hj
      have := s_pos (μin := μin) 0
      rw [ρbar_zero] at h1 h2
      refine ⟨by unfold ι at h1; linarith, by rw [sum_range_one]; linarith⟩
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨h1, h2⟩ := hstep (j + 1) hj
      have := s_pos (μin := μin) (j + 1)
      refine ⟨by unfold ι at h1; linarith, ?_⟩
      rw [sum_range_succ]
      linarith
  obtain ⟨h1, h2⟩ := hρ j hj
  -- "because `w_i` more than doubles from level to level": `∑_{i≤j} w_i ≤ 2w_j`
  have hwsum : ∑ i ∈ range (j + 1), (lvl μin i).w (μT μin (i + 1)) ≤
      2 * (lvl μin j).w (μT μin (j + 1)) := by
    refine sum_le_two_mul (fun i hi => (w_pos (μT_pos hF (by omega))).le) fun i hi => ?_
    rw [w_eq_M, w_eq_M]
    have hμ := μT_mono hF (Nat.le_succ (i + 1)) (by omega : i + 2 < k)
    have hM := M_pos (μin := μin) (i + 1)
    have h0 := μT_nonneg (μin := μin) (i + 1)
    rw [M_succ_eq (i + 1)]
    nlinarith [mul_le_mul_of_nonneg_left hμ hM.le]
  -- "and `s_iι = (2490/1300)M_{i−1} < M_i/100`", so `∑_{i≤j} s_iι ≤ 2M_j/100 = M_j/50`
  have hssum : ∑ i ∈ range (j + 1), (lvl μin i).s * ι ≤ (lvl μin (j + 1)).M / 50 := by
    have hle : ∀ i, (lvl μin i).s * ι ≤ (lvl μin (i + 1)).M / 100 := by
      intro i
      have := M_pos (μin := μin) i
      rw [M_succ_eq]
      simp only [Level.s, Level.Δb, ι]
      nlinarith
    calc ∑ i ∈ range (j + 1), (lvl μin i).s * ι
        ≤ ∑ i ∈ range (j + 1), (lvl μin (i + 1)).M / 100 := sum_le_sum fun i _ => hle i
      _ ≤ 2 * ((lvl μin (j + 1)).M / 100) := by
          refine sum_le_two_mul (fun i _ => (div_pos (M_pos _) (by norm_num)).le) fun i _ => ?_
          rw [M_succ_eq (i + 1)]
          have := M_pos (μin := μin) (i + 1)
          linarith
      _ = (lvl μin (j + 1)).M / 50 := by ring
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [sum_add_distrib]
    linarith
  · -- `2w_j = (8/13)M_jμ_j ≤ M_jμ_j` and `7/6 + M_j/50 ≤ M_j`, as `M_j ≥ 12·208`
    rw [w_eq_M]
    have hM : (lvl μin (j + 1)).M = 12 * 208 ^ (j + 1) := (weights_b (μin := μin)).2.1 (j + 1)
    have hM1 : (2496 : ℝ) ≤ (lvl μin (j + 1)).M := by
      rw [hM, pow_succ]
      have : (1 : ℝ) ≤ 208 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have h0 := μT_nonneg (μin := μin) (j + 1)
    nlinarith

/-- The proof of `lem:sizes`: "Hence `|F_{τ_2}^{(j)}| = ϖ_j|R_0m_δ^{(j)} − ρ̄_j| ≤ 2Ω_j` and
`|F_{τ_1}^{(j)}| ≤ |F_{τ_2}^{(j)}| + ΔF_j ≤ 3Ω_j`", at the step `j → j + 1`. -/
lemma sizes_F {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) =
        ϖ μin (j + 1) * (R0 * (lvl μin j).mδ - (lvl μin (j + 1)).ρbar) ∧
    |(lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)| ≤ 2 * Ω μin (j + 1) ∧
    |(lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)| ≤ 3 * Ω μin (j + 1) := by
  obtain ⟨hρ0, hρ1, hρ2, hρ3⟩ := sizes_ρbar hF hj
  have hρ := hρ1.trans (hρ2.trans hρ3)
  obtain ⟨-, -, -, -, -, hΔF0, hΔF1, -⟩ := sizes_dE hF hj
  have hϖ : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
  have hβ := (lvl μin j).βδ_pos
  -- `ρ̄_{j+1} = R_0m_δ − β_δF_{τ_2}` (P6)
  have hFτ₂ : (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) =
      ϖ μin (j + 1) * (R0 * (lvl μin j).mδ - (lvl μin (j + 1)).ρbar) := by
    show _ = ϖ μin (j + 1) * (R0 * (lvl μin j).mδ -
      (R0 * (lvl μin j).mδ - (lvl μin j).βδ * (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)))
    rw [hϖ]
    field_simp
    ring
  have hϖ0 := ϖ_pos (μin := μin) (j + 1)
  have hMj := M_pos (μin := μin) j
  have hM1 : (lvl μin (j + 1)).M = 208 * (lvl μin j).M := M_succ_eq j
  have h0 := μT_nonneg (μin := μin) (j + 1)
  have hτ₂ : |(lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)| ≤ 2 * Ω μin (j + 1) := by
    rw [hFτ₂, abs_mul, abs_of_pos hϖ0, Ω]
    have hR : |R0 * (lvl μin j).mδ - (lvl μin (j + 1)).ρbar| ≤
        2 * ((lvl μin (j + 1)).M * (1 + μT μin (j + 1))) := by
      rw [abs_le, R0_eq]
      simp only [Level.mδ]
      constructor <;> nlinarith
    nlinarith
  refine ⟨hFτ₂, hτ₂, ?_⟩
  rw [Level.Fτ₁]
  calc |(lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) + (lvl μin j).ΔF (μT μin (j + 1))|
      ≤ |(lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)| + |(lvl μin j).ΔF (μT μin (j + 1))| :=
        abs_add_le _ _
    _ ≤ 3 * Ω μin (j + 1) := by rw [abs_of_nonneg hΔF0]; linarith

/-- `R_0 + R_1^{(j)} ≤ 1 + μ_{j+1}` (the proof of `lem:sizes`: "`R_0 + R_1^{(j−1)} ≤ 1 + μ_j`"):
`R_0 + R_1^{(j)} = 2/3 + ∑_{i≤j} μ_i` and `∑_{i≤j} μ_i < μ_{j+1}` (`lem:inputs`). -/
lemma R0_add_R1_le {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    0 < R0 + R1T μin j ∧ R0 + R1T μin j ≤ 1 + μT μin (j + 1) := by
  have hin := ((inputs hF (by omega)).2.2.1 j (by omega)).1
  have hs : 0 ≤ ∑ i ∈ range (j + 1), μT μin i := sum_nonneg fun i _ => μT_nonneg i
  unfold R1T
  rw [R0_eq]
  unfold ζ₁ ε₀
  constructor <;> linarith

/-- The proof of `lem:sizes`: "By (P7), as `s_j < M_j` and `R_0 + R_1^{(j−1)} ≤ 1 + μ_j`,
`|K_j| ≤ d_j(E_j ∖ {b_j}) + 12|F_{τ_1}^{(j)}| + 13ϖ_j(w_j/2 + s_j(1 + μ_j)/2) ≤ 50Ω_j`", at the step
`j → j + 1`. -/
lemma sizes_K {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    |(lvl μin j).K (μT μin (j + 1)) (R1T μin j)| ≤ (lvl μin j).dE (μT μin (j + 1)) +
      12 * |(lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)| +
      13 * ϖ μin (j + 1) * ((lvl μin j).w (μT μin (j + 1)) / 2 +
        (lvl μin j).s * (1 + μT μin (j + 1)) / 2) ∧
    |(lvl μin j).K (μT μin (j + 1)) (R1T μin j)| ≤ 50 * Ω μin (j + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -⟩ := sizes_dE hF hj
  obtain ⟨-, -, hdEk, hdE2, -, -, -, -⟩ := sizes_dE hF hj
  obtain ⟨-, -, hFτ₁⟩ := sizes_F hF hj
  obtain ⟨hR0, hR1⟩ := R0_add_R1_le hF hj
  have hϖ : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
  have hϖ0 := ϖ_pos (μin := μin) (j + 1)
  have hw := w_pos (μin := μin) (μT_pos hF (by omega : j + 1 < k))
  have hs := s_pos (μin := μin) j
  have hdE0 : 0 ≤ (lvl μin j).dE (μT μin (j + 1)) := by
    have := (sizes_dE hF hj).2.1
    linarith
  -- `s_j < M_j`: `s = (2490/13)M_{j−1} < 208M_{j−1}`
  have hsM : (lvl μin j).s < (lvl μin (j + 1)).M := by
    rw [M_succ_eq]
    have := M_pos (μin := μin) j
    simp only [Level.s, Level.Δb]
    linarith
  have hK : (lvl μin j).K (μT μin (j + 1)) (R1T μin j) = (lvl μin j).dE (μT μin (j + 1)) +
      12 * (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) -
      13 * ϖ μin (j + 1) * ((lvl μin j).w (μT μin (j + 1)) / 2 -
        (lvl μin j).s * (R0 + R1T μin j) / 2) := by
    rw [Level.K, hϖ]
    ring
  have hbr : |(lvl μin j).w (μT μin (j + 1)) / 2 - (lvl μin j).s * (R0 + R1T μin j) / 2| ≤
      (lvl μin j).w (μT μin (j + 1)) / 2 + (lvl μin j).s * (1 + μT μin (j + 1)) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have h1 : |(lvl μin j).K (μT μin (j + 1)) (R1T μin j)| ≤ (lvl μin j).dE (μT μin (j + 1)) +
      12 * |(lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)| +
      13 * ϖ μin (j + 1) * ((lvl μin j).w (μT μin (j + 1)) / 2 +
        (lvl μin j).s * (1 + μT μin (j + 1)) / 2) := by
    rw [hK]
    set X := (lvl μin j).w (μT μin (j + 1)) / 2 - (lvl μin j).s * (R0 + R1T μin j) / 2
    set Fτ₁ := (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)
    have hA : |(lvl μin j).dE (μT μin (j + 1)) + 12 * Fτ₁| ≤
        (lvl μin j).dE (μT μin (j + 1)) + 12 * |Fτ₁| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hdE0, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
    have hB : |13 * ϖ μin (j + 1) * X| ≤ 13 * ϖ μin (j + 1) *
        ((lvl μin j).w (μT μin (j + 1)) / 2 + (lvl μin j).s * (1 + μT μin (j + 1)) / 2) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 13 * ϖ μin (j + 1))]
      exact mul_le_mul_of_nonneg_left hbr (by positivity)
    exact (abs_sub _ _).trans (add_le_add hA hB)
  refine ⟨h1, h1.trans ?_⟩
  -- `13ϖ_j w_j/2 = 2ϖ_jM_jμ_j ≤ 2Ω_j` and `13ϖ_j s_j(1 + μ_j)/2 ≤ (13/2)Ω_j`
  have hwM := w_eq_M (μin := μin) j
  have hΩ : Ω μin (j + 1) = ϖ μin (j + 1) * (lvl μin (j + 1)).M * (1 + μT μin (j + 1)) := rfl
  have h0 := μT_nonneg (μin := μin) (j + 1)
  have hM := M_pos (μin := μin) (j + 1)
  have e1 : 13 * ϖ μin (j + 1) * ((lvl μin j).w (μT μin (j + 1)) / 2) ≤ 2 * Ω μin (j + 1) := by
    rw [hwM, hΩ]
    have : 0 ≤ ϖ μin (j + 1) * (lvl μin (j + 1)).M := by positivity
    nlinarith
  have e2 : 13 * ϖ μin (j + 1) * ((lvl μin j).s * (1 + μT μin (j + 1)) / 2) ≤
      13 / 2 * Ω μin (j + 1) := by
    rw [hΩ]
    have : 0 ≤ ϖ μin (j + 1) * (1 + μT μin (j + 1)) := by positivity
    nlinarith
  nlinarith

/-- The proof of `lem:sizes`: "Then `|Δ_p^{(j)}| ≤ M_j(|F_{τ_2}^{(j)}| + |K_j| + d_j(E_j ∖ {b_j}) +
|F_{τ_1}^{(j)}|) ≤ 60M_jΩ_j`", at the step `j → j + 1`. -/
lemma sizes_Δp {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    |(lvl μin j).Δp (μT μin (j + 1)) (R1T μin j)| ≤ (lvl μin (j + 1)).M *
      (|(lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)| +
        |(lvl μin j).K (μT μin (j + 1)) (R1T μin j)| + (lvl μin j).dE (μT μin (j + 1)) +
        |(lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)|) ∧
    |(lvl μin j).Δp (μT μin (j + 1)) (R1T μin j)| ≤ 60 * ((lvl μin (j + 1)).M * Ω μin (j + 1)) := by
  obtain ⟨-, -, hdEk, hdE2, -, -, -, -⟩ := sizes_dE hF hj
  have hdE0 : 0 ≤ (lvl μin j).dE (μT μin (j + 1)) := (sizes_dE hF hj).2.1.trans hdEk
  obtain ⟨-, hτ₂, hτ₁⟩ := sizes_F hF hj
  obtain ⟨-, hK⟩ := sizes_K hF hj
  have hMj := M_pos (μin := μin) j
  have hM1 : (lvl μin (j + 1)).M = 208 * (lvl μin j).M := M_succ_eq j
  set Fτ₂ := (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)
  set Fτ₁ := (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)
  set K := (lvl μin j).K (μT μin (j + 1)) (R1T μin j)
  set dE := (lvl μin j).dE (μT μin (j + 1))
  set M := (lvl μin (j + 1)).M
  -- `m_δ ≤ M_j` and `m̄ ≤ M_j`
  have hmδ : 0 < (lvl μin j).mδ ∧ (lvl μin j).mδ ≤ M := by
    simp only [Level.mδ, M, hM1]
    constructor <;> linarith
  have hmbar : 0 < (lvl μin j).mbar ∧ (lvl μin j).mbar ≤ M := by
    simp only [Level.mbar, Level.mδ, Level.s, Level.Δb, M, hM1]
    constructor <;> linarith
  have hX : |K - dE + Fτ₁| ≤ |K| + dE + |Fτ₁| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self K, neg_abs_le K, le_abs_self Fτ₁, neg_abs_le Fτ₁]
  have h1 : |(lvl μin j).Δp (μT μin (j + 1)) (R1T μin j)| ≤ M * (|Fτ₂| + |K| + dE + |Fτ₁|) := by
    calc |(lvl μin j).Δp (μT μin (j + 1)) (R1T μin j)|
        = |(lvl μin j).mδ * Fτ₂ + (K - dE + Fτ₁) * (lvl μin j).mbar| := rfl
      _ ≤ |(lvl μin j).mδ * Fτ₂| + |(K - dE + Fτ₁) * (lvl μin j).mbar| := abs_add_le _ _
      _ = (lvl μin j).mδ * |Fτ₂| + |K - dE + Fτ₁| * (lvl μin j).mbar := by
          rw [abs_mul, abs_mul, abs_of_pos hmδ.1, abs_of_pos hmbar.1]
      _ ≤ M * |Fτ₂| + (|K| + dE + |Fτ₁|) * M :=
          add_le_add (mul_le_mul_of_nonneg_right hmδ.2 (abs_nonneg _))
            (mul_le_mul hX hmbar.2 hmbar.1.le (by positivity))
      _ = M * (|Fτ₂| + |K| + dE + |Fτ₁|) := by ring
  refine ⟨h1, h1.trans ?_⟩
  have hM : 0 < M := M_pos (j + 1)
  nlinarith

/-- The proof of `lem:sizes`: "`q_j ≤ ϖ_jM_j²` (`lem:weights`(c)) and
`|p_j| ≤ p_0 + ∑_{i≤j}|Δ_p^{(i)}| ≤ 10 + 120M_jΩ_j`", for the level `j + 1` with `j + 2 ≤ k`. -/
lemma sizes_p {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    0 < (lvl μin (j + 1)).q ∧ (lvl μin (j + 1)).q ≤ ϖ μin (j + 1) * (lvl μin (j + 1)).M ^ 2 ∧
    |(lvl μin (j + 1)).p| ≤
      10 + ∑ i ∈ range (j + 1), |(lvl μin i).Δp (μT μin (i + 1)) (R1T μin i)| ∧
    |(lvl μin (j + 1)).p| ≤ 10 + 120 * ((lvl μin (j + 1)).M * Ω μin (j + 1)) := by
  -- `p_{j+1} = p_0 + ∑_{i≤j} Δ_p^{(i)}` (P8)
  have hp : ∀ j, (lvl μin (j + 1)).p = 10 + ∑ i ∈ range (j + 1),
      (lvl μin i).Δp (μT μin (i + 1)) (R1T μin i) := by
    intro j
    induction j with
    | zero => show p₀ + _ = _; unfold p₀; simp
    | succ j ih =>
      show (lvl μin (j + 1)).p + _ = _
      rw [ih, sum_range_succ _ (j + 1)]
      ring
  have h1 : |(lvl μin (j + 1)).p| ≤
      10 + ∑ i ∈ range (j + 1), |(lvl μin i).Δp (μT μin (i + 1)) (R1T μin i)| := by
    rw [hp]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_pos (show (0 : ℝ) < 10 by norm_num)]
    gcongr
    exact abs_sum_le_sum_abs _ _
  refine ⟨q_pos (j + 1), ((weights_c (μin := μin)).2 j).2, h1, h1.trans ?_⟩
  -- `M_iΩ_i` more than doubles from level to level
  have hsum : ∑ i ∈ range (j + 1), 60 * ((lvl μin (i + 1)).M * Ω μin (i + 1)) ≤
      2 * (60 * ((lvl μin (j + 1)).M * Ω μin (j + 1))) := by
    have hnn : ∀ i, 0 ≤ 60 * ((lvl μin (i + 1)).M * Ω μin (i + 1)) := fun i => by
      have := M_pos (μin := μin) (i + 1)
      have := Ω_pos (μin := μin) (i + 1)
      positivity
    refine sum_le_two_mul (fun i _ => hnn i) fun i hi => ?_
    have hΩ := Ω_double hF (by omega : i + 2 < k)
    have hM := M_pos (μin := μin) (i + 1)
    have hΩ0 := Ω_pos (μin := μin) (i + 1)
    rw [M_succ_eq (i + 1)]
    nlinarith
  have hle : ∑ i ∈ range (j + 1), |(lvl μin i).Δp (μT μin (i + 1)) (R1T μin i)| ≤
      ∑ i ∈ range (j + 1), 60 * ((lvl μin (i + 1)).M * Ω μin (i + 1)) :=
    sum_le_sum fun i hi => (sizes_Δp hF (by have := mem_range.1 hi; omega)).2
  linarith

/-- The formula for `g_j` in the proof of `lem:sizes` (`def:tower`):
`g_j(S) = g_{j−1}(S ∩ E_{j−1}) + F_{τ_1}^{(j)}[τ_{1,j} ∈ S] + F_{τ_2}^{(j)}[τ_{2,j} ∈ S] +
[b_j ∈ S](K_j − d_j(S ∖ {b_j}))`, here for `g_{j+1}`, with `b_{j+1} = none`, `τ_{2,j+1} = some none`
and `τ_{1,j+1} = some (some none)`; `S ∩ E_j` is `S` with `none` erased three times. -/
lemma gT_succ_apply (j : ℕ) (S : Finset (Option (Option (Option (Gr j))))) :
    gT μin (j + 1) S = gT μin j (eraseNone (eraseNone (eraseNone S))) +
      (if some (some none) ∈ S then (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) else 0) +
      (if some none ∈ S then (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) else 0) +
      (if none ∈ S then (lvl μin j).K (μT μin (j + 1)) (R1T μin j) -
        ∑ e ∈ eraseNone S, (lvl μin j).dE' (μT μin (j + 1)) e else 0) := by
  have hd : ∀ e, (stepD μin j).dStep (mT μin j) (βT μin j) e = (lvl μin j).dE' (μT μin (j + 1)) e :=
    fun e => Level.dStep_eq _ _ _ e
  show (stepD μin j).gNew (gT μin j) (mT μin j) (βT μin j) S = _
  simp only [StepData.gNew, extend, StepData.fStep, addSingleton, subMod, mem_eraseNone, hd]
  split_ifs <;> simp [stepD] <;> ring

/-- `|f_0| ≤ 4/3` (`prop:base`: the values of `f_0` are `0, 1/3, 7/6, 2/3, 1, 4/3`). -/
lemma abs_f₀_le (S : Finset (Fin 3)) : |Base.f₀ S| ≤ 4 / 3 := by
  have : ∀ a b c : Bool, |Base.tab a b c| ≤ 4 / 3 := by
    intro a b c
    cases a <;> cases b <;> cases c <;> norm_num [Base.tab, abs_of_nonneg]
  exact this _ _ _

/-- The proof of `lem:sizes`: "we get `max_{S⊆E_j}|g_j(S)| ≤ 4/3 + ∑_{i≤j}(|F_{τ_1}^{(i)}| +
|F_{τ_2}^{(i)}| + |K_i| + d_i(E_i ∖ {b_i})) ≤ 2 + 114Ω_j`", for the level `j + 1` with
`j + 2 ≤ k`. -/
lemma sizes_g {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) (S : Finset (Gr (j + 1))) :
    |gT μin (j + 1) S| ≤ 4 / 3 + ∑ i ∈ range (j + 1),
      (|(lvl μin i).Fτ₁ (μT μin (i + 1)) (R1T μin i)| +
        |(lvl μin i).Fτ₂ (μT μin (i + 1)) (R1T μin i)| +
        |(lvl μin i).K (μT μin (i + 1)) (R1T μin i)| + (lvl μin i).dE (μT μin (i + 1))) ∧
    |gT μin (j + 1) S| ≤ 2 + 114 * Ω μin (j + 1) := by
  -- the recursion, with `d(S ∖ {b}) ≤ d(E_i ∖ {b_i})` as `d ≥ 0`
  have hrec : ∀ i (T : Finset (Gr i)), |gT μin i T| ≤ 4 / 3 + ∑ l ∈ range i,
      (|(lvl μin l).Fτ₁ (μT μin (l + 1)) (R1T μin l)| +
        |(lvl μin l).Fτ₂ (μT μin (l + 1)) (R1T μin l)| +
        |(lvl μin l).K (μT μin (l + 1)) (R1T μin l)| + (lvl μin l).dE (μT μin (l + 1))) := by
    intro i
    induction i with
    | zero =>
      intro T
      show |Base.f₀ T| ≤ _
      simpa using abs_f₀_le T
    | succ i ih =>
      intro T
      change Finset (Option (Option (Option (Gr i)))) at T
      rw [gT_succ_apply, sum_range_succ]
      have hsum : 0 ≤ ∑ e ∈ eraseNone T, (lvl μin i).dE' (μT μin (i + 1)) e :=
        sum_nonneg fun e _ => dE'_nonneg i e
      have hsum' : ∑ e ∈ eraseNone T, (lvl μin i).dE' (μT μin (i + 1)) e ≤
          (lvl μin i).dE (μT μin (i + 1)) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun e _ _ => dE'_nonneg i e
      have h1 := ih (eraseNone (eraseNone (eraseNone T)))
      set Fτ₁ := (lvl μin i).Fτ₁ (μT μin (i + 1)) (R1T μin i)
      set Fτ₂ := (lvl μin i).Fτ₂ (μT μin (i + 1)) (R1T μin i)
      set K := (lvl μin i).K (μT μin (i + 1)) (R1T μin i)
      have e1 : |(if some (some none) ∈ T then Fτ₁ else 0)| ≤ |Fτ₁| := by split_ifs <;> simp
      have e2 : |(if some none ∈ T then Fτ₂ else 0)| ≤ |Fτ₂| := by split_ifs <;> simp
      have e3 : |(if none ∈ T then K - ∑ e ∈ eraseNone T, (lvl μin i).dE' (μT μin (i + 1)) e
          else 0)| ≤ |K| + (lvl μin i).dE (μT μin (i + 1)) := by
        split_ifs
        · refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg hsum]
          linarith
        · simp only [abs_zero]
          linarith [abs_nonneg K, hsum.trans hsum']
      calc _ ≤ |gT μin i (eraseNone (eraseNone (eraseNone T)))| +
            |(if some (some none) ∈ T then Fτ₁ else 0)| + |(if some none ∈ T then Fτ₂ else 0)| +
            |(if none ∈ T then K - ∑ e ∈ eraseNone T, (lvl μin i).dE' (μT μin (i + 1)) e
              else 0)| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ _ := by linarith
  have h1 := hrec (j + 1) S
  refine ⟨h1, h1.trans ?_⟩
  -- each step adds at most `(3 + 2 + 50 + 2)Ω_i = 57Ω_i`, and `Ω_i` more than doubles
  have hstep : ∀ i ∈ range (j + 1),
      |(lvl μin i).Fτ₁ (μT μin (i + 1)) (R1T μin i)| +
        |(lvl μin i).Fτ₂ (μT μin (i + 1)) (R1T μin i)| +
        |(lvl μin i).K (μT μin (i + 1)) (R1T μin i)| + (lvl μin i).dE (μT μin (i + 1)) ≤
      57 * Ω μin (i + 1) := by
    intro i hi
    have hi' : i + 2 ≤ k := by have := mem_range.1 hi; omega
    obtain ⟨-, hτ₂, hτ₁⟩ := sizes_F hF hi'
    obtain ⟨-, hK⟩ := sizes_K hF hi'
    obtain ⟨-, -, -, hdE, -, -, -, -⟩ := sizes_dE hF hi'
    linarith
  have hsum : ∑ i ∈ range (j + 1), 57 * Ω μin (i + 1) ≤ 2 * (57 * Ω μin (j + 1)) :=
    sum_le_two_mul (fun i _ => by have := Ω_pos (μin := μin) (i + 1); positivity)
      fun i hi => by have := Ω_double hF (by omega : i + 2 < k); linarith
  linarith [sum_le_sum hstep]

/-- The curvatures (the proof of `lem:sizes`): "`1/β_e ∈ {1, 1/4} ∪ {(3/4)·8^i, 9·8^i : i ≥ 0}`",
with `i < j` for the elements of `E_j`: the base has `β = (1, 4, 4)`, and the step `i → i + 1` adds
`1/β_{τ_1} = 1/β_{τ_2} = (3/4)·8^i` and `1/β_b = 9·8^i` ((P2)). -/
lemma inv_βT_mem (j : ℕ) (e : Gr j) : 1 / βT μin j e = 1 ∨ 1 / βT μin j e = 1 / 4 ∨
    ∃ i < j, 1 / βT μin j e = 3 / 4 * 8 ^ i ∨ 1 / βT μin j e = 9 * 8 ^ i := by
  induction j with
  | zero =>
    change Fin 3 at e
    show 1 / Base.β e = 1 ∨ 1 / Base.β e = 1 / 4 ∨ _
    fin_cases e <;> simp [Base.β]
  | succ j ih =>
    change Option (Option (Option (Gr j))) at e
    have hβ : 1 / (lvl μin j).βδ = 3 / 4 * 8 ^ j := by rw [Level.inv_βδ, lvl_k]
    rcases e with _ | _ | _ | c
    · -- `b`: `1/β_b = 12/β_δ = 9·8^j`
      refine Or.inr (Or.inr ⟨j, Nat.lt_succ_self j, Or.inr ?_⟩)
      rw [βT_succ_none]
      unfold Level.βb
      rw [one_div_div, ← mul_one_div, hβ]
      ring
    · refine Or.inr (Or.inr ⟨j, Nat.lt_succ_self j, Or.inl ?_⟩)
      exact hβ
    · refine Or.inr (Or.inr ⟨j, Nat.lt_succ_self j, Or.inl ?_⟩)
      exact hβ
    · rcases ih c with h | h | ⟨i, hi, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨i, by omega, h⟩)

/-- The proof of `lem:sizes`: "every `1/β_e` is at most `12ϖ_j`" (level `j + 1`), and
`1/β_e ∈ (1/4)ℤ` ("`… ⊆ (1/4)ℤ`"); also `1/β_e > 0`. -/
lemma inv_βT_bounds (j : ℕ) (e : Gr (j + 1)) :
    0 < 1 / βT μin (j + 1) e ∧ 1 / βT μin (j + 1) e ≤ 12 * ϖ μin (j + 1) ∧
    InZ 4 (1 / βT μin (j + 1) e) := by
  have h8 : ∀ i, (1 : ℝ) ≤ 8 ^ i := fun i => one_le_pow₀ (by norm_num)
  rw [ϖ_succ]
  rcases inv_βT_mem (μin := μin) (j + 1) e with h | h | ⟨i, hi, h | h⟩ <;> rw [h]
  · exact ⟨by norm_num, by nlinarith [h8 j], ⟨4, by norm_num⟩⟩
  · exact ⟨by norm_num, by nlinarith [h8 j], ⟨1, by norm_num⟩⟩
  · have : (8 : ℝ) ^ i ≤ 8 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    exact ⟨by positivity, by nlinarith [h8 i], ⟨3 * 8 ^ i, by push_cast; ring⟩⟩
  · have : (8 : ℝ) ^ i ≤ 8 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    exact ⟨by positivity, by nlinarith [h8 i], ⟨36 * 8 ^ i, by push_cast; ring⟩⟩

/-! ### The denominators -/

variable (μin) in
/-- `1/δ = 3μ^in_1` (the proof of `lem:sizes`: "Here `1/δ = 3μ^in_1` is an integer"). -/
def dδ : ℕ := 3 * μin 0

variable (μin) in
/-- `𝔈_j = 600·13·415·208^{j−1}/δ` for `j ≥ 1` (the proof of `lem:sizes`; the value at `0` is
not used). -/
def 𝔈 : ℕ → ℕ
  | 0 => 1
  | j + 1 => 600 * 13 * 415 * 208 ^ j * dδ μin

variable (μin) in
/-- `𝔇_0 = 6` and `𝔇_j = 12𝔈_j` for `j ≥ 1` (the proof of `lem:sizes`). -/
def 𝔇 : ℕ → ℕ
  | 0 => 6
  | j + 1 => 12 * 𝔈 μin (j + 1)

variable (μin) in
/-- `𝔗_j = 3·8^{j−1}𝔈_j` for `j ≥ 1` (the proof of `lem:sizes`; the value at `0` is not used). -/
def 𝔗 : ℕ → ℕ
  | 0 => 1
  | j + 1 => 3 * 8 ^ j * 𝔈 μin (j + 1)

variable (μin) in
/-- `𝔓 = 200·13·6·415/δ` (the proof of `lem:sizes`). -/
def 𝔓 : ℕ := 200 * 13 * 6 * 415 * dδ μin

/-- `1/δ = 3μ^in_1` as a real number. -/
lemma dδ_cast : (dδ μin : ℝ) = 3 * μin 0 := by unfold dδ; push_cast; ring

/-- `𝔈_{j+1} = 600·13·415·208^j/δ` as a real number. -/
lemma 𝔈_cast (j : ℕ) : (𝔈 μin (j + 1) : ℝ) = 600 * 13 * 415 * 208 ^ j * (3 * μin 0) := by
  unfold 𝔈 dδ; push_cast; ring

/-- "`μ_j ∈ δℤ` for `j ≥ 0`": `μ_j/δ = μ^in_{j+1}`. -/
lemma μT_inZ {k : ℕ} (hF : InF μin k) (j : ℕ) : InZ (dδ μin) (μT μin j) := by
  have h0 : (0 : ℝ) < μin 0 := by exact_mod_cast μin0_pos hF
  refine ⟨μin j, ?_⟩
  rw [dδ_cast]
  unfold μT δT
  field_simp
  push_cast
  ring

/-- "All rewards … are integers" (`lem:weights`(b)). -/
lemma mT_inZ (j : ℕ) (e : Gr j) : InZ 1 (mT μin j e) := by
  obtain ⟨n, -, hv, -⟩ := (weights_b (μin := μin)).1 j e
  rw [hv]
  exact InZ.nat n

/-- "`M_j = 12·208^j`" (the proof of `lem:sizes`, by `lem:weights`(b)). -/
lemma M_eq (j : ℕ) : (lvl μin j).M = 12 * 208 ^ j := (weights_b (μin := μin)).2.1 j

/-- "`Δ_j = 2490·208^{j−1}`" (before `lem:weights`), here for the step `j → j + 1`. -/
lemma Δb_eq (j : ℕ) : (lvl μin j).Δb = 2490 * 208 ^ j := by
  simp only [Level.Δb, M_eq]
  ring

/-- "… and `ϖ_jΔ_j²` are integers, `ϖ_jΔ_j ∈ (1/2)ℤ`, …", and `ϖ_j ∈ (1/4)ℤ` ("`… ⊆ (1/4)ℤ`"),
at the step `j → j + 1`. -/
lemma ϖΔ_inZ (j : ℕ) : InZ 1 (ϖ μin (j + 1) * (lvl μin j).Δb ^ 2) ∧
    InZ 2 (ϖ μin (j + 1) * (lvl μin j).Δb) ∧ InZ 4 (ϖ μin (j + 1)) := by
  rw [ϖ_succ, Δb_eq]
  refine ⟨⟨3 * 1550025 * 8 ^ j * 208 ^ (2 * j), ?_⟩, ⟨3735 * 1664 ^ j, ?_⟩, ⟨3 * 8 ^ j, ?_⟩⟩ <;>
    push_cast <;> ring_nf
  rw [← mul_pow]
  norm_num

/-- `x ∈ (1/a)ℤ ⊆ (1/b)ℤ` when `a ∣ b` in `ℕ` (not in the paper). -/
lemma InZ.mono_nat {a b : ℕ} {x : ℝ} (hx : InZ a x) (h : a ∣ b) : InZ b x := by
  obtain ⟨c, rfl⟩ := h
  exact hx.mono c (by push_cast; ring)

/-- `InZ.mono_nat` for a denominator written as a real expression `N = a` (not in the paper). -/
lemma InZ.mono_cast {a b : ℕ} {N x : ℝ} (hx : InZ N x) (hN : N = a) (h : a ∣ b) : InZ b x :=
  InZ.mono_nat (hN ▸ hx) h

/-- `R_0 + R_1^{(j)} = 1 + ∑_{1≤i≤j} μ_i ∈ δℤ` (the proof of `lem:sizes`:
"`R_0 + R_1^{(j−1)} = 1 + ∑_{1≤i<j} μ_i ∈ δℤ`"). -/
lemma R0_add_R1_eq {k : ℕ} (hF : InF μin k) (j : ℕ) :
    R0 + R1T μin j = 1 + ∑ i ∈ range j, μT μin (i + 1) ∧ InZ (dδ μin) (R0 + R1T μin j) := by
  have h0 := μin0_pos hF
  have hR : R0 + R1T μin j = 1 + ∑ i ∈ range j, μT μin (i + 1) := by
    unfold R1T
    rw [sum_range_succ', μT_zero h0, R0_eq]
    unfold ζ₁ ε₀
    ring
  refine ⟨hR, ?_⟩
  rw [hR]
  refine InZ.add ⟨3 * μin 0, by rw [dδ_cast]; push_cast; ring⟩ (InZ.sum fun i _ => μT_inZ hF _)

/-- The list of the proof of `lem:sizes`, at the step `j → j + 1` (to the level `j + 1`):
"`w_j, m_{*,j}μ_j ∈ δℤ`, and `d_e` for `e ∈ E_j ∖ {b_j}`, `d_j(E_{j−1})`, `d_j(E_j ∖ {b_j})` and
`Π` lie in `(δ/4)ℤ`. `s_j, m̄, ψ_j, q_j ∈ (1/13)ℤ`, as `13s_j = 12Δ_j`.
`ΔF_j ∈ (δ/(48·2490·208^{j−1}))ℤ` by (P5), as `1/s_j = 13/(12Δ_j)`. `a_2 ∈ (δ/130)ℤ`, as
`μ_j − |𝓡_{j−1}|/2 ∈ (δ/10)ℤ` by `1/15 = (1/5)δμ^in_1`." -/
lemma sizes_items {k : ℕ} (hF : InF μin k) (j : ℕ) :
    InZ (dδ μin) ((lvl μin j).w (μT μin (j + 1))) ∧
    InZ (dδ μin) ((lvl μin j).mstar * μT μin (j + 1)) ∧
    (∀ e, InZ (4 * dδ μin) ((lvl μin j).dE' (μT μin (j + 1)) e)) ∧
    InZ (4 * dδ μin) ((lvl μin j).dEk (μT μin (j + 1))) ∧
    InZ (4 * dδ μin) ((lvl μin j).dE (μT μin (j + 1))) ∧
    InZ (4 * dδ μin) ((lvl μin j).Pcal (μT μin (j + 1))) ∧
    InZ 13 (lvl μin j).s ∧ InZ 13 (lvl μin j).mbar ∧ InZ 13 (lvl μin j).ψ ∧
    InZ 13 (lvl μin (j + 1)).q ∧
    InZ (48 * 2490 * 208 ^ j * dδ μin) ((lvl μin j).ΔF (μT μin (j + 1))) ∧
    InZ (130 * dδ μin) (Level.a2 (μT μin (j + 1)) (R1T μin j)) := by
  have hμ := μT_inZ hF (j + 1)
  have hM := M_eq (μin := μin) j
  obtain ⟨hϖΔ2, hϖΔ, hϖ⟩ := ϖΔ_inZ (μin := μin) j
  have hϖ' : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
  -- `w = 64Mμ` and `m_*μ = (129/2)Mμ` with `64M, (129/2)M ∈ ℤ`
  have hw : InZ (dδ μin) ((lvl μin j).w (μT μin (j + 1))) := by
    have : (lvl μin j).w (μT μin (j + 1)) = ((768 * 208 ^ j : ℕ) : ℤ) * μT μin (j + 1) := by
      simp only [Level.w, hM]; push_cast; ring
    rw [this]
    exact hμ.zmul _
  have hms : InZ (dδ μin) ((lvl μin j).mstar * μT μin (j + 1)) := by
    have : (lvl μin j).mstar * μT μin (j + 1) = ((774 * 208 ^ j : ℕ) : ℤ) * μT μin (j + 1) := by
      simp only [Level.mstar, Level.mδ, hM]; push_cast; ring
    rw [this]
    exact hμ.zmul _
  -- `d_e = μ(m_* − m_e)(1/β_e)` with `m_* − m_e ∈ ℤ`, `1/β_e ∈ (1/4)ℤ`; `d_{τ_1} = d_{τ_2} = wϖ`
  have hdc : ∀ c, InZ (4 * dδ μin) ((lvl μin j).d (μT μin (j + 1)) c) := by
    intro c
    obtain ⟨n, -, hv, -⟩ := (weights_b (μin := μin)).1 j c
    have hβ : InZ 4 (1 / βT μin j c) := by
      rcases j with _ | j
      · rcases inv_βT_mem (μin := μin) 0 c with h | h | ⟨i, hi, -⟩
        · rw [h]; exact ⟨4, by norm_num⟩
        · rw [h]; exact ⟨1, by norm_num⟩
        · omega
      · exact (inv_βT_bounds (μin := μin) j c).2.2
    have hm : InZ 1 ((lvl μin j).mstar - (lvl μin j).m c) := by
      have : (lvl μin j).mstar - (lvl μin j).m c = ((774 * 208 ^ j : ℕ) : ℤ) - ((n : ℕ) : ℤ) := by
        simp only [Level.mstar, Level.mδ, hM]
        change _ - mT μin j c = _
        rw [hv]
        push_cast
        ring
      rw [this]
      exact ⟨((774 * 208 ^ j : ℕ) : ℤ) - n, by push_cast; ring⟩
    have := (hμ.mul hm).mul hβ
    refine this.mono 1 (by push_cast; ring) |>.of_eq ?_
    unfold Level.d
    rw [mul_one_div]
    rfl
  have hdτ₁ : InZ (4 * dδ μin) ((lvl μin j).w (μT μin (j + 1)) / (lvl μin j).βδ) := by
    refine (hw.mul hϖ).mono 1 (by ring) |>.of_eq ?_
    rw [hϖ']
    ring
  have hdE' : ∀ e, InZ (4 * dδ μin) ((lvl μin j).dE' (μT μin (j + 1)) e) := by
    rintro (_ | _ | c)
    · exact hdτ₁
    · exact hdτ₁
    · exact hdc c
  have hdEk : InZ (4 * dδ μin) ((lvl μin j).dEk (μT μin (j + 1))) := InZ.sum fun c _ => hdc c
  have hdE : InZ (4 * dδ μin) ((lvl μin j).dE (μT μin (j + 1))) := InZ.sum fun e _ => hdE' e
  have hPi : InZ (4 * dδ μin) ((lvl μin j).Pcal (μT μin (j + 1))) := by
    refine InZ.sum fun c _ => ?_
    obtain ⟨n, -, hv, -⟩ := (weights_b (μin := μin)).1 j c
    have : (lvl μin j).mδ - (lvl μin j).m c = ((6 * 208 ^ j : ℕ) : ℤ) - ((n : ℕ) : ℤ) := by
      simp only [Level.mδ, hM]
      change _ - mT μin j c = _
      rw [hv]
      push_cast
      ring
    rw [this]
    exact ((hdc c).zmul (((6 * 208 ^ j : ℕ) : ℤ) - n)).of_eq (by push_cast; ring)
  -- `13s = 12Δ_b`, `13m̄ = 13m_δ + 12Δ_b`, `13ψ = 12ϖΔ_b²`, and `q_{j+1} = q_0 + ∑ψ`
  have hs : InZ 13 (lvl μin j).s :=
    ⟨12 * 2490 * 208 ^ j, by simp only [Level.s, Δb_eq]; push_cast; ring⟩
  have hmbar : InZ 13 (lvl μin j).mbar :=
    ⟨13 * 6 * 208 ^ j + 12 * 2490 * 208 ^ j, by
      simp only [Level.mbar, Level.mδ, Level.s, Δb_eq, hM]; push_cast; ring⟩
  have hψ : ∀ i, InZ 13 (lvl μin i).ψ := by
    intro i
    obtain ⟨z, hz⟩ := (ϖΔ_inZ (μin := μin) i).1
    refine ⟨12 * z, ?_⟩
    have hϖi : ϖ μin (i + 1) = 1 / (lvl μin i).βδ := rfl
    push_cast
    rw [← hz, hϖi]
    simp only [Level.ψ]
    ring
  have hq : ∀ i, InZ 13 (lvl μin i).q := by
    intro i
    induction i with
    | zero => exact ⟨91, by show (13 : ℝ) * q₀ = _; unfold q₀; norm_num⟩
    | succ i ih => rw [q_succ]; exact ih.add (hψ i)
  -- `ΔF = w/β_δ + d(E_j) − 13(q_jμ − Π)/(12Δ_b)`
  have hΔF : InZ (48 * 2490 * 208 ^ j * dδ μin) ((lvl μin j).ΔF (μT μin (j + 1))) := by
    have hqμ : InZ (13 * dδ μin) ((lvl μin j).q * μT μin (j + 1)) := (hq j).mul hμ
    have h52 : InZ (52 * dδ μin) ((lvl μin j).q * μT μin (j + 1) -
        (lvl μin j).Pcal (μT μin (j + 1))) :=
      (hqμ.mono 4 (by ring)).sub (hPi.mono 13 (by ring))
    have h3 : InZ (4 * dδ μin) (13 * ((lvl μin j).q * μT μin (j + 1) -
        (lvl μin j).Pcal (μT μin (j + 1)))) := by
      obtain ⟨z, hz⟩ := h52
      exact ⟨z, by rw [← hz]; ring⟩
    have h4 := h3.div_int (12 * 2490 * 208 ^ j) (by positivity)
    have e : (lvl μin j).ΔF (μT μin (j + 1)) =
        (lvl μin j).w (μT μin (j + 1)) / (lvl μin j).βδ + (lvl μin j).dEk (μT μin (j + 1)) -
        13 * ((lvl μin j).q * μT μin (j + 1) - (lvl μin j).Pcal (μT μin (j + 1))) /
          ((12 * 2490 * 208 ^ j : ℤ) : ℝ) := by
      simp only [Level.ΔF, Level.s, Δb_eq]
      push_cast
      field_simp
      ring
    rw [e]
    have hN : (48 * 2490 * 208 ^ j * dδ μin : ℝ) =
        ((12 * 2490 * 208 ^ j : ℤ) : ℝ) * (4 * dδ μin) := by push_cast; ring
    refine ((hdτ₁.add hdEk).mono (12 * 2490 * 208 ^ j) hN).sub (h4.mono 1 ?_)
    rw [hN]; push_cast; ring
  -- `a_2 = (12/13)(μ − |𝓡|/2)` with `|𝓡| = ∑_{i≤j} μ_i + 1/15` and `1/15 = (1/5)δμ^in_1`
  have ha2 : InZ (130 * dδ μin) (Level.a2 (μT μin (j + 1)) (R1T μin j)) := by
    have h15 : InZ (5 * dδ μin) (1 / 15 : ℝ) := ⟨μin 0, by rw [dδ_cast]; push_cast; ring⟩
    have hlen : InZ (5 * dδ μin) (lenR μin j) := by
      rw [lenR_eq]
      exact (InZ.sum fun i _ => (μT_inZ hF i).mono 5 (by ring)).add h15
    obtain ⟨a, ha⟩ := hμ
    obtain ⟨b, hb⟩ := hlen
    refine ⟨120 * a - 12 * b, ?_⟩
    have : R1T μin j - R0 = lenR μin j := rfl
    simp only [Level.a2, this]
    push_cast
    rw [← ha, ← hb]
    ring
  exact ⟨hw, hms, hdE', hdEk, hdE, hPi, hs, hmbar, hψ j, hq (j + 1), hΔF, ha2⟩

/-- `(*)` of the proof of `lem:sizes`: "By (P6), with `ϖ_j d̄_j w_j = d_j(E_{j−1})` and
`ϖ_j a_0 = q_{j−1}μ_j − Π`,
`F_{τ_2}^{(j)} = ϖ_jR_0m_δ^{(j)} − ϖ_jρ̄_{j−1} − (3/2)ϖ_jw_j + ϖ_ja_2Δ_j −
d_j(E_{j−1}) + (q_{j−1}μ_j − Π)/Δ_j − ϖ_js_jι`", at the step `j → j + 1`. -/
lemma Fτ₂_star {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    ϖ μin (j + 1) * (lvl μin j).dbar (μT μin (j + 1)) * (lvl μin j).w (μT μin (j + 1)) =
      (lvl μin j).dEk (μT μin (j + 1)) ∧
    ϖ μin (j + 1) * (lvl μin j).a0 (μT μin (j + 1)) =
      (lvl μin j).q * μT μin (j + 1) - (lvl μin j).Pcal (μT μin (j + 1)) ∧
    (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) =
      ϖ μin (j + 1) * R0 * (lvl μin j).mδ - ϖ μin (j + 1) * (lvl μin j).ρbar -
        3 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) +
        ϖ μin (j + 1) * Level.a2 (μT μin (j + 1)) (R1T μin j) * (lvl μin j).Δb -
        (lvl μin j).dEk (μT μin (j + 1)) +
        ((lvl μin j).q * μT μin (j + 1) - (lvl μin j).Pcal (μT μin (j + 1))) / (lvl μin j).Δb -
        ϖ μin (j + 1) * (lvl μin j).s * ι := by
  have hw := (w_pos (μin := μin) (μT_pos hF (by omega : j + 1 < k))).ne'
  have hβ := (lvl μin j).βδ_pos.ne'
  have hΔ : (lvl μin j).Δb ≠ 0 := by rw [Δb_eq]; positivity
  have hϖ : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
  have h1 : ϖ μin (j + 1) * (lvl μin j).dbar (μT μin (j + 1)) * (lvl μin j).w (μT μin (j + 1)) =
      (lvl μin j).dEk (μT μin (j + 1)) := by
    rw [hϖ, Level.dbar]
    field_simp
  have h2 : ϖ μin (j + 1) * (lvl μin j).a0 (μT μin (j + 1)) =
      (lvl μin j).q * μT μin (j + 1) - (lvl μin j).Pcal (μT μin (j + 1)) := by
    rw [hϖ, Level.a0]
    field_simp
  refine ⟨h1, h2, ?_⟩
  -- (P6): `F_{τ_2} = ϖ(R_0m_δ − ρ̄ − w + u^0 − sι)` with `u^0 = a_2Δ_b − (1/2 + d̄)w + a_0/Δ_b`
  have hFτ₂ : (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) = ϖ μin (j + 1) *
      (R0 * (lvl μin j).mδ - (lvl μin j).ρbar - (lvl μin j).w (μT μin (j + 1)) +
        (lvl μin j).u0 (μT μin (j + 1)) (R1T μin j) - (lvl μin j).s * ι) := by
    rw [Level.Fτ₂, hϖ]
    ring
  rw [hFτ₂, Level.u0]
  have e1 : ϖ μin (j + 1) * ((1 / 2 + (lvl μin j).dbar (μT μin (j + 1))) *
      (lvl μin j).w (μT μin (j + 1))) = 1 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) +
        (lvl μin j).dEk (μT μin (j + 1)) := by
    rw [← h1]
    ring
  have e2 : ϖ μin (j + 1) * ((lvl μin j).a0 (μT μin (j + 1)) / (lvl μin j).Δb) =
      ((lvl μin j).q * μT μin (j + 1) - (lvl μin j).Pcal (μT μin (j + 1))) / (lvl μin j).Δb := by
    rw [← h2]
    ring
  linear_combination e2 - e1

/-- The proof of `lem:sizes`: "where `ϖ_1ρ̄_0 = 7/8` and
`ϖ_jρ̄_{j−1} = ϖ_jR_0m_δ^{(j−1)} − 8F_{τ_2}^{(j−1)}` for `j ≥ 2`", here for the level `j + 2`. -/
lemma ϖ_ρbar (j : ℕ) : ϖ μin 1 * (lvl μin 0).ρbar = 7 / 8 ∧
    ϖ μin (j + 2) * (lvl μin (j + 1)).ρbar = ϖ μin (j + 2) * R0 * (lvl μin j).mδ -
      8 * (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) := by
  refine ⟨by rw [ϖ_succ, ρbar_zero]; norm_num, ?_⟩
  show ϖ μin (j + 2) * (R0 * (lvl μin j).mδ -
    (lvl μin j).βδ * (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)) = _
  have h8 : ϖ μin (j + 2) * (lvl μin j).βδ = 8 := by
    rw [ϖ_succ]
    simp only [Level.βδ, lvl_k]
    field_simp
    ring
  linear_combination (-(lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)) * h8

/-- The seven terms of `(*)` at the step `j → j + 1`, except the second (`ϖρ̄`, which `ϖ_ρbar`
splits): "The seven terms lie in `(1/40)ℤ`, in `(1/8)ℤ` or `(1/40)ℤ + (1/𝔈_{j−1})ℤ`, in `(δ/8)ℤ`,
`(δ/260)ℤ`, `(δ/4)ℤ`, `(δ/(312·415·208^{j−1}))ℤ` and `(1/1300)ℤ`." -/
lemma Fτ₂_terms {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    InZ 40 (ϖ μin (j + 1) * R0 * (lvl μin j).mδ) ∧
    InZ 40 (ϖ μin (j + 2) * R0 * (lvl μin j).mδ) ∧
    InZ (8 * dδ μin) (3 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1))) ∧
    InZ (260 * dδ μin) (ϖ μin (j + 1) * Level.a2 (μT μin (j + 1)) (R1T μin j) * (lvl μin j).Δb) ∧
    InZ (4 * dδ μin) ((lvl μin j).dEk (μT μin (j + 1))) ∧
    InZ (312 * 415 * 208 ^ j * dδ μin)
      (((lvl μin j).q * μT μin (j + 1) - (lvl μin j).Pcal (μT μin (j + 1))) / (lvl μin j).Δb) ∧
    InZ 1300 (ϖ μin (j + 1) * (lvl μin j).s * ι) := by
  obtain ⟨hw, -, -, hdEk, -, hPi, hs, -, -, -, -, ha2⟩ := sizes_items hF j
  obtain ⟨-, hϖΔ, hϖ⟩ := ϖΔ_inZ (μin := μin) j
  have hq := (sizes_items hF (j - 1)).2.2.2.2.2.2.2.2.2.1
  have hqj : InZ 13 (lvl μin j).q := by
    rcases j with _ | j
    · exact ⟨91, by show (13 : ℝ) * q₀ = _; unfold q₀; norm_num⟩
    · simpa using hq
  have hM := M_eq (μin := μin) j
  refine ⟨⟨54 * 1664 ^ j, ?_⟩, ⟨432 * 1664 ^ j, ?_⟩, ?_, ?_, hdEk, ?_, ⟨22410 * 1664 ^ j, ?_⟩⟩
  · rw [ϖ_succ, R0_eq]
    simp only [Level.mδ, hM]
    push_cast
    rw [show (1664 : ℝ) ^ j = 8 ^ j * 208 ^ j by rw [← mul_pow]; norm_num]
    ring
  · rw [ϖ_succ, R0_eq]
    simp only [Level.mδ, hM]
    push_cast
    rw [show (1664 : ℝ) ^ j = 8 ^ j * 208 ^ j by rw [← mul_pow]; norm_num]
    ring
  · obtain ⟨z, hz⟩ := hϖ.mul hw
    exact ⟨3 * z, by push_cast; rw [← hz]; ring⟩
  · obtain ⟨z, hz⟩ := hϖΔ.mul ha2
    exact ⟨z, by rw [← hz]; ring⟩
  · have h52 : InZ (52 * dδ μin) ((lvl μin j).q * μT μin (j + 1) -
        (lvl μin j).Pcal (μT μin (j + 1))) :=
      ((hqj.mul (μT_inZ hF (j + 1))).mono 4 (by ring)).sub (hPi.mono 13 (by ring))
    have := h52.div_int (2490 * 208 ^ j) (by positivity)
    rw [Δb_eq]
    refine (this.mono 1 (by push_cast; ring)).of_eq ?_
    push_cast
    ring
  · rw [ϖ_succ]
    simp only [Level.s, Δb_eq, ι]
    push_cast
    rw [show (1664 : ℝ) ^ j = 8 ^ j * 208 ^ j by rw [← mul_pow]; norm_num]
    ring

/-- The divisibilities behind "so all of them lie in `(1/𝔈_j)ℤ`" (the proof of `lem:sizes`): the
denominators of the terms of `(*)` divide `𝔈_{j+1}`, and `𝔈_{j+1} ∣ 𝔈_{j+2}` (not in the paper). -/
lemma dvd_𝔈 (j : ℕ) : 40 ∣ 𝔈 μin (j + 1) ∧ 8 ∣ 𝔈 μin (j + 1) ∧ 8 * dδ μin ∣ 𝔈 μin (j + 1) ∧
    260 * dδ μin ∣ 𝔈 μin (j + 1) ∧ 4 * dδ μin ∣ 𝔈 μin (j + 1) ∧
    312 * 415 * 208 ^ j * dδ μin ∣ 𝔈 μin (j + 1) ∧ 1300 ∣ 𝔈 μin (j + 1) ∧
    𝔈 μin (j + 1) ∣ 𝔈 μin (j + 2) := by
  unfold 𝔈
  refine ⟨⟨15 * 13 * 415 * 208 ^ j * dδ μin, by ring⟩, ⟨75 * 13 * 415 * 208 ^ j * dδ μin, by ring⟩,
    ⟨75 * 13 * 415 * 208 ^ j, by ring⟩, ⟨30 * 415 * 208 ^ j, by ring⟩,
    ⟨150 * 13 * 415 * 208 ^ j, by ring⟩, ⟨25, by ring⟩, ⟨6 * 415 * 208 ^ j * dδ μin, by ring⟩,
    ⟨208, by ring⟩⟩

/-- The proof of `lem:sizes`: "so all of them lie in `(1/𝔈_j)ℤ`. By induction on `j`,
`F_{τ_2}^{(j)} ∈ (1/𝔈_j)ℤ`, and then `F_{τ_1}^{(j)} = F_{τ_2}^{(j)} + ΔF_j ∈ (1/𝔇_j)ℤ`", at the step
`j → j + 1`. -/
lemma sizes_Fτ₂_den {k : ℕ} (hF : InF μin k) : ∀ j, j + 2 ≤ k →
    InZ (𝔈 μin (j + 1)) ((lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)) ∧
    InZ (𝔇 μin (j + 1)) ((lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)) := by
  have hFτ₂ : ∀ j, j + 2 ≤ k →
      InZ (𝔈 μin (j + 1)) ((lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j)) := by
    intro j hj
    induction j with
    | zero =>
      obtain ⟨t1, -, t3, t4, t5, t6, t7⟩ := Fτ₂_terms hF hj
      obtain ⟨d40, d8, d8δ, d260, d4, d312, d1300, -⟩ := dvd_𝔈 (μin := μin) 0
      have t2 : InZ 8 (ϖ μin (0 + 1) * (lvl μin 0).ρbar) := ⟨7, by rw [(ϖ_ρbar 0).1]; norm_num⟩
      rw [(Fτ₂_star hF hj).2.2]
      exact (((((((t1.mono_cast (by norm_num) d40).sub (t2.mono_cast (by norm_num) d8)).sub
        (t3.mono_cast (by push_cast; ring) d8δ)).add (t4.mono_cast (by push_cast; ring) d260)).sub
        (t5.mono_cast (by push_cast; ring) d4)).add (t6.mono_cast (by push_cast; ring) d312)).sub
        (t7.mono_cast (by norm_num) d1300))
    | succ j ih =>
      have ih' := ih (by omega)
      obtain ⟨t1, -, t3, t4, t5, t6, t7⟩ := Fτ₂_terms hF hj
      obtain ⟨-, t2a, -, -, -, -, -⟩ := Fτ₂_terms hF (by omega : j + 2 ≤ k)
      obtain ⟨d40, -, d8δ, d260, d4, d312, d1300, -⟩ := dvd_𝔈 (μin := μin) (j + 1)
      obtain ⟨d40', -, -, -, -, -, -, dE⟩ := dvd_𝔈 (μin := μin) j
      -- `ϖ_{j+2}ρ̄_{j+1} = ϖ_{j+2}R_0m_δ − 8F_{τ_2} ∈ (1/40)ℤ + (1/𝔈_{j+1})ℤ`
      have t2 : InZ (𝔈 μin (j + 2)) (ϖ μin (j + 2) * (lvl μin (j + 1)).ρbar) := by
        rw [(ϖ_ρbar j).2]
        exact (t2a.mono_cast (by norm_num) (dvd_trans d40' dE)).sub ((ih'.zmul 8).mono_nat dE)
      rw [(Fτ₂_star hF hj).2.2]
      exact (((((((t1.mono_cast (by norm_num) d40).sub t2).sub
        (t3.mono_cast (by push_cast; ring) d8δ)).add (t4.mono_cast (by push_cast; ring) d260)).sub
        (t5.mono_cast (by push_cast; ring) d4)).add (t6.mono_cast (by push_cast; ring) d312)).sub
        (t7.mono_cast (by norm_num) d1300))
  intro j hj
  refine ⟨hFτ₂ j hj, ?_⟩
  have hΔF := (sizes_items hF j).2.2.2.2.2.2.2.2.2.2.1
  rw [Level.Fτ₁]
  refine ((hFτ₂ j hj).mono_nat ⟨12, by unfold 𝔇; ring⟩).add
    (hΔF.mono_cast (a := 48 * 2490 * 208 ^ j * dδ μin) (by push_cast; ring) ⟨325, ?_⟩)
  unfold 𝔇 𝔈
  ring

/-- The proof of `lem:sizes`: "By (P7),
`K_j = d_j(E_j ∖ {b_j}) + 12F_{τ_1}^{(j)} − (13/2)ϖ_jw_j + 6ϖ_jΔ_j(R_0 + R_1^{(j−1)})`, with
`R_0 + R_1^{(j−1)} = 1 + ∑_{1≤i<j} μ_i ∈ δℤ`, so `K_j ∈ (1/𝔇_j)ℤ`", at the step `j → j + 1`. -/
lemma sizes_K_den {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    (lvl μin j).K (μT μin (j + 1)) (R1T μin j) = (lvl μin j).dE (μT μin (j + 1)) +
      12 * (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) -
      13 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) +
      6 * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j) ∧
    InZ (𝔇 μin (j + 1)) ((lvl μin j).K (μT μin (j + 1)) (R1T μin j)) := by
  have hϖ : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
  have hK : (lvl μin j).K (μT μin (j + 1)) (R1T μin j) = (lvl μin j).dE (μT μin (j + 1)) +
      12 * (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) -
      13 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) +
      6 * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j) := by
    rw [Level.K, hϖ]
    simp only [Level.s]
    ring
  refine ⟨hK, ?_⟩
  obtain ⟨hw, -, -, -, hdE, -⟩ := sizes_items hF j
  obtain ⟨-, ⟨b, hb⟩, hϖ4⟩ := ϖΔ_inZ (μin := μin) j
  obtain ⟨-, hFτ₁⟩ := sizes_Fτ₂_den hF j hj
  obtain ⟨-, hR⟩ := R0_add_R1_eq hF j
  rw [hK]
  have d1 : InZ (𝔇 μin (j + 1)) ((lvl μin j).dE (μT μin (j + 1))) :=
    hdE.mono_cast (a := 4 * dδ μin) (by push_cast; ring)
      ⟨3 * 600 * 13 * 415 * 208 ^ j, by unfold 𝔇 𝔈; ring⟩
  have d3 : InZ (𝔇 μin (j + 1)) (13 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1))) := by
    obtain ⟨z, hz⟩ := hϖ4.mul hw
    have h8 : InZ (8 * dδ μin) (13 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1))) :=
      ⟨13 * z, by push_cast; rw [← hz]; ring⟩
    exact h8.mono_cast (a := 8 * dδ μin) (by push_cast; ring)
      ⟨900 * 13 * 415 * 208 ^ j, by unfold 𝔇 𝔈; ring⟩
  have d4 : InZ (𝔇 μin (j + 1)) (6 * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j)) := by
    obtain ⟨c, hc⟩ := hR
    have h1 : InZ (dδ μin) (6 * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j)) :=
      ⟨3 * b * c, by push_cast; rw [← hb, ← hc]; ring⟩
    exact h1.mono_nat ⟨12 * 600 * 13 * 415 * 208 ^ j, by unfold 𝔇 𝔈; ring⟩
  exact ((d1.add (hFτ₁.zmul 12)).sub d3).add d4

/-- `𝔇_j ∣ 𝔇_{j+1}`, for the induction on `j` in `sizes_g_den` (not in the paper). -/
lemma 𝔇_dvd_succ (j : ℕ) : 𝔇 μin j ∣ 𝔇 μin (j + 1) := by
  rcases j with _ | j
  · exact ⟨2 * 600 * 13 * 415 * dδ μin, by unfold 𝔇 𝔈; ring⟩
  · exact ⟨208, by unfold 𝔇 𝔈; ring⟩

/-- The proof of `lem:sizes`: "By the formula for `g_j` above and induction on `j`, starting from
the base values in `(1/6)ℤ = (1/𝔇_0)ℤ`, every value of `g_j` lies in `(1/𝔇_j)ℤ`", for the levels
`j ≤ k − 1`. -/
lemma sizes_g_den {k : ℕ} (hF : InF μin k) : ∀ j, j + 1 ≤ k → ∀ S, InZ (𝔇 μin j) (gT μin j S) := by
  intro j hj
  induction j with
  | zero =>
    intro S
    show InZ 6 (Base.f₀ S)
    have : ∀ a b c : Bool, InZ 6 (Base.tab a b c) := by
      intro a b c
      cases a <;> cases b <;> cases c
      exacts [⟨0, by norm_num [Base.tab]⟩, ⟨4, by norm_num [Base.tab]⟩, ⟨7, by norm_num [Base.tab]⟩,
        ⟨8, by norm_num [Base.tab]⟩, ⟨2, by norm_num [Base.tab]⟩, ⟨6, by norm_num [Base.tab]⟩,
        ⟨7, by norm_num [Base.tab]⟩, ⟨8, by norm_num [Base.tab]⟩]
    exact this _ _ _
  | succ j ih =>
    intro S
    change Finset (Option (Option (Option (Gr j)))) at S
    have hj' : j + 2 ≤ k := by omega
    obtain ⟨hFτ₂, hFτ₁⟩ := sizes_Fτ₂_den hF j hj'
    obtain ⟨-, hK⟩ := sizes_K_den hF hj'
    obtain ⟨-, -, hdE', -⟩ := sizes_items hF j
    have hd : ∀ e, InZ (𝔇 μin (j + 1)) ((lvl μin j).dE' (μT μin (j + 1)) e) := fun e =>
      (hdE' e).mono_cast (a := 4 * dδ μin) (by push_cast; ring)
        ⟨3 * 600 * 13 * 415 * 208 ^ j, by unfold 𝔇 𝔈; ring⟩
    have hite : ∀ (P : Prop) [Decidable P] {x : ℝ}, InZ (𝔇 μin (j + 1)) x →
        InZ (𝔇 μin (j + 1)) (if P then x else 0) := by
      intro P _ x hx
      split_ifs
      exacts [hx, InZ.zero]
    rw [gT_succ_apply]
    exact ((((ih (by omega) _).mono_nat (𝔇_dvd_succ j)).add (hite _ hFτ₁)).add
      (hite _ (hFτ₂.mono_nat ⟨12, by unfold 𝔇; ring⟩))).add
      (hite _ (hK.sub (InZ.sum fun e _ => hd e)))

/-- `(†)` of the proof of `lem:sizes`: "Next, (P7) gives
`K_j − d_j(E_j ∖ {b_j}) + F_{τ_1}^{(j)} = 13(F_{τ_1}^{(j)} − (1/2)ϖ_jw_j) +
6ϖ_jΔ_j(R_0 + R_1^{(j−1)})`, and `13m̄ = (4993/2)M_{j−1}`, so (P8) becomes
`Δ_p^{(j)} = 2497M_{j−1}F_{τ_2}^{(j)} + (4993/2)M_{j−1}ΔF_j − (4993/4)M_{j−1}ϖ_jw_j +
6m̄ϖ_jΔ_j(R_0 + R_1^{(j−1)})`. As
`M_{j−1} = 12·208^{j−1}`, the four terms lie in `(δ/(50·13·415))ℤ`, `(δ/(48·415))ℤ`, `(δ/4)ℤ` and
`(δ/13)ℤ`, hence in `(1/𝔓)ℤ`. As `p_0 = 10`, we get `Δ_p^{(j)}, p_j ∈ (1/𝔓)ℤ`", at the step
`j → j + 1`. -/
lemma Δp_dagger {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    (lvl μin j).K (μT μin (j + 1)) (R1T μin j) - (lvl μin j).dE (μT μin (j + 1)) +
        (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) =
      13 * ((lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) -
        1 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1))) +
      6 * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j) ∧
    13 * (lvl μin j).mbar = 4993 / 2 * (lvl μin j).M ∧
    (lvl μin j).Δp (μT μin (j + 1)) (R1T μin j) =
      2497 * (lvl μin j).M * (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) +
      4993 / 2 * (lvl μin j).M * (lvl μin j).ΔF (μT μin (j + 1)) -
      4993 / 4 * (lvl μin j).M * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) +
      6 * (lvl μin j).mbar * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j) ∧
    InZ (𝔓 μin) ((lvl μin j).Δp (μT μin (j + 1)) (R1T μin j)) := by
  obtain ⟨hK, -⟩ := sizes_K_den hF hj
  have e1 : (lvl μin j).K (μT μin (j + 1)) (R1T μin j) - (lvl μin j).dE (μT μin (j + 1)) +
        (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) =
      13 * ((lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) -
        1 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1))) +
      6 * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j) := by
    rw [hK]
    ring
  have e2 : 13 * (lvl μin j).mbar = 4993 / 2 * (lvl μin j).M := by
    simp only [Level.mbar, Level.mδ, Level.s, Level.Δb]
    ring
  have e3 : (lvl μin j).Δp (μT μin (j + 1)) (R1T μin j) =
      2497 * (lvl μin j).M * (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) +
      4993 / 2 * (lvl μin j).M * (lvl μin j).ΔF (μT μin (j + 1)) -
      4993 / 4 * (lvl μin j).M * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) +
      6 * (lvl μin j).mbar * ϖ μin (j + 1) * (lvl μin j).Δb * (R0 + R1T μin j) := by
    have : (lvl μin j).Δp (μT μin (j + 1)) (R1T μin j) =
        (lvl μin j).mδ * (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) +
        ((lvl μin j).K (μT μin (j + 1)) (R1T μin j) - (lvl μin j).dE (μT μin (j + 1)) +
          (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j)) * (lvl μin j).mbar := rfl
    rw [this, e1, Level.Fτ₁]
    have hmδ : (lvl μin j).mδ = (lvl μin j).M / 2 := rfl
    linear_combination ((lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) +
      (lvl μin j).ΔF (μT μin (j + 1)) -
      1 / 2 * ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1))) * e2 +
      (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) * hmδ
  refine ⟨e1, e2, e3, ?_⟩
  rw [e3]
  have hM := M_eq (μin := μin) j
  obtain ⟨hw, -, -, -, -, -, -, ⟨a, ha⟩, -, -, hΔF, -⟩ := sizes_items hF j
  obtain ⟨-, ⟨b, hb⟩, -⟩ := ϖΔ_inZ (μin := μin) j
  obtain ⟨-, ⟨c, hc⟩⟩ := R0_add_R1_eq hF j
  obtain ⟨⟨f, hf⟩, -⟩ := sizes_Fτ₂_den hF j hj
  obtain ⟨g, hg⟩ := hΔF
  obtain ⟨z, hz⟩ := hw
  have h𝔓 : (𝔓 μin : ℝ) = 200 * 13 * 6 * 415 * dδ μin := by unfold 𝔓; push_cast; ring
  rw [𝔈_cast] at hf
  -- the four terms, multiplied by `𝔓`
  refine ⟨24 * 2497 * f + 325 * 4993 * g - 50 * 13 * 6 * 415 * 4993 * 9 * 1664 ^ j * z +
    200 * 6 * 415 * 3 * a * b * c, ?_⟩
  rw [h𝔓, hM, ϖ_succ]
  push_cast
  rw [← hf, ← hg, ← hz, ← ha, ← hb, ← hc, dδ_cast, ϖ_succ]
  rw [show (1664 : ℝ) ^ j = 8 ^ j * 208 ^ j by rw [← mul_pow]; norm_num]
  ring

/-- The proof of `lem:sizes`: "As `p_0 = 10`, we get `Δ_p^{(j)}, p_j ∈ (1/𝔓)ℤ`", for the level
`j + 1` with `j + 2 ≤ k`. -/
lemma sizes_p_den {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    InZ (𝔓 μin) (lvl μin (j + 1)).p := by
  induction j with
  | zero =>
    show InZ (𝔓 μin) (p₀ + _)
    exact InZ.add ⟨10 * 𝔓 μin, by unfold p₀; push_cast; ring⟩ (Δp_dagger hF hj).2.2.2
  | succ j ih =>
    show InZ (𝔓 μin) ((lvl μin (j + 1)).p + _)
    exact (ih (by omega)).add (Δp_dagger hF hj).2.2.2

/-- The proof of `lem:sizes`: "Finally, `ρ̄_j = R_0m_δ^{(j)} − F_{τ_2}^{(j)}/ϖ_j` and
`u^0_j = ρ̄_{j−1} + w_j + s_jι − ρ̄_j` (`lem:closedforms`(c)) lie in `(1/𝔗_j)ℤ`", for the level
`j + 1` with `j + 2 ≤ k`. -/
lemma sizes_ρbar_den {k : ℕ} (hF : InF μin k) : ∀ j, j + 2 ≤ k →
    (lvl μin (j + 1)).ρbar = R0 * (lvl μin j).mδ -
      (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) / ϖ μin (j + 1) ∧
    InZ (𝔗 μin (j + 1)) (lvl μin (j + 1)).ρbar ∧
    (lvl μin j).u0 (μT μin (j + 1)) (R1T μin j) = (lvl μin j).ρbar +
      (lvl μin j).w (μT μin (j + 1)) + (lvl μin j).s * ι - (lvl μin (j + 1)).ρbar ∧
    InZ (𝔗 μin (j + 1)) ((lvl μin j).u0 (μT μin (j + 1)) (R1T μin j)) := by
  have hρ : ∀ j, j + 2 ≤ k → (lvl μin (j + 1)).ρbar = R0 * (lvl μin j).mδ -
        (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) / ϖ μin (j + 1) ∧
      InZ (𝔗 μin (j + 1)) (lvl μin (j + 1)).ρbar := by
    intro j hj
    have hϖ : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
    have e : (lvl μin (j + 1)).ρbar = R0 * (lvl μin j).mδ -
        (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) / ϖ μin (j + 1) := by
      show R0 * (lvl μin j).mδ - (lvl μin j).βδ * (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) = _
      rw [hϖ]
      field_simp
    refine ⟨e, ?_⟩
    obtain ⟨⟨f, hf⟩, -⟩ := sizes_Fτ₂_den hF j hj
    rw [𝔈_cast] at hf
    refine ⟨3 * 3 * 1080 * 13 * 415 * 8 ^ j * 208 ^ j * 208 ^ j * μin 0 - 4 * f, ?_⟩
    rw [e, ϖ_succ, R0_eq]
    unfold 𝔗 𝔈 dδ
    simp only [Level.mδ, M_eq]
    push_cast
    rw [← hf]
    field_simp
    ring
  intro j hj
  obtain ⟨e, hden⟩ := hρ j hj
  refine ⟨e, hden, ?_, ?_⟩
  · obtain ⟨-, -, h2⟩ := closedforms_c_aux (μin := μin) j
    have h1 := (closedforms_c_aux (μin := μin) j).2.1
    rw [h1, h2]
    ring
  · obtain ⟨-, -, h2⟩ := closedforms_c_aux (μin := μin) j
    have h1 := (closedforms_c_aux (μin := μin) j).2.1
    have hu : (lvl μin j).u0 (μT μin (j + 1)) (R1T μin j) = (lvl μin j).ρbar +
        (lvl μin j).w (μT μin (j + 1)) + (lvl μin j).s * ι - (lvl μin (j + 1)).ρbar := by
      rw [h1, h2]
      ring
    rw [hu]
    obtain ⟨hw, -, -, -, -, -, ⟨a, ha⟩, -⟩ := sizes_items hF j
    -- `ρ̄_j ∈ (1/𝔗_j)ℤ` (`ρ̄_0 = 7/6`), `w ∈ δℤ`, `sι ∈ (1/1300)ℤ`
    have hprev : InZ (𝔗 μin (j + 1)) (lvl μin j).ρbar := by
      rcases j with _ | j
      · rw [ρbar_zero]
        exact ⟨7 * 1618500 * dδ μin, by unfold 𝔗 𝔈; push_cast; ring⟩
      · exact (hρ j (by omega)).2.mono_nat ⟨8 * 208, by unfold 𝔗 𝔈; ring⟩
    have hw' : InZ (𝔗 μin (j + 1)) ((lvl μin j).w (μT μin (j + 1))) :=
      hw.mono_nat ⟨3 * 8 ^ j * 600 * 13 * 415 * 208 ^ j, by unfold 𝔗 𝔈; ring⟩
    have hsι : InZ (𝔗 μin (j + 1)) ((lvl μin j).s * ι) := by
      have : InZ 1300 ((lvl μin j).s * ι) := ⟨a, by rw [← ha]; unfold ι; ring⟩
      exact this.mono_cast (a := 1300) (by norm_num)
        ⟨3 * 8 ^ j * 6 * 415 * 208 ^ j * dδ μin, by unfold 𝔗 𝔈; ring⟩
    exact ((hprev.add hw').add hsι).sub hden

/-! ### The bits -/

/-- A number in `(1/n)ℤ` with `0 < n ≤ 2^B` and `|x| ≤ 2^B` has at most `B` bits (the definition
of `Bits`). -/
lemma bits_of {B : ℕ} {N x : ℝ} (n : ℕ) (hN : N = n) (hn : 0 < n) (hx : InZ N x)
    (hnB : (n : ℝ) ≤ 2 ^ B) (hmag : |x| ≤ 2 ^ B) : Bits B x :=
  ⟨hmag, n, hn, hnB, hN ▸ hx⟩

/-- The end of the denominator paragraph of the proof of `lem:sizes`, in powers of `2`: "The
integers `𝔇_j`, `𝔗_j` and `𝔓` have `O(j + log μ^in_1)` bits", and the magnitudes `M_j`, `ϖ_j`,
`1 + μ_j`, `Ω_j` and `M_jΩ_j`, with `L = ⌊log₂ μ^in_k⌋`, for the level `j + 1` with `j + 2 ≤ k`.
The Lean bounds the three integers by `2^{O(j + L)}`, through `μ^in_1 ≤ μ^in_k`, not by
`2^{O(j + log μ^in_1)}`; the bits of `lem:sizes` are in `log μ^in_k` anyway. -/
lemma sizes_pow {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    (dδ μin : ℝ) ≤ 2 ^ (Nat.log 2 (μin (k - 1)) + 3) ∧
    1 + μT μin (j + 1) ≤ 2 ^ (Nat.log 2 (μin (k - 1)) + 2) ∧
    (lvl μin (j + 1)).M ≤ 2 ^ (8 * j + 12) ∧ ϖ μin (j + 1) ≤ 2 ^ (3 * j) ∧
    (𝔈 μin (j + 1) : ℝ) ≤ 2 ^ (8 * j + Nat.log 2 (μin (k - 1)) + 25) ∧
    (𝔇 μin (j + 1) : ℝ) ≤ 2 ^ (8 * j + Nat.log 2 (μin (k - 1)) + 29) ∧
    (𝔗 μin (j + 1) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 27) ∧
    (𝔓 μin : ℝ) ≤ 2 ^ (Nat.log 2 (μin (k - 1)) + 26) ∧
    Ω μin (j + 1) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 14) ∧
    (lvl μin (j + 1)).M * Ω μin (j + 1) ≤ 2 ^ (19 * j + Nat.log 2 (μin (k - 1)) + 26) := by
  set L := Nat.log 2 (μin (k - 1))
  have hμk : (μin (k - 1) : ℝ) < 2 ^ (L + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) (μin (k - 1))
  have h0 : (μin 0 : ℝ) ≤ μin (k - 1) := by exact_mod_cast μin_mono hF (Nat.zero_le _) (by omega)
  have hpos : (0 : ℝ) < μin 0 := by exact_mod_cast μin0_pos hF
  have h2 : ∀ a b : ℕ, (2 : ℝ) ^ (a + b) = 2 ^ a * 2 ^ b := fun a b => pow_add 2 a b
  have h208 : ∀ i : ℕ, (208 : ℝ) ^ i ≤ 2 ^ (8 * i) := fun i => by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) i
  have h8 : ∀ i : ℕ, (8 : ℝ) ^ i = 2 ^ (3 * i) := fun i => by rw [pow_mul]; norm_num
  have hdδ : (dδ μin : ℝ) ≤ 2 ^ (L + 3) := by
    rw [dδ_cast, h2, show (2 : ℝ) ^ 3 = 8 by norm_num]
    rw [pow_succ] at hμk
    nlinarith
  have hμ : 1 + μT μin (j + 1) ≤ 2 ^ (L + 2) := by
    have := μT_le hF (by omega : j + 1 < k)
    have h1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
    rw [pow_succ] at hμk
    rw [pow_succ, pow_succ]
    nlinarith
  have hM : (lvl μin (j + 1)).M ≤ 2 ^ (8 * j + 12) := by
    rw [M_eq, pow_succ, h2]
    have := h208 j
    have h12 : (12 : ℝ) * 208 ≤ 2 ^ 12 := by norm_num
    calc (12 : ℝ) * (208 ^ j * 208) = 12 * 208 * 208 ^ j := by ring
      _ ≤ 2 ^ 12 * 2 ^ (8 * j) := mul_le_mul h12 this (by positivity) (by positivity)
      _ = 2 ^ (8 * j) * 2 ^ 12 := by ring
  have hϖ : ϖ μin (j + 1) ≤ 2 ^ (3 * j) := by
    rw [ϖ_succ, h8]
    have : (0 : ℝ) ≤ 2 ^ (3 * j) := by positivity
    linarith
  have hE : (𝔈 μin (j + 1) : ℝ) ≤ 2 ^ (8 * j + L + 25) := by
    have e : (𝔈 μin (j + 1) : ℝ) = 3237000 * 208 ^ j * (dδ μin) := by unfold 𝔈; push_cast; ring
    rw [e, show 8 * j + L + 25 = 22 + 8 * j + (L + 3) by ring, h2, h2]
    gcongr
    · norm_num
    · exact h208 j
  have hΩ : Ω μin (j + 1) ≤ 2 ^ (11 * j + L + 14) := by
    rw [Ω, show 11 * j + L + 14 = 3 * j + (8 * j + 12) + (L + 2) by ring, h2, h2]
    have h1 := ϖ_pos (μin := μin) (j + 1)
    have h3 := M_pos (μin := μin) (j + 1)
    have h4 : 0 ≤ 1 + μT μin (j + 1) := by linarith [μT_nonneg (μin := μin) (j + 1)]
    exact mul_le_mul (mul_le_mul hϖ hM h3.le (by positivity)) hμ h4 (by positivity)
  refine ⟨hdδ, hμ, hM, hϖ, hE, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (𝔇 μin (j + 1) : ℝ) = 12 * (𝔈 μin (j + 1) : ℝ) := by unfold 𝔇; push_cast; ring
    rw [e, show 8 * j + L + 29 = 4 + (8 * j + L + 25) by ring, h2]
    gcongr
    norm_num
  · have e : (𝔗 μin (j + 1) : ℝ) = 3 * 8 ^ j * (𝔈 μin (j + 1) : ℝ) := by unfold 𝔗; push_cast; ring
    rw [e, show 11 * j + L + 27 = 2 + 3 * j + (8 * j + L + 25) by ring, h2, h2, ← h8]
    gcongr
    norm_num
  · have e : (𝔓 μin : ℝ) = 6474000 * (dδ μin) := by unfold 𝔓; push_cast; ring
    rw [e, show L + 26 = 23 + (L + 3) by ring, h2]
    gcongr
    norm_num
  · exact hΩ
  · rw [show 19 * j + L + 26 = (8 * j + 12) + (11 * j + L + 14) by ring, h2]
    exact mul_le_mul hM hΩ (Ω_pos _).le (by positivity)

/-- `InZ` along an equality of denominators (not in the paper). -/
lemma InZ.den_eq {N N' x : ℝ} (h : InZ N x) (hN : N = N') : InZ N' x := hN ▸ h

/-! ### The lemma -/

variable (μin) in
/-- The numbers that the parameter rule computes at the step `j → j + 1` (`def:ruleP`,
`tab:ruleP`), for the level `j + 1`: (P1) `M`, `m_δ`, `m_*`; (P2) `1/β_δ`, `β_δ`, `β_b`; (P3) `w`,
`d_e` on `E = E_j ∪ {τ_1, τ_2}`, `d̄`, `d(E_j)` and `d(E)`; (P4) `Δ_b`, `m_b`, `s`, `m̄` and `ψ`;
(P5) `Π` and `ΔF`; (P6) `ρ̄_j`, `a_2`, `a_0`, `u^0`, `F_{τ_2}` and `F_{τ_1}`; (P7) `K`; (P8)
`q_{j+1}`, `p_{j+1}` and `Δ_p`; the rewards and curvatures of the level `j + 1` (and the `1/β_e`;
its `M_{j+1} = m_b` is listed in (P4)), `ρ̄_{j+1}`, and `φ = β_δΔF/w`, which the proof of
`lem:sizes` counts among them. -/
def RuleNumber (j : ℕ) (x : ℝ) : Prop :=
  x = (lvl μin j).M ∨ x = (lvl μin j).mδ ∨ x = (lvl μin j).mstar ∨
  x = 1 / (lvl μin j).βδ ∨ x = (lvl μin j).βδ ∨ x = (lvl μin j).βb ∨
  x = (lvl μin j).w (μT μin (j + 1)) ∨ (∃ e, x = (lvl μin j).dE' (μT μin (j + 1)) e) ∨
  x = (lvl μin j).dbar (μT μin (j + 1)) ∨ x = (lvl μin j).dEk (μT μin (j + 1)) ∨
  x = (lvl μin j).dE (μT μin (j + 1)) ∨
  x = (lvl μin j).Δb ∨ x = (lvl μin j).mb ∨ x = (lvl μin j).s ∨ x = (lvl μin j).mbar ∨
  x = (lvl μin j).ψ ∨
  x = (lvl μin j).Pcal (μT μin (j + 1)) ∨ x = (lvl μin j).ΔF (μT μin (j + 1)) ∨
  x = (lvl μin j).ρbar ∨ x = Level.a2 (μT μin (j + 1)) (R1T μin j) ∨
  x = (lvl μin j).a0 (μT μin (j + 1)) ∨ x = (lvl μin j).u0 (μT μin (j + 1)) (R1T μin j) ∨
  x = (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) ∨
  x = (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) ∨
  x = (lvl μin j).K (μT μin (j + 1)) (R1T μin j) ∨
  x = (lvl μin (j + 1)).q ∨ x = (lvl μin (j + 1)).p ∨
  x = (lvl μin j).Δp (μT μin (j + 1)) (R1T μin j) ∨
  (∃ e, x = mT μin (j + 1) e) ∨ (∃ e, x = βT μin (j + 1) e) ∨ (∃ e, x = 1 / βT μin (j + 1) e) ∨
  x = (lvl μin (j + 1)).ρbar ∨ x = φ μin j

/-- The magnitudes of the step `j → j + 1` measured in `X = M_{j+1}Ω_{j+1}` (from the bounds of the
proof of `lem:sizes` above): `M_{j+1} ≥ 2496`, `ϖ_{j+1} ≥ 3/4`, `M_{j+1}(1 + μ_{j+1}) ≤ 2Ω_{j+1}`,
`1 ≤ Ω_{j+1} ≤ X`, `M_{j+1} ≤ X`, `ϖ_{j+1} ≤ Ω_{j+1}`, `q_{j+1} ≤ X`, `w ≤ 2X`,
`ϖ_{j+1}w ≤ Ω_{j+1}`, `q_jμ ≤ X` and `M_{j+1}d(E) ≤ 2X` (not in the paper: the bookkeeping of
the bounds that the proof states). -/
lemma sizes_units {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    (2496 : ℝ) ≤ (lvl μin (j + 1)).M ∧ (3 : ℝ) / 4 ≤ ϖ μin (j + 1) ∧
    (lvl μin (j + 1)).M * (1 + μT μin (j + 1)) ≤ 2 * Ω μin (j + 1) ∧
    1 ≤ Ω μin (j + 1) ∧ Ω μin (j + 1) ≤ (lvl μin (j + 1)).M * Ω μin (j + 1) ∧
    (lvl μin (j + 1)).M ≤ (lvl μin (j + 1)).M * Ω μin (j + 1) ∧
    ϖ μin (j + 1) ≤ Ω μin (j + 1) ∧
    (lvl μin (j + 1)).q ≤ (lvl μin (j + 1)).M * Ω μin (j + 1) ∧
    (lvl μin j).w (μT μin (j + 1)) ≤ 2 * ((lvl μin (j + 1)).M * Ω μin (j + 1)) ∧
    ϖ μin (j + 1) * (lvl μin j).w (μT μin (j + 1)) ≤ Ω μin (j + 1) ∧
    (lvl μin j).q * μT μin (j + 1) ≤ (lvl μin (j + 1)).M * Ω μin (j + 1) ∧
    (lvl μin (j + 1)).M * (lvl μin j).dE (μT μin (j + 1)) ≤
      2 * ((lvl μin (j + 1)).M * Ω μin (j + 1)) := by
  set M := (lvl μin (j + 1)).M
  set μ := μT μin (j + 1)
  set Ωj := Ω μin (j + 1)
  set ϖj := ϖ μin (j + 1)
  have hMge : (2496 : ℝ) ≤ M := by
    show (2496 : ℝ) ≤ (lvl μin (j + 1)).M
    rw [M_succ_eq, M_eq]
    have : (1 : ℝ) ≤ 208 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have hμ0 : 0 ≤ μ := μT_nonneg _
  have hϖ0 : (3 : ℝ) / 4 ≤ ϖj := by
    show (3 : ℝ) / 4 ≤ ϖ μin (j + 1)
    rw [ϖ_succ]
    have : (1 : ℝ) ≤ 8 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hΩdef : Ωj = ϖj * M * (1 + μ) := rfl
  have hM1μ : 0 ≤ M * (1 + μ) := by positivity
  have hΩ1 : M * (1 + μ) ≤ 2 * Ωj := by
    rw [hΩdef, mul_assoc]
    nlinarith
  have hΩge : 1 ≤ Ωj := by nlinarith
  have hΩX : Ωj ≤ M * Ωj := by nlinarith
  have hMX : M ≤ M * Ωj := by nlinarith
  have hϖΩ : ϖj ≤ Ωj := by
    rw [hΩdef, mul_assoc]
    have : 1 ≤ M * (1 + μ) := by nlinarith
    nlinarith
  have hqX : (lvl μin (j + 1)).q ≤ M * Ωj := by
    have hq := ((weights_c (μin := μin)).2 j).2
    have : ϖj * M ^ 2 ≤ M * Ωj := by
      rw [hΩdef]
      have : 0 ≤ ϖj * M ^ 2 := by positivity
      nlinarith
    exact hq.trans this
  have hwM := w_eq_M (μin := μin) j
  have hw2 : (lvl μin j).w μ ≤ 2 * (M * Ωj) := by
    rw [hwM]
    have hMμ : 0 ≤ M * μ := mul_nonneg (by linarith) hμ0
    have e : M * (1 + μ) = M + M * μ := by ring
    have : 4 / 13 * M * μ ≤ M * (1 + μ) := by linarith
    linarith
  have hϖw : ϖj * (lvl μin j).w μ ≤ Ωj := by
    rw [hwM, hΩdef]
    have : 0 ≤ ϖj * M := by positivity
    nlinarith
  have hqμ : (lvl μin j).q * μ ≤ M * Ωj := by
    have hqj : 0 < (lvl μin j).q := q_pos j
    have hqle : (lvl μin j).q ≤ (lvl μin (j + 1)).q := by
      rw [q_succ]
      have : 0 ≤ (lvl μin j).ψ := by unfold Level.ψ; have := (lvl μin j).βδ_pos; positivity
      linarith
    have h1 : (lvl μin j).q * μ ≤ (lvl μin (j + 1)).q * (1 + μ) := by nlinarith
    have h2 : (lvl μin (j + 1)).q * (1 + μ) ≤ ϖj * M ^ 2 * (1 + μ) := by
      have := ((weights_c (μin := μin)).2 j).2
      nlinarith
    have h3 : ϖj * M ^ 2 * (1 + μ) = M * Ωj := by rw [hΩdef]; ring
    linarith
  have hMdE : M * (lvl μin j).dE μ ≤ 2 * (M * Ωj) := by
    have := (sizes_dE hF hj).2.2.2.1
    nlinarith
  exact ⟨hMge, hϖ0, hΩ1, hΩge, hΩX, hMX, hϖΩ, hqX, hw2, hϖw, hqμ, hMdE⟩

/-- The denominators of the step `j → j + 1` are at most `2^{11j + L + 29}`,
`L = ⌊log₂ μ^in_k⌋` (from `sizes_pow`; not in the paper: the bookkeeping of the denominators that
the proof states). -/
lemma sizes_dens {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) :
    (∀ c : ℕ, (c : ℝ) ≤ 2 ^ 17 →
      ((c * dδ μin : ℕ) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29)) ∧
    (∀ c : ℕ, (c : ℝ) ≤ 2 ^ 6 →
      ((c * 8 ^ j : ℕ) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29)) ∧
    (∀ c : ℕ, (c : ℝ) ≤ 2 ^ 16 → (c : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29)) ∧
    ((48 * 2490 * 208 ^ j * dδ μin : ℕ) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29) ∧
    ((𝔈 μin (j + 1) : ℕ) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29) ∧
    ((𝔇 μin (j + 1) : ℕ) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29) ∧
    ((𝔗 μin (j + 1) : ℕ) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29) ∧
    ((𝔓 μin : ℕ) : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29) := by
  set L := Nat.log 2 (μin (k - 1))
  obtain ⟨hdδ, -, -, -, hEb, hDb, hTb, hPb, -, -⟩ := sizes_pow hF hj
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  have h8 : ∀ i : ℕ, (8 : ℝ) ^ i = 2 ^ (3 * i) := fun i => by rw [pow_mul]; norm_num
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => hc.trans (two_pow _ _ (by omega)), ?_,
    hEb.trans (two_pow _ _ (by omega)), hDb.trans (two_pow _ _ (by omega)),
    hTb.trans (two_pow _ _ (by omega)), hPb.trans (two_pow _ _ (by omega))⟩
  · push_cast
    calc (c : ℝ) * dδ μin ≤ 2 ^ 17 * 2 ^ (L + 3) :=
          mul_le_mul hc hdδ (by positivity) (by positivity)
      _ = 2 ^ (L + 20) := by rw [← pow_add]; ring_nf
      _ ≤ _ := two_pow _ _ (by omega)
  · push_cast
    rw [h8]
    calc (c : ℝ) * 2 ^ (3 * j) ≤ 2 ^ 6 * 2 ^ (3 * j) := by gcongr
      _ = 2 ^ (3 * j + 6) := by rw [← pow_add]; ring_nf
      _ ≤ _ := two_pow _ _ (by omega)
  · push_cast
    have h208 : (208 : ℝ) ^ j ≤ 2 ^ (8 * j) := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
    calc (119520 : ℝ) * 208 ^ j * dδ μin ≤ 2 ^ 17 * 2 ^ (8 * j) * 2 ^ (L + 3) := by
          gcongr; norm_num
      _ = 2 ^ (8 * j + L + 20) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ _ := two_pow _ _ (by omega)

/-- A number of the step `j → j + 1` with a denominator `n ≤ 2^{11j + L + 29}` and
`|x| ≤ 10 + 200M_{j+1}Ω_{j+1}` has at most `30(k + L + 1)` bits, `L = ⌊log₂ μ^in_k⌋` (the end of
the denominator paragraph of the proof of `lem:sizes`: "With the magnitudes above, every value of
`g_{k−1}` and every number … of the levels `1, …, k − 1` therefore has `O(k + log μ^in_k)`
bits"; not in the paper: the arithmetic of that sentence). -/
lemma sizes_prim {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) {x : ℝ} (n : ℕ) (hn : 0 < n)
    (hx : InZ n x) (hnb : (n : ℝ) ≤ 2 ^ (11 * j + Nat.log 2 (μin (k - 1)) + 29))
    (hmag : |x| ≤ 10 + 200 * ((lvl μin (j + 1)).M * Ω μin (j + 1))) :
    Bits (30 * (k + Nat.log 2 (μin (k - 1)) + 1)) x := by
  set L := Nat.log 2 (μin (k - 1))
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  obtain ⟨-, -, -, -, -, -, -, -, -, hMΩ⟩ := sizes_pow hF hj
  have h1 : (1 : ℝ) ≤ 2 ^ (19 * j + L + 26) := one_le_pow₀ (by norm_num)
  have h9 : (2 : ℝ) ^ (19 * j + L + 26) * 2 ^ 9 ≤ 2 ^ (30 * (k + L + 1)) := by
    rw [← pow_add]; exact two_pow _ _ (by omega)
  refine bits_of n rfl hn hx (hnb.trans (two_pow _ _ (by omega))) (hmag.trans ?_)
  have : (0 : ℝ) ≤ 2 ^ (19 * j + L + 26) := by positivity
  linarith

/-- The numbers of the step `j → j + 1` have at most `100(k + ⌊log₂ μ^in_k⌋ + 1)` bits: those
bounded above have at most `30(k + ⌊log₂ μ^in_k⌋ + 1)` (`sizes_prim`); "The sums `d_j(E_{j−1})`
and `Π` lie in `(δ/4)ℤ`, with magnitudes at most `2Ω_j` and `2M_jΩ_j`, and `a_2` lies in
`(δ/130)ℤ`, with magnitude at most `1 + μ_j`, as `|𝓡_{j−1}| ≤ R_0 + R_1^{(j−1)} ≤ 1 + μ_j`. So they
too have `O(k + log μ^in_k)` bits" (`sizes_prim` with these denominators and magnitudes), "and so do
the remaining quantities `d̄`, `φ` and `a_0` of the parameter rule, which are obtained from these
by `O(1)` arithmetic operations at each level" (quotients of such numbers, `Bits.div`)
(appD-hardness.tex:1654-1655). -/
lemma sizes_step {k : ℕ} (hF : InF μin k) {j : ℕ} (hj : j + 2 ≤ k) (x : ℝ)
    (hx : RuleNumber μin j x) : Bits (100 * (k + Nat.log 2 (μin (k - 1)) + 1)) x := by
  set L := Nat.log 2 (μin (k - 1)) with hL
  have hBB : 30 * (k + L + 1) ≤ 100 * (k + L + 1) := by omega
  have h3B : 3 * (30 * (k + L + 1)) ≤ 100 * (k + L + 1) := by omega
  set X := (lvl μin (j + 1)).M * Ω μin (j + 1) with hXdef
  set μ := μT μin (j + 1) with hμdef
  obtain ⟨hMge, hϖ0, hΩ1, hΩge, hΩX, hMX, hϖΩ, hqX, hw2, hϖw, hqμ, hMdE⟩ := sizes_units hF hj
  obtain ⟨dδc, d8c, dc, dΔF, dE, dD, dT, dP⟩ := sizes_dens hF hj
  have hX0 : 0 ≤ X := by linarith
  have prim := fun {y : ℝ} (n : ℕ) (hn : 0 < n) (hy : InZ n y)
      (hnb : (n : ℝ) ≤ 2 ^ (11 * j + L + 29)) (hy' : |y| ≤ 10 + 200 * X) =>
    (sizes_prim hF hj n hn hy hnb hy').mono hBB
  have hM0 := M_pos (μin := μin) j
  have hM1 : (lvl μin (j + 1)).M = 208 * (lvl μin j).M := M_succ_eq j
  have hMj := M_eq (μin := μin) j
  have hdδ0 : 0 < dδ μin := by unfold dδ; have := μin0_pos hF; omega
  obtain ⟨hw, -, hdE', hdEk, hdE, hPi, hs, hmbar, hψ, hq, hΔF, ha2⟩ := sizes_items hF j
  obtain ⟨-, hdEk0, hdEkle, hdE2, -, hΔF0, hΔF1, hPi1⟩ := sizes_dE hF hj
  obtain ⟨-, hFτ₂_1, hFτ₁_1⟩ := sizes_F hF hj
  obtain ⟨-, hK1⟩ := sizes_K hF hj
  obtain ⟨-, hΔp1⟩ := sizes_Δp hF hj
  obtain ⟨hq0, -, -, hp1⟩ := sizes_p hF hj
  obtain ⟨hρ0, hρ1, hρ2, hρ3⟩ := sizes_ρbar hF hj
  obtain ⟨hFτ₂d, hFτ₁d⟩ := sizes_Fτ₂_den hF j hj
  obtain ⟨-, hKd⟩ := sizes_K_den hF hj
  obtain ⟨-, -, -, hΔpd⟩ := Δp_dagger hF hj
  have hpd := sizes_p_den hF hj
  obtain ⟨-, hρd, hu0eq, hu0d⟩ := sizes_ρbar_den hF j hj
  obtain ⟨-, -, hϖ4⟩ := ϖΔ_inZ (μin := μin) j
  obtain ⟨-, -, -, -, hυ0, hυ1⟩ := sizes_dbar_φ hF hj
  have hwpos := w_pos (μin := μin) (μT_pos hF (by omega : j + 1 < k))
  have hϖdef : ϖ μin (j + 1) = 1 / (lvl μin j).βδ := rfl
  have hβδ := (lvl μin j).βδ_pos
  have hϖpos := ϖ_pos (μin := μin) (j + 1)
  have hρ := hρ1.trans (hρ2.trans hρ3)
  have hEpos : 0 < 𝔈 μin (j + 1) := by unfold 𝔈; positivity
  have hDpos : 0 < 𝔇 μin (j + 1) := by unfold 𝔇; positivity
  have hTpos : 0 < 𝔗 μin (j + 1) := by unfold 𝔗; positivity
  have hPpos : 0 < 𝔓 μin := by unfold 𝔓; positivity
  have hM10 : 0 < (lvl μin (j + 1)).M := M_pos _
  -- integers below `M_{j+1}`
  have int : ∀ (y : ℝ) (z : ℕ), y = z → y ≤ X → Bits (100 * (k + L + 1)) y := by
    intro y z hyz hyX
    refine prim 1 one_pos ⟨z, by rw [hyz]; push_cast; ring⟩ (dc 1 (by norm_num)) ?_
    rw [abs_of_nonneg (by rw [hyz]; positivity)]
    linarith
  -- the three quotients
  have bϖw : Bits (30 * (k + L + 1)) (ϖ μin (j + 1) * (lvl μin j).w μ) :=
    sizes_prim hF hj (4 * dδ μin) (by positivity) ((hϖ4.mul hw).den_eq (by push_cast; ring))
      (dδc 4 (by norm_num)) (by rw [abs_of_pos (by positivity)]; linarith)
  have bϖw0 : ϖ μin (j + 1) * (lvl μin j).w μ ≠ 0 := by positivity
  rcases hx with h | h | h | h | h | h | h | ⟨e, h⟩ | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | h | h <;> rw [h]
  · -- (P1) `M`
    exact int _ (12 * 208 ^ j) (by rw [hMj]; push_cast; ring) (by linarith)
  · exact int _ (6 * 208 ^ j) (by simp only [Level.mδ, hMj]; push_cast; ring)
      (by simp only [Level.mδ]; linarith)
  · exact int _ (774 * 208 ^ j) (by simp only [Level.mstar, Level.mδ, hMj]; push_cast; ring)
      (by simp only [Level.mstar, Level.mδ]; linarith)
  · -- (P2) `1/β_δ = ϖ`
    exact prim 4 (by norm_num) (hϖ4.den_eq (by norm_num)) (dc 4 (by norm_num))
      (by rw [← hϖdef, abs_of_pos hϖpos]; linarith)
  · refine prim (3 * 8 ^ j) (by positivity) ⟨4, ?_⟩ (d8c 3 (by norm_num)) ?_
    · simp only [Level.βδ, lvl_k]; push_cast; field_simp
    · have : (lvl μin j).βδ ≤ 4 / 3 := by
        rw [show (lvl μin j).βδ = 1 / ϖ μin (j + 1) by rw [hϖdef]; field_simp]
        rw [div_le_iff₀ hϖpos]; linarith
      rw [abs_of_pos hβδ]; linarith
  · refine prim (9 * 8 ^ j) (by positivity) ⟨1, ?_⟩ (d8c 9 (by norm_num)) ?_
    · simp only [Level.βb, Level.βδ, lvl_k]; push_cast; field_simp; ring
    · have : (lvl μin j).βδ ≤ 4 / 3 := by
        rw [show (lvl μin j).βδ = 1 / ϖ μin (j + 1) by rw [hϖdef]; field_simp]
        rw [div_le_iff₀ hϖpos]; linarith
      unfold Level.βb
      rw [abs_of_pos (by positivity)]; linarith
  · -- (P3) `w`, `d_e`, `d̄`, `d(E_j)`, `d(E)`
    exact prim (1 * dδ μin) (by positivity) (hw.den_eq (by push_cast; ring)) (dδc 1 (by norm_num))
      (by rw [abs_of_pos hwpos]; linarith)
  · have hle : (lvl μin j).dE' μ e ≤ (lvl μin j).dE μ :=
      single_le_sum (fun e _ => dE'_nonneg j e) (mem_univ e)
    exact prim (4 * dδ μin) (by positivity) ((hdE' e).den_eq (by push_cast; ring))
      (dδc 4 (by norm_num)) (by rw [abs_of_nonneg (dE'_nonneg j e)]; linarith)
  · have e1 : (lvl μin j).dbar μ = (lvl μin j).dEk μ / (ϖ μin (j + 1) * (lvl μin j).w μ) := by
      rw [Level.dbar, hϖdef]; field_simp
    rw [e1]
    have bdEk : Bits (30 * (k + L + 1)) ((lvl μin j).dEk μ) :=
      sizes_prim hF hj (4 * dδ μin) (by positivity) (hdEk.den_eq (by push_cast; ring))
        (dδc 4 (by norm_num)) (by rw [abs_of_nonneg hdEk0]; linarith)
    exact (bdEk.div bϖw bϖw0).mono h3B
  · exact prim (4 * dδ μin) (by positivity) (hdEk.den_eq (by push_cast; ring))
      (dδc 4 (by norm_num)) (by rw [abs_of_nonneg hdEk0]; linarith)
  · exact prim (4 * dδ μin) (by positivity) (hdE.den_eq (by push_cast; ring))
      (dδc 4 (by norm_num)) (by rw [abs_of_nonneg (hdEk0.trans hdEkle)]; linarith)
  · -- (P4) `Δ_b`, `m_b`, `s`, `m̄`, `ψ`
    exact int _ (2490 * 208 ^ j) (by rw [Δb_eq]; push_cast; ring)
      (by simp only [Level.Δb]; linarith)
  · exact int _ (12 * 208 ^ (j + 1)) (by rw [← M_succ, M_eq]; push_cast; ring)
      (by rw [← M_succ]; linarith)
  · refine prim 13 (by norm_num) (hs.den_eq (by norm_num)) (dc 13 (by norm_num)) ?_
    rw [abs_of_pos (s_pos j)]
    simp only [Level.s, Level.Δb]
    linarith
  · refine prim 13 (by norm_num) (hmbar.den_eq (by norm_num)) (dc 13 (by norm_num)) ?_
    have : 0 < (lvl μin j).mbar := by
      simp only [Level.mbar, Level.mδ, Level.s, Level.Δb]; linarith
    rw [abs_of_pos this]
    simp only [Level.mbar, Level.mδ, Level.s, Level.Δb]
    linarith
  · refine prim 13 (by norm_num) (hψ.den_eq (by norm_num)) (dc 13 (by norm_num)) ?_
    have hψ0 : 0 ≤ (lvl μin j).ψ := by unfold Level.ψ; positivity
    have : (lvl μin j).ψ ≤ (lvl μin (j + 1)).q := by
      rw [q_succ]; have := q_pos (μin := μin) j; linarith
    rw [abs_of_nonneg hψ0]; linarith
  · -- (P5) `Π`, `ΔF`
    exact prim (4 * dδ μin) (by positivity) (hPi.den_eq (by push_cast; ring))
      (dδc 4 (by norm_num)) (by linarith)
  · exact prim _ (by positivity) (hΔF.den_eq (by push_cast; ring)) dΔF
      (by rw [abs_of_nonneg hΔF0]; linarith)
  · -- (P6) `ρ̄_j`, `a_2`, `a_0`, `u^0`, `F_{τ_2}`, `F_{τ_1}`
    rcases j with _ | j
    · rw [ρbar_zero]
      exact prim 6 (by norm_num) ⟨7, by norm_num⟩ (dc 6 (by norm_num))
        (by rw [abs_of_pos (by norm_num)]; linarith)
    · obtain ⟨-, hρd', -, -⟩ := sizes_ρbar_den hF j (by omega)
      obtain ⟨hρ0', hρ1', hρ2', hρ3'⟩ := sizes_ρbar hF (by omega : j + 2 ≤ k)
      obtain ⟨-, -, -, -, -, -, hT', -, -, -⟩ := sizes_pow hF (by omega : j + 2 ≤ k)
      have hMle : (lvl μin (j + 1)).M ≤ (lvl μin (j + 1 + 1)).M := by
        rw [M_succ_eq (j + 1)]; linarith [M_pos (μin := μin) (j + 1)]
      have hμle : μT μin (j + 1) ≤ μT μin (j + 1 + 1) := μT_mono hF (by omega) (by omega)
      have hTpos' : 0 < 𝔗 μin (j + 1) := by unfold 𝔗 𝔈; positivity
      refine prim (𝔗 μin (j + 1)) hTpos' hρd'
        (hT'.trans (pow_le_pow_right₀ (by norm_num) (by omega))) ?_
      rw [abs_of_pos hρ0']
      have : (lvl μin (j + 1)).M * (1 + μT μin (j + 1)) ≤
          (lvl μin (j + 1 + 1)).M * (1 + μT μin (j + 1 + 1)) := by
        have := μT_nonneg (μin := μin) (j + 1)
        exact mul_le_mul hMle (by linarith) (by positivity) (by linarith)
      linarith [hρ1'.trans (hρ2'.trans hρ3')]
  · -- "`a_2` lies in `(δ/130)ℤ`, with magnitude at most `1 + μ_j`, as
    -- `|𝓡_{j−1}| ≤ R_0 + R_1^{(j−1)} ≤ 1 + μ_j`" (`R0_add_R1_le`; at the step `j → j + 1`)
    refine prim (130 * dδ μin) (by positivity) (ha2.den_eq (by push_cast; ring))
      (dδc 130 (by norm_num)) ?_
    have hlen0 : 0 < lenR μin j := by
      rw [lenR_eq]; have : 0 ≤ ∑ i ∈ range (j + 1), μT μin i := sum_nonneg fun i _ => μT_nonneg i
      linarith
    have hR := (R0_add_R1_le hF hj).2
    have hR0 : (0 : ℝ) ≤ R0 := by rw [R0_eq]; norm_num
    have hμ0 := μT_nonneg (μin := μin) (j + 1)
    have : R1T μin j - R0 = lenR μin j := rfl
    -- `0 ≤ a_2 = |𝓡| ≤ R_0 + R_1 ≤ 1 + μ ≤ M(1 + μ) ≤ 2Ω ≤ 2X`
    have h1μ : 1 + μ ≤ (lvl μin (j + 1)).M * (1 + μ) :=
      le_mul_of_one_le_left (by linarith) (by linarith)
    simp only [Level.a2, this]
    rw [abs_le]
    constructor <;> linarith
  · have e1 : (lvl μin j).a0 μ = ((lvl μin j).q * μ - (lvl μin j).Pcal μ) / ϖ μin (j + 1) := by
      rw [eq_div_iff hϖpos.ne', mul_comm]
      exact (Fτ₂_star hF hj).2.1
    rw [e1]
    have hqμP : InZ ((52 * dδ μin : ℕ) : ℝ) ((lvl μin j).q * μ - (lvl μin j).Pcal μ) := by
      have hqj : InZ 13 (lvl μin j).q := by
        rcases j with _ | j
        · exact ⟨91, by show (13 : ℝ) * q₀ = _; unfold q₀; norm_num⟩
        · exact (sizes_items hF j).2.2.2.2.2.2.2.2.2.1
      have h52 : InZ (52 * dδ μin : ℝ) ((lvl μin j).q * μ - (lvl μin j).Pcal μ) :=
        ((hqj.mul (μT_inZ hF (j + 1))).mono 4 (by ring)).sub (hPi.mono 13 (by ring))
      exact h52.den_eq (by push_cast; ring)
    have bqμP : Bits (30 * (k + L + 1)) ((lvl μin j).q * μ - (lvl μin j).Pcal μ) := by
      refine sizes_prim hF hj _ (by positivity) hqμP (dδc 52 (by norm_num)) ?_
      have hqμ0 : 0 ≤ (lvl μin j).q * μ := mul_nonneg (q_pos j).le (μT_nonneg _)
      calc |(lvl μin j).q * μ - (lvl μin j).Pcal μ| ≤ |(lvl μin j).q * μ| + |(lvl μin j).Pcal μ| :=
            abs_sub _ _
        _ ≤ 10 + 200 * X := by rw [abs_of_nonneg hqμ0]; linarith
    have bϖ : Bits (30 * (k + L + 1)) (ϖ μin (j + 1)) :=
      sizes_prim hF hj 4 (by norm_num) (hϖ4.den_eq (by norm_num)) (dc 4 (by norm_num))
        (by rw [abs_of_pos hϖpos]; linarith)
    exact (bqμP.div bϖ hϖpos.ne').mono h3B
  · refine prim (𝔗 μin (j + 1)) hTpos hu0d dT ?_
    have hu : (lvl μin j).u0 μ (R1T μin j) = υ0 μin j * (lvl μin j).w μ := by
      rw [υ0, div_mul_cancel₀ _ hwpos.ne']
    rw [hu, abs_of_pos (by positivity)]
    have : υ0 μin j * (lvl μin j).w μ ≤ (lvl μin j).w μ := mul_le_of_le_one_left hwpos.le hυ1.le
    linarith
  · exact prim (𝔈 μin (j + 1)) hEpos hFτ₂d dE (by linarith)
  · exact prim (𝔇 μin (j + 1)) hDpos hFτ₁d dD (by linarith)
  · -- (P7) `K`
    exact prim (𝔇 μin (j + 1)) hDpos hKd dD (by linarith)
  · -- (P8) `q_{j+1}`, `p_{j+1}`, `Δ_p`
    exact prim 13 (by norm_num) (hq.den_eq (by norm_num)) (dc 13 (by norm_num))
      (by rw [abs_of_pos hq0]; linarith)
  · exact prim (𝔓 μin) hPpos hpd dP (by linarith)
  · exact prim (𝔓 μin) hPpos hΔpd dP (by linarith)
  · -- the rewards, the curvatures and the `1/β_e` of the level `j + 1`
    obtain ⟨n, -, hv, hle⟩ := (weights_b (μin := μin)).1 (j + 1) e
    exact int _ n hv (by rw [hv] at *; linarith)
  · have hb := inv_βT_bounds (μin := μin) j e
    have hβ0 : 0 < βT μin (j + 1) e := one_div_pos.1 hb.1
    refine prim (36 * 8 ^ j) (by positivity) ?_ (d8c 36 (by norm_num)) ?_
    · rcases inv_βT_mem (μin := μin) (j + 1) e with h | h | ⟨i, hi, h | h⟩ <;>
        rw [one_div, inv_eq_iff_eq_inv] at h <;> rw [h]
      · exact ⟨36 * 8 ^ j, by push_cast; ring⟩
      · exact ⟨144 * 8 ^ j, by push_cast; ring⟩
      · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
        exact ⟨48 * 8 ^ d, by push_cast; rw [pow_add]; field_simp; ring⟩
      · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
        exact ⟨4 * 8 ^ d, by push_cast; rw [pow_add]; field_simp; ring⟩
    · -- `1/β ≥ 1/4`, so `β ≤ 4`
      have h4 : 1 / 4 ≤ 1 / βT μin (j + 1) e := by
        have h8 : ∀ i, (1 : ℝ) ≤ 8 ^ i := fun i => one_le_pow₀ (by norm_num)
        -- (`rw` closes the case `1/β = 1/4` by `rfl`)
        rcases inv_βT_mem (μin := μin) (j + 1) e with h | h | ⟨i, -, h | h⟩ <;> rw [h]
        · norm_num
        · linarith [h8 i]
        · linarith [h8 i]
      have : βT μin (j + 1) e ≤ 4 := by
        rw [div_le_div_iff₀ (by norm_num) hβ0] at h4; linarith
      rw [abs_of_pos hβ0]; linarith
  · obtain ⟨h0, h1, h2⟩ := inv_βT_bounds (μin := μin) j e
    exact prim 4 (by norm_num) (h2.den_eq (by norm_num)) (dc 4 (by norm_num))
      (by rw [abs_of_pos h0]; linarith)
  · -- `ρ̄_{j+1}`
    exact prim (𝔗 μin (j + 1)) hTpos hρd dT (by rw [abs_of_pos hρ0]; linarith)
  · -- `φ = ΔF/(ϖw)`
    have e1 : φ μin j = (lvl μin j).ΔF μ / (ϖ μin (j + 1) * (lvl μin j).w μ) := by
      rw [φ, hϖdef, ← hμdef]
      have hw0 : (lvl μin j).w μ ≠ 0 := hwpos.ne'
      field_simp
    rw [e1]
    have bΔF : Bits (30 * (k + L + 1)) ((lvl μin j).ΔF μ) :=
      sizes_prim hF hj _ (by positivity) (hΔF.den_eq (by push_cast; ring)) dΔF
        (by rw [abs_of_nonneg hΔF0]; linarith)
    exact (bΔF.div bϖw bϖw0).mono h3B

/-- **`lem:sizes`** (Lemma C.24, `stoc-sections/appD-hardness.tex:1547-1552`, proof lines
1554-1660): let `μ^in ∈ 𝔉` have length `k`. Every number computed by the parameter rule for the
levels `1, …, k − 1` (the steps `j → j + 1`, `j + 2 ≤ k`, `RuleNumber`), and every value of
`g_{k−1}`, is a rational with `O(k + log μ^in_k)` bits: its magnitude and its denominator are at
most `2^B` with `B = 100(k + ⌊log₂ μ^in_k⌋ + 1)` (`Bits`).

The proof's steps: (1) "A rational number has `O(k + log μ^in_k)` bits if its magnitude and its
denominator are at most `2^{O(k+log μ^in_k)}`" (`Bits`); (2) the magnitudes: `M_j = 12·208^j`,
`ϖ_j = (3/4)·8^{j−1}`, `μ_j ≤ μ^in_k` (`μT_le`), `Ω_j` (`Ω`, `Ω_double`), `d̄_j` and `φ_j`
(`sizes_dbar_φ`), `w_j` (`w_eq_M`), `d_j(E_j ∖ {b_j})`, `ΔF_j` and `Π` (`sizes_dE`), `ρ̄_j`
(`sizes_ρbar`), `F_{τ_2}` and `F_{τ_1}` (`sizes_F`), `K_j` (`sizes_K`), `Δ_p`, `q_j` and `p_j`
(`sizes_Δp`, `sizes_p`), the formula for `g_j` (`gT_succ_apply`) and its values (`sizes_g`), the
rewards and the `1/β_e` (`mT_le_M`, `inv_βT_bounds`); (3) the denominators: `1/δ = 3μ^in_1`,
`μ_j ∈ δℤ`, the rewards, `Δ_j`, `ϖ_jΔ_j²`, `ϖ_jΔ_j` and the `1/β_e` (`μT_inZ`, `mT_inZ`, `Δb_eq`,
`ϖΔ_inZ`, `inv_βT_mem`), the common denominators `𝔇_j`, `𝔈_j`, `𝔗_j`, `𝔓`, the list
(`sizes_items`), `(*)` (`Fτ₂_star`, `ϖ_ρbar`, `Fτ₂_terms`), `F_{τ_2}` and `F_{τ_1}`
(`sizes_Fτ₂_den`), `K_j` (`sizes_K_den`), the values of `g_j` (`sizes_g_den`), `(†)` and `Δ_p`
(`Δp_dagger`), `p_j` (`sizes_p_den`), `ρ̄_j` and `u^0_j` (`sizes_ρbar_den`); (4) "The integers
`𝔇_j`, `𝔗_j` and `𝔓` have `O(j + log μ^in_1)` bits" (`sizes_pow`, `sizes_dens`, in `log μ^in_k`
instead of `log μ^in_1`), so every number has `O(k + log μ^in_k)` bits (`sizes_prim`), and so do
the sums `d_j(E_{j−1})` and `Π` and `a_2`, by their denominators and magnitudes, and the remaining
quantities `d̄`, `φ` and `a_0` (`sizes_step`, with `Bits.div` for the `O(1)` arithmetic
operations).

Not formalised: the running time (the last paragraph of the proof), as Turing machines are not
formalised and arithmetic operations are not counted. -/
theorem sizes {k : ℕ} (hF : InF μin k) :
    (∀ j, j + 2 ≤ k → ∀ x, RuleNumber μin j x →
      Bits (100 * (k + Nat.log 2 (μin (k - 1)) + 1)) x) ∧
    ∀ S, Bits (100 * (k + Nat.log 2 (μin (k - 1)) + 1)) (gT μin (k - 1) S) := by
  refine ⟨fun j hj x hx => sizes_step hF hj x hx, ?_⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- `k = 1`: `g_0 = f_0`, with values in `(1/6)ℤ` and at most `4/3`
    obtain rfl : k = 1 := by have := hF.1; omega
    intro S
    refine bits_of 6 rfl (by norm_num) (sizes_g_den hF 0 (by omega) S) ?_ ?_
    · have : (6 : ℝ) ≤ 2 ^ 3 := by norm_num
      exact this.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    · have h := abs_f₀_le S
      have : (4 / 3 : ℝ) ≤ 2 ^ 1 := by norm_num
      exact h.trans (this.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  · -- `k ≥ 2`: `g_{k−1} = g_{j+1}` with `j = k − 2` (`sizes_g`, `sizes_g_den`)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    intro S
    obtain ⟨-, hg⟩ := sizes_g hF (le_refl (j + 2)) S
    obtain ⟨-, -, -, hΩge, hΩX, -⟩ := sizes_units hF (le_refl (j + 2))
    obtain ⟨-, -, -, -, -, hD, -, -⟩ := sizes_dens hF (le_refl (j + 2))
    have hDpos : 0 < 𝔇 μin (j + 1) := by unfold 𝔇 𝔈 dδ; have := μin0_pos hF; positivity
    have hb := sizes_prim hF (le_refl (j + 2)) (𝔇 μin (j + 1)) hDpos
      (sizes_g_den hF (j + 1) (by omega) S) hD (by linarith)
    exact hb.mono (by omega)

end

end Hardness

end Stoc
