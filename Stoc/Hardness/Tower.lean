-- stamp r9 2026-11-02
import Stoc.Hardness.Base
import Stoc.Hardness.Step

/-!
# The levels and the parameter rule

The STOC version's `def:tower` ("the levels") and `def:ruleP` ("the parameter rule") (Appendix C.5,
`sec:D-base`, "The steps and the parameter rule", `stoc-sections/appD-hardness.tex:551-715`), and
parts (a)–(c) of `lem:weights` (Appendix C.7, `stoc-sections/appD-hardness.tex:1228-1236`, proof
lines 1249-1269), which concern the levels alone and which the paragraph after `def:ruleP` uses:
the rewards are integers, `M_k` is the largest reward of `E_k`, so `d ≥ 0` and every step is an
extension in the setting of `thm:splice` (`stepD_hyp`, `fpHyp_gT`).

* `δT`, `μT`, `R1T`, `ΓT`: the width `δ = 1/(3μ^in_1)`, the translations `μ_j = δ μ^in_{j+1}`,
  `R_1^{(j)} = ζ_1 + ∑_{i ≤ j} μ_i + ε_0` and `Γ_j = {ζ_1 + ∑_{i ∈ Q} μ_i : Q ⊆ {0, …, j}}`, in
  the closed forms of `def:tower`; the recursions are `R1T_succ`, `ΓT_succ`.
* `ι`: the constant `ι = 1/100` that (P6) uses (the text before `def:ruleP`).
* `Level`, `Level.step`, `Level.next`: the parameter rule (`def:ruleP`, `tab:ruleP`). A `Level`
  holds the data of level `k` that the rule uses: `k`, the rewards and curvatures of the elements
  of `E_k`, `M_k`, the line `p_k + q_k α` and `ρ̄_k`. The numbers (P1)–(P8) are defined as the rule
  defines them (`Level.d` is the `d_e` of (P3) for `e ∈ E_k`, and `Level.dEk`, `Level.dE` and
  `Level.Pcal` are the sums `d(E_k)`, `d(E)` and `Π`); `Level.Fτ₂` is `F_{τ_2}` of (P6), given by
  its closed formula, with the equation that (P6) states for it (`Level.Fτ₂_spec`), and
  `Level.Fτ₁ = F_{τ_2} + ΔF`; `Level.βb` is `β_b` of (P2), the curvature of `b` (`βT_succ_none`).
* `lvl`, `stepD`, `mT`, `βT`, `gT`: the levels of `def:tower` for an input `μin`, built by the
  parameter rule; `gT μin k` is `g_k` on `E_k = Gr k`.
* `weights_a`, `weights_b`, `weights_c`: `lem:weights`(a)–(c).

Indices of the input from 0: `μin i` is the STOC version's `μ^in_{i+1}`. The ground set `E_k` is
the type `Gr k`; step `k + 1` adds `b = none`, `τ_2 = some none` and `τ_1 = some (some none)` to
level `k`, to `E_k`, whose elements are the `some (some (some c))`.

Taken over on 2026-10-20 from `Paper/Hardness/Tower.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### The ground sets -/

/-- The ground set `E_k` of level `k`: `Gr 0 = Fin 3` (the base elements `C₀, C₁, C₂`), and step
`k + 1` adds `b = none`, `τ_2 = some none` and `τ_1 = some (some none)` to level `k`, `Gr k`
(`def:tower`: "For `j ≥ 1`, step `j` adds three elements `τ_{1,j}, τ_{2,j}, b_j` to level
`j − 1`"). -/
def Gr : ℕ → Type
  | 0 => Fin 3
  | k + 1 => Option (Option (Option (Gr k)))

instance instFintypeGr : (k : ℕ) → Fintype (Gr k)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | k + 1 => haveI := instFintypeGr k
    inferInstanceAs (Fintype (Option (Option (Option (Gr k)))))

instance instDecEqGr : (k : ℕ) → DecidableEq (Gr k)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | k + 1 => haveI := instDecEqGr k
    inferInstanceAs (DecidableEq (Option (Option (Option (Gr k)))))

/-! ### `def:tower`: the inputs, the windows and the contacts -/

/-- The constant `ι = 1/100` that (P6) of the parameter rule uses, the length of a short stretch
`[R_0 − ι, R_0]` to the left of the windows (the text before `def:ruleP`,
`stoc-sections/appD-hardness.tex:607-612`). -/
def ι : ℝ := 1 / 100

section Inputs

variable (μin : ℕ → ℕ)

/-- The width `δ = 1/(3μ^in_1)` (`def:tower`; `μin 0` is `μ^in_1`). -/
def δT : ℝ := 1 / (3 * μin 0)

/-- The translation `μ_j = δ μ^in_{j+1}` of level `j` (`def:tower`; `μin j` is `μ^in_{j+1}`). -/
def μT (j : ℕ) : ℝ := δT μin * μin j

/-- `R_1^{(j)} = ζ_1 + ∑_{i=0}^{j} μ_i + ε_0`, the right end of the window
`𝓡_j = [R_0, R_1^{(j)}]` (`def:tower`). -/
def R1T (j : ℕ) : ℝ := ζ₁ + ∑ i ∈ range (j + 1), μT μin i + ε₀

/-- The contact set `Γ_j = {ζ_1 + ∑_{i ∈ Q} μ_i : Q ⊆ {0, …, j}}` (`def:tower`). -/
def ΓT (j : ℕ) : Finset ℝ :=
  (range (j + 1)).powerset.image fun Q => ζ₁ + ∑ i ∈ Q, μT μin i

variable {μin}

/-- `μ_0 = 1/3 = ζ_2 − ζ_1`. -/
lemma μT_zero (h : 0 < μin 0) : μT μin 0 = 1 / 3 := by
  have : (0 : ℝ) < μin 0 := by exact_mod_cast h
  unfold μT δT
  field_simp

lemma μT_nonneg (j : ℕ) : 0 ≤ μT μin j := by
  unfold μT δT
  positivity

/-- The recursion of the windows (after `def:tower`): `R_1^{(j+1)} = R_1^{(j)} + μ_{j+1}`. -/
lemma R1T_succ (j : ℕ) : R1T μin (j + 1) = R1T μin j + μT μin (j + 1) := by
  unfold R1T
  rw [sum_range_succ]
  ring

/-- The recursion of the contact sets (after `def:tower`):
`Γ_{j+1} = Γ_j ∪ (Γ_j + μ_{j+1})`. -/
lemma ΓT_succ (j : ℕ) : ΓT μin (j + 1) = ΓT μin j ∪ (ΓT μin j).image (· + μT μin (j + 1)) := by
  have key : ((range (j + 1)).powerset.image (insert (j + 1))).image
      (fun Q => ζ₁ + ∑ i ∈ Q, μT μin i) = (ΓT μin j).image (· + μT μin (j + 1)) := by
    rw [ΓT, image_image, image_image]
    refine image_congr fun Q hQ => ?_
    have hn : j + 1 ∉ Q := fun h => by
      have := mem_powerset.1 (mem_coe.1 hQ) h
      simp at this
    simp only [Function.comp, sum_insert hn]
    ring
  rw [ΓT, range_add_one, powerset_insert, image_union, key]
  rfl

end Inputs

/-! ### `def:ruleP` -/

/-- The data of level `k` that the parameter rule uses (`def:ruleP`, Definition C.12,
`stoc-sections/appD-hardness.tex:614-650`): the level `k`, the rewards `m` and the curvatures `β`
of the elements of `E_k` (the type `C`), `M_k`, the line `L_k(α) = p_k + q_k α`, and `ρ̄_k`. -/
structure Level (C : Type*) where
  /-- the level `k` -/
  k : ℕ
  /-- the rewards of `E_k` -/
  m : C → ℝ
  /-- the curvatures of `E_k` -/
  β : C → ℝ
  /-- `M_k` -/
  M : ℝ
  /-- `p_k` -/
  p : ℝ
  /-- `q_k` -/
  q : ℝ
  /-- `ρ̄_k` -/
  ρbar : ℝ

namespace Level

variable {C : Type*} [Fintype C] (L : Level C) (μ R1 : ℝ)

/-- (P1): `m_δ = M/2`. -/
def mδ : ℝ := L.M / 2

/-- (P1): `m_* = m_δ + 64M`. -/
def mstar : ℝ := L.mδ + 64 * L.M

/-- (P2): `β_δ` with `1/β_δ = (3/4)·8^k`. -/
def βδ : ℝ := 1 / (3 / 4 * 8 ^ L.k)

/-- (P2): `β_b = β_δ/12`. -/
def βb : ℝ := L.βδ / 12

/-- (P3): `w = 64Mμ`. -/
def w : ℝ := 64 * L.M * μ

/-- (P3): `d_e = μ(m_* − m_e)/β_e` for `e ∈ E_k`. -/
def d (c : C) : ℝ := μ * (L.mstar - L.m c) / L.β c

/-- (P3): `d` on `E = E_k ∪ {τ_1, τ_2}` (`τ_2 = none`, `τ_1 = some none`):
`d_{τ_1} = d_{τ_2} = w/β_δ` and `d_e` on `E_k`. -/
def dE' (e : Option (Option C)) : ℝ :=
  Option.elim e (L.w μ / L.βδ) fun o => Option.elim o (L.w μ / L.βδ) (L.d μ)

/-- `d(E_k) = ∑_{e ∈ E_k} d_e`. -/
def dEk : ℝ := ∑ c, L.d μ c

/-- `d(E) = ∑_{e ∈ E} d_e`. -/
def dE : ℝ := ∑ e, L.dE' μ e

/-- (P3): `d̄ = d(E_k)/d_{τ_1}`. -/
def dbar : ℝ := L.dEk μ / (L.w μ / L.βδ)

/-- (P4): `Δ_b = 415M/2`. -/
def Δb : ℝ := 415 / 2 * L.M

/-- (P4): `m_b = m_δ + Δ_b`. -/
def mb : ℝ := L.mδ + L.Δb

/-- (P4): `s = (12/13)Δ_b`. -/
def s : ℝ := 12 / 13 * L.Δb

/-- (P4): `m̄ = m_δ + s`. -/
def mbar : ℝ := L.mδ + L.s

/-- (P4): `ψ_{k+1} = (12/13)Δ_b²/β_δ`. -/
def ψ : ℝ := 12 / 13 * L.Δb ^ 2 / L.βδ

/-- (P5): `Π = ∑_{e ∈ E_k} (m_δ − m_e) d_e`. -/
def Pcal : ℝ := ∑ c, (L.mδ - L.m c) * L.d μ c

/-- (P5): `ΔF = w/β_δ + d(E_k) − (q_k μ − Π)/s`. -/
def ΔF : ℝ := L.w μ / L.βδ + L.dEk μ - (L.q * μ - L.Pcal μ) / L.s

/-- (P6): `a_2 = (12/13)(μ − |𝓡|/2)` with `|𝓡| = R_1 − R_0`. -/
def a2 (μ R1 : ℝ) : ℝ := 12 / 13 * (μ - (R1 - R0) / 2)

/-- (P6): `a_0 = β_δ(q_k μ − Π)`. -/
def a0 : ℝ := L.βδ * (L.q * μ - L.Pcal μ)

/-- (P6): `u^0 = a_2 Δ_b − (1/2 + d̄)w + a_0/Δ_b`. -/
def u0 : ℝ := a2 μ R1 * L.Δb - (1 / 2 + L.dbar μ) * L.w μ + L.a0 μ / L.Δb

/-- (P6): `F_{τ_2} = (R_0 m_δ − ρ̄_k − w + u^0 − sι)/β_δ`, so that
`R_0 m_δ − β_δ F_{τ_2} = ρ̄_k + w − u^0 + sι` (`Fτ₂_spec`). -/
def Fτ₂ : ℝ := (R0 * L.mδ - L.ρbar - L.w μ + L.u0 μ R1 - L.s * ι) / L.βδ

/-- (P6): `F_{τ_1} = F_{τ_2} + ΔF`. -/
def Fτ₁ : ℝ := L.Fτ₂ μ R1 + L.ΔF μ

/-- (P7): `K = d(E) + 12F_{τ_1} − 13(w/2 − s(R_0 + R_1)/2)/β_δ`. -/
def K : ℝ := L.dE μ + 12 * L.Fτ₁ μ R1 - 13 * (L.w μ / 2 - L.s * (R0 + R1) / 2) / L.βδ

/-- (P8): `Δ_p = m_δ F_{τ_2} + (K − d(E) + F_{τ_1}) m̄`. -/
def Δp : ℝ := L.mδ * L.Fτ₂ μ R1 + (L.K μ R1 - L.dE μ + L.Fτ₁ μ R1) * L.mbar

/-- The numbers of the step `k → k + 1` as a `StepData`: `μ`, `m_*`, `m_δ`, `β_δ`, `m_b`, `F_{τ_1}`,
`F_{τ_2}` and `K` (with `β_b = β_δ/12` in `StepData.βNew`). -/
def step : StepData := ⟨μ, L.mstar, L.mδ, L.βδ, L.mb, L.Fτ₁ μ R1, L.Fτ₂ μ R1, L.K μ R1⟩

/-- Level `k + 1` (`def:ruleP`, last paragraph): `m_δ^{(k+1)} = m_δ`, `β_δ^{(k+1)} = β_δ`,
`M_{k+1} = m_b`, the new elements `τ_1, τ_2` with reward `m_δ` and curvature `β_δ` and `b` with
reward `m_b` and curvature `β_δ/12`, (P8) `q_{k+1} = q_k + ψ_{k+1}` and `p_{k+1} = p_k + Δ_p`, and
`ρ̄_{k+1} = R_0 m_δ^{(k+1)} − β_δ^{(k+1)} F_{τ_2}^{(k+1)}` (P6). -/
def next : Level (Option (Option (Option C))) where
  k := L.k + 1
  m := (L.step μ R1).mNew L.m
  β := (L.step μ R1).βNew L.β
  M := L.mb
  p := L.p + L.Δp μ R1
  q := L.q + L.ψ
  ρbar := R0 * L.mδ - L.βδ * L.Fτ₂ μ R1

omit [Fintype C] in
lemma βδ_pos : 0 < L.βδ := by unfold βδ; positivity

omit [Fintype C] in
lemma inv_βδ : 1 / L.βδ = 3 / 4 * 8 ^ L.k := by
  unfold βδ
  rw [one_div_one_div]

/-- (P6): `F_{τ_2} := (R_0 m_δ − ρ̄_k − w + u^0 − sι)/β_δ`, "so that
`R_0 m_δ − β_δ F_{τ_2} = ρ̄_k + w − u^0 + sι`". -/
lemma Fτ₂_spec : R0 * L.mδ - L.βδ * L.Fτ₂ μ R1 = L.ρbar + L.w μ - L.u0 μ R1 + L.s * ι := by
  have hβ := L.βδ_pos.ne'
  unfold Fτ₂
  field_simp
  ring

@[simp] lemma step_μ : (L.step μ R1).μ = μ := rfl
@[simp] lemma step_mstar : (L.step μ R1).mstar = L.mstar := rfl
@[simp] lemma step_mδ : (L.step μ R1).mδ = L.mδ := rfl
@[simp] lemma step_βδ : (L.step μ R1).βδ = L.βδ := rfl
@[simp] lemma step_mb : (L.step μ R1).mb = L.mb := rfl
@[simp] lemma step_Fτ₁ : (L.step μ R1).Fτ₁ = L.Fτ₁ μ R1 := rfl
@[simp] lemma step_Fτ₂ : (L.step μ R1).Fτ₂ = L.Fτ₂ μ R1 := rfl
@[simp] lemma step_K : (L.step μ R1).K = L.K μ R1 := rfl

/-- `m_* − m_δ = 64M`, so `w = (m_* − m_δ)μ` (`tab:ruleP`). -/
lemma w_eq_step : (L.step μ R1).w = L.w μ := by
  simp only [StepData.w, step_μ, step_mstar, step_mδ, mstar, w]
  ring

/-- `d = m_* μ β⁻¹ − μ t` on `E` (P3): the parameter rule's `d` is the `d` of the step. -/
lemma dStep_eq (e : Option (Option C)) : (L.step μ R1).dStep L.m L.β e = L.dE' μ e := by
  rcases e with _ | _ | c
  · simp only [StepData.dStep, StepData.mf_none, StepData.βf_none, dE', Option.elim, step_μ,
      step_mstar, step_mδ, step_βδ, w, mstar]
    ring
  · simp only [StepData.dStep, StepData.mf_τ₁, StepData.βf_τ₁, dE', Option.elim, step_μ,
      step_mstar, step_mδ, step_βδ, w, mstar]
    ring
  · rfl

/-- `d(E)` of the parameter rule is `d(E)` of the step. -/
lemma dE_eq_step : (L.step μ R1).dE L.m L.β = L.dE μ := by
  unfold StepData.dE dE
  exact sum_congr rfl fun e _ => L.dStep_eq μ R1 e

/-- `d(E) = d(E_k) + 2 w/β_δ`, as `d_{τ_1} = d_{τ_2} = w/β_δ` (P3). -/
lemma dE_split : L.dE μ = L.dEk μ + 2 * (L.w μ / L.βδ) := by
  unfold dE dEk
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [dE', Option.elim]
  ring

/-- `m̄ = (12m_b + m_δ)/13` and `s = m̄ − m_δ` (`tab:ruleP`): the numbers of the step. -/
lemma mbar_eq_step : (L.step μ R1).mbar' = L.mbar := by
  simp only [StepData.mbar', step_mb, step_mδ, mbar, mb, s]
  ring

lemma s_eq_step : (L.step μ R1).s = L.s := by
  simp only [StepData.s, mbar_eq_step, mbar, step_mδ]
  ring

/-- `ψ_{k+1} = SSq({b, τ_1})` of the step: `(12/13)Δ_b²/β_δ = 12(m_b − m_δ)²/(13 β_δ)`. -/
lemma ψ_eq_step : (L.step μ R1).ψ = L.ψ := by
  simp only [StepData.ψ, step_mb, step_mδ, step_βδ, ψ, mb]
  have := L.βδ_pos.ne'
  field_simp
  ring

/-- `Δ_p` of (P8) is `Δ_p` of `lem:dmt` for the step. -/
lemma Δp_eq_step : (L.step μ R1).Δp L.m L.β = L.Δp μ R1 := by
  simp only [StepData.Δp, dE_eq_step, mbar_eq_step, step_mδ, step_Fτ₂, step_K, step_Fτ₁, Δp]

end Level

/-! ### The levels -/

/-- The data of the base, level `0`: `k = 0`, `m = (5, 12, 4)`, `β = (1, 4, 4)`, `M_0 = 12`,
`p_0 = 10`, `q_0 = 7` and `ρ̄_0 = 7/6`. -/
def baseLevel : Level (Fin 3) := ⟨0, Base.m, Base.β, 12, p₀, q₀, 7 / 6⟩

section Tower

variable (μin : ℕ → ℕ)

/-- The levels of `def:tower` for the input `μin`, with the data that the parameter rule uses:
level `k + 1` is built from level `k` by the parameter rule with `μ = μ_{k+1}` and
`R_1 = R_1^{(k)}`. -/
def lvl : (k : ℕ) → Level (Gr k)
  | 0 => baseLevel
  | k + 1 => (lvl k).next (μT μin (k + 1)) (R1T μin k)

/-- The numbers of the step `k → k + 1` (the parameter rule with `μ = μ_{k+1}` and
`R_1 = R_1^{(k)}`). -/
def stepD (k : ℕ) : StepData := (lvl μin k).step (μT μin (k + 1)) (R1T μin k)

/-- The rewards of level `k`. -/
def mT (k : ℕ) : Gr k → ℝ := (lvl μin k).m

/-- The curvatures of level `k`. -/
def βT (k : ℕ) : Gr k → ℝ := (lvl μin k).β

/-- `g_k` (`def:tower`, Definition C.11, `stoc-sections/appD-hardness.tex:553-591`): `g_0 = f_0`,
and `g_{k+1}` is the extension of `f_{k+1} = g_k ⊕ π_{F_{τ_1}} ⊕ π_{F_{τ_2}}` by `b_{k+1}` with
`d_{k+1}` and `K_{k+1}`. -/
def gT : (k : ℕ) → Finset (Gr k) → ℝ
  | 0 => Base.f₀
  | k + 1 => (stepD μin k).gNew (gT k) (mT μin k) (βT μin k)

/-- The gap `L_j(α) − r(ξ^{(j)}(α))` of level `j` (`def:tower`). -/
def gapT (j : ℕ) (α : ℝ) : ℝ :=
  gap (gT μin j) (mT μin j) (βT μin j) (lvl μin j).p (lvl μin j).q α

/-- `ϖ_j = 1/β_δ^{(j)}` for `j ≥ 1`, and `ϖ_0 = 1` (before `lem:weights`). -/
def ϖ : ℕ → ℝ
  | 0 => 1
  | j + 1 => 1 / (lvl μin j).βδ

variable {μin}

@[simp] lemma lvl_k (k : ℕ) : (lvl μin k).k = k := by
  induction k with
  | zero => rfl
  | succ k ih => show (lvl μin k).k + 1 = k + 1; rw [ih]

lemma mT_succ (k : ℕ) : mT μin (k + 1) = (stepD μin k).mNew (mT μin k) := rfl

/-- (P2) and `def:tower`: the new element `b_{k+1}` of level `k + 1` has the curvature
`β_b = β_δ/12` of the step `k → k + 1`. -/
lemma βT_succ_none (k : ℕ) : βT μin (k + 1) none = (lvl μin k).βb := rfl

lemma M_succ (k : ℕ) : (lvl μin (k + 1)).M = (lvl μin k).mb := rfl

lemma q_succ (k : ℕ) : (lvl μin (k + 1)).q = (lvl μin k).q + (lvl μin k).ψ := rfl

/-- `ϖ_{j+1} = (3/4)·8^j`. -/
lemma ϖ_succ (j : ℕ) : ϖ μin (j + 1) = 3 / 4 * 8 ^ j := by
  show 1 / (lvl μin j).βδ = _
  rw [Level.inv_βδ, lvl_k]

lemma ϖ_pos (j : ℕ) : 0 < ϖ μin j := by
  cases j with
  | zero => show (0 : ℝ) < 1; norm_num
  | succ j => rw [ϖ_succ]; positivity

lemma sum_three {α : Type*} [Fintype α] (y : Option (Option (Option α)) → ℝ) :
    ∑ e, y e = y none + y (some none) + y (some (some none)) + ∑ c, y (some (some (some c))) := by
  rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_option]
  ring

/-! ### `lem:weights`(a)–(c) -/

/-- **`lem:weights`(a)** (Lemma C.20, `stoc-sections/appD-hardness.tex:1230-1233`, proof lines
1249-1254): `β⁻¹(E_k) = 2ϖ_{k+1}` for every `k ≥ 0`; hence `β⁻¹({τ_{1,k+1}, τ_{2,k+1}}) = β⁻¹(E_k)`
and `β⁻¹(E_k ∪ {τ_{1,k+1}, τ_{2,k+1}, b_{k+1}}) = 16ϖ_{k+1}` for `k ≥ 0`, and
`β⁻¹(E_k ∖ {b_k}) = 4ϖ_k` for `k ≥ 1` (here at level `k + 1`, whose elements other than
`b_{k+1} = none` are the `some e`).

The proof's steps: (1) by induction on `k`, `β⁻¹(E_0) = 3/2 = 2ϖ_1`, and by (P2) the step
`k → k + 1` adds `1/β_{τ_1} = 1/β_{τ_2} = ϖ_{k+1}` and `1/β_b = 12ϖ_{k+1}`, so
`β⁻¹(E_{k+1}) = β⁻¹(E_k) + 14ϖ_{k+1} = 16ϖ_{k+1} = 2ϖ_{k+2}`; (2) this gives the first two
consequences; (3) for `k ≥ 1`, `1/β_{b_k} = 12ϖ_k` and `β⁻¹(E_k) = 16ϖ_k`, so
`β⁻¹(E_k ∖ {b_k}) = 4ϖ_k`. -/
theorem weights_a :
    (∀ k, ∑ e, 1 / βT μin k e = 2 * ϖ μin (k + 1)) ∧
    (∀ k, 1 / (stepD μin k).βδ + 1 / (stepD μin k).βδ = ∑ e, 1 / βT μin k e) ∧
    (∀ k, ∑ e, 1 / βT μin (k + 1) e = 16 * ϖ μin (k + 1)) ∧
    (∀ k, ∑ e : Option (Option (Gr k)), 1 / βT μin (k + 1) (some e) = 4 * ϖ μin (k + 1)) := by
  -- (1) "By induction on `k`. First, `β⁻¹(E_0) = 1 + 1/4 + 1/4 = 3/2 = 2ϖ_1`. By (P2), the step
  -- `k → k + 1` adds `1/β_{τ_1} = 1/β_{τ_2} = ϖ_{k+1}` and `1/β_b = 12ϖ_{k+1}`, so
  -- `β⁻¹(E_{k+1}) = β⁻¹(E_k) + 14ϖ_{k+1} = 16ϖ_{k+1} = 2ϖ_{k+2}`."
  have hτ₁ : ∀ k, 1 / (lvl μin k).βδ = ϖ μin (k + 1) := fun k => rfl
  have hb : ∀ k, 1 / βT μin (k + 1) none = 12 * ϖ μin (k + 1) := fun k => by
    rw [βT_succ_none, ← hτ₁ k]
    have := (lvl μin k).βδ_pos.ne'
    unfold Level.βb
    field_simp
  have hstep : ∀ k, ∑ e, 1 / βT μin (k + 1) e = ∑ e, 1 / βT μin k e + 14 * ϖ μin (k + 1) := by
    intro k
    change ∑ e : Option (Option (Option (Gr k))), 1 / βT μin (k + 1) e = _
    rw [sum_three, hb k]
    change 12 * ϖ μin (k + 1) + 1 / (lvl μin k).βδ + 1 / (lvl μin k).βδ +
      ∑ c, 1 / βT μin k c = _
    rw [hτ₁ k]
    ring
  have h1 : ∀ k, ∑ e, 1 / βT μin k e = 2 * ϖ μin (k + 1) := by
    intro k
    induction k with
    | zero =>
      show ∑ e : Fin 3, 1 / Base.β e = 2 * ϖ μin 1
      rw [Fin.sum_univ_three, ϖ_succ]
      simp [Base.β]
      norm_num
    | succ k ih =>
      rw [hstep, ih, ϖ_succ, ϖ_succ]
      ring
  refine ⟨h1, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · -- (2) "This gives the first two consequences."
    rw [h1 k]
    change 1 / (lvl μin k).βδ + 1 / (lvl μin k).βδ = _
    rw [hτ₁ k]
    ring
  · rw [hstep, h1 k]
    ring
  · -- (3) "For `k ≥ 1`, `1/β_{b_k} = 12ϖ_k` and `β⁻¹(E_k) = 2ϖ_{k+1} = 16ϖ_k`, so
    -- `β⁻¹(E_k ∖ {b_k}) = 4ϖ_k`."
    have h := h1 (k + 1)
    change ∑ e : Option (Option (Option (Gr k))), 1 / βT μin (k + 1) e = _ at h
    rw [Fintype.sum_option, hb k, ϖ_succ, ϖ_succ, pow_succ] at h
    rw [ϖ_succ]
    linarith

/-- **`lem:weights`(b)** (`stoc-sections/appD-hardness.tex:1234-1235`, proof lines 1256-1259):
for every `k ≥ 0`, all rewards of `E_k` are integers in `(0, M_k]`, and `M_k = 12 · 208^k` is the
reward of `C_1` if `k = 0` and of `b_k` if `k ≥ 1`.

The proof's steps: (1) by induction on `k`: the rewards of `E_0` are `5, 12, 4`, and
`M_0 = 12`; (2) by (P1) and (P4), the step `k → k + 1` adds the reward `M_k/2` (of `τ_1` and `τ_2`)
and `m_b = M_k/2 + (415/2)M_k = 208M_k = M_{k+1}` (of `b`), and `M_k/2` is an integer, as `M_k`
is even. -/
theorem weights_b :
    (∀ k (e : Gr k), ∃ n : ℕ, 0 < n ∧ mT μin k e = n ∧ (n : ℝ) ≤ (lvl μin k).M) ∧
    (∀ k, (lvl μin k).M = 12 * 208 ^ k) ∧
    mT μin 0 (show Gr 0 from (1 : Fin 3)) = (lvl μin 0).M ∧
    (∀ k, mT μin (k + 1) none = (lvl μin (k + 1)).M) := by
  -- "By induction on `k`", with `M_k = 12 · 208^k` and the rewards of `E_k` together.
  have key : ∀ k, (lvl μin k).M = 12 * 208 ^ k ∧
      ∀ e : Gr k, ∃ n : ℕ, 0 < n ∧ mT μin k e = n ∧ (n : ℝ) ≤ (lvl μin k).M := by
    intro k
    induction k with
    | zero =>
      -- (1) "The rewards of `E_0` are `5, 12, 4`, and `M_0 = 12`."
      refine ⟨by show (12 : ℝ) = 12 * 208 ^ 0; norm_num, fun e => ?_⟩
      show ∃ n : ℕ, 0 < n ∧ Base.m e = n ∧ (n : ℝ) ≤ 12
      fin_cases e
      · exact ⟨5, by norm_num, by simp [Base.m], by norm_num⟩
      · exact ⟨12, by norm_num, by simp [Base.m], by norm_num⟩
      · exact ⟨4, by norm_num, by simp [Base.m], by norm_num⟩
    | succ k ih =>
      obtain ⟨hMk', ih⟩ := ih
      -- (2) "By (P1) and (P4), the step `k → k + 1` adds the reward `(1/2)M_k` (of `τ_1` and
      -- `τ_2`) and `m_b = (1/2)M_k + (415/2)M_k = 208M_k = M_{k+1}` (of `b`), and `(1/2)M_k` is an
      -- integer, as `M_k` is even."
      have hM1' : (lvl μin (k + 1)).M = 12 * 208 ^ (k + 1) := by
        rw [M_succ]
        simp only [Level.mb, Level.mδ, Level.Δb, hMk']
        ring
      refine ⟨hM1', fun e => ?_⟩
      change Option (Option (Option (Gr k))) at e
      have hM1 : (lvl μin (k + 1)).M = 208 * (lvl μin k).M := by rw [hM1', hMk']; ring
      have hmδ : (stepD μin k).mδ = ((6 * 208 ^ k : ℕ) : ℝ) := by
        show (lvl μin k).M / 2 = _
        rw [hMk']
        push_cast
        ring
      have hMk : 0 < (lvl μin k).M := by rw [hMk']; positivity
      rcases e with _ | _ | _ | c
      · refine ⟨12 * 208 ^ (k + 1), by positivity, ?_, ?_⟩
        · show (lvl μin k).mb = _
          rw [← M_succ, hM1']
          push_cast
          ring
        · rw [hM1']
          push_cast
          exact le_rfl
      · refine ⟨6 * 208 ^ k, by positivity, ?_, ?_⟩
        · rw [mT_succ, StepData.mNew_some_apply, StepData.mf_none, hmδ]
        · rw [hM1, hMk']
          push_cast
          nlinarith [pow_pos (show (0 : ℝ) < 208 by norm_num) k]
      · refine ⟨6 * 208 ^ k, by positivity, ?_, ?_⟩
        · rw [mT_succ, StepData.mNew_some_apply, StepData.mf_τ₁, hmδ]
        · rw [hM1, hMk']
          push_cast
          nlinarith [pow_pos (show (0 : ℝ) < 208 by norm_num) k]
      · obtain ⟨n, hn, hval, hle⟩ := ih c
        refine ⟨n, hn, ?_, ?_⟩
        · rw [mT_succ, StepData.mNew_some_apply, StepData.mf_old, hval]
        · rw [hM1]
          linarith
  exact ⟨fun k => (key k).2, fun k => (key k).1, by simp [mT, lvl, baseLevel, Base.m],
    fun k => rfl⟩

/-- The `q_k` are positive, by induction on `k`, as `q_0 = 7 > 0` and `q_{k+1} = q_k + ψ_{k+1}`
with `ψ_{k+1} ≥ 0` (not in the paper: the proof of `lem:weights`(c) leaves this induction implicit
in "As `q_0 = 7 > 0`, this gives `q_k ≥ ψ_k`"). -/
lemma q_pos (k : ℕ) : 0 < (lvl μin k).q := by
  induction k with
  | zero => show (0 : ℝ) < q₀; unfold q₀; norm_num
  | succ k ih =>
    rw [q_succ]
    have := (lvl μin k).βδ_pos
    have : 0 ≤ (lvl μin k).ψ := by unfold Level.ψ; positivity
    linarith

/-- **`lem:weights`(c)** (`stoc-sections/appD-hardness.tex:1236`, proof lines 1261-1269):
`q_0 = 7`, and `(9/10)ϖ_k M_k² < q_k ≤ ϖ_k M_k²` for `k ≥ 1` (here for `k + 1`).

The proof's steps: (1) by (P2), (P4) and (P8), `q_{k+1} = q_k + ψ_{k+1}` with
`ψ_{k+1} = (12/13)ϖ_{k+1}Δ_b² = (12/13)(415/416)²ϖ_{k+1}M_{k+1}²`, and
`9/10 < (12/13)(415/416)² < 12/13`; (2) as `q_0 = 7 > 0`, `q_k ≥ ψ_k > (9/10)ϖ_k M_k²` for
`k ≥ 1`; (3) `q_1 = 7 + ψ_1 < ϖ_1 M_1²`, as `(1/13)ϖ_1 M_1² > 7`; (4) for `k ≥ 2`, by induction,
`q_{k−1} ≤ ϖ_{k−1}M_{k−1}² < (1/13)ϖ_k M_k²`, so `q_k < ϖ_k M_k²`. -/
theorem weights_c :
    (lvl μin 0).q = 7 ∧
    ∀ k, 9 / 10 * ϖ μin (k + 1) * (lvl μin (k + 1)).M ^ 2 < (lvl μin (k + 1)).q ∧
      (lvl μin (k + 1)).q ≤ ϖ μin (k + 1) * (lvl μin (k + 1)).M ^ 2 := by
  have hM := (weights_b (μin := μin)).2.1
  -- (1) "By (P2), (P4) and (P8), `q_{k+1} = q_k + ψ_{k+1}` with
  -- `ψ_{k+1} = (12/13)ϖ_{k+1}Δ_b² = (12/13)(415/416)²ϖ_{k+1}M_{k+1}²`, and
  -- `9/10 < (12/13)(415/416)² < 12/13`." (The inequality is checked by `nlinarith` and
  -- `norm_num` in (2) to (4).)
  have hψ : ∀ k, (lvl μin k).ψ =
      12 / 13 * (415 / 416) ^ 2 * ϖ μin (k + 1) * (lvl μin (k + 1)).M ^ 2 := by
    intro k
    rw [M_succ]
    show 12 / 13 * (lvl μin k).Δb ^ 2 / (lvl μin k).βδ = _ * (1 / (lvl μin k).βδ) * _
    simp only [Level.mb, Level.mδ, Level.Δb]
    have := (lvl μin k).βδ_pos.ne'
    field_simp
    ring
  refine ⟨rfl, fun k => ⟨?_, ?_⟩⟩
  · -- (2) "As `q_0 = 7 > 0`, this gives `q_k ≥ ψ_k > (9/10)ϖ_k M_k²` for `k ≥ 1`."
    rw [q_succ, hψ]
    have := q_pos (μin := μin) k
    have : 0 < ϖ μin (k + 1) * (lvl μin (k + 1)).M ^ 2 := by
      have := ϖ_pos (μin := μin) (k + 1)
      rw [hM]
      positivity
    nlinarith
  · induction k with
    | zero =>
      -- (3) "For the upper bound, `q_1 = 7 + ψ_1 < 7 + (12/13)ϖ_1M_1² < ϖ_1M_1²`, as
      -- `(1/13)ϖ_1M_1² = (1/13)·(3/4)·2496² > 7`."
      rw [q_succ, hψ, ϖ_succ, hM]
      show q₀ + _ ≤ _
      unfold q₀
      norm_num
    | succ k ih =>
      -- (4) "For `k ≥ 2`, by induction, `q_{k−1} ≤ ϖ_{k−1}M_{k−1}² = ϖ_kM_k²/(8·208²) <
      -- (1/13)ϖ_kM_k²`, so `q_k = q_{k−1} + ψ_k < (1/13 + 12/13)ϖ_kM_k²`."
      rw [q_succ, hψ]
      rw [ϖ_succ, hM] at ih
      rw [ϖ_succ, hM]
      have h8 : (0 : ℝ) < 8 ^ k := by positivity
      have h208 : (0 : ℝ) < 208 ^ k := by positivity
      have e1 : (3 / 4 * 8 ^ (k + 1) * (12 * 208 ^ (k + 1 + 1)) ^ 2 : ℝ) =
          8 * 208 ^ 2 * (3 / 4 * 8 ^ k * (12 * 208 ^ (k + 1)) ^ 2) := by ring
      rw [e1]
      have : 0 < 3 / 4 * 8 ^ k * (12 * 208 ^ (k + 1) : ℝ) ^ 2 := by positivity
      nlinarith

/-! ### The setting of every step (the paragraph after `def:ruleP`) -/

/-- The paragraph after `def:ruleP` (`stoc-sections/appD-hardness.tex:691-695`), for one step: as
`M_k` is the largest reward of `E_k` (`lem:weights`(b)), `m_* = m_δ + 64M ≥ M ≥ m_e` for every
`e ∈ E`, hence `d ≥ 0`; so, if `g_k` is submodular with `g_k(∅) = 0`, then `g_{k+1}` is an
extension of `f_{k+1}` as in the setting of `thm:splice` (`StepData.Hyp`). -/
lemma stepD_hyp_of {k : ℕ} (H : FPHyp (gT μin k) (βT μin k)) :
    (stepD μin k).Hyp (gT μin k) (mT μin k) (βT μin k) := by
  have hb := (weights_b (μin := μin)).1 k
  have hM := (weights_b (μin := μin)).2.1 k
  have hMpos : 0 < (lvl μin k).M := by rw [hM]; positivity
  refine ⟨H, (lvl μin k).βδ_pos, fun c => ?_, ?_, μT_nonneg _⟩
  · obtain ⟨n, -, hval, hle⟩ := hb c
    show mT μin k c ≤ (lvl μin k).mstar
    simp only [Level.mstar, Level.mδ]
    rw [hval]
    linarith
  · show (lvl μin k).mδ ≤ (lvl μin k).mstar
    simp only [Level.mstar]
    linarith

/-- Every level `g_k` is submodular with `g_k(∅) = 0`, with `β > 0`: `g_0 = f_0` is a rank
function (`prop:base`), and `g_{k+1}` is an extension with `d ≥ 0` (`lem:translation`(a),
`FPHyp.extend`). -/
theorem fpHyp_gT : ∀ k, FPHyp (gT μin k) (βT μin k)
  | 0 => Base.fpHyp_f₀
  | k + 1 => (stepD_hyp_of (fpHyp_gT k)).newHyp

/-- The setting of the step `k → k + 1` (the paragraph after `def:ruleP`): the hypotheses
`StepData.Hyp` of an extension as in `thm:splice` and `lem:dmt`. -/
theorem stepD_hyp (k : ℕ) : (stepD μin k).Hyp (gT μin k) (mT μin k) (βT μin k) :=
  stepD_hyp_of (fpHyp_gT k)

end Tower

end

end Hardness

end Stoc
