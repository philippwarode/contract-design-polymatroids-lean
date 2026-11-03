-- stamp r9 2026-11-03
import ContractDesignPolymatroids.Hardness.Splice

/-!
# One step of the construction: the doubly merged translation

The STOC version's `lem:dmt` (Appendix B.6.4, `sec:B-dmt`, "The doubly merged translation",
`stoc-sections/appB-tools.tex:458-539`), with its setting, and the configuration `(∅, ∅)` of the
proof of `lem:onelevel` (Appendix C.6, `stoc-sections/appD-hardness.tex:911-917`, `config_empty`).

Step `j` builds level `j` from level `j − 1`, the old function `(f_C, m_C, β_C)` (here
`(gC, mC, βC)`) on a finite type `C`, with two auxiliary elements (the dummies) and one new element.
The ground set `E = C ∪ {τ_1, τ_2}` is `Option (Option C)`: `τ_2` is `none`, `τ_1` is `some none`
and the old element `c` is `some (some c)`; the new element `b` is `none` in
`Option (Option (Option C))`. The function `f = f_C ⊕ π_{F_{τ_1}} ⊕ π_{F_{τ_2}}` is `fStep` (two
direct sums with modular singletons, `Stoc.Hardness.addSingleton`), `d_e = μ(m* − m_e)/β_e` is
`dStep`, `h = f − d` is `hStep`, and the extension `f'` of `f` by `b` with the constant `K` is
`gNew` (`def:tower`). The paper's named objects of the setting and of `lem:dmt`: `m̄` (`mbar'`),
`s`, `ψ`, `w`, `ΔF = F_{τ_1} − F_{τ_2}` (`ΔF`), `Δ_p` (`Δp`), the lines `L_C(α) = p_C + q_C α`
(`LC`) and `L(α) = L_C(α) + ψ α + Δ_p` (`L`), and `d(E)`, `d(C)` (`dE`, `dC`).

`lem:dmt`: the setting is `DmtSetting` (with `DmtSetting.hyp`, `dStep_eq_translation`,
`sum_dStep`, `DmtSetting.s_pos`, `mbar_block_τ₁`, `mbar_block_τ₂`, `SS_block_τ₁`, `SS_block_τ₂` for
its claims); the exact statement is `dmt`, the conjunction of its parts `dmt_a`, `dmt_b`, `dmt_c`,
which are derived from `dmt_a_aux` and `dmt_b_aux`, which carry the paper's proofs under `Hyp` (no
positivity of `m`, `μ ≥ 0`). The weak configurations are hypotheses, as in the paper. For (b),
`hStep_eq_addSingleton` is the direct-sum split of `h` and `xi_h_of_addSingleton` the application
of `lem:fullplane`(f) and of `lem:translation`(c) to `f_C`.

The configuration `(∅, ∅)` (`config_empty`) is (`eq:windows`), that is, `lem:windows`(a) with
`U = W = ∅` and `D = {b}` (`block_b_sums`, `mbar_block_b`, `SS_block_b`), with `lem:fullplane`(f)
and `lem:translation`(c) applied to all of `f` (`xi_h`, `xi_f_old`, `xi_f_τ₁`, `xi_f_τ₂`). The other
lemmas on one step that the later files use: the marginals of `f` and `h` (`rho_f_old`, `rho_f_τ₁`,
`rho_f_τ₂`, `rho_h_old`, `rho_h_τ₁`, `rho_h_τ₂`), the best responses `xi_f_old`, `xi_f_τ₁`,
`xi_f_τ₂`, `xi_h`, the marginal `θout` of `b` in a configuration of `lem:onelevel`,
and the values of `f` and the sums over the blocks that the windows of `lem:onelevel` use.

Taken over on 2026-10-20 from `Paper/Hardness/Step.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-- The numbers that fix one step, from level `j − 1` to level `j` (`def:tower`; the parameter rule,
`def:ruleP`, computes them; here they are free). -/
structure StepData where
  /-- the translation `μ` -/
  μ : ℝ
  /-- `m*`, at least every reward of the old level -/
  mstar : ℝ
  /-- the reward of the dummies -/
  mδ : ℝ
  /-- the curvature of the dummies -/
  βδ : ℝ
  /-- the reward of the new element `b` -/
  mb : ℝ
  /-- `F_{τ_1}` -/
  Fτ₁ : ℝ
  /-- `F_{τ_2}` -/
  Fτ₂ : ℝ
  /-- `K` -/
  K : ℝ

namespace StepData

variable (P : StepData) {C : Type*} [Fintype C] [DecidableEq C]

/-- `σ = m* μ`. -/
def σ : ℝ := P.mstar * P.μ

/-- `w = μ (m* − m_δ)`, the width of the bands of the dummies. -/
def w : ℝ := P.μ * (P.mstar - P.mδ)

/-- The rewards on `Option (Option C)`: `τ_2 = none`, `τ_1 = some none`, old elements. -/
def mf (mC : C → ℝ) : Option (Option C) → ℝ :=
  fun o => Option.elim o P.mδ fun o' => Option.elim o' P.mδ mC

/-- The curvatures on `Option (Option C)`. -/
def βf (βC : C → ℝ) : Option (Option C) → ℝ :=
  fun o => Option.elim o P.βδ fun o' => Option.elim o' P.βδ βC

/-- The rewards of the new level; `b = none` has `m_b`. -/
def mNew (mC : C → ℝ) : Option (Option (Option C)) → ℝ :=
  fun o => Option.elim o P.mb (P.mf mC)

/-- The curvatures of the new level; `b = none` has `β_b = β_δ / 12`. -/
def βNew (βC : C → ℝ) : Option (Option (Option C)) → ℝ :=
  fun o => Option.elim o (P.βδ / 12) (P.βf βC)

/-- `f = f_C ⊕ π_{F_{τ_1}} ⊕ π_{F_{τ_2}}`. -/
def fStep (gC : Finset C → ℝ) : Finset (Option (Option C)) → ℝ :=
  addSingleton (addSingleton gC P.Fτ₁) P.Fτ₂

/-- `d_e = μ (m* − m_e)/β_e`, that is, `d = σ β⁻¹ − μ t`. -/
def dStep (mC βC : C → ℝ) : Option (Option C) → ℝ :=
  fun e => P.μ * (P.mstar - P.mf mC e) / P.βf βC e

/-- The new level: the extension of `f` by `b` with `d` and `K`. -/
def gNew (gC : Finset C → ℝ) (mC βC : C → ℝ) : Finset (Option (Option (Option C))) → ℝ :=
  extend (P.fStep gC) (P.dStep mC βC) P.K

/-- `h = f − d`. -/
def hStep (gC : Finset C → ℝ) (mC βC : C → ℝ) : Finset (Option (Option C)) → ℝ :=
  subMod (P.fStep gC) (P.dStep mC βC)

variable {P} {gC : Finset C → ℝ} {mC βC : C → ℝ}

/-- The standing hypotheses of a step. -/
structure Hyp (P : StepData) (gC : Finset C → ℝ) (mC βC : C → ℝ) : Prop where
  old : FPHyp gC βC
  βδ_pos : 0 < P.βδ
  mstar_ge : ∀ c, mC c ≤ P.mstar
  mδ_le : P.mδ ≤ P.mstar
  μ_nonneg : 0 ≤ P.μ

section

omit [Fintype C]

/-- `f = f_C ⊕ π_{F_{τ_1}} ⊕ π_{F_{τ_2}}` is submodular with `f(∅) = 0` (`FPHyp.addSingleton`,
twice), with `β > 0` on `E`. -/
theorem Hyp.fHyp (H : P.Hyp gC mC βC) : FPHyp (P.fStep gC) (P.βf βC) :=
  (H.old.addSingleton (β' := fun o => Option.elim o P.βδ βC) H.βδ_pos P.Fτ₁).addSingleton
    (β' := P.βf βC) H.βδ_pos P.Fτ₂

/-- The setting of `sec:B-dmt` (`appB-tools.tex:469`, `484`): `d_e = μ(m* − m_e)/β_e ≥ 0`, as
`μ ≥ 0` and `m* ≥ max_{e∈E} m_e`. -/
theorem Hyp.d_nonneg (H : P.Hyp gC mC βC) (e : Option (Option C)) : 0 ≤ P.dStep mC βC e := by
  unfold dStep
  rcases e with _ | _ | c
  · exact div_nonneg (mul_nonneg H.μ_nonneg (sub_nonneg.2 H.mδ_le)) H.βδ_pos.le
  · exact div_nonneg (mul_nonneg H.μ_nonneg (sub_nonneg.2 H.mδ_le)) H.βδ_pos.le
  · exact div_nonneg (mul_nonneg H.μ_nonneg (sub_nonneg.2 (H.mstar_ge c))) (H.old.pos c).le

/-- The setting of `sec:B-dmt` (`appB-tools.tex:471`): as `d ≥ 0`, the extension `f'` is
submodular with `f'(∅) = 0` (`FPHyp.extend`, the proof of `lem:translation`(a)), with `β > 0` on
`E ∪ {b}`. -/
theorem Hyp.newHyp (H : P.Hyp gC mC βC) : FPHyp (P.gNew gC mC βC) (P.βNew βC) :=
  H.fHyp.extend (β' := P.βNew βC) H.d_nonneg (div_pos H.βδ_pos (by norm_num)) P.K

/-- `h` is the shift of `f` by `d = σ β⁻¹ − μ t`. -/
theorem hStep_eq_shift : P.hStep gC mC βC = shiftFun (P.fStep gC) (P.mf mC) (P.βf βC) P.σ P.μ := by
  funext T
  unfold hStep subMod shiftFun
  rw [← sum_shift]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  unfold dStep σ
  ring

end

/-! ### The marginals of `f` and `h` -/

section Densities

variable (H : P.Hyp gC mC βC) (α : ℝ)
include H

/-- `eq:D-bands` (`stoc-sections/appD-hardness.tex:722-728`), by `lem:fullplane`(f):
`ρ^f_e(α) = ρ^{f_C}_e(α)` for `e ∈ C`. -/
theorem rho_f_old (c : C) : rho (P.fStep gC) (P.mf mC) (P.βf βC) α (some (some c)) =
    rho gC mC βC α c := by
  unfold fStep
  rw [rho_addSingleton_some (H.old.addSingleton (β' := fun o => Option.elim o P.βδ βC)
    H.βδ_pos P.Fτ₁) H.βδ_pos]
  exact rho_addSingleton_some (β' := fun o => Option.elim o P.βδ βC) H.old H.βδ_pos P.Fτ₁ α c

/-- By `lem:fullplane`(f) (`stoc-sections/appD-hardness.tex:729`):
`ρ^f_{τ_1}(α) = α m_δ − β_δ F_{τ_1}`. -/
theorem rho_f_τ₁ :
    rho (P.fStep gC) (P.mf mC) (P.βf βC) α (some none) = α * P.mδ - P.βδ * P.Fτ₁ := by
  unfold fStep
  rw [rho_addSingleton_some (H.old.addSingleton (β' := fun o => Option.elim o P.βδ βC)
    H.βδ_pos P.Fτ₁) H.βδ_pos]
  exact rho_addSingleton_none (β' := fun o => Option.elim o P.βδ βC) H.old H.βδ_pos P.Fτ₁ α

/-- By `lem:fullplane`(f): `ρ^f_{τ_2}(α) = α m_δ − β_δ F_{τ_2}`. -/
theorem rho_f_τ₂ : rho (P.fStep gC) (P.mf mC) (P.βf βC) α none = α * P.mδ - P.βδ * P.Fτ₂ := by
  unfold fStep
  exact rho_addSingleton_none (H.old.addSingleton (β' := fun o => Option.elim o P.βδ βC)
    H.βδ_pos P.Fτ₁) H.βδ_pos P.Fτ₂ α

/-- By `lem:fullplane`(f), `ξ^f(α) = (ξ^{f_C}(α), F_{τ_1}, F_{τ_2})` (`appB-tools.tex:505`): the old
coordinates. -/
theorem xi_f_old (c : C) : xi (P.fStep gC) (P.mf mC) (P.βf βC) α (some (some c)) =
    xi gC mC βC α c := by
  unfold fStep
  rw [xi_addSingleton (H.old.addSingleton (β' := fun o => Option.elim o P.βδ βC)
    H.βδ_pos P.Fτ₁) H.βδ_pos]
  simp only [Option.elim]
  rw [xi_addSingleton (β' := fun e => P.βf βC (some e)) H.old H.βδ_pos]
  rfl

/-- By `lem:fullplane`(f): `ξ^f_{τ_1}(α) = F_{τ_1}`. -/
theorem xi_f_τ₁ : xi (P.fStep gC) (P.mf mC) (P.βf βC) α (some none) = P.Fτ₁ := by
  unfold fStep
  rw [xi_addSingleton (H.old.addSingleton (β' := fun o => Option.elim o P.βδ βC)
    H.βδ_pos P.Fτ₁) H.βδ_pos]
  simp only [Option.elim]
  rw [xi_addSingleton (β' := fun e => P.βf βC (some e)) H.old H.βδ_pos]
  rfl

/-- By `lem:fullplane`(f): `ξ^f_{τ_2}(α) = F_{τ_2}`. -/
theorem xi_f_τ₂ : xi (P.fStep gC) (P.mf mC) (P.βf βC) α none = P.Fτ₂ := by
  unfold fStep
  rw [xi_addSingleton (H.old.addSingleton (β' := fun o => Option.elim o P.βδ βC)
    H.βδ_pos P.Fτ₁) H.βδ_pos]
  rfl

/-- By `lem:translation`(c), applied to `f` with `(μ_α, μ_θ) = (μ, m* μ)` (`hStep_eq_shift`):
`ρ^h(α) = ρ^f(α − μ) + m* μ`. -/
theorem rho_h (e : Option (Option C)) : rho (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α e =
    rho (P.fStep gC) (P.mf mC) (P.βf βC) (α - P.μ) e + P.σ := by
  rw [hStep_eq_shift]
  exact rho_shift H.fHyp _ _ _ _ e

/-- By `lem:translation`(c), applied to `f` with `(μ_α, μ_θ) = (μ, m* μ)` (`hStep_eq_shift`):
`ξ^h(α) = ξ^f(α − μ) − d`. -/
theorem xi_h (e : Option (Option C)) : xi (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α e =
    xi (P.fStep gC) (P.mf mC) (P.βf βC) (α - P.μ) e - P.dStep mC βC e := by
  rw [hStep_eq_shift, xi_shift H.fHyp]
  unfold dStep σ
  ring

/-- `eq:D-bands` (`stoc-sections/appD-hardness.tex:722-728`), by `lem:fullplane`(f) and
`lem:translation`(c): `ρ^h_e(α) = ρ^{f_C}_e(α − μ) + m* μ` for `e ∈ C`. -/
theorem rho_h_old (c : C) : rho (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α (some (some c)) =
    rho gC mC βC (α - P.μ) c + P.σ := by
  rw [rho_h H, rho_f_old H]

/-- `ρ^h_{τ_1} = ρ^f_{τ_1} + w` (`stoc-sections/appD-hardness.tex:731-732`), as
`m* μ − μ m_δ = w`. -/
theorem rho_h_τ₁ : rho (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α (some none) =
    α * P.mδ - P.βδ * P.Fτ₁ + P.w := by
  rw [rho_h H, rho_f_τ₁ H]
  unfold σ w
  ring

/-- `ρ^h_{τ_2} = ρ^f_{τ_2} + w` (`stoc-sections/appD-hardness.tex:731-732`), as
`m* μ − μ m_δ = w`. -/
theorem rho_h_τ₂ : rho (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α none =
    α * P.mδ - P.βδ * P.Fτ₂ + P.w := by
  rw [rho_h H, rho_f_τ₂ H]
  unfold σ w
  ring

end Densities

end StepData

namespace StepData

variable {P : StepData} {C : Type*} [Fintype C] [DecidableEq C]
variable {gC : Finset C → ℝ} {mC βC : C → ℝ}

/-! ### The quantities of a step -/

variable (P) (mC βC)

/-- `d(E)` for `E = C ∪ {τ_1, τ_2}`. -/
def dE : ℝ := ∑ e, P.dStep mC βC e

/-- `d(C)`, the old part. -/
def dC : ℝ := ∑ c, P.dStep mC βC (some (some c))

/-- `m̄ = (12 m_b + m_δ)/13` (`appB-tools.tex:475`), the weighted mean reward of `{b, τ_1}` and of
`{b, τ_2}` (`mbar_block_τ₁`, `mbar_block_τ₂`). -/
def mbar' : ℝ := (12 * P.mb + P.mδ) / 13

/-- `s = m̄ − m_δ` (`appB-tools.tex:475`). -/
def s : ℝ := P.mbar' - P.mδ

/-- `ψ = 12 (m_b − m_δ)²/(13 β_δ)` (`appB-tools.tex:475`), which is `S_2({b, τ_1}) = S_2({b, τ_2})`
(`SS_block_τ₁`, `SS_block_τ₂`). -/
def ψ : ℝ := 12 * (P.mb - P.mδ) ^ 2 / (13 * P.βδ)

/-- `θ_out = α m_b − β_b K` (`stoc-sections/appD-hardness.tex:892`), the marginal of `b` in the
configuration `(∅, ∅)`, which is `θ_{U,W}` for `U = W = ∅` (`config_empty`). -/
def θout (α : ℝ) : ℝ := α * P.mb - P.βδ / 12 * P.K

/-- `ΔF = F_{τ_1} − F_{τ_2}` (`appB-tools.tex:477`). -/
def ΔF : ℝ := P.Fτ₁ - P.Fτ₂

/-- `Δ_p = m_δ F_{τ_2} + (K − d(E) + F_{τ_1}) m̄` (`lem:dmt`, `appB-tools.tex:484`). -/
def Δp : ℝ := P.mδ * P.Fτ₂ + (P.K - P.dE mC βC + P.Fτ₁) * P.mbar'

/-- The line `L_C(α) = p_C + q_C α` of `lem:dmt`(c) (`appB-tools.tex:494`). -/
def LC (pC qC α : ℝ) : ℝ := pC + qC * α

/-- The line `L(α) = L_C(α) + ψ α + Δ_p` of `lem:dmt`(c) (`appB-tools.tex:498`). -/
def L (pC qC α : ℝ) : ℝ := LC pC qC α + P.ψ * α + P.Δp mC βC

variable {P} {mC βC}

section

omit [Fintype C] [DecidableEq C]

lemma mNew_some : (fun e => P.mNew mC (some e)) = P.mf mC := rfl

lemma βNew_some : (fun e => P.βNew βC (some e)) = P.βf βC := rfl

@[simp] lemma mNew_some_apply (e : Option (Option C)) : P.mNew mC (some e) = P.mf mC e := rfl

@[simp] lemma mNew_none : P.mNew mC none = P.mb := rfl

@[simp] lemma mf_none : P.mf mC none = P.mδ := rfl

@[simp] lemma mf_τ₁ : P.mf mC (some none) = P.mδ := rfl

@[simp] lemma mf_old (c : C) : P.mf mC (some (some c)) = mC c := rfl

@[simp] lemma βNew_some_apply (e : Option (Option C)) : P.βNew βC (some e) = P.βf βC e := rfl

@[simp] lemma βNew_none : P.βNew βC none = P.βδ / 12 := rfl

@[simp] lemma βf_none : P.βf βC none = P.βδ := rfl

@[simp] lemma βf_τ₁ : P.βf βC (some none) = P.βδ := rfl

@[simp] lemma βf_old (c : C) : P.βf βC (some (some c)) = βC c := rfl

/-- The setting of `sec:B-dmt` (`appB-tools.tex:469`): `d_{τ_1} = w/β_δ` with `w = μ(m* − m_δ)`. -/
lemma dStep_τ₁ : P.dStep mC βC (some none) = P.w / P.βδ := by
  simp [dStep, mf, βf, w]

/-- The setting of `sec:B-dmt` (`appB-tools.tex:469`): `d_{τ_2} = w/β_δ` with `w = μ(m* − m_δ)`. -/
lemma dStep_τ₂ : P.dStep mC βC none = P.w / P.βδ := by
  simp [dStep, mf, βf, w]

end

omit [DecidableEq C] in
/-- `d(E) = d(C) + 2w/β_δ`, as `d_{τ_1} = d_{τ_2} = w/β_δ` (`appB-tools.tex:518`). -/
lemma dE_eq : P.dE mC βC = P.dC mC βC + 2 * (P.w / P.βδ) := by
  simp only [dE, dC, Fintype.sum_option, dStep_τ₁, dStep_τ₂]
  ring

omit [Fintype C] in
/-- The values of `f` that the windows use. -/
lemma fStep_apply (T : Finset (Option (Option C))) :
    P.fStep gC T = gC (eraseNone (eraseNone T)) + (if none ∈ eraseNone T then P.Fτ₁ else 0) +
      (if none ∈ T then P.Fτ₂ else 0) := rfl

/-! ### The setting of `sec:B-dmt` (`appB-tools.tex:466-479`) -/

variable (P) (gC) (mC βC)

/-- The setting of `sec:B-dmt` (`appB-tools.tex:466-479`) for the data `P` and the old function
`f_C = gC` with `m|_C = mC` and `β|_C = βC`, on `E = C ∪ {τ_1, τ_2}`: `f_C` is submodular with
`f_C(∅) = 0`, `m|_C, β|_C > 0`, `m_{τ_1} = m_{τ_2} = m_δ > 0` and `β_{τ_1} = β_{τ_2} = β_δ > 0` (the
rewards and curvatures of `E` are positive, as in the setting of `sec:B-extensions`), `μ > 0`,
`m* ≥ max_{e∈E} m_e`, and the new element `b` has `m_b > m_δ`; `β_b = β_δ/12` is built into
`βNew`, and `F_{τ_1}`, `F_{τ_2}`, `K` are arbitrary. -/
structure DmtSetting : Prop where
  submod : Submodular gC
  empty : gC ∅ = 0
  mC_pos : ∀ c, 0 < mC c
  βC_pos : ∀ c, 0 < βC c
  mδ_pos : 0 < P.mδ
  βδ_pos : 0 < P.βδ
  μ_pos : 0 < P.μ
  mstar_ge : ∀ e, P.mf mC e ≤ P.mstar
  mb_gt : P.mδ < P.mb

variable {P} {gC} {mC βC}

omit [Fintype C] in
/-- The setting of `sec:B-dmt` gives the standing hypotheses `Hyp` of the auxiliary lemmas. -/
theorem DmtSetting.hyp (hS : P.DmtSetting gC mC βC) : P.Hyp gC mC βC :=
  ⟨⟨hS.submod, hS.empty, hS.βC_pos⟩, hS.βδ_pos, fun c => hS.mstar_ge (some (some c)),
    hS.mstar_ge none, hS.μ_pos.le⟩

omit [Fintype C] [DecidableEq C] in
/-- The setting (`appB-tools.tex:469-470`): `d_e = μ(m* − m_e)/β_e` is the vector `d` of
`lem:translation` with `(μ_α, μ_θ) = (μ, m* μ)`, that is, `d_e = (m* μ − μ m_e)/β_e`. -/
lemma dStep_eq_translation (e : Option (Option C)) :
    P.dStep mC βC e = (P.mstar * P.μ - P.μ * P.mf mC e) / P.βf βC e := by
  unfold dStep
  ring

omit [Fintype C] [DecidableEq C] in
/-- The setting (`appB-tools.tex:469`): `d(S) = μ (m* β⁻¹(S) − t(S))` for `S ⊆ E`. -/
lemma sum_dStep (S : Finset (Option (Option C))) :
    ∑ e ∈ S, P.dStep mC βC e =
      P.μ * (P.mstar * ∑ e ∈ S, 1 / P.βf βC e - ∑ e ∈ S, P.mf mC e / P.βf βC e) := by
  rw [mul_sum, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun e _ => by unfold dStep; ring

omit [Fintype C] in
/-- The setting (`appB-tools.tex:475`): `s = m̄ − m_δ = 12 (m_b − m_δ)/13 > 0`, as `m_b > m_δ` (not
in the paper: it leaves implicit that `s ≠ 0`, which the formula for `ΔF` in `lem:dmt`(c) needs). -/
lemma DmtSetting.s_pos (hS : P.DmtSetting gC mC βC) : 0 < P.s := by
  have := hS.mb_gt
  unfold s mbar'
  linarith

end StepData

namespace StepData

variable {P : StepData} {C : Type*} [Fintype C] [DecidableEq C]
variable {gC : Finset C → ℝ} {mC βC : C → ℝ}

/-! ### Finite-set bookkeeping on `Option (Option C)` -/

omit [DecidableEq C] in
lemma sum_E (y : Option (Option C) → ℝ) :
    ∑ e, y e = y none + y (some none) + ∑ c, y (some (some c)) := by
  rw [Fintype.sum_option, Fintype.sum_option]
  ring

lemma sum_erase_τ₁ (y : Option (Option C) → ℝ) :
    ∑ e ∈ (univ : Finset (Option (Option C))).erase (some none), y e =
      y none + ∑ c, y (some (some c)) := by
  have h := add_sum_erase (univ : Finset (Option (Option C))) y (mem_univ (some none))
  rw [sum_E] at h
  linarith

lemma sum_compl_τ₂ (y : Option (Option C) → ℝ) :
    ∑ e ∈ ({none} : Finset (Option (Option C)))ᶜ, y e = y (some none) + ∑ c, y (some (some c)) := by
  have h := sum_add_sum_compl ({none} : Finset (Option (Option C))) y
  rw [sum_E, sum_singleton] at h
  linarith

/-- The block `D = (W ∖ U) ∪ {b}` for `(U, W) = (E ∖ {τ_1}, E)` is `{b, τ_1}`
(`appB-tools.tex:504`). -/
lemma insertNone_τ₁ :
    insertNone ((univ : Finset (Option (Option C))) \ univ.erase (some none)) =
      {none, some (some none)} := by
  ext o
  rcases o with _ | _ | _ | c <;> simp [mem_insertNone]

omit [Fintype C] in
/-- The block `D = (W ∖ U) ∪ {b}` for `(U, W) = (∅, {τ_2})` is `{b, τ_2}` (`appB-tools.tex:509`). -/
lemma insertNone_τ₂ :
    insertNone (({none} : Finset (Option (Option C))) \ ∅) = {none, some none} := by
  ext o
  rcases o with _ | _ | _ | c <;> simp [mem_insertNone]

/-- `f(E) = f_C(C) + F_{τ_1} + F_{τ_2}`. -/
lemma fStep_univ : P.fStep gC univ = gC univ + P.Fτ₁ + P.Fτ₂ := by
  rw [fStep_apply]
  simp [eraseNone_univ']

/-- `f(E ∖ {τ_1}) = f_C(C) + F_{τ_2}`, so `f(E) − f(E ∖ {τ_1}) = F_{τ_1}` (`appB-tools.tex:504`). -/
lemma fStep_erase_τ₁ : P.fStep gC ((univ : Finset (Option (Option C))).erase (some none)) =
    gC univ + P.Fτ₂ := by
  rw [fStep_apply]
  have h2 :
      eraseNone ((univ : Finset (Option (Option C))).erase (some none)) = univ.erase none := by
    ext o
    simp [mem_eraseNone]
  have h3 : eraseNone ((univ : Finset (Option C)).erase none) = univ := by
    ext c
    simp [mem_eraseNone]
  simp [h2, h3]

omit [Fintype C] in
/-- `f({τ_2}) = F_{τ_2}` (`appB-tools.tex:509`). -/
lemma fStep_τ₂ (h0 : gC ∅ = 0) : P.fStep gC ({none} : Finset (Option (Option C))) = P.Fτ₂ := by
  rw [fStep_apply]
  have h2 : eraseNone ({none} : Finset (Option (Option C))) = ∅ := by
    ext o
    simp
  simp [h2, h0]

omit [Fintype C] in
/-- `f(∅) = 0`. -/
lemma fStep_empty (h0 : gC ∅ = 0) : P.fStep gC (∅ : Finset (Option (Option C))) = 0 := by
  rw [fStep_apply]
  simp [h0]

/-! ### The blocks of the windows, `lem:dmt` and the configuration `(∅, ∅)` -/

section Windows

variable (H : P.Hyp gC mC βC)
include H

section

omit [Fintype C]

/-- `β_b = β_δ/12 > 0`. -/
lemma βb_pos : 0 < P.βδ / 12 := div_pos H.βδ_pos (by norm_num)

/-- `β > 0` on `E ∪ {b}`. -/
lemma newPos : ∀ o, 0 < P.βNew βC o := H.newHyp.pos

/-- The block `{b, τ_1}` of the first window: its sums. -/
lemma block_τ₁_sums :
    ∑ o ∈ ({none, some (some none)} : Finset (Option (Option (Option C)))), 1 / P.βNew βC o =
      13 / P.βδ ∧
    ∑ o ∈ ({none, some (some none)} : Finset (Option (Option (Option C)))),
      P.mNew mC o / P.βNew βC o = (12 * P.mb + P.mδ) / P.βδ := by
  have hne : (none : Option (Option (Option C))) ≠ some (some none) := by simp
  have := H.βδ_pos.ne'
  rw [sum_pair hne, sum_pair hne]
  simp only [βNew, mNew, βf, mf, Option.elim]
  constructor <;> field_simp
  ring

/-- The block `{b, τ_2}` of the second window: its sums. -/
lemma block_τ₂_sums :
    ∑ o ∈ ({none, some none} : Finset (Option (Option (Option C)))), 1 / P.βNew βC o =
      13 / P.βδ ∧
    ∑ o ∈ ({none, some none} : Finset (Option (Option (Option C)))),
      P.mNew mC o / P.βNew βC o = (12 * P.mb + P.mδ) / P.βδ := by
  have hne : (none : Option (Option (Option C))) ≠ some none := by simp
  have := H.βδ_pos.ne'
  rw [sum_pair hne, sum_pair hne]
  simp only [βNew, mNew, βf, mf, Option.elim]
  constructor <;> field_simp
  ring

/-- The setting (`appB-tools.tex:478`): `m̄` is the weighted mean reward `m̄_{{b,τ_1}}` of
`{b, τ_1}`, as `1/β_b = 12/β_δ`. -/
lemma mbar_block_τ₁ : mbar (P.mNew mC) (P.βNew βC) {none, some (some none)} = P.mbar' := by
  rw [mbar, (block_τ₁_sums H).1, (block_τ₁_sums H).2, mbar']
  have := H.βδ_pos.ne'
  field_simp

/-- The setting (`appB-tools.tex:478`): `m̄` is the weighted mean reward `m̄_{{b,τ_2}}` of
`{b, τ_2}`. -/
lemma mbar_block_τ₂ : mbar (P.mNew mC) (P.βNew βC) {none, some none} = P.mbar' := by
  rw [mbar, (block_τ₂_sums H).1, (block_τ₂_sums H).2, mbar']
  have := H.βδ_pos.ne'
  field_simp

/-- The setting (`appB-tools.tex:479`): `ψ = S_2({b, τ_1})`, as
`S_2({b, τ_1}) = (m_b − m_δ)²/(β_b + β_δ)` by `eq:B-pair` (`Stoc.Hardness.SS_pair`). -/
lemma SS_block_τ₁ : SS (P.mNew mC) (P.βNew βC) {none, some (some none)} = P.ψ := by
  have hne : (none : Option (Option (Option C))) ≠ some (some none) := by simp
  rw [SS_pair (newPos H) hne]
  have := H.βδ_pos.ne'
  simp only [βNew, mNew, βf, mf, Option.elim, ψ]
  field_simp
  ring

/-- The setting (`appB-tools.tex:479`): `ψ = S_2({b, τ_2})`, by `eq:B-pair`. -/
lemma SS_block_τ₂ : SS (P.mNew mC) (P.βNew βC) {none, some none} = P.ψ := by
  have hne : (none : Option (Option (Option C))) ≠ some none := by simp
  rw [SS_pair (newPos H) hne]
  have := H.βδ_pos.ne'
  simp only [βNew, mNew, βf, mf, Option.elim, ψ]
  field_simp
  ring

/-- The block `D = {b}` of the configuration `(∅, ∅)`: `β⁻¹({b}) = 1/β_b = 12/β_δ` and
`t({b}) = t_b = 12 m_b/β_δ`. -/
lemma block_b_sums :
    ∑ o ∈ ({none} : Finset (Option (Option (Option C)))), 1 / P.βNew βC o = 12 / P.βδ ∧
    ∑ o ∈ ({none} : Finset (Option (Option (Option C)))), P.mNew mC o / P.βNew βC o =
      12 * P.mb / P.βδ := by
  have := H.βδ_pos.ne'
  simp only [sum_singleton, βNew_none, mNew_none]
  constructor <;> field_simp

/-- The block `D = {b}`: its weighted mean reward is `m̄_{{b}} = m_b`. -/
lemma mbar_block_b : mbar (P.mNew mC) (P.βNew βC) {none} = P.mb := by
  have := H.βδ_pos.ne'
  simp only [mbar, sum_singleton, βNew_none, mNew_none]
  field_simp

/-- The block `D = {b}`: `S_2({b}) = (m_b − m̄_{{b}})²/β_b = 0`. -/
lemma SS_block_b : SS (P.mNew mC) (P.βNew βC) {none} = 0 := by
  rw [SS, sum_singleton, mbar_block_b H, mNew_none, sub_self]
  ring

end

/-- `∅` is tight for `ξ^f(α)`, as `f(∅) = 0`. -/
lemma tight_empty_f (α : ℝ) :
    IsTight (P.fStep gC) (xi (P.fStep gC) (P.mf mC) (P.βf βC) α) ∅ := by
  simp [IsTight, fStep_empty H.old.empty]

/-- `∅` is tight for `ξ^h(α)`, as `h(∅) = 0`. -/
lemma tight_empty_h (α : ℝ) :
    IsTight (subMod (P.fStep gC) (P.dStep mC βC))
      (xi (subMod (P.fStep gC) (P.dStep mC βC)) (P.mf mC) (P.βf βC) α) ∅ := by
  simp [IsTight, subMod, fStep_empty H.old.empty]

/-! ### `lem:dmt`: the doubly merged translation (`appB-tools.tex:483-534`) -/

omit [Fintype C] H in
/-- `lem:dmt`(b), the first step (`appB-tools.tex:510`): `h = f − d` is the direct sum of
`f_C − d|_C` and the two modular singletons with the values `F_{τ_1} − w/β_δ` and `F_{τ_2} − w/β_δ`;
here `f_C − d|_C` is `shiftFun gC mC βC (m* μ) μ`, as `d_e = μ(m* − m_e)/β_e` for `e ∈ C`, and
`d_{τ_1} = d_{τ_2} = w/β_δ`. -/
theorem hStep_eq_addSingleton : P.hStep gC mC βC =
    addSingleton (addSingleton (shiftFun gC mC βC (P.mstar * P.μ) P.μ) (P.Fτ₁ - P.w / P.βδ))
      (P.Fτ₂ - P.w / P.βδ) := by
  funext T
  have hd : ∀ T' : Finset C, ∑ c ∈ T', P.dStep mC βC (some (some c)) =
      P.mstar * P.μ * ∑ c ∈ T', 1 / βC c - P.μ * ∑ c ∈ T', mC c / βC c := fun T' => by
    rw [← sum_shift]
    exact sum_congr rfl fun c _ => by simp only [dStep, mf_old, βf_old]; ring
  simp only [hStep, subMod, fStep, addSingleton, shiftFun]
  rw [sum_option_finset T, sum_option_finset (eraseNone T), hd, dStep_τ₂, dStep_τ₁]
  split_ifs <;> ring

/-- `lem:dmt`(b), the second step (`appB-tools.tex:511-515`): by `lem:fullplane`(f)
(`xi_addSingleton`, twice) and `lem:translation`(c) applied to `f_C` with
`(μ_α, μ_θ) = (μ, m* μ)` (`xi_shift`), `ξ^h_e(α) = ξ^{f_C}_e(α − μ) − d_e` for `e ∈ C`, and
`ξ^h_{τ_1}(α) = F_{τ_1} − w/β_δ`. -/
theorem xi_h_of_addSingleton (α : ℝ) :
    (∀ c, xi (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α (some (some c)) =
        xi gC mC βC (α - P.μ) c - P.dStep mC βC (some (some c))) ∧
      xi (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α (some none) = P.Fτ₁ - P.w / P.βδ := by
  have H1 : FPHyp (shiftFun gC mC βC (P.mstar * P.μ) P.μ) βC := H.old.shift mC _ _
  have H2 : FPHyp (addSingleton (shiftFun gC mC βC (P.mstar * P.μ) P.μ) (P.Fτ₁ - P.w / P.βδ))
      (fun e => P.βf βC (some e)) :=
    H1.addSingleton (β' := fun o => Option.elim o P.βδ βC) H.βδ_pos _
  -- (1) "So, by `lem:fullplane`(f) and `lem:translation`(c) (applied to `f_C` with
  -- `(μ_α, μ_θ) = (μ, m_*μ)`), `ξ^h_e(α) = ξ^{f_C}_e(α − μ) − d_e` for `e ∈ C`, … and
  -- `ξ^h_{τ_1}(α) = F_{τ_1} − w/β_δ`."
  -- The Lean applies `lem:fullplane`(f) to the outer and the inner modular singleton
  -- (`xi_addSingleton`).
  have hout := xi_addSingleton (m' := P.mf mC) (β' := P.βf βC) H2 H.βδ_pos
    (P.Fτ₂ - P.w / P.βδ) α
  have hin := xi_addSingleton (m' := fun e => P.mf mC (some e))
    (β' := fun e => P.βf βC (some e)) H1 H.βδ_pos (P.Fτ₁ - P.w / P.βδ) α
  -- It applies `lem:translation`(c) to `f_C` (`xi_shift`).
  have hsh := xi_shift H.old mC (P.mstar * P.μ) P.μ α
  rw [hStep_eq_addSingleton, hout]
  refine ⟨fun c => ?_, ?_⟩
  · simp only [Option.elim]
    rw [hin]
    simp only [Option.elim]
    change xi (shiftFun gC mC βC (P.mstar * P.μ) P.μ) mC βC α c = _
    rw [hsh]
    simp only [dStep, mf_old, βf_old]
    ring
  · simp only [Option.elim]
    rw [hin]
    rfl

/-- `lem:dmt`(a), auxiliary form (`appB-tools.tex:503-506`, under `Hyp`): if `(E ∖ {τ_1}, E)` is a
weak configuration at `α`, then `r(ξ^{f'}(α)) = r(ξ^{f_C}(α)) + ψ α + Δ_p`. Steps:
(1) `lem:windows`(a) with `U = E ∖ {τ_1}` and `W = E`: `D = {b, τ_1}`, and
`X_{U,W} = K + h(E) − f(E ∖ {τ_1}) = K − d(E) + F_{τ_1}`, as `f(E) − f(E ∖ {τ_1}) = F_{τ_1}`; (2) by
`lem:fullplane`(f), `ξ^f(α) = (ξ^{f_C}(α), F_{τ_1}, F_{τ_2})`, so the first sum in (`eq:windows`) is
`r(ξ^{f_C}(α)) + m_δ F_{τ_2}`, while the second is empty; (3) with `S_2({b, τ_1}) = ψ` and
`m̄_{{b,τ_1}} = m̄`, (`eq:windows`) becomes
`r(ξ^{f'}(α)) = r(ξ^{f_C}(α)) + m_δ F_{τ_2} + ψ α + (K − d(E) + F_{τ_1}) m̄`, which is the claim. -/
theorem dmt_a_aux {α : ℝ}
    (hconf : IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α
      ((univ : Finset (Option (Option C))).erase (some none)) univ) :
    reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
      reward mC (xi gC mC βC α) + P.ψ * α + P.Δp mC βC := by
  set U : Finset (Option (Option C)) := univ.erase (some none)
  set W : Finset (Option (Option C)) := univ
  -- (1) "Apply `lem:windows`(a) with `U = E ∖ {τ_1}` and `W = E`. Then `D = {b, τ_1}`, and
  -- `X_{U,W} = K + h(E) − f(E ∖ {τ_1}) = K − d(E) + F_{τ_1}`, as `f(E) − f(E ∖ {τ_1}) = F_{τ_1}`."
  have hwin := (windows_a_aux H.fHyp H.d_nonneg (βb_pos H) (subset_univ U) hconf).2.2.2
  have hD : blockUW U W = {none, some (some none)} := insertNone_τ₁
  have hfτ₁ : P.fStep gC univ - P.fStep gC U = P.Fτ₁ := by
    rw [fStep_univ, fStep_erase_τ₁]
    ring
  have hX : bigX (P.fStep gC) (P.dStep mC βC) P.K U W = P.K - P.dE mC βC + P.Fτ₁ := by
    simp only [bigX, subMod, W, dE]
    linarith
  -- (2) "By `lem:fullplane`(f), `ξ^f(α) = (ξ^{f_C}(α), F_{τ_1}, F_{τ_2})`, so the first sum in
  -- (`eq:windows`) is `r(ξ^{f_C}(α)) + m_δ F_{τ_2}`, while the second is empty."
  have hfirst : ∑ e ∈ U, P.mNew mC (some e) *
      xi (P.fStep gC) (fun e => P.mNew mC (some e)) (fun e => P.βNew βC (some e)) α e =
      reward mC (xi gC mC βC α) + P.mδ * P.Fτ₂ := by
    rw [mNew_some, βNew_some, sum_erase_τ₁]
    simp only [mNew_some_apply, mf_none, mf_old, xi_f_τ₂ H, xi_f_old H, reward]
    ring
  have hsecond : ∑ e ∈ Wᶜ, P.mNew mC (some e) * xi (subMod (P.fStep gC) (P.dStep mC βC))
      (fun e => P.mNew mC (some e)) (fun e => P.βNew βC (some e)) α e = 0 := by
    simp [W]
  -- (3) "With `S_2({b, τ_1}) = ψ` and `m̄_{{b,τ_1}} = m̄`, (`eq:windows`) becomes
  -- `r(ξ^{f'}(α)) = r(ξ^{f_C}(α)) + m_δ F_{τ_2} + ψα + (K − d(E) + F_{τ_1})m̄`, which is the
  -- claim."
  show reward (P.mNew mC)
    (xiPrime (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α) = _
  rw [hwin, hD, SS_block_τ₁ H, mbar_block_τ₁ H, hX, hfirst, hsecond, Δp]
  ring

/-- `lem:dmt`(b), auxiliary form (`appB-tools.tex:508-524`, under `Hyp`): if `(∅, {τ_2})` is a weak
configuration at `α`, then
`r(ξ^{f'}(α)) = r(ξ^{f_C}(α − μ)) + ψ α + Δ_p + ∑_{e∈C} (m̄ − m_e) d_e + s (w/β_δ − ΔF)`. Steps:
(1) `lem:windows`(a) with `U = ∅` and `W = {τ_2}`: `D = {b, τ_2}`, and
`X_{U,W} = K + h({τ_2}) = K + F_{τ_2} − w/β_δ`, as `d_{τ_2} = w/β_δ`; (2) `h = f − d` is the direct
sum of `f_C − d|_C` and the two modular singletons with the values `F_{τ_1} − w/β_δ` and
`F_{τ_2} − w/β_δ` (`hStep_eq_addSingleton`), so by `lem:fullplane`(f) and `lem:translation`(c)
`ξ^h_e(α) = ξ^{f_C}_e(α − μ) − d_e` for `e ∈ C`, hence
`∑_{e∈C} m_e ξ^h_e(α) = r(ξ^{f_C}(α − μ)) − ∑_{e∈C} m_e d_e`, and `ξ^h_{τ_1}(α) = F_{τ_1} − w/β_δ`
(`xi_h_of_addSingleton`); (3) the first sum in (`eq:windows`) is empty, and the second, over
`E ∖ W = C ∪ {τ_1}`, is `r(ξ^{f_C}(α − μ)) − ∑_{e∈C} m_e d_e + m_δ (F_{τ_1} − w/β_δ)`; (4) we insert
this into (`eq:windows`), with `S_2({b, τ_2}) = ψ` and `m̄_{{b,τ_2}} = m̄`, and subtract
`r(ξ^{f_C}(α − μ)) + ψ α + Δ_p`; using `d(E) = d(C) + 2w/β_δ`, the remaining constant is
`∑_{e∈C} (m̄ − m_e) d_e + s (w/β_δ − ΔF)`. -/
theorem dmt_b_aux {α : ℝ}
    (hconf : IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α ∅
      {none}) :
    reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
      reward mC (xi gC mC βC (α - P.μ)) + P.ψ * α + P.Δp mC βC +
        (∑ c, (P.mbar' - mC c) * P.dStep mC βC (some (some c)) +
          P.s * (P.w / P.βδ - P.ΔF)) := by
  set U : Finset (Option (Option C)) := ∅
  set W : Finset (Option (Option C)) := {none}
  -- (1) "Apply `lem:windows`(a) with `U = ∅` and `W = {τ_2}`. Then `D = {b, τ_2}`, and
  -- `X_{U,W} = K + h({τ_2}) = K + F_{τ_2} − w/β_δ`, as `d_{τ_2} = w/β_δ`."
  have hwin := (windows_a_aux H.fHyp H.d_nonneg (βb_pos H) (empty_subset W) hconf).2.2.2
  have hD : blockUW U W = {none, some none} := insertNone_τ₂
  have hX : bigX (P.fStep gC) (P.dStep mC βC) P.K U W = P.K + P.Fτ₂ - P.w / P.βδ := by
    simp only [bigX, subMod, W, U, fStep_τ₂ H.old.empty, fStep_empty H.old.empty, sum_singleton,
      dStep_τ₂]
    ring
  -- (2) "The function `h = f − d` is the direct sum of `f_C − d|_C` and the two modular singletons
  -- with the values `F_{τ_1} − w/β_δ` and `F_{τ_2} − w/β_δ`, and `d_e = μ(m_* − m_e)/β_e` for
  -- `e ∈ C`. So, by `lem:fullplane`(f) and `lem:translation`(c) (applied to `f_C` with
  -- `(μ_α, μ_θ) = (μ, m_*μ)`), `ξ^h_e(α) = ξ^{f_C}_e(α − μ) − d_e` for `e ∈ C`, hence
  -- `∑_{e∈C} m_e ξ^h_e(α) = r(ξ^{f_C}(α − μ)) − ∑_{e∈C} m_e d_e`, and
  -- `ξ^h_{τ_1}(α) = F_{τ_1} − w/β_δ`."
  -- The first sentence is `hStep_eq_addSingleton`, used inside `xi_h_of_addSingleton`; the sum
  -- is `hC`.
  obtain ⟨hξC, hξτ₁⟩ := xi_h_of_addSingleton H α
  have hC : ∑ c, mC c * xi (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α (some (some c)) =
      reward mC (xi gC mC βC (α - P.μ)) - ∑ c, mC c * P.dStep mC βC (some (some c)) := by
    simp only [hξC, mul_sub, sum_sub_distrib, reward]
  -- (3) "The first sum in (`eq:windows`) is empty, and the second, over `E ∖ W = C ∪ {τ_1}`, is
  -- `r(ξ^{f_C}(α − μ)) − ∑_{e∈C} m_e d_e + m_δ(F_{τ_1} − w/β_δ)`."
  have hfirst : ∑ e ∈ U, P.mNew mC (some e) *
      xi (P.fStep gC) (fun e => P.mNew mC (some e)) (fun e => P.βNew βC (some e)) α e = 0 :=
    sum_empty
  have hsecond : ∑ e ∈ Wᶜ, P.mNew mC (some e) * xi (subMod (P.fStep gC) (P.dStep mC βC))
      (fun e => P.mNew mC (some e)) (fun e => P.βNew βC (some e)) α e =
      reward mC (xi gC mC βC (α - P.μ)) - ∑ c, mC c * P.dStep mC βC (some (some c)) +
        P.mδ * (P.Fτ₁ - P.w / P.βδ) := by
    rw [mNew_some, βNew_some, sum_compl_τ₂]
    have hτ₁ : xi (subMod (P.fStep gC) (P.dStep mC βC)) (P.mf mC) (P.βf βC) α (some none) =
        P.Fτ₁ - P.w / P.βδ := hξτ₁
    have hCs : ∑ c, P.mf mC (some (some c)) *
        xi (subMod (P.fStep gC) (P.dStep mC βC)) (P.mf mC) (P.βf βC) α (some (some c)) =
        reward mC (xi gC mC βC (α - P.μ)) - ∑ c, mC c * P.dStep mC βC (some (some c)) := hC
    simp only [mNew_some_apply]
    rw [hτ₁, hCs, mf_τ₁]
    ring
  -- (4) "We insert this into (`eq:windows`), with `S_2({b, τ_2}) = ψ` and `m̄_{{b,τ_2}} = m̄`, and
  -- subtract `r(ξ^{f_C}(α − μ)) + ψα + Δ_p`. Using `d(E) = d(C) + 2w/β_δ`, the remaining constant
  -- is `−∑_{e∈C} m_e d_e + m_δ(F_{τ_1} − w/β_δ) + (K + F_{τ_2} − w/β_δ)m̄`
  -- `− m_δ F_{τ_2} − (K − d(C) − 2w/β_δ + F_{τ_1})m̄`
  -- `= −∑_{e∈C} m_e d_e + m̄ d(C) − (m̄ − m_δ)ΔF + (m̄ − m_δ)w/β_δ`
  -- `= ∑_{e∈C} (m̄ − m_e)d_e + s(w/β_δ − ΔF)`."
  have hconst : -∑ c, mC c * P.dStep mC βC (some (some c)) + P.mδ * (P.Fτ₁ - P.w / P.βδ) +
        (P.K + P.Fτ₂ - P.w / P.βδ) * P.mbar' - P.mδ * P.Fτ₂ -
        (P.K - P.dC mC βC - 2 * (P.w / P.βδ) + P.Fτ₁) * P.mbar' =
      ∑ c, (P.mbar' - mC c) * P.dStep mC βC (some (some c)) + P.s * (P.w / P.βδ - P.ΔF) :=
    calc -∑ c, mC c * P.dStep mC βC (some (some c)) + P.mδ * (P.Fτ₁ - P.w / P.βδ) +
          (P.K + P.Fτ₂ - P.w / P.βδ) * P.mbar' - P.mδ * P.Fτ₂ -
          (P.K - P.dC mC βC - 2 * (P.w / P.βδ) + P.Fτ₁) * P.mbar'
        = -∑ c, mC c * P.dStep mC βC (some (some c)) + P.mbar' * P.dC mC βC -
            (P.mbar' - P.mδ) * P.ΔF + (P.mbar' - P.mδ) * (P.w / P.βδ) := by
          unfold ΔF
          ring
      _ = ∑ c, (P.mbar' - mC c) * P.dStep mC βC (some (some c)) +
            P.s * (P.w / P.βδ - P.ΔF) := by
          simp only [dC, s, sub_mul, sum_sub_distrib, mul_sum]
          ring
  show reward (P.mNew mC)
    (xiPrime (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α) = _
  rw [hwin, hD, SS_block_τ₂ H, mbar_block_τ₂ H, hX, hfirst, hsecond, Δp, dE_eq]
  linarith [hconst]

/-- The configuration `(∅, ∅)` in the proof of `lem:onelevel`(b)
(`stoc-sections/appD-hardness.tex:911-917`), which `ContractDesignPolymatroids/Hardness/OneLevel.lean` uses: if every
`h`-marginal is at most `θ_b` at `α`, then `θ_b = θ_out = α m_b − β_b K`, which is `θ_{U,W}` for
`U = W = ∅` (`appD-hardness.tex:892-893`), and (`eq:windows`), with `lem:fullplane`(f) and
`lem:translation`(c) (translation vector `(μ, m* μ)`), gives
`r(ξ^{f'}(α)) = r(ξ^{f_C}(α − μ)) + m_δ(F_{τ_1} + F_{τ_2}) − ∑_{e∈E} m_e d_e + K m_b`, where
`∑_{e∈E} m_e d_e = 2 m_δ w/β_δ + ∑_{e∈C} m_e d_e` as `d_{τ_1} = d_{τ_2} = w/β_δ`. Steps: (1)
`(∅, ∅)` is a weak configuration at `α`: `ρ^h_e ≤ θ_b` for `e ∈ E`, and `∅` is tight for `ξ^f(α)`
and for `ξ^h(α)`; (2) `lem:windows`(a) with `U = W = ∅` (`windows_a_aux`): `D = {b}` and
`X_{∅,∅} = K + h(∅) − f(∅) = K`, so `θ_b = θ_{∅,∅} = (α t_b − K)/(1/β_b) = θ_out`, and
(`eq:windows`) reads `r(ξ^{f'}(α)) = ∑_{e∈E} m_e ξ^h_e(α) + α S_2({b}) + K m̄_{{b}}`, with
`S_2({b}) = 0` and `m̄_{{b}} = m_b`; (3) by `lem:translation`(c), applied to `f` with
`(μ_α, μ_θ) = (μ, m* μ)`, `ξ^h(α) = ξ^f(α − μ) − d` (`xi_h`), and by `lem:fullplane`(f),
`ξ^f(α − μ) = (ξ^{f_C}(α − μ), F_{τ_1}, F_{τ_2})` (`xi_f_old`, `xi_f_τ₁`, `xi_f_τ₂`). -/
theorem config_empty {α : ℝ}
    (hlow : ∀ e, rho (P.hStep gC mC βC) (P.mf mC) (P.βf βC) α e ≤
      rho (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α none) :
    rho (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α none = P.θout α ∧
      curve (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α =
        curve gC mC βC (α - P.μ) + P.mδ * (P.Fτ₁ + P.Fτ₂) - 2 * P.mδ * (P.w / P.βδ) -
          ∑ c, mC c * P.dStep mC βC (some (some c)) + P.K * P.mb := by
  -- (1) `(∅, ∅)` is a weak configuration at `α`: `ρ^h_e ≤ θ_b` for every `e ∈ E ∖ ∅`, and `∅` is
  -- tight for `ξ^f(α)` and for `ξ^h(α)`
  have hconf : IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α ∅ ∅ :=
    ⟨fun e he => absurd he (notMem_empty e), fun e he => by simp at he, fun e _ => hlow e,
      tight_empty_f H α, tight_empty_h H α⟩
  -- (2) `lem:windows`(a) with `U = W = ∅`: `D = {b}` and `X_{∅,∅} = K + h(∅) − f(∅) = K`
  obtain ⟨hθ, -, -, hr⟩ := windows_a_aux H.fHyp H.d_nonneg (βb_pos H) (empty_subset ∅) hconf
  have hD : blockUW (∅ : Finset (Option (Option C))) ∅ = {none} := by
    ext o
    rcases o with _ | _ | _ | c <;> simp [blockUW, mem_insertNone]
  have hX : bigX (P.fStep gC) (P.dStep mC βC) P.K ∅ ∅ = P.K := by
    simp [bigX, subMod, fStep_empty H.old.empty]
  constructor
  · -- so `θ_b = θ_{∅,∅} = (α t_b − K)/(1/β_b) = α m_b − β_b K = θ_out`
    have := H.βδ_pos.ne'
    show thetaB (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α = _
    rw [hθ, thetaUW, hD, hX, (block_b_sums H).1, (block_b_sums H).2]
    unfold θout
    field_simp
  · -- and (`eq:windows`) reads `r(ξ^{f'}(α)) = ∑_{e∈E} m_e ξ^h_e(α) + α S_2({b}) + K m̄_{{b}}`,
    -- with `S_2({b}) = 0` and `m̄_{{b}} = m_b`
    show reward (P.mNew mC)
      (xiPrime (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α) = _
    rw [hr, mNew_some, βNew_some, hD, hX, SS_block_b H, mbar_block_b H]
    simp only [sum_empty, zero_add, compl_empty, mul_zero, add_zero]
    -- (3) by `lem:translation`(c) applied to `f`, `ξ^h(α) = ξ^f(α − μ) − d`, and by
    -- `lem:fullplane`(f), `ξ^f(α − μ) = (ξ^{f_C}(α − μ), F_{τ_1}, F_{τ_2})`
    have hxh : ∀ e, xi (subMod (P.fStep gC) (P.dStep mC βC)) (P.mf mC) (P.βf βC) α e =
        xi (P.fStep gC) (P.mf mC) (P.βf βC) (α - P.μ) e - P.dStep mC βC e := xi_h H α
    rw [sum_E]
    simp only [mNew_some_apply, hxh, mf_none, mf_τ₁, mf_old, xi_f_τ₂ H, xi_f_τ₁ H, xi_f_old H,
      dStep_τ₁, dStep_τ₂, curve, mul_sub, sum_sub_distrib]
    ring_nf

end Windows

/-! ### `lem:dmt`: its parts and the exact statement -/

/-- **`lem:dmt`(a)** (Lemma B.14, `appB-tools.tex:483-489`, proof
`appB-tools.tex:503-506`): in the setting of `sec:B-dmt` (`DmtSetting`), with
`Δ_p = m_δ F_{τ_2} + (K − d(E) + F_{τ_1}) m̄` (`Δp`): if `(E ∖ {τ_1}, E)` is a weak configuration at
`α`, then
`r(ξ^{f'}(α)) = r(ξ^{f_C}(α)) + ψ α + Δ_p`. Steps (in `dmt_a_aux`): (1) `lem:windows`(a) with
`U = E ∖ {τ_1}` and `W = E`: `D = {b, τ_1}` and `X_{U,W} = K − d(E) + F_{τ_1}`, as
`f(E) − f(E ∖ {τ_1}) = F_{τ_1}`; (2) by `lem:fullplane`(f),
`ξ^f(α) = (ξ^{f_C}(α), F_{τ_1}, F_{τ_2})`, so the first sum in (`eq:windows`) is
`r(ξ^{f_C}(α)) + m_δ F_{τ_2}`, and the second is empty; (3) with `S_2({b, τ_1}) = ψ` and
`m̄_{{b,τ_1}} = m̄`, (`eq:windows`) becomes the claim. -/
theorem dmt_a (hS : P.DmtSetting gC mC βC) {α : ℝ}
    (hconf : IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α
      ((univ : Finset (Option (Option C))).erase (some none)) univ) :
    reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
      reward mC (xi gC mC βC α) + P.ψ * α + P.Δp mC βC :=
  dmt_a_aux hS.hyp hconf

/-- **`lem:dmt`(b)** (`appB-tools.tex:490-492`, proof `appB-tools.tex:508-524`): in the setting of
`sec:B-dmt` (`DmtSetting`), with `ΔF = F_{τ_1} − F_{τ_2}` (`ΔF`): if `(∅, {τ_2})` is a weak
configuration at `α`, then
`r(ξ^{f'}(α)) = r(ξ^{f_C}(α − μ)) + ψ α + Δ_p + ∑_{e∈C} (m̄ − m_e) d_e + s (w/β_δ − ΔF)`. Steps (in
`dmt_b_aux`): (1) `lem:windows`(a) with `U = ∅` and `W = {τ_2}`: `D = {b, τ_2}` and
`X_{U,W} = K + F_{τ_2} − w/β_δ`; (2) `h = f − d` is the direct sum of `f_C − d|_C` and the modular
singletons with the values `F_{τ_1} − w/β_δ` and `F_{τ_2} − w/β_δ` (`hStep_eq_addSingleton`), so by
`lem:fullplane`(f) and `lem:translation`(c), `ξ^h_e(α) = ξ^{f_C}_e(α − μ) − d_e` for `e ∈ C` and
`ξ^h_{τ_1}(α) = F_{τ_1} − w/β_δ` (`xi_h_of_addSingleton`); (3) the first sum in (`eq:windows`) is
empty and the second is `r(ξ^{f_C}(α − μ)) − ∑_{e∈C} m_e d_e + m_δ (F_{τ_1} − w/β_δ)`; (4) with
`S_2({b, τ_2}) = ψ`, `m̄_{{b,τ_2}} = m̄` and `d(E) = d(C) + 2w/β_δ`, the remaining constant is
`∑_{e∈C} (m̄ − m_e) d_e + s (w/β_δ − ΔF)`. -/
theorem dmt_b (hS : P.DmtSetting gC mC βC) {α : ℝ}
    (hconf : IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α ∅
      {none}) :
    reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
      reward mC (xi gC mC βC (α - P.μ)) + P.ψ * α + P.Δp mC βC +
        (∑ c, (P.mbar' - mC c) * P.dStep mC βC (some (some c)) +
          P.s * (P.w / P.βδ - P.ΔF)) :=
  dmt_b_aux hS.hyp hconf

/-- **`lem:dmt`(c)** (`appB-tools.tex:494-498`, proof `appB-tools.tex:526-533`): in the setting of
`sec:B-dmt` (`DmtSetting`), let `L_C(α) = p_C + q_C α` (`LC`) and suppose that
`ΔF = w/β_δ + d(C) − (q_C μ − ∑_{e∈C} (m_δ − m_e) d_e)/s`. Then `L(α) = L_C(α) + ψ α + Δ_p` (`L`)
satisfies `L(α) − r(ξ^{f'}(α)) = L_C(α) − r(ξ^{f_C}(α))` in case (a) and
`L(α) − r(ξ^{f'}(α)) = L_C(α − μ) − r(ξ^{f_C}(α − μ))` in case (b). Steps: (1) with the given
`ΔF`, `s (w/β_δ − ΔF) = −s d(C) + q_C μ − ∑_{e∈C} (m_δ − m_e) d_e`; (2) as `m̄ = m_δ + s`,
`∑_{e∈C} (m̄ − m_e) d_e = s d(C) + ∑_{e∈C} (m_δ − m_e) d_e`; (3) so the constant of (b) is
`q_C μ`; (4) in case (b),
`L(α) − r(ξ^{f'}(α)) = L_C(α) − q_C μ − r(ξ^{f_C}(α − μ)) = L_C(α − μ) − r(ξ^{f_C}(α − μ))`;
(5) in case (a), the claim follows from (a) directly, as the terms `ψ α + Δ_p` cancel. -/
theorem dmt_c (hS : P.DmtSetting gC mC βC) (pC qC : ℝ)
    (hΔF : P.ΔF = P.w / P.βδ + P.dC mC βC -
      (qC * P.μ - ∑ c, (P.mδ - mC c) * P.dStep mC βC (some (some c))) / P.s) (α : ℝ) :
    (IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α
        ((univ : Finset (Option (Option C))).erase (some none)) univ →
      P.L mC βC pC qC α - reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
        LC pC qC α - reward mC (xi gC mC βC α)) ∧
    (IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α ∅ {none} →
      P.L mC βC pC qC α - reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
        LC pC qC (α - P.μ) - reward mC (xi gC mC βC (α - P.μ))) := by
  have hs : P.s ≠ 0 := hS.s_pos.ne'
  -- (1) "With the given `ΔF`, we have `s(w/β_δ − ΔF) = −s d(C) + q_C μ − ∑_{e∈C} (m_δ − m_e)d_e`."
  have h1 : P.s * (P.w / P.βδ - P.ΔF) = -(P.s * P.dC mC βC) + qC * P.μ -
      ∑ c, (P.mδ - mC c) * P.dStep mC βC (some (some c)) := by
    rw [hΔF]
    field_simp
    ring
  -- (2) "As `m̄ = m_δ + s`, also `∑_{e∈C} (m̄ − m_e)d_e = s d(C) + ∑_{e∈C} (m_δ − m_e)d_e`."
  have h2 : ∑ c, (P.mbar' - mC c) * P.dStep mC βC (some (some c)) =
      P.s * P.dC mC βC + ∑ c, (P.mδ - mC c) * P.dStep mC βC (some (some c)) := by
    simp only [dC, s, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun c _ => by ring
  -- (3) "So the constant of (b) is `q_C μ`."
  have h3 : ∑ c, (P.mbar' - mC c) * P.dStep mC βC (some (some c)) +
      P.s * (P.w / P.βδ - P.ΔF) = qC * P.μ := by
    rw [h1, h2]
    ring
  -- (4) "In case (b), therefore,
  -- `L(α) − r(ξ^{f'}(α)) = L_C(α) − q_C μ − r(ξ^{f_C}(α − μ))`
  -- `= L_C(α − μ) − r(ξ^{f_C}(α − μ))`."
  have hcase_b : IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α ∅
      {none} → P.L mC βC pC qC α -
          reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
        LC pC qC (α - P.μ) - reward mC (xi gC mC βC (α - P.μ)) := fun hb =>
    calc P.L mC βC pC qC α -
          reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α)
        = LC pC qC α - qC * P.μ - reward mC (xi gC mC βC (α - P.μ)) := by
          rw [dmt_b hS hb, h3]
          unfold L
          ring
      _ = LC pC qC (α - P.μ) - reward mC (xi gC mC βC (α - P.μ)) := by
          unfold LC
          ring
  -- (5) "In case (a), the claim follows from (a) directly, as the terms `ψα + Δ_p` cancel."
  have hcase_a : IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α
      ((univ : Finset (Option (Option C))).erase (some none)) univ →
      P.L mC βC pC qC α -
          reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
        LC pC qC α - reward mC (xi gC mC βC α) := fun ha => by
    rw [dmt_a hS ha]
    unfold L
    ring
  exact ⟨hcase_a, hcase_b⟩

/-- **`lem:dmt`** (Lemma B.14, `stoc-sections/appB-tools.tex:483-500`): in the setting of
`sec:B-dmt` (`DmtSetting`), let `Δ_p := m_δ F_{τ_2} + (K − d(E) + F_{τ_1}) m̄` (`Δp`). (a) If
`(E ∖ {τ_1}, E)` is a weak configuration at `α`, then `r(ξ^{f'}(α)) = r(ξ^{f_C}(α)) + ψα + Δ_p`. (b)
If `(∅, {τ_2})` is a weak configuration at `α`, then
`r(ξ^{f'}(α)) = r(ξ^{f_C}(α − μ)) + ψα + Δ_p + ∑_{e∈C} (m̄ − m_e) d_e + s (w/β_δ − ΔF)`. (c) Let
`L_C(α) = p_C + q_C α` (`LC`), and suppose that
`ΔF = w/β_δ + d(C) − (q_C μ − ∑_{e∈C} (m_δ − m_e) d_e)/s`. Then `L(α) := L_C(α) + ψα + Δ_p` (`L`)
satisfies `L(α) − r(ξ^{f'}(α)) = L_C(α) − r(ξ^{f_C}(α))` in case (a) and
`L(α) − r(ξ^{f'}(α)) = L_C(α − μ) − r(ξ^{f_C}(α − μ))` in case (b).

Its parts are `dmt_a`, `dmt_b` and `dmt_c`; their docstrings give the paper's steps. -/
theorem dmt (hS : P.DmtSetting gC mC βC) :
    -- (a)
    (∀ {α : ℝ}, IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α
        ((univ : Finset (Option (Option C))).erase (some none)) univ →
      reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
        reward mC (xi gC mC βC α) + P.ψ * α + P.Δp mC βC) ∧
    -- (b)
    (∀ {α : ℝ}, IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α ∅
        {none} →
      reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
        reward mC (xi gC mC βC (α - P.μ)) + P.ψ * α + P.Δp mC βC +
          (∑ c, (P.mbar' - mC c) * P.dStep mC βC (some (some c)) +
            P.s * (P.w / P.βδ - P.ΔF))) ∧
    -- (c)
    ∀ pC qC : ℝ, P.ΔF = P.w / P.βδ + P.dC mC βC -
        (qC * P.μ - ∑ c, (P.mδ - mC c) * P.dStep mC βC (some (some c))) / P.s → ∀ α : ℝ,
      (IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α
          ((univ : Finset (Option (Option C))).erase (some none)) univ →
        P.L mC βC pC qC α - reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
          LC pC qC α - reward mC (xi gC mC βC α)) ∧
      (IsWeakConfig (P.fStep gC) (P.dStep mC βC) P.K (P.mNew mC) (P.βNew βC) α ∅ {none} →
        P.L mC βC pC qC α - reward (P.mNew mC) (xi (P.gNew gC mC βC) (P.mNew mC) (P.βNew βC) α) =
          LC pC qC (α - P.μ) - reward mC (xi gC mC βC (α - P.μ))) :=
  ⟨dmt_a hS, dmt_b hS, dmt_c hS⟩

end StepData

end

end Hardness

end Stoc
