-- stamp r10 2026-11-03
import ContractDesignPolymatroids.Hardness.Inputs

/-!
# The two windows of a step: bands and closed forms

The STOC version's notation of `sec:D-onelevel`, "The two windows"
(`stoc-sections/appD-hardness.tex:718-747`), and `lem:closedforms` (lines 749-788), for the step
`k → k + 1` of the levels of `def:tower` built by the parameter rule (`def:ruleP`):

* `ρT`, `ρf`, `ρh`, `θb`: the marginals `ρ^{(k)}` of level `k`, `ρ^f` of `f = f_{k+1}`, `ρ^h` of
  `h = f − d` (on `E = E_k ∪ {τ_1, τ_2}`), and the marginal `θ_b` of `b = b_{k+1}` in level `k + 1`;
* `D_bands`: (`eq:D-bands`) and the bands of the dummies, `ρf_τ₂_eq`: `ρ^f_{τ_2} = ρ^f_{τ_1} + φw`;
* `θ1`, `θ2`: the numbers `θ_1`, `θ_2`, which are the numbers `θ_{U,W}` (`θUW`) of `lem:windows`
  for `(U, W) = (E ∖ {τ_1}, E)` and `(∅, {τ_2})` (`θ1_θUW`, `θ2_θUW`); `u1 = θ_1 − ρ^f_{τ_1}`,
  `u2 = θ_2 − ρ^f_{τ_2}` and `φ = β_δ ΔF/w`;
* `closedforms_a`, `closedforms_b`, `closedforms_c`: `lem:closedforms`(a)–(c), for an input
  `μ^in ∈ 𝔉` of length at least `k + 2` (`def:tower`), derived from `closedforms_a_aux`,
  `closedforms_b_aux` and `closedforms_c_aux`, which carry the paper's proofs under the weaker
  hypothesis `μ = μ_{k+1} > 0` (for (a) and (b); (c) needs none) and which the proofs of the later
  results without the hypothesis `μ^in ∈ 𝔉` use;
* `closedforms`: the statement of `lem:closedforms`, the conjunction of (a)–(c), with the input
  `μ^in ∈ 𝔉` taken once, proved by the three parts.

Taken over on 2026-10-20 from `Paper/Hardness/ClosedForms.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

section Tower

variable (μin : ℕ → ℕ)

/-! ### The notation of `sec:D-onelevel` -/

/-- `ρ^{(k)} = ρ^{g_k}`, the marginals of level `k` (`def:tower`). -/
def ρT (k : ℕ) (α : ℝ) (e : Gr k) : ℝ := rho (gT μin k) (mT μin k) (βT μin k) α e

/-- `ρ^f`, the marginals of `f = f_{k+1}` on `E = E_k ∪ {τ_1, τ_2}` at the step `k → k + 1`
(`τ_2 = none`, `τ_1 = some none`). -/
def ρf (k : ℕ) (α : ℝ) (e : Option (Option (Gr k))) : ℝ :=
  rho ((stepD μin k).fStep (gT μin k)) ((stepD μin k).mf (mT μin k))
    ((stepD μin k).βf (βT μin k)) α e

/-- `ρ^h`, the marginals of `h = f − d` at the step `k → k + 1`. -/
def ρh (k : ℕ) (α : ℝ) (e : Option (Option (Gr k))) : ℝ :=
  rho ((stepD μin k).hStep (gT μin k) (mT μin k) (βT μin k)) ((stepD μin k).mf (mT μin k))
    ((stepD μin k).βf (βT μin k)) α e

/-- `θ_b`, the marginal of the new element `b = b_{k+1}` (`none`) in level `k + 1`. -/
def θb (k : ℕ) (α : ℝ) : ℝ := ρT μin (k + 1) α none

/-- `θ_1(α) = (α(t_b + t_{τ_1}) − (K − d(E) + F_{τ_1}))/(1/β_b + 1/β_δ)` (before `lem:closedforms`),
with `t_b = m_b/β_b` and `t_{τ_1} = m_δ/β_δ`. -/
def θ1 (k : ℕ) (α : ℝ) : ℝ :=
  (α * ((lvl μin k).mb / (lvl μin k).βb + (lvl μin k).mδ / (lvl μin k).βδ) -
      ((lvl μin k).K (μT μin (k + 1)) (R1T μin k) - (lvl μin k).dE (μT μin (k + 1)) +
        (lvl μin k).Fτ₁ (μT μin (k + 1)) (R1T μin k))) /
    (1 / (lvl μin k).βb + 1 / (lvl μin k).βδ)

/-- `θ_2(α) = (α(t_b + t_{τ_2}) − (K + F_{τ_2} − w/β_δ))/(1/β_b + 1/β_δ)` (before
`lem:closedforms`), with `t_{τ_2} = m_δ/β_δ`. -/
def θ2 (k : ℕ) (α : ℝ) : ℝ :=
  (α * ((lvl μin k).mb / (lvl μin k).βb + (lvl μin k).mδ / (lvl μin k).βδ) -
      ((lvl μin k).K (μT μin (k + 1)) (R1T μin k) + (lvl μin k).Fτ₂ (μT μin (k + 1)) (R1T μin k) -
        (lvl μin k).w (μT μin (k + 1)) / (lvl μin k).βδ)) /
    (1 / (lvl μin k).βb + 1 / (lvl μin k).βδ)

/-- The number `θ_{U,W} = (α t(D) − X_{U,W})/β⁻¹(D)` of `lem:windows` at the step `k → k + 1`, for
`U ⊆ W ⊆ E` and `D = (W ∖ U) ∪ {b}` (`thetaUW` of the step). -/
abbrev θUW (k : ℕ) (α : ℝ) (U W : Finset (Option (Option (Gr k)))) : ℝ :=
  thetaUW ((stepD μin k).fStep (gT μin k)) ((stepD μin k).dStep (mT μin k) (βT μin k))
    (stepD μin k).K (mT μin (k + 1)) (βT μin (k + 1)) α U W

/-- `u_1 = θ_1 − ρ^f_{τ_1}`, the position of `b` in the band of `τ_1`. -/
def u1 (k : ℕ) (α : ℝ) : ℝ := θ1 μin k α - ρf μin k α (some none)

/-- `u_2 = θ_2 − ρ^f_{τ_2}`, the position of `b` in the band of `τ_2`. -/
def u2 (k : ℕ) (α : ℝ) : ℝ := θ2 μin k α - ρf μin k α none

/-- `φ = β_δ ΔF/w`. -/
def φ (k : ℕ) : ℝ :=
  (lvl μin k).βδ * (lvl μin k).ΔF (μT μin (k + 1)) / (lvl μin k).w (μT μin (k + 1))

variable {μin}

/-! The numbers of the step are those of the parameter rule (`tab:ruleP`). -/

@[simp] lemma stepD_μ (k : ℕ) : (stepD μin k).μ = μT μin (k + 1) := rfl
@[simp] lemma stepD_mδ (k : ℕ) : (stepD μin k).mδ = (lvl μin k).mδ := rfl
@[simp] lemma stepD_βδ (k : ℕ) : (stepD μin k).βδ = (lvl μin k).βδ := rfl
@[simp] lemma stepD_mb (k : ℕ) : (stepD μin k).mb = (lvl μin k).mb := rfl
@[simp] lemma stepD_w (k : ℕ) : (stepD μin k).w = (lvl μin k).w (μT μin (k + 1)) :=
  Level.w_eq_step _ _ _
@[simp] lemma stepD_s (k : ℕ) : (stepD μin k).s = (lvl μin k).s := Level.s_eq_step _ _ _
@[simp] lemma stepD_mbar (k : ℕ) : (stepD μin k).mbar' = (lvl μin k).mbar :=
  Level.mbar_eq_step _ _ _
@[simp] lemma stepD_ψ (k : ℕ) : (stepD μin k).ψ = (lvl μin k).ψ := Level.ψ_eq_step _ _ _
@[simp] lemma stepD_dE (k : ℕ) :
    (stepD μin k).dE (mT μin k) (βT μin k) = (lvl μin k).dE (μT μin (k + 1)) :=
  Level.dE_eq_step _ _ _
@[simp] lemma stepD_Δp (k : ℕ) :
    (stepD μin k).Δp (mT μin k) (βT μin k) = (lvl μin k).Δp (μT μin (k + 1)) (R1T μin k) :=
  Level.Δp_eq_step _ _ _

/-- `M_k > 0` (`lem:weights`(b)). -/
lemma M_pos (k : ℕ) : 0 < (lvl μin k).M := by
  rw [(weights_b (μin := μin)).2.1 k]
  positivity

/-- `s = (12/13)Δ_b > 0`. -/
lemma s_pos (k : ℕ) : 0 < (lvl μin k).s := by
  have := M_pos (μin := μin) k
  unfold Level.s Level.Δb
  positivity

/-- `w = 64Mμ > 0` for `μ > 0`. -/
lemma w_pos {k : ℕ} (hμ : 0 < μT μin (k + 1)) : 0 < (lvl μin k).w (μT μin (k + 1)) := by
  have := M_pos (μin := μin) k
  unfold Level.w
  positivity

/-- `μ_j > 0` for an input in `𝔉` and `j` below its length. -/
lemma μT_pos {K : ℕ} (hF : InF μin K) {j : ℕ} (hj : j < K) : 0 < μT μin j := by
  obtain ⟨-, hpos, -⟩ := hF
  have h0 : (0 : ℝ) < μin 0 := by exact_mod_cast hpos 0 (by omega)
  have hj' : (0 : ℝ) < μin j := by exact_mod_cast hpos j hj
  unfold μT δT
  positivity

/-- `μ^in_1 > 0` for an input in `𝔉`. -/
lemma μin0_pos {K : ℕ} (hF : InF μin K) : 0 < μin 0 := hF.2.1 0 (by have := hF.1; omega)

/-- The paragraph before `lem:closedforms` (`stoc-sections/appD-hardness.tex:722-732`): by
`lem:fullplane`(f) and `lem:translation`(c) with the translation vector `(μ, m_*μ)`, every
`e ∈ E_k` satisfies (`eq:D-bands`) `ρ^f_e(α) = ρ^{(k)}_e(α)` and
`ρ^h_e(α) = ρ^{(k)}_e(α − μ) + m_*μ`, and the dummies have `ρ^f_{τ_1}(α) = αm_δ − β_δF_{τ_1}`,
`ρ^h_{τ_1} = ρ^f_{τ_1} + w` and `ρ^h_{τ_2} = ρ^f_{τ_2} + w`, as `m_*μ − μm_δ = w`; and
`ρ^f_{τ_2}(α) = αm_δ − β_δF_{τ_2}`. (In the setting of `thm:splice` at the step, `stepD_hyp`; the
formulas are `rho_f_old`, `rho_h_old`, `rho_f_τ₁`, `rho_f_τ₂`, `rho_h_τ₁`, `rho_h_τ₂` of
`ContractDesignPolymatroids/Hardness/Step.lean`.) -/
theorem D_bands (k : ℕ) (α : ℝ) :
    (∀ c, ρf μin k α (some (some c)) = ρT μin k α c) ∧
    (∀ c, ρh μin k α (some (some c)) =
      ρT μin k (α - μT μin (k + 1)) c + (lvl μin k).mstar * μT μin (k + 1)) ∧
    ρf μin k α (some none) =
      α * (lvl μin k).mδ - (lvl μin k).βδ * (lvl μin k).Fτ₁ (μT μin (k + 1)) (R1T μin k) ∧
    ρf μin k α none =
      α * (lvl μin k).mδ - (lvl μin k).βδ * (lvl μin k).Fτ₂ (μT μin (k + 1)) (R1T μin k) ∧
    ρh μin k α (some none) = ρf μin k α (some none) + (lvl μin k).w (μT μin (k + 1)) ∧
    ρh μin k α none = ρf μin k α none + (lvl μin k).w (μT μin (k + 1)) := by
  have H := stepD_hyp (μin := μin) k
  refine ⟨fun c => StepData.rho_f_old H α c, fun c => StepData.rho_h_old H α c,
    StepData.rho_f_τ₁ H α, StepData.rho_f_τ₂ H α, ?_, ?_⟩
  · show rho _ _ _ α (some none) = rho _ _ _ α (some none) + _
    rw [StepData.rho_h_τ₁ H, StepData.rho_f_τ₁ H, stepD_w]
  · show rho _ _ _ α none = rho _ _ _ α none + _
    rw [StepData.rho_h_τ₂ H, StepData.rho_f_τ₂ H, stepD_w]

/-- The paragraph before `lem:closedforms` (`stoc-sections/appD-hardness.tex:729-730`):
`ρ^f_{τ_2} = ρ^f_{τ_1} + φw` with `φ = β_δΔF/w`, as `F_{τ_1} = F_{τ_2} + ΔF` (P6). -/
theorem ρf_τ₂_eq {k : ℕ} (hμ : 0 < μT μin (k + 1)) (α : ℝ) :
    ρf μin k α none = ρf μin k α (some none) + φ μin k * (lvl μin k).w (μT μin (k + 1)) := by
  obtain ⟨-, -, hτ₁, hτ₂, -, -⟩ := D_bands (μin := μin) k α
  rw [hτ₁, hτ₂]
  have hw := (w_pos hμ).ne'
  simp only [φ, Level.Fτ₁]
  field_simp
  ring

/-- The sentence before `lem:closedforms` (`stoc-sections/appD-hardness.tex:735-745`): `θ_1` is
the number `θ_{U,W} = (α t(D) − X_{U,W})/β⁻¹(D)` of `lem:windows` for `(U, W) = (E ∖ {τ_1}, E)`,
with `D = (W ∖ U) ∪ {b} = {b, τ_1}` and `X_{U,W} = K − d(E) + F_{τ_1}`. -/
theorem θ1_θUW (k : ℕ) (α : ℝ) : θ1 μin k α = θUW μin k α (univ.erase (some none)) univ := by
  have hX : bigX ((stepD μin k).fStep (gT μin k)) ((stepD μin k).dStep (mT μin k) (βT μin k))
      (stepD μin k).K (univ.erase (some none)) univ =
      (stepD μin k).K - (stepD μin k).dE (mT μin k) (βT μin k) + (stepD μin k).Fτ₁ := by
    simp only [bigX, subMod, StepData.fStep_univ, StepData.fStep_erase_τ₁, StepData.dE]
    ring
  have hne : (none : Option (Option (Option (Gr k)))) ≠ some (some none) := by simp
  unfold θUW thetaUW blockUW
  rw [StepData.insertNone_τ₁, hX, sum_pair hne, sum_pair hne, stepD_dE]
  rfl

/-- The sentence before `lem:closedforms`: `θ_2` is the number `θ_{U,W}` of `lem:windows` for
`(U, W) = (∅, {τ_2})`, with `D = {b, τ_2}` and `X_{U,W} = K + F_{τ_2} − w/β_δ`. -/
theorem θ2_θUW (k : ℕ) (α : ℝ) : θ2 μin k α = θUW μin k α ∅ {none} := by
  have H := stepD_hyp (μin := μin) k
  have hX : bigX ((stepD μin k).fStep (gT μin k)) ((stepD μin k).dStep (mT μin k) (βT μin k))
      (stepD μin k).K ∅ {none} =
      (stepD μin k).K + (stepD μin k).Fτ₂ - (stepD μin k).w / (stepD μin k).βδ := by
    simp only [bigX, subMod, StepData.fStep_τ₂ H.old.empty, StepData.fStep_empty H.old.empty,
      sum_singleton, StepData.dStep_τ₂]
    ring
  have hne : (none : Option (Option (Option (Gr k)))) ≠ some none := by simp
  unfold θUW thetaUW blockUW
  rw [StepData.insertNone_τ₂, hX, sum_pair hne, sum_pair hne, stepD_w]
  rfl

/-- The first step of the proof of `lem:closedforms`(b) (`stoc-sections/appD-hardness.tex:765-767`):
as `1/β_b + 1/β_δ = 13/β_δ` and `t_b + t_{τ_1} = (12m_b + m_δ)/β_δ`,
`θ_1(α) = αm̄ − β_δ(K − d(E) + F_{τ_1})/13`. -/
lemma θ1_eq (k : ℕ) (α : ℝ) :
    θ1 μin k α = α * (lvl μin k).mbar - (lvl μin k).βδ * ((lvl μin k).K (μT μin (k + 1))
      (R1T μin k) - (lvl μin k).dE (μT μin (k + 1)) +
        (lvl μin k).Fτ₁ (μT μin (k + 1)) (R1T μin k)) / 13 := by
  have hβ := (lvl μin k).βδ_pos.ne'
  -- "`1/β_b + 1/β_δ = 13/β_δ`"
  have h13 : 1 / (lvl μin k).βb + 1 / (lvl μin k).βδ = 13 / (lvl μin k).βδ := by
    unfold Level.βb
    field_simp
    ring
  -- "`t_b + t_{τ_1} = t_b + t_{τ_2} = (12m_b + m_δ)/β_δ`"
  -- The Lean: `t_b + t_{τ_1} = (12m_b + m_δ)/β_δ`, the part that `θ_1` needs.
  have ht : (lvl μin k).mb / (lvl μin k).βb + (lvl μin k).mδ / (lvl μin k).βδ =
      (12 * (lvl μin k).mb + (lvl μin k).mδ) / (lvl μin k).βδ := by
    unfold Level.βb
    field_simp
  rw [θ1, h13, ht]
  simp only [Level.mbar, Level.s, Level.mb]
  field_simp
  ring

/-- As `θ1_eq`, the step of the proof of `lem:closedforms`(b) "in the same way" for `θ_2`
(`stoc-sections/appD-hardness.tex:770-771`): as `t_b + t_{τ_2} = (12m_b + m_δ)/β_δ`,
`θ_2(α) = αm̄ − β_δ(K + F_{τ_2} − w/β_δ)/13`. -/
lemma θ2_eq (k : ℕ) (α : ℝ) :
    θ2 μin k α = α * (lvl μin k).mbar - (lvl μin k).βδ * ((lvl μin k).K (μT μin (k + 1))
      (R1T μin k) + (lvl μin k).Fτ₂ (μT μin (k + 1)) (R1T μin k) -
        (lvl μin k).w (μT μin (k + 1)) / (lvl μin k).βδ) / 13 := by
  have hβ := (lvl μin k).βδ_pos.ne'
  have h13 : 1 / (lvl μin k).βb + 1 / (lvl μin k).βδ = 13 / (lvl μin k).βδ := by
    unfold Level.βb
    field_simp
    ring
  have ht : (lvl μin k).mb / (lvl μin k).βb + (lvl μin k).mδ / (lvl μin k).βδ =
      (12 * (lvl μin k).mb + (lvl μin k).mδ) / (lvl μin k).βδ := by
    unfold Level.βb
    field_simp
  rw [θ2, h13, ht]
  simp only [Level.mbar, Level.s, Level.mb]
  field_simp
  ring

/-- `u_1` is affine with slope `s` (the last claim of `lem:closedforms`(b), which does not need
`μ > 0`): `θ_1` has slope `m̄` (`θ1_eq`) and `ρ^f_{τ_1}` slope `m_δ` (`D_bands`), and
`m̄ − m_δ = s`. -/
lemma u1_slope (k : ℕ) (α α' : ℝ) : u1 μin k α' - u1 μin k α = (lvl μin k).s * (α' - α) := by
  rw [u1, u1, θ1_eq, θ1_eq, (D_bands (μin := μin) k α).2.2.1, (D_bands (μin := μin) k α').2.2.1]
  simp only [Level.mbar]
  ring

/-- `u_2` is affine with slope `s` (as `u1_slope`, with `θ2_eq`). -/
lemma u2_slope (k : ℕ) (α α' : ℝ) : u2 μin k α' - u2 μin k α = (lvl μin k).s * (α' - α) := by
  rw [u2, u2, θ2_eq, θ2_eq, (D_bands (μin := μin) k α).2.2.2.1,
    (D_bands (μin := μin) k α').2.2.2.1]
  simp only [Level.mbar]
  ring

/-! ### `lem:closedforms` -/

/-- `lem:closedforms`(a) under the weaker hypothesis `μ = μ_{k+1} > 0` instead of `μ^in ∈ 𝔉` of
length at least `k + 2`, which is what the proofs below use (`stoc-sections/appD-hardness.tex:752`,
proof lines 762-763): at the step `k → k + 1`, `d(E) = (2 + d̄)w/β_δ` and `φ = 1 + d̄ − a_0/(sw)`.

The proof's steps: (a1) by (P3), `d(E) = d(E_k) + 2w/β_δ = (2 + d̄)w/β_δ`; (a2) (P5) with the
definition of `a_0` in (P6) gives `φ = β_δΔF/w = 1 + d̄ − a_0/(sw)`. -/
theorem closedforms_a_aux (k : ℕ) (hμ : 0 < μT μin (k + 1)) :
    (lvl μin k).dE (μT μin (k + 1)) =
        (2 + (lvl μin k).dbar (μT μin (k + 1))) * (lvl μin k).w (μT μin (k + 1)) /
          (lvl μin k).βδ ∧
      φ μin k = 1 + (lvl μin k).dbar (μT μin (k + 1)) -
        (lvl μin k).a0 (μT μin (k + 1)) / ((lvl μin k).s * (lvl μin k).w (μT μin (k + 1))) := by
  have hw := (w_pos hμ).ne'
  have hs := (s_pos (μin := μin) k).ne'
  have hβ := (lvl μin k).βδ_pos.ne'
  constructor
  · -- (a1) "By (P3), `d(E) = d(E_k) + 2w/β_δ = (2 + d̄)w/β_δ`."
    rw [Level.dE_split, Level.dbar]
    field_simp
    ring
  · -- (a2) "(P5) with the definition of `a_0` in (P6) gives `φ = β_δΔF/w = 1 + d̄ − a_0/(sw)`."
    simp only [φ, Level.ΔF, Level.dbar, Level.a0]
    field_simp

/-- `lem:closedforms`(b) under the weaker hypothesis `μ = μ_{k+1} > 0` instead of `μ^in ∈ 𝔉` of
length at least `k + 2`, which is what the proofs below use
(`stoc-sections/appD-hardness.tex:753-755`, proof lines 765-780): at the step `k → k + 1`,
`u_1(α) = s(α − (R_0 + R_1)/2) + w/2` and `u_2(α) = u_1(α) − (1 + d̄)w + a_0/Δ_b` for every
`α ∈ ℝ`; in particular `u_2(R_0 + μ) = u^0`, and `u_1` and `u_2` increase with slope `s > 0`.

The proof's steps: (b1) as `1/β_b + 1/β_δ = 13/β_δ` and
`t_b + t_{τ_1} = t_b + t_{τ_2} = (12m_b + m_δ)/β_δ`, `θ_1(α) = αm̄ − β_δ(K − d(E) + F_{τ_1})/13`
(`θ1_eq`); (b2) as `ρ^f_{τ_1}(α) = αm_δ − β_δF_{τ_1}` and `m̄ − m_δ = s`,
`u_1(α) = sα − β_δ(K − d(E) − 12F_{τ_1})/13`, and (P7) gives the formula for `u_1`; (b3) in the same
way `u_2(α) = sα − β_δ(K − 12F_{τ_2} − w/β_δ)/13` (`θ2_eq`), so
`u_2 − u_1 = β_δ(w/β_δ − d(E) − 12ΔF)/13`; (b4) inserting (a), (P5), and the definition of `a_0`
in (P6) gives `u_2 − u_1 = −w − β_δd(E_k) + (12/13)·(a_0/s) = −(1 + d̄)w + a_0/Δ_b`, as
`β_δd(E_k) = d̄w` and `s = (12/13)Δ_b`; (b5) at `R_0 + μ`,
`u_1(R_0 + μ) = s(μ − |𝓡|/2) + w/2 = a_2Δ_b + w/2`, which gives `u_2(R_0 + μ) = u^0`. -/
theorem closedforms_b_aux (k : ℕ) (hμ : 0 < μT μin (k + 1)) :
    (∀ α, u1 μin k α = (lvl μin k).s * (α - (R0 + R1T μin k) / 2) +
      (lvl μin k).w (μT μin (k + 1)) / 2) ∧
    (∀ α, u2 μin k α = u1 μin k α -
      (1 + (lvl μin k).dbar (μT μin (k + 1))) * (lvl μin k).w (μT μin (k + 1)) +
        (lvl μin k).a0 (μT μin (k + 1)) / (lvl μin k).Δb) ∧
    u2 μin k (R0 + μT μin (k + 1)) = (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) ∧
    0 < (lvl μin k).s ∧
    (∀ α α', u1 μin k α' - u1 μin k α = (lvl μin k).s * (α' - α)) ∧
    (∀ α α', u2 μin k α' - u2 μin k α = (lvl μin k).s * (α' - α)) := by
  have hw := (w_pos hμ).ne'
  have hs := s_pos (μin := μin) k
  have hβ := (lvl μin k).βδ_pos.ne'
  have hΔ : (lvl μin k).Δb ≠ 0 := by
    have := M_pos (μin := μin) k
    unfold Level.Δb
    positivity
  -- (b1) "As `1/β_b + 1/β_δ = 13/β_δ` and `t_b + t_{τ_1} = t_b + t_{τ_2} = (12m_b + m_δ)/β_δ`, we
  -- have `θ_1(α) = αm̄ − β_δ(K − d(E) + F_{τ_1})/13`."
  have hθ1 := θ1_eq (μin := μin) k
  -- (b2) "As `ρ^f_{τ_1}(α) = αm_δ − β_δF_{τ_1}` and `m̄ − m_δ = s`, this gives
  -- `u_1(α) = sα − β_δ(K − d(E) − 12F_{τ_1})/13`,"
  have hms : (lvl μin k).mbar - (lvl μin k).mδ = (lvl μin k).s := by
    unfold Level.mbar
    ring
  have hu1' : ∀ α, u1 μin k α = (lvl μin k).s * α - (lvl μin k).βδ *
      ((lvl μin k).K (μT μin (k + 1)) (R1T μin k) - (lvl μin k).dE (μT μin (k + 1)) -
        12 * (lvl μin k).Fτ₁ (μT μin (k + 1)) (R1T μin k)) / 13 := fun α => by
    rw [u1, hθ1, (D_bands (μin := μin) k α).2.2.1, ← hms]
    ring
  -- "and (P7) gives the formula for `u_1`."
  have hu1 : ∀ α, u1 μin k α = (lvl μin k).s * (α - (R0 + R1T μin k) / 2) +
      (lvl μin k).w (μT μin (k + 1)) / 2 := fun α => by
    rw [hu1']
    simp only [Level.K]
    field_simp
    ring
  -- (b3) "In the same way, `u_2(α) = sα − β_δ(K − 12F_{τ_2} − w/β_δ)/13`,"
  have hθ2 := θ2_eq (μin := μin) k
  have hu2' : ∀ α, u2 μin k α = (lvl μin k).s * α - (lvl μin k).βδ *
      ((lvl μin k).K (μT μin (k + 1)) (R1T μin k) -
        12 * (lvl μin k).Fτ₂ (μT μin (k + 1)) (R1T μin k) -
          (lvl μin k).w (μT μin (k + 1)) / (lvl μin k).βδ) / 13 := fun α => by
    rw [u2, hθ2, (D_bands (μin := μin) k α).2.2.2.1, ← hms]
    ring
  -- "so `u_2 − u_1 = β_δ(w/β_δ − d(E) − 12ΔF)/13`."
  have hd : ∀ α, u2 μin k α - u1 μin k α = (lvl μin k).βδ * ((lvl μin k).w (μT μin (k + 1)) /
      (lvl μin k).βδ - (lvl μin k).dE (μT μin (k + 1)) -
        12 * (lvl μin k).ΔF (μT μin (k + 1))) / 13 := fun α => by
    rw [hu2', hu1', Level.Fτ₁]
    ring
  -- (b4) "Inserting (a), (P5), and the definition of `a_0` in (P6) gives
  -- `u_2 − u_1 = −w − β_δd(E_k) + (12/13)·(a_0/s)`"
  have ha := (closedforms_a_aux k hμ).1
  have hd2 : ∀ α, u2 μin k α - u1 μin k α = -(lvl μin k).w (μT μin (k + 1)) -
      (lvl μin k).βδ * (lvl μin k).dEk (μT μin (k + 1)) +
        12 / 13 * (lvl μin k).a0 (μT μin (k + 1)) / (lvl μin k).s := fun α => by
    rw [hd, ha]
    simp only [Level.ΔF, Level.a0, Level.dbar]
    field_simp
    ring
  -- "`= −(1 + d̄)w + a_0/Δ_b`, as `β_δd(E_k) = d̄w` and `s = (12/13)Δ_b`."
  have hβd : (lvl μin k).βδ * (lvl μin k).dEk (μT μin (k + 1)) =
      (lvl μin k).dbar (μT μin (k + 1)) * (lvl μin k).w (μT μin (k + 1)) := by
    unfold Level.dbar
    field_simp
  have hsΔ : (lvl μin k).s = 12 / 13 * (lvl μin k).Δb := rfl
  have hu2 : ∀ α, u2 μin k α = u1 μin k α -
      (1 + (lvl μin k).dbar (μT μin (k + 1))) * (lvl μin k).w (μT μin (k + 1)) +
        (lvl μin k).a0 (μT μin (k + 1)) / (lvl μin k).Δb := fun α => by
    have h := hd2 α
    rw [hβd, hsΔ] at h
    have e : 12 / 13 * (lvl μin k).a0 (μT μin (k + 1)) / (12 / 13 * (lvl μin k).Δb) =
        (lvl μin k).a0 (μT μin (k + 1)) / (lvl μin k).Δb := by
      field_simp
    linarith
  -- (b5) "At `R_0 + μ`, `u_1(R_0 + μ) = s(μ − |𝓡|/2) + w/2 = a_2Δ_b + w/2`, which gives
  -- `u_2(R_0 + μ) = u^0`."
  have hR : u1 μin k (R0 + μT μin (k + 1)) =
      (lvl μin k).s * (μT μin (k + 1) - (R1T μin k - R0) / 2) +
        (lvl μin k).w (μT μin (k + 1)) / 2 := by
    rw [hu1]
    ring
  have hR' : u1 μin k (R0 + μT μin (k + 1)) =
      Level.a2 (μT μin (k + 1)) (R1T μin k) * (lvl μin k).Δb +
        (lvl μin k).w (μT μin (k + 1)) / 2 := by
    rw [hR, Level.a2, hsΔ]
    ring
  have hu0 : u2 μin k (R0 + μT μin (k + 1)) = (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) := by
    rw [hu2, hR', Level.u0]
    ring
  -- "In particular, `u_2(R_0 + μ) = u^0`, and `u_1` and `u_2` increase with slope `s`." (the
  -- statement of (b); `u_2(R_0 + μ) = u^0` is `hu0` of (b5))
  refine ⟨hu1, hu2, hu0, hs, fun α α' => ?_, fun α α' => ?_⟩
  · rw [hu1, hu1]
    ring
  · rw [hu2, hu2, hu1, hu1]
    ring

/-- `lem:closedforms`(c) without a hypothesis on the input, which is what the proofs below use
(`stoc-sections/appD-hardness.tex:756-757`, proof lines 782-787): at the step `k → k + 1`,
`ρ^f_{τ_2}(α) = (α − R_0)m_δ + ρ̄_k + w − u^0 + sι` for every `α ∈ ℝ`; in particular
`ρ̄_{k+1} = ρ^f_{τ_2}(R_0) = ρ̄_k + w − u^0 + sι`.

The proof's steps: (c1) `ρ^f_{τ_2}(R_0) = R_0m_δ − β_δF_{τ_2} = R_0m_δ − β_δ(F_{τ_1} − ΔF)`, which
is `ρ̄_k + w − u^0 + sι` by (P6), and `ρ^f_{τ_2}` has slope `m_δ`; (c2) the last claim is the
definition of `ρ̄_{k+1}` in (P6), as `m_δ^{(k+1)} = m_δ`, `β_δ^{(k+1)} = β_δ`, and
`F_{τ_2}^{(k+1)} = F_{τ_2}`. -/
theorem closedforms_c_aux (k : ℕ) :
    (∀ α, ρf μin k α none = (α - R0) * (lvl μin k).mδ + (lvl μin k).ρbar +
      (lvl μin k).w (μT μin (k + 1)) - (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) +
        (lvl μin k).s * ι) ∧
    (lvl μin (k + 1)).ρbar = ρf μin k R0 none ∧
    ρf μin k R0 none = (lvl μin k).ρbar + (lvl μin k).w (μT μin (k + 1)) -
      (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) + (lvl μin k).s * ι := by
  -- (c1) "We have `ρ^f_{τ_2}(R_0) = R_0m_δ − β_δF_{τ_2} = R_0m_δ − β_δ(F_{τ_1} − ΔF)`, which is
  -- `ρ̄_k + w − u^0 + sι` by (P6), and `ρ^f_{τ_2}` has slope `m_δ`."
  have hτ₂ : ∀ α, ρf μin k α none =
      α * (lvl μin k).mδ - (lvl μin k).βδ * (lvl μin k).Fτ₂ (μT μin (k + 1)) (R1T μin k) :=
    fun α => (D_bands (μin := μin) k α).2.2.2.1
  have hR : ρf μin k R0 none = (lvl μin k).ρbar + (lvl μin k).w (μT μin (k + 1)) -
      (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) + (lvl μin k).s * ι :=
    calc ρf μin k R0 none
        = R0 * (lvl μin k).mδ - (lvl μin k).βδ * (lvl μin k).Fτ₂ (μT μin (k + 1)) (R1T μin k) :=
          hτ₂ R0
      _ = R0 * (lvl μin k).mδ - (lvl μin k).βδ * ((lvl μin k).Fτ₁ (μT μin (k + 1)) (R1T μin k) -
            (lvl μin k).ΔF (μT μin (k + 1))) := by
          rw [Level.Fτ₁, add_sub_cancel_right]
      _ = (lvl μin k).ρbar + (lvl μin k).w (μT μin (k + 1)) -
            (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) + (lvl μin k).s * ι := by
          -- "by (P6)": `F_{τ_1} − ΔF = F_{τ_2}`, and (P6) defines `F_{τ_2}` "so that
          -- `R_0m_δ − β_δF_{τ_2} = ρ̄_k + w − u^0 + sι`"
          rw [Level.Fτ₁, add_sub_cancel_right]
          exact (lvl μin k).Fτ₂_spec (μT μin (k + 1)) (R1T μin k)
  refine ⟨fun α => ?_, ?_, hR⟩
  · have h1 := hR
    rw [hτ₂] at h1
    rw [hτ₂]
    linarith
  · -- (c2) "The last claim is the definition of `ρ̄_{k+1}` in (P6), as `m_δ^{(k+1)} = m_δ`,
    -- `β_δ^{(k+1)} = β_δ`, and `F_{τ_2}^{(k+1)} = F_{τ_2}`."
    rw [hτ₂]
    rfl

/-- **`lem:closedforms`(a)** (Lemma C.13, `stoc-sections/appD-hardness.tex:752`, proof lines
762-763): let `μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). At the step `k → k + 1`,
`d(E) = (2 + d̄)w/β_δ` and `φ = 1 + d̄ − a_0/(sw)`. The proof (steps (a1), (a2)) is that of
`closedforms_a_aux`, with `μ = μ_{k+1} > 0` as `μ^in ∈ 𝔉`. -/
theorem closedforms_a {K : ℕ} (k : ℕ) (hF : InF μin K) (hK : k + 2 ≤ K) :
    (lvl μin k).dE (μT μin (k + 1)) =
        (2 + (lvl μin k).dbar (μT μin (k + 1))) * (lvl μin k).w (μT μin (k + 1)) /
          (lvl μin k).βδ ∧
      φ μin k = 1 + (lvl μin k).dbar (μT μin (k + 1)) -
        (lvl μin k).a0 (μT μin (k + 1)) / ((lvl μin k).s * (lvl μin k).w (μT μin (k + 1))) :=
  closedforms_a_aux k (μT_pos hF (by omega))

/-- **`lem:closedforms`(b)** (`stoc-sections/appD-hardness.tex:753-755`, proof lines 765-780): let
`μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). At the step `k → k + 1`,
`u_1(α) = s(α − (R_0 + R_1)/2) + w/2` and `u_2(α) = u_1(α) − (1 + d̄)w + a_0/Δ_b` for every
`α ∈ ℝ`; in particular `u_2(R_0 + μ) = u^0`, and `u_1` and `u_2` increase with slope `s > 0`. The
proof (steps (b1)–(b5)) is that of `closedforms_b_aux`, with `μ = μ_{k+1} > 0` as `μ^in ∈ 𝔉`. -/
theorem closedforms_b {K : ℕ} (k : ℕ) (hF : InF μin K) (hK : k + 2 ≤ K) :
    (∀ α, u1 μin k α = (lvl μin k).s * (α - (R0 + R1T μin k) / 2) +
      (lvl μin k).w (μT μin (k + 1)) / 2) ∧
    (∀ α, u2 μin k α = u1 μin k α -
      (1 + (lvl μin k).dbar (μT μin (k + 1))) * (lvl μin k).w (μT μin (k + 1)) +
        (lvl μin k).a0 (μT μin (k + 1)) / (lvl μin k).Δb) ∧
    u2 μin k (R0 + μT μin (k + 1)) = (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) ∧
    0 < (lvl μin k).s ∧
    (∀ α α', u1 μin k α' - u1 μin k α = (lvl μin k).s * (α' - α)) ∧
    (∀ α α', u2 μin k α' - u2 μin k α = (lvl μin k).s * (α' - α)) :=
  closedforms_b_aux k (μT_pos hF (by omega))

/-- **`lem:closedforms`(c)** (`stoc-sections/appD-hardness.tex:756-757`, proof lines 782-787): let
`μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). At the step `k → k + 1`,
`ρ^f_{τ_2}(α) = (α − R_0)m_δ + ρ̄_k + w − u^0 + sι` for every `α ∈ ℝ`; in particular
`ρ̄_{k+1} = ρ^f_{τ_2}(R_0) = ρ̄_k + w − u^0 + sι`. The proof (steps (c1), (c2)) is that of
`closedforms_c_aux`, which does not use the hypothesis on the input. -/
theorem closedforms_c {K : ℕ} (k : ℕ) (_hF : InF μin K) (_hK : k + 2 ≤ K) :
    (∀ α, ρf μin k α none = (α - R0) * (lvl μin k).mδ + (lvl μin k).ρbar +
      (lvl μin k).w (μT μin (k + 1)) - (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) +
        (lvl μin k).s * ι) ∧
    (lvl μin (k + 1)).ρbar = ρf μin k R0 none ∧
    ρf μin k R0 none = (lvl μin k).ρbar + (lvl μin k).w (μT μin (k + 1)) -
      (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) + (lvl μin k).s * ι :=
  closedforms_c_aux k

/-- **`lem:closedforms`** (Lemma C.13, `stoc-sections/appD-hardness.tex:749-759`): let
`μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`). At the step `k → k + 1`, the following hold.
(a) `d(E) = (2 + d̄)w/β_δ` and `φ = 1 + d̄ − a_0/(sw)`. (b) `u_1(α) = s(α − (R_0 + R_1)/2) + w/2`
and `u_2(α) = u_1(α) − (1 + d̄)w + a_0/Δ_b` for every `α ∈ ℝ`. In particular, `u_2(R_0 + μ) = u^0`,
and `u_1` and `u_2` increase with slope `s` (with `s > 0`). (c)
`ρ^f_{τ_2}(α) = (α − R_0)m_δ + ρ̄_k + w − u^0 + sι` for every `α ∈ ℝ`. In particular,
`ρ̄_{k+1} = ρ^f_{τ_2}(R_0) = ρ̄_k + w − u^0 + sι`.

The input `μ^in` of `def:tower` comes from the family `𝔉`, as in the paper, and is taken once for
the three parts. Its parts are `closedforms_a`, `closedforms_b` and `closedforms_c`; their
docstrings give the paper's steps. -/
theorem closedforms {K : ℕ} (k : ℕ) (hF : InF μin K) (hK : k + 2 ≤ K) :
    -- (a)
    ((lvl μin k).dE (μT μin (k + 1)) =
        (2 + (lvl μin k).dbar (μT μin (k + 1))) * (lvl μin k).w (μT μin (k + 1)) /
          (lvl μin k).βδ ∧
      φ μin k = 1 + (lvl μin k).dbar (μT μin (k + 1)) -
        (lvl μin k).a0 (μT μin (k + 1)) / ((lvl μin k).s * (lvl μin k).w (μT μin (k + 1)))) ∧
    -- (b)
    ((∀ α, u1 μin k α = (lvl μin k).s * (α - (R0 + R1T μin k) / 2) +
        (lvl μin k).w (μT μin (k + 1)) / 2) ∧
      (∀ α, u2 μin k α = u1 μin k α -
        (1 + (lvl μin k).dbar (μT μin (k + 1))) * (lvl μin k).w (μT μin (k + 1)) +
          (lvl μin k).a0 (μT μin (k + 1)) / (lvl μin k).Δb) ∧
      u2 μin k (R0 + μT μin (k + 1)) = (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) ∧
      0 < (lvl μin k).s ∧
      (∀ α α', u1 μin k α' - u1 μin k α = (lvl μin k).s * (α' - α)) ∧
      (∀ α α', u2 μin k α' - u2 μin k α = (lvl μin k).s * (α' - α))) ∧
    -- (c)
    ((∀ α, ρf μin k α none = (α - R0) * (lvl μin k).mδ + (lvl μin k).ρbar +
        (lvl μin k).w (μT μin (k + 1)) - (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) +
          (lvl μin k).s * ι) ∧
      (lvl μin (k + 1)).ρbar = ρf μin k R0 none ∧
      ρf μin k R0 none = (lvl μin k).ρbar + (lvl μin k).w (μT μin (k + 1)) -
        (lvl μin k).u0 (μT μin (k + 1)) (R1T μin k) + (lvl μin k).s * ι) :=
  ⟨closedforms_a k hF hK, closedforms_b k hF hK, closedforms_c k hF hK⟩

end Tower

end

end Hardness

end Stoc
