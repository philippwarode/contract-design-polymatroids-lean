-- stamp r11 2026-11-03
import ContractDesignPolymatroids.Hardness.AllLevels

/-!
# The comb gadget: `thm:gadget`

The STOC version's `thm:gadget` (Appendix C.3, `sec:D-correct`, "The gadget",
`stoc-sections/appD-hardness.tex:191-197`; proof in Appendix C.7, `sec:D-alllevels`, "Every level
works", lines 1660-1780), for `μ^in ∈ 𝔉` of length `k` (`InF μin k`) and the last
level `g := g_{k−1}` on `E := E_{k−1}` (`def:tower`, `thm:alllevels`).

The proof has four parts, which open with sentences instead of labels; we number them (1)-(4):
* (1) "We first define the output and the numbers that come with it": `gΘ` (`Θ`), `gΛ` (`Λ`),
  `gNmin` (`N_min`), `gΛ'` (`Λ' = δN − ζ_1`), `gαΓ` (`α_Γ = δN`), `gfc` (`f_c = g + Λ't − Θβ⁻¹`),
  `gq` (`q = q_{k−1}`), `gC` (`C_g = (q + κ)α_Γ`), `gadgetF`, `gadgetM`, `gadgetB` (the output
  `I(μ^in, N)`: `(f_c, m, β)` plus the capped linear summand `e_g` of `lem:ops`(c)), `gp` (`p`),
  and `gLc` (`L_c`) and `gΓ` (`Γ`) of the later parts;
* (2) "Next we show that `f_c` is a polymatroid rank function and that `(f_c, m, β)` keeps the gap
  of level `k − 1`, shifted by `Λ'`, to the right of `α_Γ`": `gadget_embed`;
* (3) "Then we show that the output is a comb. The summand `e_g` takes care of the gap to the left
  of the contacts.": `gadget_knob`;
* (4) "Finally, we show that the output lies in `𝒞_cut`, that its numbers have polynomial size,
  and that it is computed in polynomial time": in `gadget`, `thm:gadget` itself;
* the D3 lemmas (not in the paper): `card_Gr` (`|E_j| = 3(j + 1)`), `gT_baseEmb` (`g = f_0` on
  `2^{E_0}`), `hasCutForm_gT` (`g_j` has a cut form, by induction on `j`), `q_ge_q₀`
  (`q_j ≥ q_0`, by induction on `j`) and `gαΓ_gC_pos` (`α_Γ, C_g > 0`, which part (3) needs for
  `lem:ops`(c)).

The Lean name `gadget_knob` of (3) and `knob` of the summand are the names of the earlier versions
of the paper, which called a capped linear summand a "knob".

The bit lengths and the rationality of the numbers (`lem:sizes` and the size part of (4)) are in
`ContractDesignPolymatroids/Hardness/Sizes.lean` and `ContractDesignPolymatroids/Hardness/GadgetSizes.lean`, with the cut form of the output
computed along the construction (`gadgetForm`); here a cut form of the output exists
(`HasCutForm`, inside `Ccut`). Not formalised: the running time of the algorithm (Turing machines
are not formalised, and arithmetic operations are not counted).

Taken over on 2026-10-20 from `Paper/Hardness/Gadget.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### The levels -/

/-- Every level is nonempty. -/
instance instNonemptyGr : (k : ℕ) → Nonempty (Gr k)
  | 0 => ⟨(0 : Fin 3)⟩
  | k + 1 => ⟨(none : Option (Option (Option (Gr k))))⟩

/-- Level `j` has `3(j + 1)` elements (`def:tower`: `E_0` has three, and every step adds `τ_{1,j}`,
`τ_{2,j}`, `b_j`) (not in the paper: the proof of `thm:gadget` states `|E| = 3k` for `E = E_{k−1}`
without proof). -/
theorem card_Gr : ∀ j, Fintype.card (Gr j) = 3 * (j + 1)
  | 0 => by
    show Fintype.card (Fin 3) = 3
    simp
  | j + 1 => by
    have ih := card_Gr j
    show Fintype.card (Option (Option (Option (Gr j)))) = 3 * (j + 1 + 1)
    simp only [Fintype.card_option, ih]
    ring

/-- The base elements `E_0 ⊆ E_j` inside level `j` (`def:tower`:
`E_j = E_{j−1} ∪ {τ_{1,j}, τ_{2,j}, b_j}`, and the old elements of `E_j` are the
`some (some (some c))`). -/
def baseEmb : (j : ℕ) → Fin 3 → Gr j
  | 0 => fun e => e
  | j + 1 => fun e => some (some (some (baseEmb j e)))

section Levels

variable {μin : ℕ → ℕ}

/-- `g_j = f_0` on `2^{E_0}`, and the base elements keep their rewards and curvatures (not in the
paper: the proof of `thm:gadget` uses this without proof, "as `g = f_0` on `2^{E_0}` by
`def:tower`"). -/
lemma gT_baseEmb : ∀ (j : ℕ) (S : Finset (Fin 3)),
    gT μin j (S.image (baseEmb j)) = Base.f₀ S ∧
      ∀ e, mT μin j (baseEmb j e) = Base.m e ∧ βT μin j (baseEmb j e) = Base.β e
  | 0, S => by
    refine ⟨?_, fun e => ⟨rfl, rfl⟩⟩
    show Base.f₀ (S.image fun e => e) = Base.f₀ S
    rw [image_id']
  | j + 1, S => by
    obtain ⟨ih, ihm⟩ := gT_baseEmb j S
    refine ⟨?_, fun e => ihm e⟩
    have e1 : S.image (baseEmb (j + 1)) =
        (((S.image (baseEmb j)).image some).image some).image some := by
      simp only [image_image]
      rfl
    have hn1 : (none : Option (Option (Option (Gr j)))) ∉
        (((S.image (baseEmb j)).image some).image some).image some := by simp
    have hn2 : (none : Option (Option (Gr j))) ∉ ((S.image (baseEmb j)).image some).image some := by
      simp
    have hn3 : (none : Option (Gr j)) ∉ (S.image (baseEmb j)).image some := by simp
    rw [← ih, e1]
    show extend (StepData.fStep (stepD μin j) (gT μin j))
      ((stepD μin j).dStep (mT μin j) (βT μin j)) (stepD μin j).K
      ((((S.image (baseEmb j)).image some).image some).image some) = _
    simp only [extend, StepData.fStep, addSingleton, hn1, hn2, hn3, ↓reduceIte, add_zero,
      eraseNone_image_some]

/-- `g_j` has a cut form, by induction on `j` with `prop:base` and `lem:cutforms`(c): `g_j` is
obtained from `g_{j−1}` by two direct sums with modular singletons and a one-element extension with
`d_j ≥ 0` (not in the paper: part (2) of the proof of `thm:gadget` says only "by `prop:base` and
`lem:cutforms`(c), the function `g` has a cut form" and leaves the induction over the steps
implicit). -/
theorem hasCutForm_gT : ∀ j, HasCutForm (gT μin j)
  | 0 => ⟨Base.form, Base.base.2.1⟩
  | j + 1 => (((hasCutForm_gT j).addSingleton _).addSingleton _).extend
      (stepD_hyp (μin := μin) j).d_nonneg _

/-- `q_j ≥ q_0 = 7`, by induction on `j` with (P8): `q_{j+1} = q_j + ψ_{j+1}` with `ψ_{j+1} ≥ 0`
(not in the paper: part (3) of the proof of `thm:gadget` says "`q = q_{k−1} ≥ q_0 = 7 > 0` by
(P8)" and leaves the induction over the steps implicit). -/
lemma q_ge_q₀ : ∀ j, q₀ ≤ (lvl μin j).q
  | 0 => le_rfl
  | j + 1 => by
    rw [q_succ]
    linarith [q_ge_q₀ j, ψ_nonneg (μin := μin) j]

end Levels

/-! ### The construction: part (1) of the proof -/

section Construction

variable (μin : ℕ → ℕ) (k : ℕ)

/-- `Θ = max_{e∈E} (β_e g({e}) − ζ_1 m_e)` (part (1) of the proof of `thm:gadget`, "We first
define the output and the numbers that come with it"). -/
def gΘ : ℝ :=
  univ.sup' univ_nonempty fun e =>
    βT μin (k - 1) e * gT μin (k - 1) {e} - ζ₁ * mT μin (k - 1) e

/-- `Λ = max(0, max_{e∈E} (Θ/β_e − g(E) + g(E ∖ {e}))/t_e)`, with `t_e = m_e/β_e`. -/
def gΛ : ℝ :=
  max 0 (univ.sup' univ_nonempty fun e =>
    (gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ + gT μin (k - 1) (univ.erase e)) /
      (mT μin (k - 1) e / βT μin (k - 1) e))

/-- `N_min = max(1, ⌈(ζ_1 + Λ)/δ⌉)`. -/
def gNmin : ℕ := max 1 ⌈(ζ₁ + gΛ μin k) / δT μin⌉₊

variable {k}

/-- `Λ' = δN − ζ_1`. -/
def gΛ' (N : ℕ) : ℝ := δT μin * N - ζ₁

/-- `α_Γ = δN`. -/
def gαΓ (N : ℕ) : ℝ := δT μin * N

variable (k)

/-- `f_c = g + Λ't − Θβ⁻¹`. -/
def gfc (N : ℕ) (S : Finset (Gr (k - 1))) : ℝ :=
  gT μin (k - 1) S + gΛ' μin N * ∑ e ∈ S, mT μin (k - 1) e / βT μin (k - 1) e -
    gΘ μin k * ∑ e ∈ S, 1 / βT μin (k - 1) e

/-- `q = q_{k−1}`. -/
def gq : ℝ := (lvl μin (k - 1)).q

/-- The capacity `C_g = (q + κ)α_Γ` of the capped linear summand `e_g`. -/
def gC (N : ℕ) : ℝ := (gq μin k + κT μin) * gαΓ μin N

/-- The rank function of `I(μ^in, N)`: `f_c` plus the capped linear summand `e_g` (`lem:ops`(c),
`knob`) with the capacity `C_g` and the share `α_∘ := α_Γ`; `e_g` is the element of `Unit`. -/
def gadgetF (N : ℕ) : Finset (Gr (k - 1) ⊕ Unit) → ℝ := knob (gfc μin k N) (gC μin k N)

/-- The rewards of `I(μ^in, N)`: `m` on `E`, and `m_{e_g} = 1`. -/
def gadgetM : Gr (k - 1) ⊕ Unit → ℝ := Sum.elim (mT μin (k - 1)) fun _ => 1

/-- The curvatures of `I(μ^in, N)`: `β` on `E`, and `β_{e_g} = α_∘/C_g = α_Γ/C_g`
(`= 1/(q + κ)`). -/
def gadgetB (N : ℕ) : Gr (k - 1) ⊕ Unit → ℝ :=
  Sum.elim (βT μin (k - 1)) fun _ => gαΓ μin N / gC μin k N

/-- `p = p_{k−1} − qΛ' + Λ'm^⊤t − Θt(E) + C_g`. -/
def gp (N : ℕ) : ℝ :=
  (lvl μin (k - 1)).p - gq μin k * gΛ' μin N +
    gΛ' μin N * ∑ e, mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e) -
    gΘ μin k * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e + gC μin k N

/-- `L_c(α) = L_{k−1}(α − Λ') + Λ'm^⊤t − Θt(E)` (part (2) of the proof of `thm:gadget`). -/
def gLc (N : ℕ) (α : ℝ) : ℝ :=
  (lvl μin (k - 1)).p + gq μin k * (α - gΛ' μin N) +
    gΛ' μin N * ∑ e, mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e) -
    gΘ μin k * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e

/-- The contact set `Γ = {δ(N + χ^⊤μ^in) : χ ∈ {0, 1}^k}`; `χ` is the indicator of
`Q ⊆ {0, …, k − 1}` (indices from `0`: `μin i` is `μ^in_{i+1}`). -/
def gΓ (N : ℕ) : Finset ℝ :=
  (range k).powerset.image fun Q => δT μin * (N + ∑ i ∈ Q, (μin i : ℝ))

end Construction

/-! ### The proof -/

section Proof

variable {μin : ℕ → ℕ} {k : ℕ}

/-- `δ > 0` and `κ > 0` for `μ^in ∈ 𝔉`. -/
lemma δT_κT_pos (h0 : 0 < μin 0) : 0 < δT μin ∧ 0 < κT μin := by
  have : (0 : ℝ) < μin 0 := by exact_mod_cast h0
  have hδ : 0 < δT μin := by unfold δT; positivity
  exact ⟨hδ, lt_min one_pos (by positivity)⟩

/-- `Λ' + Γ_{k−1} = {δ(N + χ^⊤μ^in) : χ ∈ {0, 1}^k} = Γ`, as `μ_i = δμ^in_{i+1}` (part (2) of the
proof of `thm:gadget`). -/
lemma gΓ_eq (hk : 1 ≤ k) (N : ℕ) :
    (ΓT μin (k - 1)).image (· + gΛ' μin N) = gΓ μin k N := by
  rw [ΓT, image_image, gΓ, Nat.sub_add_cancel hk]
  refine image_congr fun Q _ => ?_
  simp only [Function.comp_apply, gΛ', μT, ← mul_sum]
  ring

/-- `α_Γ = δN` is the smallest point of `Γ` (part (2) of the proof of `thm:gadget`). -/
lemma gαΓ_mem (N : ℕ) : gαΓ μin N ∈ gΓ μin k N ∧ ∀ γ ∈ gΓ μin k N, gαΓ μin N ≤ γ := by
  have hδ : 0 ≤ δT μin := by unfold δT; positivity
  refine ⟨mem_image.2 ⟨∅, empty_mem_powerset _, by simp [gαΓ]⟩, fun γ hγ => ?_⟩
  obtain ⟨Q, -, rfl⟩ := mem_image.1 hγ
  have : 0 ≤ ∑ i ∈ Q, (μin i : ℝ) := sum_nonneg fun i _ => Nat.cast_nonneg _
  unfold gαΓ
  nlinarith

/-- **Part (2) of the proof of `thm:gadget`** (our numbering of its four parts, see `gadget`;
`stoc-sections/appD-hardness.tex:1680-1725`; `Λ' = δN − ζ_1 ≥ Λ` is from part (1), line 1673):
"Next we show that `f_c` is a polymatroid rank function and that `(f_c, m, β)` keeps the gap of
level `k − 1`, shifted by `Λ'`, to the right of `α_Γ`." That is, for `N ≥ N_min`, `f_c` is a
polymatroid rank function, the reward of `(f_c, m, β)` under its best response is
`r(x*_c(α + Λ')) = r(ξ^{(k−1)}(α)) + Λ'm^⊤t − Θt(E)` for `α ≥ ζ_1`, and for `α ≥ α_Γ = ζ_1 + Λ'`,
`L_c(α) − r(x*_c(α)) ≥ κ min(dist(α, Λ' + Γ_{k−1}), δ)`, with equality `0` on `Λ' + Γ_{k−1} = Γ`.

The part's sentences: (2a) by `prop:base` and `lem:cutforms`(c), `g` has a cut form, so it is
submodular by `lem:cutforms`(a), and `g(∅) = f_0(∅) = 0`; (2b) `lem:embed` with `f̃ := g`,
`a := t`, `b := β⁻¹`, and the parameters `(Λ', Θ)`: its function is `f_c`, and its instance is
`(f_c, m, β)`; (2c) its hypotheses hold: `t, β⁻¹ > 0`; `Θ > 0`, as `g = f_0` on `2^{E_0}`, so
`Θ ≥ β_{C_1}g({C_1}) − ζ_1m_{C_1} = 2/3`; for `e ∈ E` and `S ⊆ E ∖ {e}`, submodularity gives
`g(S) − g(S ∪ {e}) ≤ g(E ∖ {e}) − g(E)`, with equality for `S = E ∖ {e}`, so the lower bound that
`lem:embed` imposes on its first parameter is `Λ`, and `Λ' ≥ Λ`; equivalently, the marginal value
`f_c(S ∪ {e}) − f_c(S)` is at least `f_c(E) − f_c(E ∖ {e}) = g(E) − g(E ∖ {e}) + Λ't_e − Θ/β_e`,
which is nonnegative; (2d) so `f_c` is a polymatroid rank function; (2e) for `α ≥ ζ_1`,
`ρ^g_e(α) ≥ αm_e − β_eg({e}) ≥ ζ_1m_e − β_eg({e}) ≥ −Θ` and `α + Λ' ≥ 0`, so `lem:fullplane`(g)
gives `x*_c(α + Λ') = ξ^g(α) + Λ't − Θβ⁻¹` and the reward; (2f) for `α ≥ α_Γ`, `(H_{k−1})` of
`thm:alllevels` gives the comb bound and the contacts. -/
theorem gadget_embed (hF : InF μin k) {N : ℕ} (hN : gNmin μin k ≤ N) :
    IsRankFunction (gfc μin k N) ∧
    (∀ α, ζ₁ ≤ α → grossValue (gfc μin k N) (mT μin (k - 1)) (βT μin (k - 1)) (α + gΛ' μin N) =
      curve (gT μin (k - 1)) (mT μin (k - 1)) (βT μin (k - 1)) α +
        gΛ' μin N * ∑ e, mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e) -
        gΘ μin k * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e) ∧
    (∀ α, gαΓ μin N ≤ α → κT μin * minDist α (gΓ μin k N) (δT μin) ≤
      gLc μin k N α - grossValue (gfc μin k N) (mT μin (k - 1)) (βT μin (k - 1)) α) ∧
    ∀ γ ∈ gΓ μin k N,
      grossValue (gfc μin k N) (mT μin (k - 1)) (βT μin (k - 1)) γ = gLc μin k N γ := by
  have hk : 1 ≤ k := hF.1
  have h0 := μin0_pos hF
  obtain ⟨hδ, -⟩ := δT_κT_pos h0
  have hm : ∀ e, 0 < mT μin (k - 1) e := mT_pos (k - 1)
  have hβ : ∀ e, 0 < βT μin (k - 1) e := (fpHyp_gT (μin := μin) (k - 1)).pos
  -- From part (1): "`Λ' := δN − ζ_1 ≥ Λ`", as `N ≥ N_min`; and `Λ ≥ 0`.
  have hΛ0 : 0 ≤ gΛ μin k := le_max_left _ _
  have hΛ' : gΛ μin k ≤ gΛ' μin N := by
    have h1 : (⌈(ζ₁ + gΛ μin k) / δT μin⌉₊ : ℝ) ≤ N := by
      have := (le_max_right 1 ⌈(ζ₁ + gΛ μin k) / δT μin⌉₊).trans hN
      exact_mod_cast this
    have h2 := (Nat.le_ceil ((ζ₁ + gΛ μin k) / δT μin)).trans h1
    rw [div_le_iff₀ hδ] at h2
    unfold gΛ'
    linarith
  -- (2a) "By `prop:base` and `lem:cutforms`(c), the function `g` has a cut form, so it is
  -- submodular by `lem:cutforms`(a), and `g(∅) = f_0(∅) = 0`."
  have hsub : Submodular (gT μin (k - 1)) := by
    obtain ⟨F, hF⟩ := hasCutForm_gT (μin := μin) (k - 1)
    intro X Y
    rw [hF, hF, hF, hF]
    exact cutforms_a F X Y
  have hg0 : gT μin (k - 1) ∅ = 0 := by
    have := (gT_baseEmb (μin := μin) (k - 1) ∅).1
    rw [image_empty] at this
    rw [this]
    exact Base.base.1.empty
  -- (2b) "We apply `lem:embed` with `f̃ := g`, `a := t`, `b := β⁻¹`, and the parameters `(Λ', Θ)`.
  -- Then its function `f` is `f_c`, and its instance is `(f_c, m, β)`, as `a_e/b_e = m_e` and
  -- `1/b_e = β_e`."
  have hfeq : gfc μin k N = Exp.embedF (gT μin (k - 1))
      (fun e => mT μin (k - 1) e / βT μin (k - 1) e) (fun e => 1 / βT μin (k - 1) e) (gΛ' μin N)
      (gΘ μin k) := by
    funext S
    simp only [gfc, Exp.embedF, sum_sub_distrib, mul_sum]
    ring
  -- (2c) "Its hypotheses hold. The vectors `t` and `β⁻¹` are positive, as `m, β > 0`."
  have ht : ∀ e, 0 < mT μin (k - 1) e / βT μin (k - 1) e := fun e => div_pos (hm e) (hβ e)
  have hb : ∀ e, 0 < 1 / βT μin (k - 1) e := fun e => one_div_pos.2 (hβ e)
  -- "Next, `Θ > 0`, as `g = f_0` on `2^{E_0}` by `def:tower`, so
  -- `Θ ≥ β_{C_1}g({C_1}) − ζ_1m_{C_1} = 4 · 7/6 − 12/3 = 2/3`."
  have hΘ : 0 < gΘ μin k := by
    obtain ⟨hg1, hmβ⟩ := gT_baseEmb (μin := μin) (k - 1) {(1 : Fin 3)}
    rw [image_singleton] at hg1
    have h := le_sup' (fun e => βT μin (k - 1) e * gT μin (k - 1) {e} - ζ₁ * mT μin (k - 1) e)
      (mem_univ (baseEmb (k - 1) 1))
    simp only [hg1, (hmβ 1).1, (hmβ 1).2] at h
    have hv : Base.β 1 * Base.f₀ {1} - ζ₁ * Base.m 1 = 2 / 3 := by
      simp [Base.β, Base.f₀, Base.tab, Base.m, ζ₁]
      norm_num
    unfold gΘ
    linarith
  -- "Finally, for `e ∈ E` and `S ⊆ E ∖ {e}`, submodularity gives
  -- `g(S) − g(S ∪ {e}) ≤ g(E ∖ {e}) − g(E)`,"
  have hsubm : ∀ S e, e ∉ S → gT μin (k - 1) S - gT μin (k - 1) (insert e S) ≤
      gT μin (k - 1) (univ.erase e) - gT μin (k - 1) univ := by
    intro S e he
    have hdr := hsub.diminishingReturns (X := S) (Y := univ.erase e) (e := e)
      (fun x hx => mem_erase.2 ⟨fun h => he (h ▸ hx), mem_univ x⟩) (notMem_erase e univ)
    rw [insert_erase (mem_univ e)] at hdr
    linarith
  -- "with equality for `S = E ∖ {e}`."
  have hequal : ∀ e, gT μin (k - 1) (univ.erase e) - gT μin (k - 1) (insert e (univ.erase e)) =
      gT μin (k - 1) (univ.erase e) - gT μin (k - 1) univ := fun e => by
    rw [insert_erase (mem_univ e)]
  -- "So the lower bound that `lem:embed` imposes on its first parameter is `Λ`": a number `y` is
  -- at least `max{0, max_{S ⊆ E, e ∈ E ∖ S} (g(S) − g(S ∪ {e}) + Θ/β_e)/t_e}` if and only if
  -- `y ≥ Λ`,
  have hLB : ∀ y, (0 ≤ y ∧ ∀ S e, e ∉ S → (gT μin (k - 1) S - gT μin (k - 1) (insert e S) +
      gΘ μin k * (1 / βT μin (k - 1) e)) / (mT μin (k - 1) e / βT μin (k - 1) e) ≤ y) ↔
      gΛ μin k ≤ y := by
    intro y
    constructor
    · rintro ⟨hy0, hy⟩
      unfold gΛ
      refine max_le hy0 (sup'_le _ _ fun e _ => ?_)
      have h := hy (univ.erase e) e (notMem_erase e univ)
      rw [hequal e] at h
      calc _ = (gT μin (k - 1) (univ.erase e) - gT μin (k - 1) univ +
            gΘ μin k * (1 / βT μin (k - 1) e)) / (mT μin (k - 1) e / βT μin (k - 1) e) := by
            ring
        _ ≤ y := h
    · intro hy
      refine ⟨hΛ0.trans hy, fun S e he => ?_⟩
      calc (gT μin (k - 1) S - gT μin (k - 1) (insert e S) + gΘ μin k * (1 / βT μin (k - 1) e)) /
            (mT μin (k - 1) e / βT μin (k - 1) e)
          ≤ (gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ +
            gT μin (k - 1) (univ.erase e)) / (mT μin (k - 1) e / βT μin (k - 1) e) := by
            refine div_le_div_of_nonneg_right ?_ (ht e).le
            rw [mul_one_div]
            linarith [hsubm S e he]
        _ ≤ gΛ μin k := (le_sup' (fun e => (gΘ μin k / βT μin (k - 1) e -
            gT μin (k - 1) univ + gT μin (k - 1) (univ.erase e)) /
            (mT μin (k - 1) e / βT μin (k - 1) e)) (mem_univ e)).trans (le_max_right _ _)
        _ ≤ y := hy
  -- "and `Λ' ≥ Λ`."
  obtain ⟨hΛ'0, hα₀⟩ := (hLB (gΛ' μin N)).2 hΛ'
  -- "Equivalently, for `e ∈ E` and `S ⊆ E ∖ {e}`, the marginal value `f_c(S ∪ {e}) − f_c(S)` is
  -- at least `f_c(E) − f_c(E ∖ {e}) = g(E) − g(E ∖ {e}) + Λ't_e − Θ/β_e`, which is nonnegative
  -- as `Λ' ≥ Λ`."
  have hmarg : ∀ S e, e ∉ S → gfc μin k N (insert e S) - gfc μin k N S =
      gT μin (k - 1) (insert e S) - gT μin (k - 1) S +
        gΛ' μin N * (mT μin (k - 1) e / βT μin (k - 1) e) - gΘ μin k * (1 / βT μin (k - 1) e) :=
    fun S e he => by
      simp only [gfc, sum_insert he]
      ring
  have hequiv : ∀ S e, e ∉ S →
      gfc μin k N univ - gfc μin k N (univ.erase e) ≤
        gfc μin k N (insert e S) - gfc μin k N S ∧
      gfc μin k N univ - gfc μin k N (univ.erase e) = gT μin (k - 1) univ -
        gT μin (k - 1) (univ.erase e) + gΛ' μin N * (mT μin (k - 1) e / βT μin (k - 1) e) -
        gΘ μin k * (1 / βT μin (k - 1) e) ∧
      0 ≤ gfc μin k N univ - gfc μin k N (univ.erase e) := by
    intro S e he
    have htop := hmarg (univ.erase e) e (notMem_erase e univ)
    rw [insert_erase (mem_univ e)] at htop
    have h1 := hα₀ (univ.erase e) e (notMem_erase e univ)
    rw [hequal e, div_le_iff₀ (ht e)] at h1
    refine ⟨?_, htop, ?_⟩
    · rw [htop, hmarg S e he]
      linarith [hsubm S e he]
    · rw [htop]
      linarith
  -- (2d) "By `lem:embed`, `f_c` is a polymatroid rank function."
  have hrank : IsRankFunction (gfc μin k N) := by
    rw [hfeq]
    exact (Exp.embed hsub hg0 ht hb hΘ hΛ'0 hα₀).1
  -- (2e) "`lem:embed` describes the level sets of `(f_c, m, β)`, and `lem:fullplane`(g), with
  -- `(Λ', Θ)` in place of `(Λ, Θ)`, gives its best response `x*_c` itself. For `α ≥ ζ_1`,
  -- `ξ^g_e(α) ≤ g({e})` and `m_e > 0` give
  -- `ρ^g_e(α) ≥ αm_e − β_eg({e}) ≥ ζ_1m_e − β_eg({e}) ≥ −Θ`, and `α + Λ' ≥ 0`. So, by
  -- `lem:fullplane`(g), `x*_c(α + Λ') = ξ^g(α) + Λ't − Θβ⁻¹` for `α ≥ ζ_1`, and as
  -- `m^⊤β⁻¹ = t(E)`, the reward of `(f_c, m, β)` under its best response satisfies
  -- `r(x*_c(α + Λ')) = r(ξ^{(k−1)}(α)) + Λ'm^⊤t − Θt(E)`."
  have hrew : ∀ α, ζ₁ ≤ α →
      grossValue (gfc μin k N) (mT μin (k - 1)) (βT μin (k - 1)) (α + gΛ' μin N) =
        curve (gT μin (k - 1)) (mT μin (k - 1)) (βT μin (k - 1)) α +
        gΛ' μin N * ∑ e, mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e) -
        gΘ μin k * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e := by
    intro α hα
    have hρ : ∀ e, 0 ≤ rho (gT μin (k - 1)) (mT μin (k - 1)) (βT μin (k - 1)) α e + gΘ μin k := by
      intro e
      have hξ := (fpBase_subset_Icc (gT μin (k - 1))
        (xi_mem_fpBase (fpHyp_gT (μin := μin) (k - 1)) (mT μin (k - 1)) α)).2 e
      have h1 : α * mT μin (k - 1) e - βT μin (k - 1) e * gT μin (k - 1) {e} ≤
          rho (gT μin (k - 1)) (mT μin (k - 1)) (βT μin (k - 1)) α e := by
        have := mul_le_mul_of_nonneg_left hξ (hβ e).le
        simp only [rho, marg] at this ⊢
        linarith
      have h2 : ζ₁ * mT μin (k - 1) e ≤ α * mT μin (k - 1) e :=
        mul_le_mul_of_nonneg_right hα (hm e).le
      have h3 := le_sup' (fun e => βT μin (k - 1) e * gT μin (k - 1) {e} - ζ₁ * mT μin (k - 1) e)
        (mem_univ e)
      unfold gΘ
      linarith
    have hα' : -gΛ' μin N ≤ α := by
      have : (0 : ℝ) < ζ₁ := by unfold ζ₁; norm_num
      linarith
    have hx := fullplane_g hsub hg0 hm hβ (Λ := gΛ' μin N) (Θ := gΘ μin k) hrank hα' hρ
    unfold grossValue reward curve
    rw [show gfc μin k N = fun S => gT μin (k - 1) S +
        gΛ' μin N * ∑ e ∈ S, mT μin (k - 1) e / βT μin (k - 1) e -
        gΘ μin k * ∑ e ∈ S, 1 / βT μin (k - 1) e from rfl,
      hx, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun e _ => ?_
    ring
  -- (2f) "Let `L_c(α) := L_{k−1}(α − Λ') + Λ'm^⊤t − Θt(E)`. For `α ≥ α_Γ = ζ_1 + Λ'`, so that
  -- `α − Λ' ≥ ζ_1 > R_0`, `(H_{k−1})` of `thm:alllevels` gives
  -- `L_c(α) − r(x*_c(α)) = L_{k−1}(α − Λ') − r(ξ^{(k−1)}(α − Λ'))
  -- ≥ κ min(dist(α, Λ' + Γ_{k−1}), δ)`, with equality `0` on
  -- `Λ' + Γ_{k−1} = {δ(N + χ^⊤μ^in) : χ ∈ {0, 1}^k} = Γ`, whose smallest point is `α_Γ`."
  have hH := (alllevels hF).1 (k - 1) (by omega)
  have hgap : ∀ α, gαΓ μin N ≤ α → gLc μin k N α -
      grossValue (gfc μin k N) (mT μin (k - 1)) (βT μin (k - 1)) α =
        gapT μin (k - 1) (α - gΛ' μin N) := by
    intro α hα
    have h1 : ζ₁ ≤ α - gΛ' μin N := by unfold gαΓ at hα; unfold gΛ'; linarith
    have h2 := hrew _ h1
    rw [sub_add_cancel] at h2
    rw [h2]
    simp only [gLc, gapT, gap, gq]
    ring
  have hR0ζ : R0 < ζ₁ := by unfold R0; norm_num
  refine ⟨hrank, hrew, fun α hα => ?_, fun γ hγ => ?_⟩
  · rw [hgap α hα, ← gΓ_eq hk, minDist_translate]
    have h1 : ζ₁ ≤ α - gΛ' μin N := by unfold gαΓ at hα; unfold gΛ'; linarith
    exact hH.1 _ (by linarith)
  · rw [← gΓ_eq hk] at hγ
    obtain ⟨γ', hγ', rfl⟩ := mem_image.1 hγ
    have hγ'1 : ζ₁ ≤ γ' := by
      obtain ⟨Q, -, rfl⟩ := mem_image.1 hγ'
      have : 0 ≤ ∑ i ∈ Q, μT μin i := sum_nonneg fun i _ => μT_nonneg i
      linarith
    have hle : gαΓ μin N ≤ γ' + gΛ' μin N := by unfold gαΓ gΛ'; linarith
    have h1 := hgap _ hle
    rw [add_sub_cancel_right, gapT_eq_zero_iff.2 (hH.2 γ' hγ')] at h1
    linarith

/-- The share `α_Γ = δN` and the capacity `C_g = (q + κ)α_Γ` of the summand `e_g` are positive, for
`N ≥ N_min` (not in the paper: part (3) of the proof of `thm:gadget` applies `lem:ops`(c), which
asks for `C, α_∘ > 0`, to `e_g` without saying that they hold, and part (4) uses `C_g > 0`; here
`N ≥ N_min ≥ 1`, `δ, κ > 0` and `q = q_{k−1} ≥ q_0 = 7` by (P8), `q_ge_q₀`). -/
lemma gαΓ_gC_pos (hF : InF μin k) {N : ℕ} (hN : gNmin μin k ≤ N) :
    0 < gαΓ μin N ∧ 0 < gC μin k N := by
  obtain ⟨hδ, hκ⟩ := δT_κT_pos (μin0_pos hF)
  have hN1 : (1 : ℝ) ≤ N := by
    have := (le_max_left 1 ⌈(ζ₁ + gΛ μin k) / δT μin⌉₊).trans hN
    exact_mod_cast this
  have hαΓ : 0 < gαΓ μin N := by unfold gαΓ; positivity
  have hq : q₀ ≤ gq μin k := q_ge_q₀ (k - 1)
  unfold q₀ at hq
  exact ⟨hαΓ, mul_pos (by linarith) hαΓ⟩

/-- **Part (3) of the proof of `thm:gadget`** (`stoc-sections/appD-hardness.tex:1727-1746`): "Then
we show that the output is a comb. The summand `e_g` takes care of the gap to the left of the
contacts." That is, for `N ≥ N_min`, the output `I(μ^in, N)` is a comb with contact set `Γ`, line
`p + qα`, dip `κ`, and width `δ`, and `q = q_{k−1} ≥ q_0 = 7 > 0` by (P8).

The part's sentences: (3a) by `lem:ops`(c), the reward of the output under its best response is
`r(x*_c(α)) + C_g min(α/α_Γ, 1)`, and `L := L_c + C_g` is the line `p + qα` (`lem:ops`(c) asks for
`C_g, α_Γ > 0`, which the D3 lemma `gαΓ_gC_pos` gives); (3b) on `[α_Γ, ∞)`, the summand `e_g` adds
`C_g` to the reward and to the line, so the gap of the output is `L_c(α) − r(x*_c(α))`, and by the
bound of (2) it is at least `κ min(dist(α, Γ), δ)` (and `0` on `Γ`, by the equality of (2)); (3c) on
`[0, α_Γ)`, `r(x*_c(·))` is nondecreasing (`lem:monreward`), so
`r(x*_c(α)) ≤ r(x*_c(α_Γ)) = L_c(α_Γ) = L_c(α) + q(α_Γ − α)`, and the gap of the output is at least
`−q(α_Γ − α) + C_g(1 − α/α_Γ) = κ(α_Γ − α) = κ dist(α, Γ)`; (3d) so the output is a comb with the
stated contact set, line, dip, and width (`def:comb`), and `q = q_{k−1} ≥ q_0 = 7 > 0` by (P8)
(`q_ge_q₀`). -/
theorem gadget_knob (hF : InF μin k) {N : ℕ} (hN : gNmin μin k ≤ N) :
    IsComb (gadgetF μin k N) (gadgetM μin k) (gadgetB μin k N) (gΓ μin k N) (gp μin k N)
      (gq μin k) (κT μin) (δT μin) ∧ 0 < gq μin k := by
  have h0 := μin0_pos hF
  obtain ⟨hδ, hκ⟩ := δT_κT_pos h0
  obtain ⟨hrank, -, hcomb, hcont⟩ := gadget_embed hF hN
  have hβ : ∀ e, 0 < βT μin (k - 1) e := (fpHyp_gT (μin := μin) (k - 1)).pos
  obtain ⟨hαmem, hαmin⟩ := gαΓ_mem (μin := μin) (k := k) N
  -- (3a) "By `lem:ops`(c), the reward of the output under its best response is
  -- `r(x*_c(α)) + C_g min(α/α_Γ, 1)`, and `L := L_c + C_g` is the line `p + qα`."
  -- (`lem:ops`(c) needs `C_g > 0` and `α_Γ > 0`, `gαΓ_gC_pos`)
  obtain ⟨hαΓ, hC⟩ := gαΓ_gC_pos hF hN
  have hr : ∀ α, 0 ≤ α → grossValue (gadgetF μin k N) (gadgetM μin k) (gadgetB μin k N) α =
      grossValue (gfc μin k N) (mT μin (k - 1)) (βT μin (k - 1)) α +
        gC μin k N * min (α / gαΓ μin N) 1 :=
    fun α hα => ops_c_aux hrank hβ hC hαΓ hα
  have hL : ∀ α, gp μin k N + gq μin k * α = gLc μin k N α + gC μin k N := fun α => by
    simp only [gp, gLc]
    ring
  -- (3b) "On `[α_Γ, ∞)`, the summand `e_g` adds `C_g` to the reward and to the line, so the gap
  -- of the output is `L_c(α) − r(x*_c(α))`. By the bound in the previous paragraph, it is at least
  -- `κ min(dist(α, Γ), δ)`." (the bound of (2), `hcomb`; and the gap is `0` on `Γ`, by the
  -- equality of (2), `hcont`)
  have hright : ∀ α, gαΓ μin N ≤ α →
      gp μin k N + gq μin k * α - grossValue (gadgetF μin k N) (gadgetM μin k)
        (gadgetB μin k N) α =
      gLc μin k N α - grossValue (gfc μin k N) (mT μin (k - 1)) (βT μin (k - 1)) α :=
    fun α hα => by
      rw [hr α (hαΓ.le.trans hα), min_eq_right ((one_le_div hαΓ).2 hα), hL]
      ring
  have h3b : ∀ α, gαΓ μin N ≤ α → κT μin * minDist α (gΓ μin k N) (δT μin) ≤
      gp μin k N + gq μin k * α -
        grossValue (gadgetF μin k N) (gadgetM μin k) (gadgetB μin k N) α :=
    fun α h => by
      rw [hright α h]
      exact hcomb α h
  have hcontact : ∀ γ ∈ gΓ μin k N,
      grossValue (gadgetF μin k N) (gadgetM μin k) (gadgetB μin k N) γ =
        gp μin k N + gq μin k * γ := fun γ hγ => by
    have h1 := hright γ (hαmin γ hγ)
    rw [hcont γ hγ] at h1
    linarith
  -- (3c) "On `[0, α_Γ)`, the reward `r(x*_c(·))` is nondecreasing (`lem:monreward`), so
  -- `r(x*_c(α)) ≤ r(x*_c(α_Γ)) = L_c(α_Γ) = L_c(α) + q(α_Γ − α)`,"
  have h3c : ∀ α, 0 ≤ α → α < gαΓ μin N → κT μin * minDist α (gΓ μin k N) (δT μin) ≤
      gp μin k N + gq μin k * α -
        grossValue (gadgetF μin k N) (gadgetM μin k) (gadgetB μin k N) α := by
    intro α hα h
    have hmono := grossValue_monotone hrank (mT μin (k - 1)) (βT μin (k - 1)) h.le
    rw [hcont _ hαmem] at hmono
    have hLc : gLc μin k N (gαΓ μin N) = gLc μin k N α + gq μin k * (gαΓ μin N - α) := by
      simp only [gLc]
      ring
    -- "and the gap of the output satisfies `L(α) − r(x*_c(α)) − C_gα/α_Γ
    -- ≥ −q(α_Γ − α) + C_g(1 − α/α_Γ) = κ(α_Γ − α) = κ dist(α, Γ)`."
    have e : gC μin k N * (1 - α / gαΓ μin N) = (gq μin k + κT μin) * (gαΓ μin N - α) := by
      simp only [gC]
      field_simp
    have hdist : distTo α (gΓ μin k N) = ((gαΓ μin N - α : ℝ) : WithTop ℝ) := by
      refine le_antisymm ?_ (le_distTo_iff.2 fun γ hγ => ?_)
      · have := distTo_le (α := α) hαmem
        rwa [abs_of_neg (by linarith), neg_sub] at this
      · have := hαmin γ hγ
        rw [abs_of_neg (by linarith), neg_sub]
        linarith
    have hd : minDist α (gΓ μin k N) (δT μin) ≤ gαΓ μin N - α := by
      have := minDist_le_distTo (α := α) (Γ := gΓ μin k N) (δ := δT μin)
      rw [hdist] at this
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_left hd hκ.le
    rw [hr α hα, min_eq_left ((div_le_one hαΓ).2 h.le), hL]
    have e2 : gC μin k N * (α / gαΓ μin N) =
        gC μin k N - gC μin k N * (1 - α / gαΓ μin N) := by
      ring
    rw [e2, e]
    nlinarith
  -- (3d) "So the output is a comb with the stated contact set, line, dip, and width (`def:comb`),
  -- and `q = q_{k−1} ≥ q_0 = 7 > 0` by (P8)." (`q_ge_q₀`)
  have hq : 0 < gq μin k := by
    have := q_ge_q₀ (μin := μin) (k - 1)
    unfold q₀ at this
    unfold gq
    linarith
  refine ⟨⟨fun γ hγ => hαΓ.le.trans (hαmin γ hγ), hκ, hδ, hcontact, fun α hα => ?_⟩, hq⟩
  rcases le_or_gt (gαΓ μin N) α with h | h
  · exact h3b α h
  · exact h3c α hα h

/-- **`thm:gadget`** (Theorem C.6, `stoc-sections/appD-hardness.tex:191-197`, proof lines
1660-1780), its mathematical part: for `μ^in ∈ 𝔉` of length `k`, `N_min(μ^in) ≥ 1` is an integer,
and for every integer `N ≥ N_min(μ^in)` the instance `I(μ^in, N)` lies in `𝒞_cut` (a polymatroid
rank function given by a cut form, positive rewards and curvatures), has `3k + 1` elements, and with
`p` and `q > 0` it is a comb with contact set `Γ = {δ(N + χ^⊤μ^in) : χ ∈ {0, 1}^k}`, line `p + qα`,
dip `κ = min(1, 1/(30δ))`, and width `δ = 1/(3μ^in_1)`. The bit lengths `O(k + log μ^in_k + log N)`
of all numbers computed, their rationality and the computed cut form are `gadget_sizes` and
`gadgetForm` (`ContractDesignPolymatroids/Hardness/GadgetSizes.lean`); here the cut form exists. Not formalised: the
running time of the algorithm.

The proof has four parts, which open with sentences instead of labels; we number them (1)-(4):
(1) "We first define the output and the numbers that come with it" (`gΘ`, `gΛ`, `gNmin`, `gΛ'`,
`gfc`, `gq`, `gαΓ`, `gC`, `gadgetF`, `gadgetM`, `gadgetB`, `gp`); (2) "Next we show that `f_c` is a
polymatroid rank function and that `(f_c, m, β)` keeps the gap of level `k − 1`, shifted by `Λ'`,
to the right of `α_Γ`" (`gadget_embed`); (3) "Then we show that the output is a comb"
(`gadget_knob`); (4) "Finally, we show that the output lies in `𝒞_cut`, that its numbers have
polynomial size, and that it is computed in polynomial time", here: (4a) `f_c` is obtained from
`f_0` by one-element extensions, direct sums with modular singletons, and the addition of a modular
function, and adding `e_g` is a direct sum with a modular singleton, so by `prop:base` and
`lem:cutforms`(c) the output has a cut form; (4b) its rank function is a polymatroid rank
function, as `f_c` is one and `C_g > 0` (`gαΓ_gC_pos`); (4c) it has `3k + 1` elements and positive
`m` and `β`, so it lies in `𝒞_cut`; (4d) the sizes are `gadget_sizes`, the time is not
formalised. -/
theorem gadget (hF : InF μin k) :
    1 ≤ gNmin μin k ∧ ∀ N : ℕ, gNmin μin k ≤ N →
      Ccut (gadgetF μin k N) (gadgetM μin k) (gadgetB μin k N) ∧
      Fintype.card (Gr (k - 1) ⊕ Unit) = 3 * k + 1 ∧ 0 < gq μin k ∧
      IsComb (gadgetF μin k N) (gadgetM μin k) (gadgetB μin k N) (gΓ μin k N) (gp μin k N)
        (gq μin k) (κT μin) (δT μin) := by
  have hk : 1 ≤ k := hF.1
  refine ⟨le_max_left _ _, fun N hN => ?_⟩
  obtain ⟨hrank, -, -, -⟩ := gadget_embed hF hN
  obtain ⟨hcomb, hq⟩ := gadget_knob hF hN
  have hβ : ∀ e, 0 < βT μin (k - 1) e := (fpHyp_gT (μin := μin) (k - 1)).pos
  obtain ⟨hαΓ, hC⟩ := gαΓ_gC_pos hF hN
  -- (4) "Finally, we show that the output lies in `𝒞_cut`, that its numbers have polynomial size,
  -- and that it is computed in polynomial time."
  -- The Lean: here the output lies in `𝒞_cut`; the sizes are `gadget_sizes`, the running time is
  -- not formalised.
  -- (4a) "The function `f_c` is obtained from `f_0` by one-element extensions, direct sums with
  -- modular singletons, and the addition of a modular function, and adding `e_g` is a direct sum
  -- with a modular singleton. By `prop:base` and `lem:cutforms`(c), the output has a cut form,
  -- computed along the construction."
  -- The Lean: here the cut form exists; the form computed along the construction is `gadgetForm`
  -- (`gadgetForm_fn`).
  have hcut : HasCutForm (gadgetF μin k N) := by
    have h := (hasCutForm_gT (μin := μin) (k - 1)).add_modular fun e =>
      gΛ' μin N * (mT μin (k - 1) e / βT μin (k - 1) e) - gΘ μin k * (1 / βT μin (k - 1) e)
    have hf : gfc μin k N = fun S => gT μin (k - 1) S + ∑ e ∈ S,
        (gΛ' μin N * (mT μin (k - 1) e / βT μin (k - 1) e) -
          gΘ μin k * (1 / βT μin (k - 1) e)) := by
      funext S
      simp only [gfc, sum_sub_distrib, mul_sum]
      ring
    unfold gadgetF
    rw [hf]
    exact h.knob _
  -- (4b) "Its rank function is a polymatroid rank function, as `f_c` is one and `C_g > 0`,"
  -- (`C_g > 0`: `gαΓ_gC_pos`)
  -- (4c) "and with `3k + 1` elements and positive rational `m` and `β`, the output lies in
  -- `𝒞_cut`." (`β_{e_g} = α_Γ/C_g > 0`: `gαΓ_gC_pos`)
  refine ⟨⟨fun e => ?_, fun e => ?_, isRankFunction_dsum hrank (isRankFunction_single hC.le),
    hcut⟩, ?_, hq, hcomb⟩
  · rcases e with e | e
    · exact mT_pos (k - 1) e
    · show (0 : ℝ) < 1
      norm_num
  · rcases e with e | e
    · exact hβ e
    · exact div_pos hαΓ hC
  · rw [Fintype.card_sum, card_Gr, Fintype.card_unit]
    omega

end Proof

end

end Hardness

end Stoc
