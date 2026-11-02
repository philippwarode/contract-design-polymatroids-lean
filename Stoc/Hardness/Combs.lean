-- stamp r6 2026-11-02
import Stoc.Hardness.Operations

/-!
# Combs, and their sums and dilations

The STOC version's `def:comb` (Appendix C.1, `sec:D-ideas`, "Combs",
`stoc-sections/appD-hardness.tex:19-25`) and `lem:combsum` (Appendix C.2, `sec:D-cutforms`,
"Cut forms", `stoc-sections/appD-hardness.tex:155-177`: the statement at lines 155-160, one proof
of (a) and (b) at lines 162-177).

* `distTo`: `dist(α, Γ) = min_{γ ∈ Γ} |α − γ|` for a finite `Γ ⊆ ℝ`, with `dist(α, ∅) = ∞`, in
  `WithTop ℝ = ℝ ∪ {∞}`; `minDist α Γ δ` is the real number `min(dist(α, Γ), δ)`.
* `IsComb`: `def:comb`, for an instance `(f, m, β)` with the reward `r(x*(α))`
  (`Stoc.grossValue`).
* `combsum_a`, `combsum_b`: `lem:combsum`(a) and (b), in the order of the statement and of the
  proof, with the D3 lemma `distTo_div` (`dist(α/σ, Γ) = dist(α, σΓ)/σ`, which the paper uses
  without proof).
* `combsum`: the statement of `lem:combsum`, the conjunction of (a) and (b), proved by the two
  parts.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### The distance to a finite set -/

/-- `dist(α, Γ) = min_{γ ∈ Γ} |α − γ|` for a finite set `Γ ⊆ ℝ`, with `dist(α, ∅) = ∞`
(`def:comb`), as an element of `ℝ ∪ {∞} = WithTop ℝ`. -/
def distTo (α : ℝ) (Γ : Finset ℝ) : WithTop ℝ :=
  Γ.inf fun γ => ((|α - γ| : ℝ) : WithTop ℝ)

/-- The real number `min(dist(α, Γ), δ)` of `def:comb`; it is finite, as `δ` is. -/
def minDist (α : ℝ) (Γ : Finset ℝ) (δ : ℝ) : ℝ :=
  (min (distTo α Γ) (δ : WithTop ℝ)).untopD δ

section DistAPI

variable {α δ : ℝ} {Γ : Finset ℝ}

theorem distTo_empty : distTo α ∅ = ⊤ := inf_empty

theorem distTo_le {γ : ℝ} (hγ : γ ∈ Γ) : distTo α Γ ≤ (|α - γ| : ℝ) :=
  inf_le (f := fun γ => ((|α - γ| : ℝ) : WithTop ℝ)) hγ

theorem le_distTo_iff {c : ℝ} : (c : WithTop ℝ) ≤ distTo α Γ ↔ ∀ γ ∈ Γ, c ≤ |α - γ| := by
  unfold distTo
  rw [Finset.le_inf_iff]
  simp only [WithTop.coe_le_coe]

/-- A nearest point: for a nonempty `Γ`, `dist(α, Γ) = |α − γ|` for some `γ ∈ Γ`. -/
theorem exists_distTo_eq (hΓ : Γ.Nonempty) : ∃ γ ∈ Γ, distTo α Γ = (|α - γ| : ℝ) :=
  exists_mem_eq_inf Γ hΓ _

theorem minDist_coe : (minDist α Γ δ : WithTop ℝ) = min (distTo α Γ) δ := by
  unfold minDist
  rcases WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right (distTo α Γ) (δ : WithTop ℝ)))
    with ⟨x, hx⟩
  rw [← hx, WithTop.untopD_coe]

theorem minDist_le_right : minDist α Γ δ ≤ δ := by
  have h := minDist_coe (α := α) (Γ := Γ) (δ := δ)
  have : (minDist α Γ δ : WithTop ℝ) ≤ δ := h ▸ min_le_right _ _
  exact_mod_cast this


theorem minDist_le_distTo : (minDist α Γ δ : WithTop ℝ) ≤ distTo α Γ :=
  minDist_coe (α := α) (Γ := Γ) (δ := δ) ▸ min_le_left _ _

theorem minDist_of_eq {γ : ℝ} (h : distTo α Γ = (|α - γ| : ℝ)) :
    minDist α Γ δ = min |α - γ| δ := by
  have h' := minDist_coe (α := α) (Γ := Γ) (δ := δ)
  rw [h, ← WithTop.coe_min] at h'
  exact_mod_cast h'

theorem minDist_of_le {c : ℝ} (hc : c ≤ δ) (h : (c : WithTop ℝ) ≤ distTo α Γ) :
    c ≤ minDist α Γ δ := by
  have h' := minDist_coe (α := α) (Γ := Γ) (δ := δ)
  have : (c : WithTop ℝ) ≤ minDist α Γ δ := h' ▸ le_min h (WithTop.coe_le_coe.2 hc)
  exact_mod_cast this

theorem minDist_nonneg (hδ : 0 ≤ δ) : 0 ≤ minDist α Γ δ :=
  minDist_of_le hδ (le_distTo_iff.2 fun _ _ => abs_nonneg _)

/-- The step `dist(α/σ, Γ) = dist(α, σΓ)/σ` of the proof of `lem:combsum`(a), in `ℝ ∪ {∞}` (not in
the paper: the proof of `lem:combsum`(a) uses this without proof). -/
theorem distTo_div {σ : ℝ} (hσ : 0 < σ) :
    distTo (α / σ) Γ = (distTo α (Γ.image (σ * ·))).map (· / σ) := by
  have hmono : Monotone fun x : ℝ => x / σ := fun _ _ h => div_le_div_of_nonneg_right h hσ.le
  have hmap : ∀ x y : WithTop ℝ, WithTop.map (· / σ) (x ⊓ y) =
      WithTop.map (· / σ) x ⊓ WithTop.map (· / σ) y := by
    intro x y
    induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe
    · rfl
    · simp
    · simp
    · simp only [WithTop.map_coe]
      rw [← WithTop.coe_inf, ← WithTop.coe_inf, WithTop.map_coe]
      exact congrArg _ (hmono.map_min)
  unfold distTo
  rw [inf_image, Finset.apply_inf_eq_inf_comp (WithTop.map (· / σ)) hmap rfl]
  refine Finset.inf_congr rfl fun γ _ => ?_
  simp only [Function.comp_apply, WithTop.map_coe]
  congr 1
  rw [← abs_of_pos hσ, ← abs_div, abs_of_pos hσ]
  congr 1
  field_simp

/-- With the cap: `min(dist(α/σ, Γ), δ) = min(dist(α, σΓ), σδ)/σ`, from `distTo_div`; the
equality `(κ/σ) min(dist(α, σΓ)/σ, δ) = (κ/σ²) min(dist(α, σΓ), σδ)` of the display in the proof
of `lem:combsum`(a). -/
theorem minDist_div {σ : ℝ} (hσ : 0 < σ) :
    minDist (α / σ) Γ δ = minDist α (Γ.image (σ * ·)) (σ * δ) / σ := by
  have h1 := minDist_coe (α := α / σ) (Γ := Γ) (δ := δ)
  have h2 := minDist_coe (α := α) (Γ := Γ.image (σ * ·)) (δ := σ * δ)
  rw [distTo_div hσ] at h1
  induction hD : distTo α (Γ.image (σ * ·)) using WithTop.recTopCoe with
  | top =>
    rw [hD, WithTop.map_top, min_eq_right le_top] at h1
    rw [hD, min_eq_right le_top] at h2
    have e1 : minDist (α / σ) Γ δ = δ := by exact_mod_cast h1
    have e2 : minDist α (Γ.image (σ * ·)) (σ * δ) = σ * δ := by exact_mod_cast h2
    rw [e1, e2]
    field_simp
  | coe d =>
    rw [hD, WithTop.map_coe, ← WithTop.coe_min] at h1
    rw [hD, ← WithTop.coe_min] at h2
    have e1 : minDist (α / σ) Γ δ = min (d / σ) δ := by exact_mod_cast h1
    have e2 : minDist α (Γ.image (σ * ·)) (σ * δ) = min d (σ * δ) := by exact_mod_cast h2
    rw [e1, e2]
    have hmono : Monotone fun x : ℝ => x / σ := fun _ _ h => div_le_div_of_nonneg_right h hσ.le
    rw [hmono.map_min]
    congr 1
    field_simp

end DistAPI

/-! ### `def:comb` -/

section Comb

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **`def:comb`** (Definition C.1, `stoc-sections/appD-hardness.tex:19-25`): for a finite
`Γ ⊆ [0, ∞)`, an affine `L(α) = p + qα` and `κ, δ > 0`, the instance `(f, m, β)` is a comb with
contact set `Γ`, line `L`, dip `κ` and width `δ` if `r(x*(γ)) = L(γ)` for `γ ∈ Γ` and
`L(α) − r(x*(α)) ≥ κ min(dist(α, Γ), δ)` for all `α ≥ 0`, where `dist(α, ∅) = ∞` (`distTo`,
`minDist`). The reward under the best response is `r(x*(α)) = grossValue f m β α`. -/
structure IsComb (f : Finset E → ℝ) (m β : E → ℝ) (Γ : Finset ℝ) (p q κ δ : ℝ) : Prop where
  /-- `Γ ⊆ [0, ∞)` -/
  nonneg : ∀ γ ∈ Γ, 0 ≤ γ
  κ_pos : 0 < κ
  δ_pos : 0 < δ
  /-- `r(x*(γ)) = L(γ)` for `γ ∈ Γ` -/
  contact : ∀ γ ∈ Γ, grossValue f m β γ = p + q * γ
  /-- `L(α) − r(x*(α)) ≥ κ min(dist(α, Γ), δ)` for all `α ≥ 0` -/
  gap : ∀ α, 0 ≤ α → κ * minDist α Γ δ ≤ p + q * α - grossValue f m β α

omit [DecidableEq E] in
/-- **`lem:combsum`(a)** (Lemma C.4, `stoc-sections/appD-hardness.tex:157`, proof lines 163-174):
replacing `m` by `m/σ`, `σ > 0`, in a comb with contact set `Γ`, line `p + qα`, dip `κ` and width
`δ` gives a comb with contact set `σΓ`, line `p/σ + qα/σ²`, dip `κ/σ²` and width `σδ`.

The proof's steps: (1) by `lem:ops`(b), the reward of the new instance at `α` is
`r(x*(α/σ))/σ`; (2) the new line is `L'(α) = L(α/σ)/σ = p/σ + qα/σ²`; (3) as
`dist(α/σ, Γ) = dist(α, σΓ)/σ` (`distTo_div`, inside `minDist_div`), the comb inequality at `α/σ`
gives `L'(α) − r(x*(α/σ))/σ = (L(α/σ) − r(x*(α/σ)))/σ ≥ (κ/σ) min(dist(α, σΓ)/σ, δ)
= (κ/σ²) min(dist(α, σΓ), σδ)` (`minDist_div`); (4) at a contact `σγ` the left-hand side is
`(L(γ) − r(x*(γ)))/σ = 0`; (5) so the new instance is a comb with contact set `σΓ`, line `L'`,
dip `κ/σ²` and width `σδ`. -/
theorem combsum_a {f : Finset E → ℝ} {m β : E → ℝ} {Γ : Finset ℝ} {p q κ δ : ℝ}
    (h : IsComb f m β Γ p q κ δ) {σ : ℝ} (hσ : 0 < σ) :
    IsComb f (fun e => m e / σ) β (Γ.image (σ * ·)) (p / σ) (q / σ ^ 2) (κ / σ ^ 2)
      (σ * δ) := by
  -- (1) "Let `L(α) := p + qα` be the line of the comb. By `lem:ops`(b), at the share `α` the
  -- reward of the instance with `m/σ` in place of `m` under its best response is `r(x*(α/σ))/σ`."
  have hr := (ops_b_aux f m β hσ).2
  -- (2) "The new line is `L'(α) := L(α/σ)/σ = p/σ + qα/σ²`."
  have hL : ∀ α, p / σ + q / σ ^ 2 * α = (p + q * (α / σ)) / σ := fun α => by
    field_simp
  -- (3) "Since `dist(α/σ, Γ) = dist(α, σΓ)/σ`, the inequality of `def:comb` at the share `α/σ`
  -- gives, for every `α ≥ 0`, `L'(α) − r(x*(α/σ))/σ = (L(α/σ) − r(x*(α/σ)))/σ ≥
  -- (κ/σ) min(dist(α, σΓ)/σ, δ) = (κ/σ²) min(dist(α, σΓ), σδ)`."
  have hgap : ∀ α, 0 ≤ α → κ / σ ^ 2 * minDist α (Γ.image (σ * ·)) (σ * δ) ≤
      p / σ + q / σ ^ 2 * α - grossValue f (fun e => m e / σ) β α := by
    intro α hα
    have hd := minDist_div (α := α) (Γ := Γ) (δ := δ) hσ
    have hgap := h.gap (α / σ) (div_nonneg hα hσ.le)
    rw [hr α hα, hL]
    have e1 : (p + q * (α / σ)) / σ - grossValue f m β (α / σ) / σ =
        (p + q * (α / σ) - grossValue f m β (α / σ)) / σ := by ring
    have e2 : κ / σ ^ 2 * minDist α (Γ.image (σ * ·)) (σ * δ) =
        κ * minDist (α / σ) Γ δ / σ := by
      rw [hd]
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hgap hσ.le
  -- (4) "At a contact `σγ` with `γ ∈ Γ`, the left-hand side is `(L(γ) − r(x*(γ)))/σ = 0`."
  have hcont : ∀ γ ∈ Γ.image (σ * ·),
      grossValue f (fun e => m e / σ) β γ = p / σ + q / σ ^ 2 * γ := by
    intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := mem_image.1 hγ
    rw [hr _ (mul_nonneg hσ.le (h.nonneg γ₀ hγ₀)), hL, mul_div_cancel_left₀ _ hσ.ne',
      h.contact γ₀ hγ₀]
  -- (5) "So the new instance is a comb with contact set `σΓ`, line `L'`, dip `κ/σ²` and width
  -- `σδ`."
  refine ⟨fun γ hγ => ?_, div_pos h.κ_pos (by positivity), mul_pos hσ h.δ_pos, hcont, hgap⟩
  obtain ⟨γ₀, hγ₀, rfl⟩ := mem_image.1 hγ
  exact mul_nonneg hσ.le (h.nonneg γ₀ hγ₀)

/-- **`lem:combsum`(b)** (`stoc-sections/appD-hardness.tex:158`, proof line 176): if `I_1`
and `I_2` are combs on disjoint ground sets with the same width `δ`, contact sets
`Γ_1, Γ_2 ⊆ δℤ`, lines `L_1, L_2` and dips `κ_1, κ_2`, then `I_1 ⊕ I_2` is a comb with contact set
`Γ_1 ∩ Γ_2`, line `L_1 + L_2`, dip `min(κ_1, κ_2)` and width `δ/2`.

The proof's steps: (1) by `lem:ops`(a), the reward of `I_1 ⊕ I_2` is the sum of the rewards, so
the gaps add; (2) for `α ≥ 0`, `d_i = dist(α, Γ_i)` and `κ = min(κ_1, κ_2)`, the gap of the sum is
at least `κ_1 min(d_1, δ) + κ_2 min(d_2, δ)`; (3) if `d_1 ≥ δ/2` or `d_2 ≥ δ/2`, this is at
least `κδ/2`; (4) otherwise the nearest points `γ_i ∈ Γ_i` satisfy `|γ_1 − γ_2| < δ` and lie in
`δℤ`, so `γ_1 = γ_2 ∈ Γ_1 ∩ Γ_2` and `d_1 = d_2 = |α − γ_1| ≥ dist(α, Γ_1 ∩ Γ_2)`, and the gap is
at least `(κ_1 + κ_2)|α − γ_1| ≥ κ min(dist(α, Γ_1 ∩ Γ_2), δ/2)`; (5) on `Γ_1 ∩ Γ_2` both gaps
vanish. -/
theorem combsum_b {E₂ : Type*} [Fintype E₂] [DecidableEq E₂] {f₁ : Finset E → ℝ}
    {m₁ β₁ : E → ℝ} {f₂ : Finset E₂ → ℝ} {m₂ β₂ : E₂ → ℝ} (hf₁ : IsRankFunction f₁)
    (hf₂ : IsRankFunction f₂) (hβ₁ : ∀ e, 0 < β₁ e) (hβ₂ : ∀ e, 0 < β₂ e)
    {Γ₁ Γ₂ : Finset ℝ} {p₁ q₁ κ₁ p₂ q₂ κ₂ δ : ℝ} (h₁ : IsComb f₁ m₁ β₁ Γ₁ p₁ q₁ κ₁ δ)
    (h₂ : IsComb f₂ m₂ β₂ Γ₂ p₂ q₂ κ₂ δ) (hΓ₁ : ∀ γ ∈ Γ₁, ∃ n : ℤ, γ = δ * n)
    (hΓ₂ : ∀ γ ∈ Γ₂, ∃ n : ℤ, γ = δ * n) :
    IsComb (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) (Γ₁ ∩ Γ₂) (p₁ + p₂) (q₁ + q₂)
      (min κ₁ κ₂) (δ / 2) := by
  have hδ := h₁.δ_pos
  -- (1) "By `lem:ops`(a), the reward of `I_1 ⊕ I_2` is `r_1(x*_1(α)) + r_2(x*_2(α))`, so the gaps
  -- add."
  have hr := (ops_a_aux (m₁ := m₁) (m₂ := m₂) hf₁ hf₂ hβ₁ hβ₂).2
  have hgap : ∀ α, 0 ≤ α → min κ₁ κ₂ * minDist α (Γ₁ ∩ Γ₂) (δ / 2) ≤
      p₁ + p₂ + (q₁ + q₂) * α - grossValue (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α := by
    intro α hα
    rw [hr α hα]
    -- (2) "Fix `α ≥ 0`, let `d_i := dist(α, Γ_i)` and `κ := min(κ_1, κ_2)`. The gap of the sum
    -- is at least `κ_1 min(d_1, δ) + κ_2 min(d_2, δ)`."
    set d₁ := distTo α Γ₁ with hd₁
    set d₂ := distTo α Γ₂ with hd₂
    set κ := min κ₁ κ₂ with hκ
    have g1 := h₁.gap α hα
    have g2 := h₂.gap α hα
    have hκ1 : κ ≤ κ₁ := min_le_left _ _
    have hκ2 : κ ≤ κ₂ := min_le_right _ _
    have hκ0 : 0 < κ := lt_min h₁.κ_pos h₂.κ_pos
    have m1 := minDist_nonneg (α := α) (Γ := Γ₁) hδ.le
    have m2 := minDist_nonneg (α := α) (Γ := Γ₂) hδ.le
    have hsum : κ₁ * minDist α Γ₁ δ + κ₂ * minDist α Γ₂ δ ≤
        p₁ + p₂ + (q₁ + q₂) * α - (grossValue f₁ m₁ β₁ α + grossValue f₂ m₂ β₂ α) := by
      linarith
    have hcap : minDist α (Γ₁ ∩ Γ₂) (δ / 2) ≤ δ / 2 := minDist_le_right
    -- (3) "If `d_1 ≥ δ/2` or `d_2 ≥ δ/2`, this is at least `κδ/2`."
    by_cases hd1 : ((δ / 2 : ℝ) : WithTop ℝ) ≤ d₁
    · have h1 := minDist_of_le (δ := δ) (by linarith) hd1
      have h3 : κ * (δ / 2) ≤ κ₁ * minDist α Γ₁ δ + κ₂ * minDist α Γ₂ δ := by
        have := mul_le_mul hκ1 h1 (by positivity) h₁.κ_pos.le
        nlinarith [mul_nonneg h₂.κ_pos.le m2]
      have := mul_le_mul_of_nonneg_left hcap hκ0.le
      linarith
    by_cases hd2 : ((δ / 2 : ℝ) : WithTop ℝ) ≤ d₂
    · have h2 := minDist_of_le (δ := δ) (by linarith) hd2
      have h3 : κ * (δ / 2) ≤ κ₁ * minDist α Γ₁ δ + κ₂ * minDist α Γ₂ δ := by
        have := mul_le_mul hκ2 h2 (by positivity) h₂.κ_pos.le
        nlinarith [mul_nonneg h₁.κ_pos.le m1]
      have := mul_le_mul_of_nonneg_left hcap hκ0.le
      linarith
    -- (4) "Otherwise the points `γ_i ∈ Γ_i` nearest to `α` satisfy `|γ_1 − γ_2| < δ`, and as
    -- both lie in `δℤ`, `γ_1 = γ_2 ∈ Γ_1 ∩ Γ_2` and `d_1 = d_2 = |α − γ_1| ≥ dist(α, Γ_1 ∩ Γ_2)`.
    -- Then the gap is at least `(κ_1 + κ_2)|α − γ_1| ≥ κ min(dist(α, Γ_1 ∩ Γ_2), δ/2)`."
    push Not at hd1 hd2
    have hne1 : Γ₁.Nonempty := by
      rcases Γ₁.eq_empty_or_nonempty with h | h
      · rw [hd₁, h, distTo_empty] at hd1
        exact absurd hd1 (not_lt.2 le_top)
      · exact h
    have hne2 : Γ₂.Nonempty := by
      rcases Γ₂.eq_empty_or_nonempty with h | h
      · rw [hd₂, h, distTo_empty] at hd2
        exact absurd hd2 (not_lt.2 le_top)
      · exact h
    obtain ⟨γ₁, hγ₁, e₁⟩ := exists_distTo_eq (α := α) hne1
    obtain ⟨γ₂, hγ₂, e₂⟩ := exists_distTo_eq (α := α) hne2
    rw [← hd₁] at e₁
    rw [← hd₂] at e₂
    rw [e₁, WithTop.coe_lt_coe] at hd1
    rw [e₂, WithTop.coe_lt_coe] at hd2
    have hlt : |γ₁ - γ₂| < δ := by
      have := abs_sub_le γ₁ α γ₂
      rw [abs_sub_comm γ₁ α] at this
      linarith
    obtain ⟨n₁, rfl⟩ := hΓ₁ γ₁ hγ₁
    obtain ⟨n₂, rfl⟩ := hΓ₂ γ₂ hγ₂
    have hn : n₁ = n₂ := by
      rw [← mul_sub, abs_mul, abs_of_pos hδ] at hlt
      have h1 : |(n₁ : ℝ) - n₂| < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      have h2 : |n₁ - n₂| < 1 := by exact_mod_cast h1
      have := abs_lt.1 h2
      omega
    subst hn
    have hmem : δ * n₁ ∈ Γ₁ ∩ Γ₂ := mem_inter.2 ⟨hγ₁, hγ₂⟩
    have hd12 : d₁ = d₂ := e₁.trans e₂.symm
    have hdist : distTo α (Γ₁ ∩ Γ₂) ≤ d₁ := e₁ ▸ distTo_le hmem
    have hm1 : minDist α Γ₁ δ = |α - δ * n₁| := by
      rw [minDist_of_eq (hd₁ ▸ e₁), min_eq_left (by linarith)]
    have hm2 : minDist α Γ₂ δ = |α - δ * n₁| := by
      rw [minDist_of_eq (hd₂ ▸ e₂), min_eq_left (by linarith)]
    rw [hm1, hm2] at hsum
    -- the gap is at least `(κ_1 + κ_2)|α − γ_1|`
    have hgap1 : (κ₁ + κ₂) * |α - δ * n₁| ≤
        p₁ + p₂ + (q₁ + q₂) * α - (grossValue f₁ m₁ β₁ α + grossValue f₂ m₂ β₂ α) := by
      linarith
    -- `(κ_1 + κ_2)|α − γ_1| ≥ κ min(dist(α, Γ_1 ∩ Γ_2), δ/2)`
    have hle : minDist α (Γ₁ ∩ Γ₂) (δ / 2) ≤ |α - δ * n₁| := by
      have h := (minDist_le_distTo (α := α) (Γ := Γ₁ ∩ Γ₂) (δ := δ / 2)).trans (hdist.trans_eq e₁)
      exact_mod_cast h
    have hgap2 : κ * minDist α (Γ₁ ∩ Γ₂) (δ / 2) ≤ (κ₁ + κ₂) * |α - δ * n₁| := by
      have h1 := mul_le_mul_of_nonneg_left hle hκ0.le
      have h2 : κ * |α - δ * n₁| ≤ (κ₁ + κ₂) * |α - δ * n₁| :=
        mul_le_mul_of_nonneg_right (by linarith [h₂.κ_pos]) (abs_nonneg _)
      linarith
    linarith
  -- (5) "On `Γ_1 ∩ Γ_2` both gaps vanish."
  have hcont : ∀ γ ∈ Γ₁ ∩ Γ₂, grossValue (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) γ =
      p₁ + p₂ + (q₁ + q₂) * γ := by
    intro γ hγ
    obtain ⟨hγ1, hγ2⟩ := mem_inter.1 hγ
    rw [hr γ (h₁.nonneg γ hγ1), h₁.contact γ hγ1, h₂.contact γ hγ2]
    ring
  exact ⟨fun γ hγ => h₁.nonneg γ (mem_inter.1 hγ).1, lt_min h₁.κ_pos h₂.κ_pos, by positivity,
    hcont, hgap⟩

/-- **`lem:combsum`** (Lemma C.4, `stoc-sections/appD-hardness.tex:155-160`): (a) replacing `m` by
`m/σ`, `σ > 0`, in a comb with contact set `Γ`, line `p + qα`, dip `κ` and width `δ` gives a comb
with contact set `σΓ`, line `p/σ + qα/σ²`, dip `κ/σ²` and width `σδ`. (b) If `I_1` and `I_2` are
combs on disjoint ground sets with the same width `δ`, contact sets `Γ_1, Γ_2 ⊆ δℤ`, lines
`L_1, L_2` and dips `κ_1, κ_2`, then `I_1 ⊕ I_2` is a comb with contact set `Γ_1 ∩ Γ_2`, line
`L_1 + L_2`, dip `min(κ_1, κ_2)` and width `δ/2`.

Each part has its own ground sets; in (b) the combs `I_1`, `I_2` are instances (rank functions,
`β > 0`). Its parts are `combsum_a` and `combsum_b`; their docstrings give the paper's steps. -/
theorem combsum :
    -- (a)
    (∀ {E : Type*} [Fintype E] {f : Finset E → ℝ} {m β : E → ℝ} {Γ : Finset ℝ} {p q κ δ : ℝ},
      IsComb f m β Γ p q κ δ → ∀ {σ : ℝ}, 0 < σ →
      IsComb f (fun e => m e / σ) β (Γ.image (σ * ·)) (p / σ) (q / σ ^ 2) (κ / σ ^ 2)
        (σ * δ)) ∧
    -- (b)
    ∀ {E : Type*} [Fintype E] [DecidableEq E] {E₂ : Type*} [Fintype E₂] [DecidableEq E₂]
      {f₁ : Finset E → ℝ} {m₁ β₁ : E → ℝ} {f₂ : Finset E₂ → ℝ} {m₂ β₂ : E₂ → ℝ},
      IsRankFunction f₁ → IsRankFunction f₂ → (∀ e, 0 < β₁ e) → (∀ e, 0 < β₂ e) →
      ∀ {Γ₁ Γ₂ : Finset ℝ} {p₁ q₁ κ₁ p₂ q₂ κ₂ δ : ℝ}, IsComb f₁ m₁ β₁ Γ₁ p₁ q₁ κ₁ δ →
      IsComb f₂ m₂ β₂ Γ₂ p₂ q₂ κ₂ δ → (∀ γ ∈ Γ₁, ∃ n : ℤ, γ = δ * n) →
      (∀ γ ∈ Γ₂, ∃ n : ℤ, γ = δ * n) →
      IsComb (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) (Γ₁ ∩ Γ₂) (p₁ + p₂) (q₁ + q₂)
        (min κ₁ κ₂) (δ / 2) :=
  ⟨combsum_a, combsum_b⟩

end Comb

end

end Hardness

end Stoc
