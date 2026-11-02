-- stamp r6 2026-11-02
import ContractDesignPolymatroids.Hardness.FullPlane

/-!
# Translation extensions

The STOC version's Appendix B.6.2 (`sec:B-translation`, "Translation extensions",
`stoc-sections/appB-tools.tex:224-302`): `lem:translation`, with the one-element extension that it
shares with Appendix B.6.3 (`sec:B-extensions`).

The new element `b` is `none : Option E` (`E ∪ {b}`), and `t` and `β⁻¹` are extended by `t_b` and
`1/β_b` through vectors `m', β' : Option E → ℝ` with `m = m' ∘ some`, `β = β' ∘ some`,
`m_b = m' none`, `β_b = β' none`.

The paper's objects:
* `subMod f d`: `f − d` for a modular function `d` (the function `h = f − d` of
  `sec:B-extensions`);
* `extend f d K`: the extension `g'(S) = g(S)`, `g'(S ∪ {b}) = g(S) + K − d(S)` for `S ⊆ E`, for an
  arbitrary `d`; the translation extension of `lem:translation` is the case
  `d = μ_θ β⁻¹ − μ_α t`, that is, `d_e = (μ_θ − μ_α m_e)/β_e`;
* `shiftFun g m β μ_θ μ_α`: `g − d` for the translation `d = μ_θ β⁻¹ − μ_α t` (part (c)).

The parts of the exact statement: `translation_b` and `translation_c`. The exact statement of (a),
with its sentence on cut forms (`lem:cutforms`(c)(iii), over the reals), is
`Stoc.Hardness.translation_a_cutForm` in `ContractDesignPolymatroids/Hardness/CutForms.lean`, which comes later in the
import chain; here `translation_a` is its first sentence. The exact statement of `lem:translation`,
the conjunction of (a)–(c), is `Stoc.Hardness.translation` in `ContractDesignPolymatroids/Hardness/CutForms.lean`, after
its part (a). The auxiliary forms: `extend_diminishingReturns` (the proof of (a), for every `d ≥ 0`)
and `FPHyp.extend` (part (a) for every `d ≥ 0`, which the setting of `sec:B-extensions` uses),
`levelFun_extend_some` and `levelFun_extend_insertNone` (part (b)), `levelFun_shift`, `FPHyp.shift`,
`xi_shift`, `rho_shift` and `levelSet_xi_shift` (part (c)).
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The extension -/

/-- `f − d` for a modular `d`: `(f − d)(T) = f(T) − d(T)`. -/
def subMod (f : Finset E → ℝ) (d : E → ℝ) (T : Finset E) : ℝ :=
  f T - ∑ e ∈ T, d e

/-- The one-element extension of `f` by the new element `b = none`: `f'(S) = f(S)` and
`f'(S ∪ {b}) = K + (f − d)(S) = f(S) + K − d(S)` for `S ⊆ E`. -/
def extend (f : Finset E → ℝ) (d : E → ℝ) (K : ℝ) (T : Finset (Option E)) : ℝ :=
  if none ∈ T then K + subMod f d (eraseNone T) else f (eraseNone T)

variable {f g : Finset E → ℝ} {d : E → ℝ} {K : ℝ} {m β : E → ℝ} {m' β' : Option E → ℝ}

omit [Fintype E] [DecidableEq E] in
/-- `(E ∪ {b}) ∖ {b} = E` on `Option E`. -/
@[simp] lemma eraseNone_univ' [Fintype E] : eraseNone (univ : Finset (Option E)) = univ := by
  ext e
  simp [mem_eraseNone]

omit [Fintype E] in
/-- `f − d` is submodular with `(f − d)(∅) = 0` for a modular `d` (not in the paper: the paper uses
this without proof for the function `h = f − d` of `sec:B-extensions`, `appB-tools.tex:314`, to
which it applies `lem:fullplane`; the reason is the one of `lem:translation`(c),
`appB-tools.tex:292`, "as `d` is modular"). -/
theorem FPHyp.subMod (H : FPHyp f β) (d : E → ℝ) : FPHyp (subMod f d) β where
  submod S T := by
    have h := H.submod S T
    have h1 := sum_union_inter (s₁ := S) (s₂ := T) (f := d)
    unfold Hardness.subMod
    linarith
  empty := by simp [Hardness.subMod, H.empty]
  pos := H.pos

/-! ### `lem:translation`(a): submodularity -/

omit [Fintype E] in
/-- `lem:translation`(a), auxiliary form for every `d ≥ 0` (`appB-tools.tex:262-274`; the paper
notes that the argument uses only that `g` is submodular and `d ≥ 0`, not the form of `d`): the
marginal values of `g'` do not increase as the set grows. Steps: (1) for `X ⊆ E` and
`e ∈ E ∖ X`, `g'(X ∪ {e}) − g'(X) = g(X ∪ {e}) − g(X)`,
`g'(X ∪ {b, e}) − g'(X ∪ {b}) = g(X ∪ {e}) − g(X) − d_e` and `g'(X ∪ {b}) − g'(X) = K − d(X)`;
(2) for `X ⊆ Y ⊆ E ∪ {b}` and `e ∉ Y`: if `e = b`, the marginal values of `b` at `X` and `Y` are
`K − d(X) ≥ K − d(Y)`, as `d ≥ 0`; (3) if `e ∈ E`, with `X' = X ∖ {b}` and `Y' = Y ∖ {b}`, the
marginal value of `e` at `X` is `g(X' ∪ {e}) − g(X')`, minus `d_e` if `b ∈ X`, and at `Y` it is
`g(Y' ∪ {e}) − g(Y')`, minus `d_e` if `b ∈ Y`; as `g` is submodular, `X' ⊆ Y'`, `d_e ≥ 0` and
`b ∈ X` implies `b ∈ Y`, the first is at least the second. -/
theorem extend_diminishingReturns (hg : Submodular g) (hd : ∀ e, 0 ≤ d e) (K : ℝ) :
    DiminishingReturns (extend g d K) := by
  -- (1) "We show that the marginal values of `g'` do not increase as the set grows. By the
  -- definition of `g'`, every `X ⊆ E` and `e ∈ E ∖ X` satisfy
  -- `g'(X ∪ {e}) − g'(X) = g(X ∪ {e}) − g(X)`,
  -- `g'(X ∪ {b, e}) − g'(X ∪ {b}) = g(X ∪ {e}) − g(X) − d_e`,
  -- `g'(X ∪ {b}) − g'(X) = K − d(X)`."
  -- In the Lean, `X` is a set of `Option E`, and the paper's `X` is `eraseNone X`; `b = none` is
  -- not in `X` in `m1` and `m3`, and it is in `X` in `m2`.
  have hins : ∀ (X : Finset (Option E)) (a : E),
      eraseNone (insert (some a) X) = insert a (eraseNone X) := by
    intro X a
    ext x
    simp [mem_eraseNone]
  have hinsb : ∀ X : Finset (Option E), eraseNone (insert none X) = eraseNone X := by
    intro X
    ext x
    simp [mem_eraseNone]
  have m1 : ∀ (X : Finset (Option E)) (a : E), none ∉ X →
      extend g d K (insert (some a) X) - extend g d K X =
        g (insert a (eraseNone X)) - g (eraseNone X) := by
    intro X a hX
    have h1 : none ∉ insert (some a) X := by simp [hX]
    rw [extend, extend, ite_eq_right h1, ite_eq_right hX, hins]
  have m2 : ∀ (X : Finset (Option E)) (a : E), none ∈ X → a ∉ eraseNone X →
      extend g d K (insert (some a) X) - extend g d K X =
        g (insert a (eraseNone X)) - g (eraseNone X) - d a := by
    intro X a hX ha
    have h1 : none ∈ insert (some a) X := mem_insert_of_mem hX
    rw [extend, extend, ite_eq_left h1, ite_eq_left hX, hins, subMod, subMod, sum_insert ha]
    ring
  have m3 : ∀ X : Finset (Option E), none ∉ X →
      extend g d K (insert none X) - extend g d K X = K - ∑ e ∈ eraseNone X, d e := by
    intro X hX
    rw [extend, extend, ite_eq_left (mem_insert_self none X), ite_eq_right hX, hinsb, subMod]
    ring
  -- (2) "Let `X ⊆ Y ⊆ E ∪ {b}` and `e ∈ (E ∪ {b}) ∖ Y`."
  intro X Y e hXY heY
  rcases e with _ | a
  · -- "If `e = b`, the marginal values of `b` at `X` and at `Y` are `K − d(X) ≥ K − d(Y)`, as
    -- `d ≥ 0`."
    have hY : none ∉ Y := heY
    have hX : none ∉ X := fun h => hY (hXY h)
    rw [m3 X hX, m3 Y hY]
    have : ∑ e ∈ eraseNone X, d e ≤ ∑ e ∈ eraseNone Y, d e :=
      sum_le_sum_of_subset_of_nonneg (eraseNone.monotone hXY) fun e _ _ => hd e
    linarith
  · -- (3) "If `e ∈ E`, let `X' := X ∖ {b}` and `Y' := Y ∖ {b}`. The marginal value of `e` at `X`
    -- is `g(X' ∪ {e}) − g(X')`, minus `d_e` if `b ∈ X`, and its marginal value at `Y` is
    -- `g(Y' ∪ {e}) − g(Y')`, minus `d_e` if `b ∈ Y`. As `g` is submodular, `X' ⊆ Y'`, `d_e ≥ 0`,
    -- and `b ∈ X` implies `b ∈ Y`, the marginal value at `X` is at least the marginal value at
    -- `Y`."
    -- The Lean splits by whether `b` lies in `Y` and in `X`.
    have haY : a ∉ eraseNone Y := fun h => heY (mem_eraseNone.1 h)
    have haX : a ∉ eraseNone X := fun h => haY (eraseNone.monotone hXY h)
    have hsub : g (insert a (eraseNone Y)) - g (eraseNone Y) ≤
        g (insert a (eraseNone X)) - g (eraseNone X) :=
      hg.diminishingReturns (eraseNone.monotone hXY) haY
    by_cases hbY : none ∈ Y
    · rw [m2 Y a hbY haY]
      by_cases hbX : none ∈ X
      · rw [m2 X a hbX haX]
        linarith
      · rw [m1 X a hbX]
        linarith [hd a]
    · have hbX : none ∉ X := fun h => hbY (hXY h)
      rw [m1 Y a hbY, m1 X a hbX]
      exact hsub

omit [Fintype E] in
/-- `lem:translation`(a), auxiliary form (and the setting of `sec:B-extensions`,
`appB-tools.tex:322`): for `d ≥ 0`, the extension `g'` is submodular with `g'(∅) = 0`, by
`extend_diminishingReturns` and `g'(∅) = g(∅) = 0`; with `β' > 0`. -/
theorem FPHyp.extend (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) (K : ℝ) : FPHyp (extend f d K) β' where
  submod := (extend_diminishingReturns H.submod hd K).submodular
  empty := by simp [Hardness.extend, H.empty]
  pos o := by
    cases o with
    | none => exact hb
    | some e => exact H.pos e

omit [Fintype E] in
/-- `lem:translation`(a), its first sentence (`appB-tools.tex:240`, proof `appB-tools.tex:262-275`):
for `g` submodular with `g(∅) = 0`, `m, β > 0`, `(μ_α, μ_θ)` with `d_e = (μ_θ − μ_α m_e)/β_e ≥ 0`
for all `e ∈ E`, `K ∈ ℝ` and a new element `b` with `m_b, β_b > 0`, the function `g'` is submodular
with `g'(∅) = 0`. The exact statement of (a), with its sentence on cut forms
(`lem:cutforms`(c)(iii)), is `Stoc.Hardness.translation_a_cutForm` in `ContractDesignPolymatroids/Hardness/CutForms.lean`,
later in the import chain, which derives it from this lemma and `HasCutForm.extend`. Steps: (1)–(3)
of `extend_diminishingReturns`: the marginal values of `g'` do not increase as the set grows (the
three formulas, then the cases `e = b` and `e ∈ E`); (4) as `g'(∅) = g(∅) = 0`, this proves that
`g'` is submodular with `g'(∅) = 0`. The positivity hypotheses are not used. -/
theorem translation_a (hg : Submodular g) (hg0 : g ∅ = 0) (_hm : ∀ o, 0 < m' o)
    (_hβ : ∀ o, 0 < β' o) (μα μθ : ℝ) (hd : ∀ e, 0 ≤ (μθ - μα * m' (some e)) / β' (some e))
    (K : ℝ) :
    Submodular (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K) ∧
      extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K ∅ = 0 := by
  -- (1)–(3) "We show that the marginal values of `g'` do not increase as the set grows. …"
  -- These sentences (`appB-tools.tex:262-273`) are `extend_diminishingReturns`.
  have h := extend_diminishingReturns (K := K) hg hd
  -- (4) "As `g'(∅) = g(∅) = 0`, this proves that `g'` is submodular with `g'(∅) = 0`."
  exact ⟨h.submodular, by simp [Hardness.extend, hg0]⟩

/-! ### `lem:translation`(b) -/

omit [Fintype E] [DecidableEq E] in
/-- `d(T) = μ_θ β⁻¹(T) − μ_α t(T)` for the translation `d_e = (μ_θ − μ_α m_e)/β_e`. -/
lemma sum_shift (m β : E → ℝ) (σ μ : ℝ) (T : Finset E) :
    ∑ e ∈ T, (σ - μ * m e) / β e = σ * ∑ e ∈ T, 1 / β e - μ * ∑ e ∈ T, m e / β e := by
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun e _ => by ring

omit [Fintype E] [DecidableEq E] in
/-- The computation of `lem:translation`(b) (`appB-tools.tex:279-283`): for every `T ⊆ E`,
`d(T) = μ_θ β⁻¹(T) − μ_α t(T)`, so `F^g_{α,θ}(T) − d(T) = F^g_{α−μ_α,θ−μ_θ}(T)`; here
`(μ_α, μ_θ) = (μ, σ)`. -/
lemma levelFun_sub_shift (g : Finset E → ℝ) (m β : E → ℝ) (σ μ α θ : ℝ) (T : Finset E) :
    levelFun g m β α θ T - ∑ e ∈ T, (σ - μ * m e) / β e =
      levelFun g m β (α - μ) (θ - σ) T := by
  rw [sum_shift]
  unfold levelFun
  ring

omit [Fintype E] in
/-- `lem:translation`(b), the sets without the new element (`appB-tools.tex:278`):
`F^{g'}_{α,θ}(T) = F^g_{α,θ}(T)` for `T ⊆ E`, as `g' = g` on `2^E`; for every `d` and `K`. -/
lemma levelFun_extend_some (f : Finset E → ℝ) (d : E → ℝ) (K : ℝ) (m' β' : Option E → ℝ)
    (α θ : ℝ) (T : Finset E) :
    levelFun (extend f d K) m' β' α θ (T.map Function.Embedding.some) =
      levelFun f (fun e => m' (some e)) (fun e => β' (some e)) α θ T := by
  simp [levelFun, Hardness.extend, eraseNone_map_some, sum_map]

omit [Fintype E] in
/-- `lem:translation`(b), the sets with the new element (`appB-tools.tex:279-289`): for the
translation `d = μ_θ β⁻¹ − μ_α t`, here `(μ_α, μ_θ) = (μ, σ)`,
`F^{g'}_{α,θ}(T ∪ {b}) = F^g_{α−μ_α,θ−μ_θ}(T) + K − α t_b + θ/β_b` for `T ⊆ E`. Steps: (1)
`F^g_{α,θ}(T) − d(T) = F^g_{α−μ_α,θ−μ_θ}(T)` (`levelFun_sub_shift`); (2)
`F^{g'}_{α,θ}(T ∪ {b}) = g(T) + K − d(T) − α(t(T) + t_b) + θ(β⁻¹(T) + 1/β_b)
= F^g_{α,θ}(T) − d(T) + K − α t_b + θ/β_b = F^g_{α−μ_α,θ−μ_θ}(T) + K − α t_b + θ/β_b`. It does not
use `d ≥ 0`. -/
lemma levelFun_extend_insertNone (f : Finset E → ℝ) (K : ℝ) (m' β' : Option E → ℝ)
    (σ μ α θ : ℝ) (T : Finset E) :
    levelFun (extend f (fun e => (σ - μ * m' (some e)) / β' (some e)) K) m' β' α θ
        (insertNone T) =
      levelFun f (fun e => m' (some e)) (fun e => β' (some e)) (α - μ) (θ - σ) T + K -
        α * (m' none / β' none) + θ * (1 / β' none) := by
  -- (1) "For the second, note first that, for every `T ⊆ E`, `d(T) = μ_θ β⁻¹(T) − μ_α t(T)`, so
  -- `F^g_{α,θ}(T) − d(T) = g(T) − (α − μ_α)t(T) + (θ − μ_θ)β⁻¹(T) = F^g_{α−μ_α,θ−μ_θ}(T)`."
  -- Here `(μ_α, μ_θ) = (μ, σ)`, and the computation is `levelFun_sub_shift`.
  have h1 := levelFun_sub_shift f (fun e => m' (some e)) (fun e => β' (some e)) σ μ α θ T
  -- (2) "Hence
  -- `F^{g'}_{α,θ}(T ∪ {b}) = g(T) + K − d(T) − α(t(T) + t_b) + θ(β⁻¹(T) + 1/β_b)`
  -- `= F^g_{α,θ}(T) − d(T) + K − α t_b + θ/β_b`
  -- `= F^g_{α−μ_α,θ−μ_θ}(T) + K − α t_b + θ/β_b`."
  calc levelFun (extend f (fun e => (σ - μ * m' (some e)) / β' (some e)) K) m' β' α θ
          (insertNone T)
      = f T + K - ∑ e ∈ T, (σ - μ * m' (some e)) / β' (some e) -
          α * (∑ e ∈ T, m' (some e) / β' (some e) + m' none / β' none) +
          θ * (∑ e ∈ T, 1 / β' (some e) + 1 / β' none) := by
        simp only [levelFun, Hardness.extend, Hardness.subMod, none_mem_insertNone,
          eraseNone_insertNone, sum_insertNone, ↓reduceIte]
        ring
    _ = levelFun f (fun e => m' (some e)) (fun e => β' (some e)) α θ T -
          ∑ e ∈ T, (σ - μ * m' (some e)) / β' (some e) + K - α * (m' none / β' none) +
          θ * (1 / β' none) := by
        unfold levelFun
        ring
    _ = levelFun f (fun e => m' (some e)) (fun e => β' (some e)) (α - μ) (θ - σ) T + K -
          α * (m' none / β' none) + θ * (1 / β' none) := by
        rw [h1]

omit [Fintype E] in
/-- **`lem:translation`(b)** (`appB-tools.tex:242-246`, proof `appB-tools.tex:278-289`): for `g`
submodular with `g(∅) = 0`, `m, β > 0`, `(μ_α, μ_θ) ∈ ℝ²` with `d_e = (μ_θ − μ_α m_e)/β_e`,
`K ∈ ℝ` and a new element `b` with `m_b, β_b > 0`, for all `α, θ ∈ ℝ` and `T ⊆ E`,
`F^{g'}_{α,θ}(T) = F^g_{α,θ}(T)` and
`F^{g'}_{α,θ}(T ∪ {b}) = F^g_{α−μ_α,θ−μ_θ}(T) + K − α t_b + θ/β_b`, with `F^{g'}` taken with
respect to `t` and `β⁻¹` extended by `t_b` and `1/β_b`. Steps: (1) the first identity holds as
`g' = g` on `2^E` (`levelFun_extend_some`); (2) `d(T) = μ_θ β⁻¹(T) − μ_α t(T)`, so
`F^g_{α,θ}(T) − d(T) = F^g_{α−μ_α,θ−μ_θ}(T)`, and the expansion of `F^{g'}_{α,θ}(T ∪ {b})` gives the
second (`levelFun_extend_insertNone`). It does not use `d ≥ 0` (the lemma's last sentence,
`appB-tools.tex:254`), nor the hypotheses on `g` and the positivity. -/
theorem translation_b (_hg : Submodular g) (_hg0 : g ∅ = 0) (_hm : ∀ o, 0 < m' o)
    (_hβ : ∀ o, 0 < β' o) (μα μθ K : ℝ) (α θ : ℝ) (T : Finset E) :
    levelFun (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K) m' β' α θ
        (T.map Function.Embedding.some) =
      levelFun g (fun e => m' (some e)) (fun e => β' (some e)) α θ T ∧
    levelFun (extend g (fun e => (μθ - μα * m' (some e)) / β' (some e)) K) m' β' α θ
        (insertNone T) =
      levelFun g (fun e => m' (some e)) (fun e => β' (some e)) (α - μα) (θ - μθ) T + K -
        α * (m' none / β' none) + θ * (1 / β' none) :=
  -- (1) "The first identity holds as `g' = g` on `2^E`." (`levelFun_extend_some`)
  -- (2) "For the second, note first that, for every `T ⊆ E`, `d(T) = μ_θ β⁻¹(T) − μ_α t(T)`, …
  -- Hence …" (`levelFun_extend_insertNone`)
  ⟨levelFun_extend_some g _ K m' β' α θ T, levelFun_extend_insertNone g K m' β' μθ μα α θ T⟩

/-! ### `lem:translation`(c): the shift -/

/-- `g − d` for the translation `d = μ_θ β⁻¹ − μ_α t`, that is, `d_e = (μ_θ − μ_α m_e)/β_e`; here
`(μ_α, μ_θ) = (μ, σ)`. -/
def shiftFun (g : Finset E → ℝ) (m β : E → ℝ) (σ μ : ℝ) (T : Finset E) : ℝ :=
  g T - (σ * ∑ e ∈ T, 1 / β e - μ * ∑ e ∈ T, m e / β e)

omit [Fintype E] [DecidableEq E] in
/-- `lem:translation`(c), the first identity (`appB-tools.tex:291`):
`F^{g−d}_{α,θ} = F^g_{α,θ} − d = F^g_{α−μ_α,θ−μ_θ}` on `2^E`, the computation in (b)
(`levelFun_sub_shift`); here `(μ_α, μ_θ) = (μ, σ)`, for all real values. -/
lemma levelFun_shift (g : Finset E → ℝ) (m β : E → ℝ) (σ μ α θ : ℝ) (T : Finset E) :
    levelFun (shiftFun g m β σ μ) m β α θ T = levelFun g m β (α - μ) (θ - σ) T := by
  rw [← levelFun_sub_shift g m β σ μ α θ T, sum_shift]
  unfold levelFun shiftFun
  ring

omit [Fintype E] in
/-- `lem:translation`(c), the second step (`appB-tools.tex:292`): `g − d` is submodular with
`(g − d)(∅) = 0`, as `d` is modular. -/
theorem FPHyp.shift (H : FPHyp g β) (m : E → ℝ) (σ μ : ℝ) : FPHyp (shiftFun g m β σ μ) β where
  submod S T := by
    have h := H.submod S T
    have h1 : σ * ∑ e ∈ S ∪ T, 1 / β e + σ * ∑ e ∈ S ∩ T, 1 / β e =
        σ * ∑ e ∈ S, 1 / β e + σ * ∑ e ∈ T, 1 / β e := by
      rw [← mul_add, ← mul_add, sum_union_inter]
    have h2 : μ * ∑ e ∈ S ∪ T, m e / β e + μ * ∑ e ∈ S ∩ T, m e / β e =
        μ * ∑ e ∈ S, m e / β e + μ * ∑ e ∈ T, m e / β e := by
      rw [← mul_add, ← mul_add, sum_union_inter]
    unfold shiftFun
    linarith
  empty := by simp [shiftFun, H.empty]
  pos := H.pos

/-- `lem:translation`(c), auxiliary form (`appB-tools.tex:293-299`):
`ξ^{g−d}(α) = ξ^g(α − μ_α) − d`. Steps: (1) `y = ξ^g(α − μ_α) − d` satisfies
`y(S) ≤ g(S) − d(S)` for every `S`, with equality exactly for the sets that are tight for
`ξ^g(α − μ_α)` with respect to `g`; (2) as
`β_e d_e = μ_θ − μ_α m_e`, its marginals at the share `α` are
`ρ_e(y) = α m_e − β_e ξ^g_e(α − μ_α) + β_e d_e = ρ^g_e(α − μ_α) + μ_θ`; (3) so its upper level sets
are those of `ρ^g(α − μ_α)`, tight for `ξ^g(α − μ_α)` with respect to `g` by `lem:fullplane`(a),
hence for `y` with respect to `g − d`; (4) by `lem:fullplane`(a), `y = ξ^{g−d}(α)`. -/
theorem xi_shift (H : FPHyp g β) (m : E → ℝ) (σ μ α : ℝ) :
    xi (shiftFun g m β σ μ) m β α = fun e => xi g m β (α - μ) e - (σ - μ * m e) / β e := by
  symm
  set ξ := xi g m β (α - μ)
  set y : E → ℝ := fun e => ξ e - (σ - μ * m e) / β e with hy
  -- (1) "The vector `y := ξ^g(α − μ_α) − d` satisfies `y(S) ≤ g(S) − d(S)` for every `S ⊆ E`, with
  -- equality exactly for the sets that are tight for `ξ^g(α − μ_α)` with respect to `g`, …"
  -- Here `(μ_α, μ_θ) = (μ, σ)`.
  have hysum : ∀ S, ∑ e ∈ S, y e = ∑ e ∈ S, ξ e - ∑ e ∈ S, (σ - μ * m e) / β e := fun S => by
    simp only [hy, sum_sub_distrib]
  have htight : ∀ S, IsTight (shiftFun g m β σ μ) y S ↔ IsTight g ξ S := fun S => by
    unfold IsTight
    rw [hysum, sum_shift]
    unfold shiftFun
    constructor <;> intro h <;> linarith
  have hle : y ∈ fpPoly (shiftFun g m β σ μ) := fun S => by
    rw [hysum, sum_shift]
    unfold shiftFun
    linarith [(xi_mem_fpBase H m (α - μ)).1 S]
  -- (2) "… and as `β_e d_e = μ_θ − μ_α m_e`, its marginals at the share `α` are
  -- `ρ_e(y) = α m_e − β_e ξ^g_e(α − μ_α) + β_e d_e`
  -- `= (α − μ_α)m_e − β_e ξ^g_e(α − μ_α) + μ_θ = ρ^g_e(α − μ_α) + μ_θ`."
  have hmarg : ∀ e, marg m β α y e = rho g m β (α - μ) e + σ := by
    intro e
    have := (H.pos e).ne'
    simp only [hy, marg, rho, ξ]
    field_simp
    ring
  -- (3) "So its upper level sets are those of `ρ^g(α − μ_α)`, which are tight for `ξ^g(α − μ_α)`
  -- with respect to `g` by `lem:fullplane`(a), hence tight for `y` with respect to `g − d`."
  have hset : ∀ θ, levelSet m β α y θ = levelSet m β (α - μ) ξ (θ - σ) := fun θ => by
    ext e
    simp only [levelSet, mem_filter, mem_univ, true_and, hmarg]
    show θ ≤ rho g m β (α - μ) e + σ ↔ θ - σ ≤ rho g m β (α - μ) e
    constructor <;> intro h <;> linarith
  have ht : ∀ θ, IsTight (shiftFun g m β σ μ) y (levelSet m β α y θ) := fun θ => by
    rw [htight, hset]
    exact xi_levelSet_tight H m (α - μ) (θ - σ)
  -- (4) "By `lem:fullplane`(a), `y = ξ^{g−d}(α)`, …"
  exact eq_xi_of_levelSets (H.shift m σ μ) hle ht

/-- `lem:translation`(c), auxiliary form (`appB-tools.tex:299`):
`ρ^{g−d}(α) = ρ(ξ^{g−d}(α)) = ρ^g(α − μ_α) + μ_θ`. -/
theorem rho_shift (H : FPHyp g β) (m : E → ℝ) (σ μ α : ℝ) (e : E) :
    rho (shiftFun g m β σ μ) m β α e = rho g m β (α - μ) e + σ := by
  have := (H.pos e).ne'
  simp only [rho, marg, xi_shift H m σ μ α]
  field_simp
  ring

/-- `lem:translation`(c), the last identity, auxiliary form (`appB-tools.tex:300`):
`A^{g−d}_θ(α) = A^g_{θ−μ_θ}(α − μ_α)`, from the identity `F^{g−d}_{α,θ} = F^g_{α−μ_α,θ−μ_θ}` and
`lem:fullplane`(b), applied to `g − d` and to `g`: both sets are the largest minimizer of the same
function. -/
theorem levelSet_xi_shift (H : FPHyp g β) (m : E → ℝ) (σ μ α θ : ℝ) :
    levelSet m β α (xi (shiftFun g m β σ μ) m β α) θ =
      levelSet m β (α - μ) (xi g m β (α - μ)) (θ - σ) := by
  have h1 := levelSet_isMaxMinimiser (H.shift m σ μ) m α θ
  have h2 := levelSet_isMaxMinimiser H m (α - μ) (θ - σ)
  simp only [levelFun_shift] at h1
  exact Subset.antisymm (h2.2 _ (h1.1 _)) (h1.2 _ (h2.1 _))

/-- **`lem:translation`(c)** (`appB-tools.tex:247-252`, proof `appB-tools.tex:291-301`):
for `g` submodular with `g(∅) = 0`, `m, β > 0` and every `(μ_α, μ_θ) ∈ ℝ²` (the lemma's last
sentence, `appB-tools.tex:254`: (c) does not use `d ≥ 0`), with `d_e = (μ_θ − μ_α m_e)/β_e`:
`F^{g−d}_{α,θ} = F^g_{α−μ_α,θ−μ_θ}` on `2^E` for all `α, θ`; for every `α`,
`ξ^{g−d}(α) = ξ^g(α − μ_α) − d` and `ρ^{g−d}(α) = ρ^g(α − μ_α) + μ_θ`; and
`A^{g−d}_θ(α) = A^g_{θ−μ_θ}(α − μ_α)` for all `α, θ`. Here `g − d` is `shiftFun g m β μ_θ μ_α`.
Steps: (1) `F^{g−d}_{α,θ} = F^g_{α,θ} − d = F^g_{α−μ_α,θ−μ_θ}` is the computation in (b)
(`levelFun_shift`); (2) `g − d` is submodular with `(g − d)(∅) = 0`, as `d` is modular
(`FPHyp.shift`); (3) `y = ξ^g(α − μ_α) − d` satisfies `y(S) ≤ (g − d)(S)` with the tight sets of
`ξ^g(α − μ_α)`, and its marginals at the share `α` are `ρ^g(α − μ_α) + μ_θ`, so its upper level sets
are tight by `lem:fullplane`(a), and `y = ξ^{g−d}(α)` by `lem:fullplane`(a) (`xi_shift`);
(4) `ρ^{g−d}(α) = ρ(y) = ρ^g(α − μ_α) + μ_θ` (`rho_shift`); (5) the identity of (1) and
`lem:fullplane`(b), applied to `g − d` and to `g`, give `A^{g−d}_θ(α) = A^g_{θ−μ_θ}(α − μ_α)`
(`levelSet_xi_shift`). None of these steps uses `d ≥ 0`; the hypothesis `m > 0` is not used. -/
theorem translation_c (hg : Submodular g) (hg0 : g ∅ = 0) (_hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) (μα μθ : ℝ) :
    (∀ (α θ : ℝ) (S : Finset E),
        levelFun (shiftFun g m β μθ μα) m β α θ S = levelFun g m β (α - μα) (θ - μθ) S) ∧
      (∀ α : ℝ, xi (shiftFun g m β μθ μα) m β α =
        fun e => xi g m β (α - μα) e - (μθ - μα * m e) / β e) ∧
      (∀ α : ℝ, rho (shiftFun g m β μθ μα) m β α = fun e => rho g m β (α - μα) e + μθ) ∧
      ∀ α θ : ℝ, levelSet m β α (xi (shiftFun g m β μθ μα) m β α) θ =
        levelSet m β (α - μα) (xi g m β (α - μα)) (θ - μθ) := by
  have H : FPHyp g β := ⟨hg, hg0, hβ⟩
  -- (1) "The identity `F^{g−d}_{α,θ} = F^g_{α,θ} − d = F^g_{α−μ_α,θ−μ_θ}` on `2^E` is the
  -- computation in (b)." (`levelFun_shift`)
  have h1 := fun α θ S => levelFun_shift g m β μθ μα α θ S
  -- (2) "The function `g − d` is submodular with `(g − d)(∅) = 0`, as `d` is modular."
  -- This is `FPHyp.shift`, used inside `xi_shift` and `levelSet_xi_shift`.
  -- (3) "The vector `y := ξ^g(α − μ_α) − d` satisfies … By `lem:fullplane`(a), `y = ξ^{g−d}(α)`, …"
  -- These sentences (`appB-tools.tex:293-299`) are `xi_shift`.
  have h3 := fun α => xi_shift H m μθ μα α
  -- (4) "… and `ρ^{g−d}(α) = ρ(y) = ρ^g(α − μ_α) + μ_θ`." (`rho_shift`)
  have h4 := fun α => funext fun e => rho_shift H m μθ μα α e
  -- (5) "Finally, the identity `F^{g−d}_{α,θ} = F^g_{α−μ_α,θ−μ_θ}` and `lem:fullplane`(b), applied
  -- to `g − d` and to `g`, give `A^{g−d}_θ(α) = A^g_{θ−μ_θ}(α − μ_α)`." (`levelSet_xi_shift`)
  have h5 := fun α θ => levelSet_xi_shift H m μθ μα α θ
  exact ⟨h1, h3, h4, h5⟩

end

end Hardness

end Stoc
