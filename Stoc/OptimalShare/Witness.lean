-- stamp r7 2026-11-02
import Stoc.Hardness.Splice

/-!
# The translation step and a witness for every subset

The STOC version's Appendix B.7 (`stoc-sections/appC-bits.tex`): Corollary `cor:witness` (the
translation step) and Proposition `prop:witness` (a witness for every subset).

For a finite set `E`, `t ∈ ℝ^E_{>0}`, `g : 2^E → ℝ` and `w = (λ, θ) ∈ ℝ²`,
`F^g_w(S) = g(S) − λ t(S) + θ |S|` (`Stoc.Witness.F`), the function `F^g_{λ,θ}` of
`sec:B-fullplane` with `β = 1` (`F_eq_levelFun`), and `min F^g_w = min_{S ⊆ E} F^g_w(S)`
(`minF`). `w` is a witness of `S` for `g` with respect to `t` if `S` is the unique minimizer of
`F^g_w` (`IsWitness`).

* `cor:witness`: `witness_step`. The new element `b` is `none : Option E`, `t` is extended by
  `t_b` (`extT`), the translation vector `ŵ = (λ̂, θ̂)` is `(lhat, θhat)`, and `g'` is `extG g d K`
  (`g'(S) = g(S)`, `g'(S ∪ {b}) = g(S) + K − d(S)`), which is the function
  `Stoc.Hardness.extend g d K` of `lem:translation` (`extG_eq_extend`). The proof applies
  `lem:translation` (a), (b) and (c) (`Stoc.Hardness.translation_a`, `Stoc.Hardness.translation_b`,
  `Stoc.Hardness.translation_c`) with `β = 1`, `m = t`, `m_b = t_b`, `β_b = 1` and
  `(μ_α, μ_θ) = (λ̂, θ̂)`, with `ℓ(w)`, (`eq:C-shift`), (`eq:C-extend`) and (`eq:C-minbounds`) as in
  the paper.
* `prop:witness`: `witness`. The numbers are defined with the paper's indices `k = 1, 2, …`
  (`lam`, `lamBar`, `theta`, `thetaBar`, `d`, `D`, `K`, and `t` by the recursion `t_eq`), `g` on
  the finite sets of `ℕ`, and `E_k = {1, …, k}` is `Fin k` (`emb`: `i ↦ i + 1`) with `g_k`
  (`gE`), `t` (`tE`) and the witnesses `(λ_S, θ_S)` (`wit`). Part (i): the induction on
  `k ∈ {1, …, n}` of `claim_i` (base `t_one`, step `step_i` for `k ∈ {2, …, n}`), then the upper
  bound (`t_le_mul` for `k ∈ {2, …, n}`, `t_le_pow`); a chain `t_1 < ⋯ < t_n` is read pairwise by
  `chain_lt` (plumbing). Part (ii): the claim `(C_k)` (`ClaimC`) for all `k ∈ {0, …, n}` by
  `claim_ii`, the induction on `k` through `witness_step`, from the first part of (i), with
  `E_{k+1} = E_k ∪ {k + 1}` as `Option (Fin k) ≃ Fin (k + 1)` (`ext`) and the check that `g'` of the
  corollary is `g_{k+1}` (`g_insert`).
* The facts of `prop:witness` (i) that the proof of `thm:polybits` uses where it does not cite
  the proposition, read off `witness`: `two_le_t`, `d_nonneg`, `theta_nonneg`.
-/

namespace Stoc

namespace Witness

open Finset Hardness

/-! ### The translation step (`cor:witness`) -/

section Step

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `F^g_w(S) = F^g_{λ,θ}(S) = g(S) − λ t(S) + θ |S|` for `w = (λ, θ)`. -/
def F (g : Finset E → ℝ) (t : E → ℝ) (w : ℝ × ℝ) (S : Finset E) : ℝ :=
  g S - w.1 * ∑ e ∈ S, t e + w.2 * S.card

omit [Fintype E] [DecidableEq E] in
/-- `F^g_w` is the function `F^g_{λ,θ}` of `sec:B-fullplane` with `β = 1`. -/
lemma F_eq_levelFun (g : Finset E → ℝ) (t : E → ℝ) (w : ℝ × ℝ) (S : Finset E) :
    F g t w S = levelFun g t 1 w.1 w.2 S := by
  simp [F, levelFun]

/-- `min F^g_w = min_{S ⊆ E} F^g_w(S)`. -/
def minF (g : Finset E → ℝ) (t : E → ℝ) (w : ℝ × ℝ) : ℝ :=
  (univ : Finset (Finset E)).inf' univ_nonempty (F g t w)

omit [DecidableEq E] in
lemma minF_le (g : Finset E → ℝ) (t : E → ℝ) (w : ℝ × ℝ) (T : Finset E) :
    minF g t w ≤ F g t w T :=
  inf'_le _ (mem_univ T)

omit [DecidableEq E] in
lemma exists_eq_minF (g : Finset E → ℝ) (t : E → ℝ) (w : ℝ × ℝ) :
    ∃ T, F g t w T = minF g t w := by
  obtain ⟨T, -, hT⟩ := exists_mem_eq_inf' (univ_nonempty (α := Finset E)) (F g t w)
  exact ⟨T, hT.symm⟩

/-- `w` is a witness of `S` for `g` with respect to `t`: `S` is the unique minimizer of `F^g_w`. -/
def IsWitness (g : Finset E → ℝ) (t : E → ℝ) (w : ℝ × ℝ) (S : Finset E) : Prop :=
  ∀ T, T ≠ S → F g t w S < F g t w T

omit [DecidableEq E] in
/-- The minimum of `F^g_w` at a witness `w` of `S` is `F^g_w(S)`. -/
lemma IsWitness.minF_eq {g : Finset E → ℝ} {t : E → ℝ} {w : ℝ × ℝ} {S : Finset E}
    (h : IsWitness g t w S) : minF g t w = F g t w S := by
  refine le_antisymm (minF_le g t w S) ?_
  obtain ⟨T, hT⟩ := exists_eq_minF g t w
  rw [← hT]
  rcases eq_or_ne T S with rfl | hTS
  · exact le_rfl
  · exact (h T hTS).le

/-- `t` extended to `Option E` by `t_b` at the new element `b = none`. -/
def extT (t : E → ℝ) (tb : ℝ) : Option E → ℝ := fun o => o.elim tb t

/-- The function `g'` of `cor:witness`: `g'(S) = g(S)` and `g'(S ∪ {b}) = g(S) + K − d(S)` for
`S ⊆ E`, the new element `b` being `none`. -/
def extG (g : Finset E → ℝ) (d : E → ℝ) (K : ℝ) (T : Finset (Option E)) : ℝ :=
  if none ∈ T then g (eraseNone T) + K - ∑ e ∈ eraseNone T, d e else g (eraseNone T)

omit [Fintype E] in
/-- The function `g'` of `lem:translation` (`Stoc.Hardness.extend`) is the function `g'` of
`cor:witness`. -/
lemma extG_eq_extend (g : Finset E → ℝ) (d : E → ℝ) (K : ℝ) : extG g d K = extend g d K := by
  funext T
  unfold extG extend subMod
  split_ifs <;> ring

omit [Fintype E] in
/-- A set of `Option E` without `none` is the image of a set of `E`. -/
lemma eq_map_some {X : Finset (Option E)} (h : none ∉ X) :
    X = (eraseNone X).map Function.Embedding.some := by
  rw [map_some_eraseNone, erase_eq_of_notMem h]

omit [Fintype E] in
/-- A set of `Option E` with `none` is `insertNone` of a set of `E`. -/
lemma eq_insertNone {X : Finset (Option E)} (h : none ∈ X) : X = insertNone (eraseNone X) := by
  rw [insertNone_eraseNone, insert_eq_of_mem h]

/-- **`cor:witness`** (Corollary B.15), the translation step (statement
`stoc-sections/appC-bits.tex:33-51`, proof `appC-bits.tex:53-117`). Let `E` be a finite set,
possibly empty, let `t ∈ ℝ^E_{>0}`, and let `g` be submodular with `g(∅) = 0`. Let `𝓕 ⊆ 2^E` be a
family such that every `S ∈ 𝓕` has a witness `w_S ∈ [0, λ̄] × [0, θ̄]` for `g` with respect to `t`,
where `λ̄, θ̄ ≥ 0`. Let `b ∉ E` be a new element (`none`) with `t_b > 0`, and let
`ŵ = (λ̂, θ̂) ∈ ℝ²` (here `(lhat, θhat)`) be such that `d := θ̂ 1 − λ̂ t ≥ 0`. Let `K` satisfy
`t_b λ̄ + d(E) < K < t_b λ̂ − θ̄ − θ̂` (`eq:C-window`). Then `g'` (`extG`: `g'(S) = g(S)` and
`g'(S ∪ {b}) = g(S) + K − d(S)`) is submodular with `g'(∅) = 0`, and for every `S ∈ 𝓕`, with respect
to `g'` and the vector `t` extended by `t_b` (`extT`), the point `w_S` is a witness of `S` and the
point `w_S + ŵ` is a witness of `S ∪ {b}`.

The paper's steps: (1) `lem:translation` is applied to `g` with `β = 1`, `m = t`, `m_b = t_b`,
`β_b = 1`, the constant `K` and `(μ_α, μ_θ) = (λ̂, θ̂)`; its hypotheses `m, m_b > 0` are `t > 0` and
`t_b > 0`, its `d = μ_θ β⁻¹ − μ_α t = θ̂ 1 − λ̂ t` is the `d` above, and its `g'` is the `g'` above,
so `lem:translation` (a) (`Stoc.Hardness.translation_a`) gives the submodularity of `g'`; (2) with
`ℓ(w) = λ t_b − θ − K`: `F^{g'}_w(T) = F^g_w(T)` by `lem:translation` (b)
(`Stoc.Hardness.translation_b`), `F^g_{w−ŵ} = F^{g−d}_w` on `2^E` by `lem:translation` (c)
(`Stoc.Hardness.translation_c`), equivalently (`eq:C-shift`) `F^g_{w−ŵ}(T) = F^g_w(T) − d(T)`, and
(`eq:C-extend`) `F^{g'}_w(T ∪ {b}) = F^g_{w−ŵ}(T) − ℓ(w)` by `lem:translation` (b) with `β_b = 1`;
(3) (`eq:C-minbounds`) `min F^g_w − d(E) ≤ min F^g_{w−ŵ} ≤ min F^g_w`; (4) `w_S` is a witness of
`S`; (5) `w' = w_S + ŵ` is a witness of `S ∪ {b}`. The hypotheses `λ̄, θ̄ ≥ 0` are the paper's; its
proof does not use them. -/
theorem witness_step {g : Finset E → ℝ} (hg : Submodular g) (hg0 : g ∅ = 0) {t : E → ℝ}
    (ht : ∀ e, 0 < t e) {𝓕 : Set (Finset E)} {w : Finset E → ℝ × ℝ} {lbar θbar : ℝ}
    (_hlbar : 0 ≤ lbar) (_hθbar : 0 ≤ θbar)
    (hw : ∀ S ∈ 𝓕, IsWitness g t (w S) S ∧ (w S).1 ∈ Set.Icc 0 lbar ∧
      (w S).2 ∈ Set.Icc 0 θbar)
    {tb lhat θhat K : ℝ} (htb : 0 < tb) (hd : ∀ e, 0 ≤ θhat - lhat * t e)
    (hwin1 : tb * lbar + ∑ e, (θhat - lhat * t e) < K) (hwin2 : K < tb * lhat - θbar - θhat) :
    (Submodular (extG g (fun e => θhat - lhat * t e) K) ∧
      extG g (fun e => θhat - lhat * t e) K ∅ = 0) ∧
    ∀ S ∈ 𝓕, IsWitness (extG g (fun e => θhat - lhat * t e) K) (extT t tb) (w S)
        (S.map Function.Embedding.some) ∧
      IsWitness (extG g (fun e => θhat - lhat * t e) K) (extT t tb) (w S + (lhat, θhat))
        (insertNone S) := by
  set d : E → ℝ := fun e => θhat - lhat * t e with hd_def
  set g' := extG g d K with hg'_def
  set t' := extT t tb with ht'_def
  -- the translation vector `ŵ = (λ̂, θ̂)` of the statement
  set what : ℝ × ℝ := (lhat, θhat) with hwhat_def
  -- (1) "We apply `lem:translation` to `g` with `β := 1`, `m := t`, `m_b := t_b`, `β_b := 1`, the
  -- constant `K` and `(μ_α, μ_θ) := (λ̂, θ̂)`." Its hypotheses `m, m_b > 0` are `t > 0` and
  -- `t_b > 0`.
  have hm : ∀ o, 0 < t' o := fun o => by
    cases o with
    | none => exact htb
    | some e => exact ht e
  have hβ : ∀ o : Option E, (0 : ℝ) < (1 : Option E → ℝ) o := fun _ => one_pos
  -- "Then `μ_θ β⁻¹ − μ_α t = θ̂ 1 − λ̂ t = d ≥ 0`,"
  have hdμ : (fun e => (θhat - lhat * t' (some e)) / (1 : Option E → ℝ) (some e)) = d := by
    funext e
    simp [d, t', extT]
  have hdμ0 : ∀ e, 0 ≤ (θhat - lhat * t' (some e)) / (1 : Option E → ℝ) (some e) := fun e => by
    rw [show (θhat - lhat * t' (some e)) / (1 : Option E → ℝ) (some e) = d e from congrFun hdμ e]
    exact hd e
  -- "and the function `g'` of the lemma is the function `g'` above."
  have hg' : g' = extend g d K := extG_eq_extend g d K
  -- "By `lem:translation`(a), `g'` is submodular with `g'(∅) = 0`."
  have ha : Submodular g' ∧ g' ∅ = 0 := by
    rw [hg', ← hdμ]
    exact translation_a hg hg0 hm hβ lhat θhat hdμ0 K
  refine ⟨ha, fun S hS => ?_⟩
  -- (2) "Next, we relate `F^{g'}` to `F^g`. Let `w = (λ, θ) ∈ ℝ²` and let `ℓ(w) := λ t_b − θ − K`."
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 * tb - w.2 - K with hℓ_def
  -- "For every `T ⊆ E`, we have `F^{g'}_w(T) = F^g_w(T)` by `lem:translation`(b)."
  have hsome : ∀ (w : ℝ × ℝ) (T : Finset E),
      F g' t' w (T.map Function.Embedding.some) = F g t w T := by
    intro w T
    rw [F_eq_levelFun, F_eq_levelFun, hg', ← hdμ,
      (translation_b hg hg0 hm hβ lhat θhat K w.1 w.2 T).1]
    rfl
  -- "By `lem:translation`(c), `F^g_{w−ŵ} = F^{g−d}_w` on `2^E`."
  have hc : ∀ (w : ℝ × ℝ) (T : Finset E),
      F g t (w - what) T = levelFun (shiftFun g t 1 θhat lhat) t 1 w.1 w.2 T := by
    intro w T
    rw [F_eq_levelFun,
      (translation_c (β := 1) hg hg0 ht (fun _ => one_pos) lhat θhat).1 w.1 w.2 T]
    rfl
  -- "Equivalently, as `d(T) = θ̂ |T| − λ̂ t(T)`, (`eq:C-shift`) `F^g_{w−ŵ}(T) = F^g_w(T) − d(T)`."
  have hdT' : ∀ T : Finset E, ∑ e ∈ T, d e = θhat * T.card - lhat * ∑ e ∈ T, t e := fun T => by
    simp only [d, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_sum]
    ring
  have hshift : ∀ (w : ℝ × ℝ) (T : Finset E),
      F g t (w - what) T = F g t w T - ∑ e ∈ T, d e := by
    intro w T
    rw [hc, hdT']
    simp only [levelFun, shiftFun, F, Pi.one_apply, div_one, sum_const, nsmul_eq_mul, mul_one]
    ring
  -- "By `lem:translation`(b) with `β_b = 1`, or directly from the definition of `g'` and
  -- (`eq:C-shift`), (`eq:C-extend`)
  -- `F^{g'}_w(T ∪ {b}) = g(T) + K − d(T) − λ (t(T) + t_b) + θ (|T| + 1)
  --   = F^g_w(T) − d(T) − (λ t_b − θ − K) = F^g_{w−ŵ}(T) − ℓ(w)`."
  have hext : ∀ (w : ℝ × ℝ) (T : Finset E),
      F g' t' w (insertNone T) = F g t (w - what) T - ℓ w := by
    intro w T
    have hb := (translation_b hg hg0 hm hβ lhat θhat K w.1 w.2 T).2
    calc F g' t' w (insertNone T) = F g t (w - what) T + K - w.1 * tb + w.2 := by
          rw [F_eq_levelFun, F_eq_levelFun, hg', ← hdμ, hb]
          simp only [t', extT, Option.elim, Pi.one_apply, div_one, mul_one]
          rfl
      _ = F g t (w - what) T - ℓ w := by
          simp only [hℓ_def]
          ring
  -- (3) "As `0 ≤ d(T) ≤ d(E)` for all `T ⊆ E`, taking the minimum over `T` in (`eq:C-shift`) gives
  -- (`eq:C-minbounds`) `min F^g_w − d(E) ≤ min F^g_{w−ŵ} ≤ min F^g_w`."
  have hdT : ∀ T : Finset E, 0 ≤ ∑ e ∈ T, d e ∧ ∑ e ∈ T, d e ≤ ∑ e, d e := fun T =>
    ⟨sum_nonneg fun e _ => hd e, sum_le_sum_of_subset_of_nonneg (subset_univ T) fun e _ _ => hd e⟩
  have hminb : ∀ w : ℝ × ℝ,
      minF g t w - ∑ e, d e ≤ minF g t (w - what) ∧ minF g t (w - what) ≤ minF g t w := by
    intro w
    constructor
    · obtain ⟨T, hT⟩ := exists_eq_minF g t (w - what)
      rw [← hT, hshift]
      linarith [minF_le g t w T, (hdT T).2]
    · obtain ⟨T, hT⟩ := exists_eq_minF g t w
      rw [← hT]
      linarith [minF_le g t (w - what) T, hshift w T, (hdT T).1]
  obtain ⟨hwit, ⟨hl0, hl1⟩, ⟨hθ0, hθ1⟩⟩ := hw S hS
  have hminS : minF g t (w S) = F g t (w S) S := hwit.minF_eq
  refine ⟨fun X hX => ?_, fun X hX => ?_⟩
  · -- (4) "We now show that `w_S` is a witness of `S` for `g'`, for every `S ∈ 𝓕`. Let
    -- `w := w_S = (λ, θ)`. As `λ ≤ λ̄`, `θ ≥ 0` and `t_b > 0`, the left inequality in
    -- (`eq:C-window`) gives `ℓ(w) ≤ t_b λ̄ − K < −d(E)`."
    have hℓ : ℓ (w S) < -∑ e, d e := by
      have : (w S).1 * tb ≤ lbar * tb := mul_le_mul_of_nonneg_right hl1 htb.le
      simp only [hℓ_def]
      linarith
    rw [hsome]
    by_cases hX0 : none ∈ X
    · -- "Hence, by (`eq:C-extend`) and (`eq:C-minbounds`), every `T ⊆ E` satisfies
      -- `F^{g'}_w(T ∪ {b}) = F^g_{w−ŵ}(T) − ℓ(w) > min F^g_{w−ŵ} + d(E) ≥ min F^g_w = F^g_w(S)
      -- = F^{g'}_w(S)`,"
      rw [eq_insertNone hX0, hext]
      have h1 := minF_le g t (w S - what) (eraseNone X)
      have h2 := (hminb (w S)).1
      linarith
    · -- "and every `T ⊆ E` with `T ≠ S` satisfies `F^{g'}_w(T) = F^g_w(T) > F^g_w(S)`. So `S` is
      -- the unique minimizer of `F^{g'}_w`, as claimed."
      rw [eq_map_some hX0, hsome]
      refine hwit _ fun h => hX ?_
      rw [eq_map_some hX0, h]
  · -- (5) "Finally, we show that `w' := w_S + ŵ` is a witness of `S ∪ {b}` for `g'`, for every
    -- `S ∈ 𝓕`. Write `w_S = (λ, θ)`. As `λ ≥ 0` and `θ ≤ θ̄`, the right inequality in
    -- (`eq:C-window`) gives `ℓ(w') = (λ + λ̂) t_b − (θ + θ̂) − K ≥ t_b λ̂ − θ̄ − θ̂ − K > 0`."
    have hws : w S + what - what = w S := add_sub_cancel_right _ _
    have hℓ : 0 < ℓ (w S + what) := by
      have : 0 ≤ (w S).1 * tb := mul_nonneg hl0 htb.le
      simp only [hℓ_def, Prod.fst_add, Prod.snd_add, hwhat_def]
      linarith
    rw [hext, hws]
    by_cases hX0 : none ∉ X
    · -- "Hence, by (`eq:C-minbounds`) at the point `w'` and by (`eq:C-extend`), every `T ⊆ E`
      -- satisfies `F^{g'}_{w'}(T) = F^g_{w'}(T) ≥ min F^g_{w'} ≥ min F^g_{w_S} = F^g_{w_S}(S)
      -- > F^g_{w_S}(S) − ℓ(w') = F^{g'}_{w'}(S ∪ {b})`,"
      rw [eq_map_some hX0, hsome]
      have h1 := minF_le g t (w S + what) (eraseNone X)
      have h2 := (hminb (w S + what)).2
      rw [hws] at h2
      linarith
    · -- "and every `T ⊆ E` with `T ≠ S` satisfies
      -- `F^{g'}_{w'}(T ∪ {b}) = F^g_{w_S}(T) − ℓ(w') > F^g_{w_S}(S) − ℓ(w')
      --   = F^{g'}_{w'}(S ∪ {b})`. So `S ∪ {b}` is the unique minimizer of `F^{g'}_{w'}`."
      rw [not_not] at hX0
      rw [eq_insertNone hX0, hext, hws]
      have h := hwit (eraseNone X) fun h => hX (by rw [eq_insertNone hX0, h])
      linarith

end Step

/-! ### A witness for every subset (`prop:witness`)

The numbers of `prop:witness` (`stoc-sections/appC-bits.tex:126-152`), with the paper's indices
`k = 1, 2, …`; the values at `k = 0` are not used. The integers are in `ℤ`, and `t_k` is defined
by the paper's recursion (`t_eq`). -/

section Construction

/-- `λ_k = 3^{k−1}`. -/
def lam (k : ℕ) : ℤ := 3 ^ (k - 1)

/-- `λ̄_k = ∑_{j<k} λ_j`, which is `(3^{k−1} − 1)/2` (`lamBar_eq`). -/
def lamBar (k : ℕ) : ℤ := ∑ j ∈ Ico 1 k, lam j

/-- `θ_k` with a sequence `u` in place of `t`: `θ_1 = 0` and `θ_k = λ_k u_{k−1}` for `k ≥ 2`. -/
def thetaOf (u : ℕ → ℤ) (k : ℕ) : ℤ := if k = 1 then 0 else lam k * u (k - 1)

/-- The right-hand side `⌊(D_k + 1 + θ_k + θ̄_k)/(λ̄_k + 1)⌋ + 1` of the recursion for `t_k`,
with a sequence `u` in place of `t`; it uses `u` only below `k` (`tOf_congr`). -/
noncomputable def tOf (u : ℕ → ℤ) (k : ℕ) : ℤ :=
  ⌊((∑ i ∈ Ico 1 k, (thetaOf u k - lam k * u i) + 1 + thetaOf u k +
      ∑ j ∈ Ico 1 k, thetaOf u j : ℤ) : ℝ) / ((lamBar k + 1 : ℤ) : ℝ)⌋ + 1

/-- `t_k`, by the recursion of `prop:witness` (`t_eq`). -/
noncomputable def t (k : ℕ) : ℤ := tOf (fun i => if i < k then t i else 0) k
termination_by k
decreasing_by assumption

/-- `θ_1 = 0` and `θ_k = λ_k t_{k−1}` for `k ≥ 2`. -/
noncomputable def theta (k : ℕ) : ℤ := thetaOf t k

/-- `θ̄_k = ∑_{j<k} θ_j`. -/
noncomputable def thetaBar (k : ℕ) : ℤ := ∑ j ∈ Ico 1 k, theta j

/-- `d_i^{(k)} = θ_k − λ_k t_i`. -/
noncomputable def d (i k : ℕ) : ℤ := theta k - lam k * t i

/-- `D_k = ∑_{i<k} d_i^{(k)}`. -/
noncomputable def D (k : ℕ) : ℤ := ∑ i ∈ Ico 1 k, d i k

/-- `K_k = t_k λ̄_k + D_k + 1`. -/
noncomputable def K (k : ℕ) : ℤ := t k * lamBar k + D k + 1

/-- `g(S) = ∑_{k ∈ S} K_k − ∑_{i, k ∈ S, i < k} d_i^{(k)}`. -/
noncomputable def g (S : Finset ℕ) : ℤ := ∑ k ∈ S, K k - ∑ k ∈ S, ∑ i ∈ S.filter (· < k), d i k

lemma tOf_congr {u v : ℕ → ℤ} {k : ℕ} (hk : 1 ≤ k) (h : ∀ i, i < k → u i = v i) :
    tOf u k = tOf v k := by
  have hθ : ∀ j, 1 ≤ j → j ≤ k → thetaOf u j = thetaOf v j := by
    intro j hj1 hjk
    unfold thetaOf
    split_ifs with hj
    · rfl
    · rw [h (j - 1) (by omega)]
  have h1 : ∑ i ∈ Ico 1 k, (thetaOf u k - lam k * u i) =
      ∑ i ∈ Ico 1 k, (thetaOf v k - lam k * v i) :=
    sum_congr rfl fun i hi => by rw [hθ k hk le_rfl, h i (mem_Ico.1 hi).2]
  have h2 : ∑ j ∈ Ico 1 k, thetaOf u j = ∑ j ∈ Ico 1 k, thetaOf v j :=
    sum_congr rfl fun j hj => hθ j (mem_Ico.1 hj).1 (mem_Ico.1 hj).2.le
  unfold tOf
  rw [h1, h2, hθ k hk le_rfl]

/-- The recursion of `prop:witness`: `t_k = ⌊(D_k + 1 + θ_k + θ̄_k)/(λ̄_k + 1)⌋ + 1`. -/
lemma t_eq {k : ℕ} (hk : 1 ≤ k) :
    t k = ⌊((D k + 1 + theta k + thetaBar k : ℤ) : ℝ) / ((lamBar k + 1 : ℤ) : ℝ)⌋ + 1 := by
  rw [t, tOf_congr hk (v := t) fun i hi => by simp [hi]]
  rfl

lemma lam_pos (k : ℕ) : 0 < lam k := by unfold lam; positivity

lemma lamBar_succ {k : ℕ} (hk : 1 ≤ k) : lamBar (k + 1) = lamBar k + lam k := by
  rw [lamBar, lamBar, sum_Ico_succ_top hk]

lemma lam_succ {k : ℕ} (hk : 1 ≤ k) : lam (k + 1) = 3 * lam k := by
  unfold lam
  rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ, mul_comm]

/-- `λ_k = 2 λ̄_k + 1`. -/
lemma lam_eq {k : ℕ} (hk : 1 ≤ k) : lam k = 2 * lamBar k + 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp [lam, lamBar]
  | succ k hk ih => rw [lam_succ hk, lamBar_succ hk]; linarith

/-- `λ̄_k = (3^{k−1} − 1)/2`. -/
lemma lamBar_eq {k : ℕ} (hk : 1 ≤ k) : (lamBar k : ℝ) = (3 ^ (k - 1) - 1) / 2 := by
  have h := lam_eq hk
  have h' : ((lam k : ℤ) : ℝ) = 2 * (lamBar k : ℝ) + 1 := by exact_mod_cast h
  simp only [lam] at h'
  push_cast at h'
  linarith

lemma lamBar_nonneg (k : ℕ) : 0 ≤ lamBar k := sum_nonneg fun j _ => (lam_pos j).le

lemma theta_one : theta 1 = 0 := by simp [theta, thetaOf]

lemma theta_of_two_le {k : ℕ} (hk : 2 ≤ k) : theta k = lam k * t (k - 1) := by
  simp [theta, thetaOf, show k ≠ 1 by omega]

/-- A chain `u_1 < u_2 < ⋯ < u_n`, read pairwise: `u_i < u_j` for `1 ≤ i < j ≤ n` (plumbing, for
the chains `t_1 < ⋯ < t_k` of `prop:witness` (i)). -/
lemma chain_lt {u : ℕ → ℤ} {n : ℕ} (h : ∀ k, 1 ≤ k → k < n → u k < u (k + 1)) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n) : u i < u j := by
  induction j, hij using Nat.le_induction with
  | base => exact h i hi (by omega)
  | succ j hij ih => exact (ih (by omega)).trans (h j (by omega) (by omega))

/-- **`prop:witness` (i)**, the base `k = 1` of the induction `claim_i`: `t_1 = 2`, as
`D_1 = θ_1 = θ̄_1 = λ̄_1 = 0`. -/
lemma t_one : t 1 = 2 := by
  have hD : D 1 = 0 := by simp [D]
  have hθbar : thetaBar 1 = 0 := by simp [thetaBar]
  have hlb : lamBar 1 = 0 := by simp [lamBar]
  rw [t_eq le_rfl, hD, theta_one, hθbar, hlb]
  norm_num

/-- The induction step of `prop:witness` (i) (`appC-bits.tex:157-166`): for `k ∈ {2, …, n}`, if
`2 = t_1 < ⋯ < t_{k−1}`, then `d_i^{(k)} ≥ 0` for all `i < k` and `t_{k−1} < t_k`. The bound
`k ≤ n` is the paper's range (it defines the numbers for `k ≤ n`); the argument does not use it.

The paper's steps: (1) `d_i^{(k)} = λ_k (t_{k−1} − t_i) ≥ 0` for all `i < k`, so `D_k ≥ 0`;
(2) `θ̄_k ≥ 0`, as all `θ_j ≥ 0`; (3) as `⌊x⌋ + 1 > x` for all `x ∈ ℝ`,
`t_k > (D_k + 1 + θ_k + θ̄_k)/(λ̄_k + 1) > θ_k/(λ̄_k + 1) = 2 · 3^{k−1}/(3^{k−1} + 1) · t_{k−1}
≥ t_{k−1}`. -/
lemma step_i {n k : ℕ} (hk : 2 ≤ k) (_hkn : k ≤ n) (h1 : t 1 = 2)
    (ih : ∀ j, 1 ≤ j → j < k - 1 → t j < t (j + 1)) :
    (∀ i, 1 ≤ i → i < k → 0 ≤ d i k) ∧ t (k - 1) < t k := by
  -- "Let `k ∈ {2, …, n}` and assume that `t_1 < ⋯ < t_{k−1}`": so `2 = t_1 ≤ t_i ≤ t_{k−1}` for
  -- `1 ≤ i ≤ k − 1`
  have hle : ∀ i, 1 ≤ i → i ≤ k - 1 → t i ≤ t (k - 1) := fun i hi hik => by
    rcases hik.lt_or_eq with h | rfl
    · exact (chain_lt ih hi h le_rfl).le
    · exact le_rfl
  have h2 : ∀ i, 1 ≤ i → i ≤ k - 1 → 2 ≤ t i := fun i hi hik => by
    rcases hi.lt_or_eq with h | rfl
    · have := chain_lt ih le_rfl h hik
      linarith
    · exact h1.ge
  have hθk : theta k = lam k * t (k - 1) := theta_of_two_le hk
  -- (1) "Then `d_i^{(k)} = λ_k (t_{k−1} − t_i) ≥ 0` for all `i < k`, so `D_k ≥ 0`,"
  have hd : ∀ i, 1 ≤ i → i < k → 0 ≤ d i k := by
    intro i hi hik
    have hdi : d i k = lam k * (t (k - 1) - t i) := by rw [d, hθk]; ring
    rw [hdi]
    exact mul_nonneg (lam_pos k).le (sub_nonneg.2 (hle i hi (by omega)))
  have hD : 0 ≤ D k := sum_nonneg fun i hi => hd i (mem_Ico.1 hi).1 (mem_Ico.1 hi).2
  -- (2) "and `θ̄_k ≥ 0` as all `θ_j ≥ 0`."
  have hθ : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ theta j := by
    intro j hj hjk
    rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
    · rw [theta_one]
    · rw [theta_of_two_le hj2]
      exact mul_nonneg (lam_pos j).le (by linarith [h2 (j - 1) (by omega) (by omega)])
  have hθbar : 0 ≤ thetaBar k :=
    sum_nonneg fun j hj => hθ j (mem_Ico.1 hj).1 (mem_Ico.1 hj).2.le
  refine ⟨hd, ?_⟩
  -- (3) "As `⌊x⌋ + 1 > x` for all `x ∈ ℝ`, we obtain
  -- `t_k > (D_k + 1 + θ_k + θ̄_k)/(λ̄_k + 1) > θ_k/(λ̄_k + 1)
  --   = 2 · 3^{k−1}/(3^{k−1} + 1) · t_{k−1} ≥ t_{k−1}`."
  have hlb : (0 : ℝ) < (lamBar k : ℝ) + 1 := by
    have := lamBar_nonneg k
    have : (0 : ℝ) ≤ lamBar k := by exact_mod_cast this
    linarith
  have hfl : ((D k : ℝ) + 1 + theta k + thetaBar k) / ((lamBar k : ℝ) + 1) < t k := by
    rw [t_eq (by omega)]
    push_cast
    exact Int.lt_floor_add_one _
  have hlt : (theta k : ℝ) / ((lamBar k : ℝ) + 1) <
      ((D k : ℝ) + 1 + theta k + thetaBar k) / ((lamBar k : ℝ) + 1) := by
    have : (0 : ℝ) ≤ D k := by exact_mod_cast hD
    have : (0 : ℝ) ≤ thetaBar k := by exact_mod_cast hθbar
    exact div_lt_div_of_pos_right (by linarith) hlb
  have hlbeq : (lamBar k : ℝ) + 1 = (3 ^ (k - 1) + 1) / 2 := by
    rw [lamBar_eq (by omega)]; ring
  have heq : (theta k : ℝ) / ((lamBar k : ℝ) + 1) =
      2 * 3 ^ (k - 1) / (3 ^ (k - 1) + 1) * t (k - 1) := by
    rw [hlbeq, hθk]
    simp only [lam]
    push_cast
    field_simp
  have hge : (t (k - 1) : ℝ) ≤ 2 * 3 ^ (k - 1) / (3 ^ (k - 1) + 1) * t (k - 1) := by
    have h3 : (1 : ℝ) ≤ 3 ^ (k - 1) := one_le_pow₀ (by norm_num)
    have ht : (0 : ℝ) ≤ t (k - 1) := by
      have := h2 (k - 1) (by omega) le_rfl
      exact_mod_cast (show (0 : ℤ) ≤ t (k - 1) by linarith)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have : (t (k - 1) : ℝ) < t k := by linarith
  exact_mod_cast this

/-- **`prop:witness` (i)**, the induction on `k` (`appC-bits.tex:155-166`): for every
`k ∈ {1, …, n}`, `2 = t_1 < ⋯ < t_k`, and `d_i^{(j)} ≥ 0` for all `i < j ≤ k`. The base `k = 1` is
`t_one`, and the step (here from `k` to `k + 1 ≤ n`, the paper's step from `k − 1` to
`k ∈ {2, …, n}`) is `step_i`; "This shows that `t` is strictly increasing and that
`d_i^{(k)} ≥ 0` for all `i < k`." -/
lemma claim_i {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    t 1 = 2 ∧ (∀ j, 1 ≤ j → j < k → t j < t (j + 1)) ∧
      ∀ i j, 1 ≤ i → i < j → j ≤ k → 0 ≤ d i j := by
  induction k, hk using Nat.le_induction with
  | base =>
    -- "For `k = 1`, we have `D_1 = θ_1 = θ̄_1 = λ̄_1 = 0`, so `t_1 = ⌊1⌋ + 1 = 2`."
    exact ⟨t_one, fun j hj hj1 => absurd hj1 (by omega),
      fun i j hi hij hj1 => absurd hij (by omega)⟩
  | succ k hk ih =>
    -- "Let `k ∈ {2, …, n}` and assume that `t_1 < ⋯ < t_{k−1}`." (here `k + 1` is the paper's
    -- `k`)
    obtain ⟨h1, hchain, hd⟩ := ih (by omega)
    obtain ⟨hdk, hlt⟩ :=
      step_i (k := k + 1) (by omega) hkn h1 fun j hj hjk => hchain j hj (by omega)
    -- "This shows that `t` is strictly increasing and that `d_i^{(k)} ≥ 0` for all `i < k`."
    refine ⟨h1, fun j hj hjk => ?_, fun i j hi hij hjk => ?_⟩
    · rcases (show j < k ∨ j = k by omega) with h | rfl
      · exact hchain j hj h
      · simpa using hlt
    · rcases (show j ≤ k ∨ j = k + 1 by omega) with h | rfl
      · exact hd i j hi hij h
      · exact hdk i hi hij

/-- The step of the upper bound of `prop:witness` (i) (`appC-bits.tex:167-184`): for
`k ∈ {2, …, n}`, `t_k ≤ (2k + 2) t_{k−1}`. The facts on `t` and `d` are those of the first part of
(i) (`claim_i`).

The paper's steps: (1) `0 ≤ d_i^{(k)} ≤ θ_k = 3^{k−1} t_{k−1}` for all `i < k`, so
`D_k ≤ (k − 1) 3^{k−1} t_{k−1}`; (2) as `t` is increasing,
`θ̄_k = ∑_{j=2}^{k−1} 3^{j−1} t_{j−1} ≤ t_{k−1} ∑_{j=2}^{k−1} 3^{j−1} = (3^{k−1} − 3)/2 · t_{k−1}`;
(3) adding these bounds and using `t_{k−1} ≥ 2`,
`D_k + 1 + θ_k + θ̄_k ≤ (k + 1/2) 3^{k−1} t_{k−1} + 1 − 3/2 · t_{k−1}
≤ (k + 1/2) 3^{k−1} t_{k−1}`; (4) as `λ̄_k + 1 = (3^{k−1} + 1)/2` and `t_{k−1} ≥ 1`,
`t_k ≤ (2k + 1) 3^{k−1}/(3^{k−1} + 1) · t_{k−1} + 1 < (2k + 1) t_{k−1} + 1 ≤ (2k + 2) t_{k−1}`. -/
lemma t_le_mul {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) : t k ≤ (2 * k + 2) * t (k - 1) := by
  -- "For the upper bound, let `k ∈ {2, …, n}`." The first part of (i): `2 = t_1 < ⋯ < t_k`, and
  -- `d_i^{(k)} ≥ 0` for all `i < k`.
  obtain ⟨h1, hchain, hdnn⟩ := claim_i (k := k) (by omega) hkn
  have h2 : ∀ i, 1 ≤ i → i ≤ k → 2 ≤ t i := fun i hi hik => by
    rcases hi.lt_or_eq with h | rfl
    · have := chain_lt hchain le_rfl h hik
      linarith
    · exact h1.ge
  have htk1 : 2 ≤ t (k - 1) := h2 (k - 1) (by omega) (by omega)
  have hθk := theta_of_two_le hk
  -- (1) "Then `0 ≤ d_i^{(k)} ≤ θ_k = 3^{k−1} t_{k−1}` for all `i < k`, so
  -- `D_k ≤ (k − 1) 3^{k−1} t_{k−1}`,"
  have hdle : ∀ i ∈ Ico 1 k, 0 ≤ d i k ∧ d i k ≤ theta k := fun i hi => by
    obtain ⟨hi1, hik⟩ := mem_Ico.1 hi
    have : 0 ≤ lam k * t i := mul_nonneg (lam_pos k).le (by linarith [h2 i hi1 hik.le])
    refine ⟨hdnn i k hi1 hik le_rfl, ?_⟩
    rw [d]
    linarith
  have hD : (D k : ℝ) ≤ (k - 1) * (lam k * t (k - 1)) := by
    have h1 : D k ≤ ∑ _i ∈ Ico 1 k, theta k := sum_le_sum fun i hi => (hdle i hi).2
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, hθk] at h1
    have h1' : (D k : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * (lam k * t (k - 1)) := by exact_mod_cast h1
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h1'
  -- (2) "and as `t` is increasing,
  -- `θ̄_k = ∑_{j=2}^{k−1} 3^{j−1} t_{j−1} ≤ t_{k−1} ∑_{j=2}^{k−1} 3^{j−1}
  --   = (3^{k−1} − 3)/2 · t_{k−1}`."
  have hθbar : thetaBar k = ∑ j ∈ Ico 2 k, lam j * t (j - 1) := by
    rw [thetaBar, ← sum_Ico_consecutive _ (show 1 ≤ 2 by norm_num) hk]
    simp only [Nat.Ico_succ_singleton, sum_singleton, theta_one, zero_add]
    exact sum_congr rfl fun j hj => theta_of_two_le (mem_Ico.1 hj).1
  have hθbar_le : thetaBar k ≤ t (k - 1) * ∑ j ∈ Ico 2 k, lam j := by
    rw [hθbar, mul_sum]
    refine sum_le_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := mem_Ico.1 hj
    rw [mul_comm (t (k - 1))]
    exact mul_le_mul_of_nonneg_left
      (chain_lt hchain (i := j - 1) (j := k - 1) (by omega) (by omega) (by omega)).le
      (lam_pos j).le
  have hsum : ((∑ j ∈ Ico 2 k, lam j : ℤ) : ℝ) = (3 ^ (k - 1) - 3) / 2 := by
    have h1 : ∑ j ∈ Ico 2 k, lam j = lamBar k - lam 1 := by
      rw [lamBar, ← sum_Ico_consecutive _ (show 1 ≤ 2 by norm_num) hk]
      simp
    rw [h1]
    push_cast
    rw [lamBar_eq (by omega)]
    simp [lam]
    ring
  -- (3) "Adding these bounds and using `t_{k−1} ≥ 2`, we get
  -- `D_k + 1 + θ_k + θ̄_k ≤ (k + 1/2) 3^{k−1} t_{k−1} + 1 − 3/2 · t_{k−1}
  --   ≤ (k + 1/2) 3^{k−1} t_{k−1}`."
  have hlam : (lam k : ℝ) = 3 ^ (k - 1) := by simp [lam]
  have htk1' : (2 : ℝ) ≤ t (k - 1) := by exact_mod_cast htk1
  have hN : (D k : ℝ) + 1 + theta k + thetaBar k ≤ (k + 1 / 2) * 3 ^ (k - 1) * t (k - 1) := by
    have h1 : (thetaBar k : ℝ) ≤ t (k - 1) * ((3 ^ (k - 1) - 3) / 2) := by
      rw [← hsum]; exact_mod_cast hθbar_le
    have h2 : (theta k : ℝ) = 3 ^ (k - 1) * t (k - 1) := by rw [hθk]; push_cast; rw [hlam]
    rw [hlam] at hD
    calc (D k : ℝ) + 1 + theta k + thetaBar k
        ≤ (k + 1 / 2) * 3 ^ (k - 1) * t (k - 1) + 1 - 3 / 2 * t (k - 1) := by
          rw [h2]
          nlinarith
      _ ≤ (k + 1 / 2) * 3 ^ (k - 1) * t (k - 1) := by linarith
  -- (4) "As `λ̄_k + 1 = (3^{k−1} + 1)/2` and `t_{k−1} ≥ 1`, it follows that
  -- `t_k ≤ (2k + 1) 3^{k−1}/(3^{k−1} + 1) · t_{k−1} + 1 < (2k + 1) t_{k−1} + 1
  --   ≤ (2k + 2) t_{k−1}`."
  have hlb : (lamBar k : ℝ) + 1 = (3 ^ (k - 1) + 1) / 2 := by rw [lamBar_eq (by omega)]; ring
  have h3 : (0 : ℝ) < 3 ^ (k - 1) := by positivity
  have hfl : (t k : ℝ) ≤ ((D k : ℝ) + 1 + theta k + thetaBar k) / ((lamBar k : ℝ) + 1) + 1 := by
    rw [t_eq (by omega)]
    push_cast
    exact add_le_add_left (Int.floor_le _) 1
  have h4 : ((D k : ℝ) + 1 + theta k + thetaBar k) / ((lamBar k : ℝ) + 1) + 1 ≤
      (2 * k + 1) * 3 ^ (k - 1) / (3 ^ (k - 1) + 1) * t (k - 1) + 1 := by
    rw [hlb]
    have : ((D k : ℝ) + 1 + theta k + thetaBar k) / ((3 ^ (k - 1) + 1) / 2) ≤
        (k + 1 / 2) * 3 ^ (k - 1) * t (k - 1) / ((3 ^ (k - 1) + 1) / 2) :=
      div_le_div_of_nonneg_right hN (by positivity)
    have heq : (k + 1 / 2) * 3 ^ (k - 1) * t (k - 1) / ((3 ^ (k - 1) + 1) / 2) =
        (2 * k + 1) * 3 ^ (k - 1) / (3 ^ (k - 1) + 1) * (t (k - 1) : ℝ) := by
      field_simp
    linarith
  have h5 : (2 * k + 1) * 3 ^ (k - 1) / (3 ^ (k - 1) + 1) * (t (k - 1) : ℝ) + 1 <
      (2 * k + 1) * t (k - 1) + 1 := by
    have h6 : (2 * k + 1) * 3 ^ (k - 1) / (3 ^ (k - 1) + 1) < (2 * (k : ℝ) + 1) := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have h7 : (2 * (k : ℝ) + 1) * t (k - 1) + 1 ≤ (2 * k + 2) * t (k - 1) := by nlinarith
  have : (t k : ℝ) ≤ (2 * k + 2) * t (k - 1) := by linarith
  exact_mod_cast this

/-- The last step of `prop:witness` (i) (`appC-bits.tex:185-186`): "Hence
`t_n ≤ t_1 ∏_{k=2}^n (2k + 2) ≤ 2 (2n + 2)^{n−1}`", from `t_k ≤ (2k + 2) t_{k−1}` for
`k ∈ {2, …, n}` (`t_le_mul`). -/
lemma t_le_pow {n : ℕ} (hn : 1 ≤ n) : t n ≤ 2 * (2 * n + 2) ^ (n - 1) := by
  have hprod : ∀ m, 1 ≤ m → m ≤ n → t m ≤ t 1 * ∏ k ∈ Ico 2 (m + 1), ((2 * k + 2 : ℕ) : ℤ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; simp
    | succ m hm ih =>
      intro hmn
      rw [prod_Ico_succ_top (by omega)]
      have h := t_le_mul (k := m + 1) (by omega) hmn
      simp only [Nat.add_sub_cancel] at h
      have hpos : (0 : ℤ) ≤ ((2 * (m + 1) + 2 : ℕ) : ℤ) := Nat.cast_nonneg _
      calc t (m + 1) ≤ (2 * ((m + 1 : ℕ) : ℤ) + 2) * t m := h
        _ = ((2 * (m + 1) + 2 : ℕ) : ℤ) * t m := by push_cast; ring
        _ ≤ ((2 * (m + 1) + 2 : ℕ) : ℤ) * (t 1 * ∏ k ∈ Ico 2 (m + 1), ((2 * k + 2 : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hpos
        _ = _ := by ring
  have hbound : ∏ k ∈ Ico 2 (n + 1), (2 * k + 2 : ℕ) ≤ (2 * n + 2) ^ (n - 1) := by
    have h := prod_le_pow_card (Ico 2 (n + 1)) (fun k => 2 * k + 2) (2 * n + 2)
      fun k hk => by have := (mem_Ico.1 hk).2; omega
    rwa [Nat.card_Ico, show n + 1 - 2 = n - 1 by omega] at h
  have hbound' : ∏ k ∈ Ico 2 (n + 1), ((2 * k + 2 : ℕ) : ℤ) ≤ (2 * n + 2) ^ (n - 1) := by
    have : ((∏ k ∈ Ico 2 (n + 1), (2 * k + 2 : ℕ) : ℕ) : ℤ) ≤ (((2 * n + 2) ^ (n - 1) : ℕ) : ℤ) :=
      by exact_mod_cast hbound
    push_cast at this ⊢
    exact this
  calc t n ≤ t 1 * ∏ k ∈ Ico 2 (n + 1), ((2 * k + 2 : ℕ) : ℤ) := hprod n hn le_rfl
    _ ≤ 2 * (2 * n + 2) ^ (n - 1) := by rw [t_one]; linarith

/-! #### `prop:witness` (ii): the ground sets `E_k = {1, …, k}` -/

/-- `E_k = {1, …, k}` as `Fin k`: the element `i : Fin k` is the paper's element `i + 1`. -/
def emb (k : ℕ) : Fin k ↪ ℕ := ⟨fun i => (i : ℕ) + 1, fun i j h => Fin.ext (by simpa using h)⟩

@[simp] lemma emb_apply (k : ℕ) (i : Fin k) : emb k i = (i : ℕ) + 1 := rfl

/-- `g_k`, the restriction of `g` to `2^{E_k}`, with real values. -/
noncomputable def gE (k : ℕ) (S : Finset (Fin k)) : ℝ := g (S.map (emb k))

/-- `t = (t_1, …, t_k)` on `E_k`. -/
noncomputable def tE (k : ℕ) (i : Fin k) : ℝ := t (emb k i)

/-- The witness `(λ_S, θ_S) = ∑_{k ∈ S} (λ_k, θ_k)` of `S ⊆ E_k`. -/
noncomputable def wit (k : ℕ) (S : Finset (Fin k)) : ℝ × ℝ :=
  ∑ j ∈ S.map (emb k), ((lam j : ℝ), (theta j : ℝ))

/-- `E_{k+1} = E_k ∪ {k + 1}` as `Option (Fin k) ≃ Fin (k + 1)`: the new element `none` of
`cor:witness` is the paper's `k + 1`. -/
def ext (k : ℕ) : Option (Fin k) ≃ Fin (k + 1) := finSuccEquivLast.symm

lemma emb_ext_none (k : ℕ) : emb (k + 1) (ext k none) = k + 1 := by
  simp [ext]

lemma emb_ext_some (k : ℕ) (i : Fin k) : emb (k + 1) (ext k (some i)) = emb k i := by
  simp [ext, finSuccEquivLast_symm_some]

lemma lt_of_mem_map_emb {k j : ℕ} {S : Finset (Fin k)} (hj : j ∈ S.map (emb k)) :
    1 ≤ j ∧ j < k + 1 := by
  obtain ⟨i, -, rfl⟩ := mem_map.1 hj
  have := i.isLt
  simp only [emb_apply]
  omega

lemma map_ext_some (k : ℕ) (S : Finset (Fin k)) :
    ((S.map Function.Embedding.some).map (ext k).toEmbedding).map (emb (k + 1)) =
      S.map (emb k) := by
  ext j
  simp only [mem_map, Equiv.coe_toEmbedding, Function.Embedding.some_apply]
  constructor
  · rintro ⟨x, ⟨o, ⟨i, hi, rfl⟩, rfl⟩, rfl⟩
    exact ⟨i, hi, (emb_ext_some k i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨ext k (some i), ⟨some i, ⟨i, hi, rfl⟩, rfl⟩, emb_ext_some k i⟩

lemma map_ext_insertNone (k : ℕ) (S : Finset (Fin k)) :
    ((insertNone S).map (ext k).toEmbedding).map (emb (k + 1)) =
      insert (k + 1) (S.map (emb k)) := by
  ext j
  simp only [mem_map, mem_insert, Equiv.coe_toEmbedding, mem_insertNone]
  constructor
  · rintro ⟨x, ⟨o, ho, rfl⟩, rfl⟩
    rcases o with _ | i
    · exact Or.inl (emb_ext_none k)
    · exact Or.inr ⟨i, by simpa using ho, (emb_ext_some k i).symm⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨ext k none, ⟨none, by simp, rfl⟩, emb_ext_none k⟩
    · exact ⟨ext k (some i), ⟨some i, by simpa using hi, rfl⟩, emb_ext_some k i⟩

/-- A witness carries over along a bijection of the ground sets. -/
lemma isWitness_map {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (φ : α ≃ β) {G : Finset α → ℝ} {T : α → ℝ} {G' : Finset β → ℝ} {T' : β → ℝ}
    (hG : ∀ X, G' X = G (X.map φ.symm.toEmbedding)) (hT : ∀ b, T' b = T (φ.symm b))
    {w : ℝ × ℝ} {S : Finset α} (h : IsWitness G T w S) :
    IsWitness G' T' w (S.map φ.toEmbedding) := by
  have hF : ∀ X, F G' T' w X = F G T w (X.map φ.symm.toEmbedding) := fun X => by
    simp only [F, hG, hT, sum_map, card_map, Equiv.coe_toEmbedding]
  have hS : (S.map φ.toEmbedding).map φ.symm.toEmbedding = S := by simp [map_map]
  intro X hX
  rw [hF, hF, hS]
  exact h _ fun h' => hX (by rw [← h']; simp [map_map])

/-- The check "the function `g'` of the corollary is `g_k`" of the proof of `prop:witness` (ii):
for `S ⊆ E_{k−1}`, the pairs of elements of `S ∪ {k}` that contain `k` are the pairs `{i, k}` with
`i ∈ S`, all with `i < k`, so `g(S ∪ {k}) = g(S) + K_k − ∑_{i ∈ S} d_i^{(k)}`. -/
lemma g_insert {k : ℕ} {S : Finset ℕ} (hS : ∀ i ∈ S, i < k) :
    g (insert k S) = g S + K k - ∑ i ∈ S, d i k := by
  have hk : k ∉ S := fun h => lt_irrefl k (hS k h)
  have h1 : (insert k S).filter (· < k) = S := by
    rw [filter_insert]
    split_ifs with h
    · exact absurd h (lt_irrefl k)
    · exact filter_true_of_mem hS
  have h2 : ∀ j ∈ S, (insert k S).filter (· < j) = S.filter (· < j) := fun j hj => by
    rw [filter_insert]
    split_ifs with h
    · exact absurd h (not_lt.2 (hS j hj).le)
    · rfl
  have h3 : ∑ j ∈ S, ∑ i ∈ (insert k S).filter (· < j), d i j =
      ∑ j ∈ S, ∑ i ∈ S.filter (· < j), d i j := sum_congr rfl fun j hj => by rw [h2 j hj]
  unfold g
  rw [sum_insert hk, sum_insert hk, h1, h3]
  ring

/-- The claim `(C_k)` of the proof of `prop:witness` (ii) (`appC-bits.tex:188-192`): `g_k` (`gE k`,
the restriction of `g` to `2^{E_k}`, `E_k = {1, …, k}` being `Fin k`) is submodular with
`g_k(∅) = 0`, and every `S ⊆ E_k` has the witness `(λ_S, θ_S)` (`wit k S`) for `g_k`, with respect
to `(t_1, …, t_k)` (`tE k`). -/
def ClaimC (k : ℕ) : Prop :=
  (Submodular (gE k) ∧ gE k ∅ = 0) ∧ ∀ S : Finset (Fin k), IsWitness (gE k) (tE k) (wit k S) S

/-- **`prop:witness` (ii)**, the induction on `k` (`appC-bits.tex:188-218`): `(C_k)` (`ClaimC k`)
holds for every `k ∈ {0, …, n}`, from the first part of (i) for `n` (the hypothesis `hi`:
`2 = t_1 < ⋯ < t_n` and `d_i^{(k)} ≥ 0` for all `i < k ≤ n`). The step goes from `k` to `k + 1`
(the paper's step from `k − 1` to `k ∈ {1, …, n}`), with `E_{k+1} = E_k ∪ {k + 1}` as
`Option (Fin k) ≃ Fin (k + 1)` (`ext`).

The paper's steps: (1) for `k = 0`, the only set is `∅`, `g_0(∅) = 0`, and `(0, 0)` is a witness of
`∅`; (2) for `k ∈ {1, …, n}`, assuming `(C_{k−1})`, `cor:witness` (`witness_step`) is applied to
`E_{k−1}`, `g_{k−1}`, the family `2^{E_{k−1}}` with the witnesses
`(λ_S, θ_S) ∈ [0, λ̄_k] × [0, θ̄_k]`, `b = k`, `t_b = t_k`, `ŵ = (λ_k, θ_k)` and `K = K_k`; (3) its
hypotheses: `d = θ_k 1 − λ_k t` is the vector `(d_i^{(k)})_{i<k}`, nonnegative by (i), with
`d(E_{k−1}) = D_k`; (4) the left inequality of the window (`eq:C-window`) holds as
`K_k = t_k λ̄_k + D_k + 1`; (5) as `λ_k = 2 λ̄_k + 1`, its right inequality is equivalent to
`D_k + 1 + θ_k + θ̄_k < t_k (λ̄_k + 1)`, which holds by the definition of `t_k`; (6) the function
`g'` of the corollary is `g_k` (`g_insert`); (7) by the corollary, `g_k` is submodular with
`g_k(∅) = 0`, every `S ⊆ E_{k−1}` has the witness `(λ_S, θ_S)` and `S ∪ {k}` the witness
`(λ_S, θ_S) + (λ_k, θ_k) = (λ_{S∪{k}}, θ_{S∪{k}})`, which is `(C_k)`. -/
lemma claim_ii {n : ℕ} (hi : t 1 = 2 ∧ (∀ k, 1 ≤ k → k < n → t k < t (k + 1)) ∧
      ∀ i k, 1 ≤ i → i < k → k ≤ n → 0 ≤ d i k) (k : ℕ) (hkn : k ≤ n) : ClaimC k := by
  obtain ⟨h1, hchain, hdnn⟩ := hi
  -- the facts of (i) used below: `t_i > 0` and `θ_i ≥ 0` for `1 ≤ i ≤ n`
  have htpos : ∀ i, 1 ≤ i → i ≤ n → 0 < t i := fun i hi1 hin => by
    rcases hi1.lt_or_eq with h | rfl
    · have := chain_lt hchain le_rfl h hin
      linarith
    · linarith
  have hθnn : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ theta j := fun j hj hjn => by
    rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
    · rw [theta_one]
    · rw [theta_of_two_le hj2]
      exact mul_nonneg (lam_pos j).le (htpos (j - 1) (by omega) (by omega)).le
  -- "We prove `(C_k)` for all `k ∈ {0, …, n}` by induction on `k`."
  induction k with
  | zero =>
    -- (1) "For `k = 0`, the only set is `∅`, `g_0(∅) = 0`, and `(λ_∅, θ_∅) = (0, 0)` is a witness
    -- of `∅`."
    have hsub : ∀ X : Finset (Fin 0), X = ∅ := fun X => eq_empty_of_forall_notMem fun i => i.elim0
    refine ⟨⟨fun X Y => by rw [hsub X, hsub Y]; simp, by simp [gE, g]⟩, fun S T hTS => ?_⟩
    exact absurd ((hsub T).trans (hsub S).symm) hTS
  | succ k ih =>
    -- "Let `k ∈ {1, …, n}` and assume `(C_{k−1})`." (here `k + 1` is the paper's `k`)
    obtain ⟨⟨hsub, h0⟩, hwit⟩ := ih (by omega)
    set tb : ℝ := (t (k + 1) : ℝ)
    -- `ŵ := (λ_k, θ_k)`, with the coordinates `lhat` and `θhat`
    set lhat : ℝ := (lam (k + 1) : ℝ)
    set θhat : ℝ := (theta (k + 1) : ℝ)
    set Kb : ℝ := (K (k + 1) : ℝ)
    -- (2) "We apply `cor:witness` to `E_{k−1}`, `g_{k−1}`, the family `𝓕 := 2^{E_{k−1}}` with the
    -- witnesses `(λ_S, θ_S)`, which lie in `[0, λ̄_k] × [0, θ̄_k]` as `S ⊆ E_{k−1}`, the new
    -- element `b := k` with `t_b := t_k`, `ŵ := (λ_k, θ_k)` and `K := K_k`." (Its `t > 0` and
    -- `t_b > 0` are those of (i).)
    have ht : ∀ i, 0 < tE k i := fun i => by
      have := lt_of_mem_map_emb (S := {i}) (j := emb k i) (by simp)
      simp only [tE]
      exact_mod_cast htpos (emb k i) this.1 (by omega)
    have htb : (0 : ℝ) < tb := by
      simp only [tb]
      exact_mod_cast htpos (k + 1) (by omega) hkn
    have hw : ∀ S ∈ (Set.univ : Set (Finset (Fin k))), IsWitness (gE k) (tE k) (wit k S) S ∧
        (wit k S).1 ∈ Set.Icc 0 (lamBar (k + 1) : ℝ) ∧
        (wit k S).2 ∈ Set.Icc 0 (thetaBar (k + 1) : ℝ) := by
      intro S _
      have hsubS : S.map (emb k) ⊆ Ico 1 (k + 1) := fun j hj => by
        have := lt_of_mem_map_emb hj
        exact mem_Ico.2 this
      refine ⟨hwit S, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simp only [wit, Prod.fst_sum]
        exact sum_nonneg fun j _ => by exact_mod_cast (lam_pos j).le
      · simp only [wit, Prod.fst_sum, lamBar]
        push_cast
        exact sum_le_sum_of_subset_of_nonneg hsubS fun j _ _ => by exact_mod_cast (lam_pos j).le
      · simp only [wit, Prod.snd_sum]
        exact sum_nonneg fun j hj => by
          have := lt_of_mem_map_emb hj
          exact_mod_cast hθnn j this.1 (by omega)
      · simp only [wit, Prod.snd_sum, thetaBar]
        push_cast
        exact sum_le_sum_of_subset_of_nonneg hsubS fun j hj _ => by
          have := mem_Ico.1 hj
          exact_mod_cast hθnn j this.1 (by omega)
    have hθbar : (0 : ℝ) ≤ thetaBar (k + 1) := by
      exact_mod_cast sum_nonneg fun j hj => hθnn j (mem_Ico.1 hj).1 (by have := mem_Ico.1 hj; omega)
    -- (3) "Its hypotheses hold. Indeed, `d = θ_k 1 − λ_k t` is the vector `(d_i^{(k)})_{i<k}`,
    -- which is nonnegative by (i) and satisfies `d(E_{k−1}) = D_k`."
    have hdvec : ∀ i, θhat - lhat * tE k i = (d (emb k i) (k + 1) : ℝ) := fun i => by
      simp [θhat, lhat, tE, d]
    have hd : ∀ i, 0 ≤ θhat - lhat * tE k i := fun i => by
      rw [hdvec]
      have := lt_of_mem_map_emb (S := {i}) (j := emb k i) (by simp)
      exact_mod_cast hdnn (emb k i) (k + 1) this.1 this.2 hkn
    have hdE : ∑ i, (θhat - lhat * tE k i) = (D (k + 1) : ℝ) := by
      simp only [hdvec, emb_apply, D]
      push_cast
      rw [Fin.sum_univ_eq_sum_range (fun i => (d (i + 1) (k + 1) : ℝ)) k, sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      exact sum_congr rfl fun i _ => by rw [add_comm]
    -- (4) "So the window (`eq:C-window`) reads `t_k λ̄_k + D_k < K_k < t_k λ_k − θ̄_k − θ_k`. Its
    -- left inequality holds as `K_k = t_k λ̄_k + D_k + 1`."
    have hwin1 : tb * (lamBar (k + 1) : ℝ) + ∑ i, (θhat - lhat * tE k i) < Kb := by
      rw [hdE]
      simp only [tb, Kb, K]
      push_cast
      linarith
    -- (5) "As `λ_k = 2 λ̄_k + 1`, its right inequality is equivalent to
    -- `D_k + 1 + θ_k + θ̄_k < t_k (λ̄_k + 1)`, which holds by the definition of `t_k`, as
    -- `⌊x⌋ + 1 > x`."
    have hwin2 : Kb < tb * lhat - (thetaBar (k + 1) : ℝ) - θhat := by
      have hlamb : lhat = 2 * (lamBar (k + 1) : ℝ) + 1 := by
        simp only [lhat]
        exact_mod_cast lam_eq (by omega)
      have hlb : (0 : ℝ) < (lamBar (k + 1) : ℝ) + 1 := by
        have : (0 : ℝ) ≤ lamBar (k + 1) := by exact_mod_cast lamBar_nonneg (k + 1)
        linarith
      have hfl : ((D (k + 1) : ℝ) + 1 + theta (k + 1) + thetaBar (k + 1)) /
          ((lamBar (k + 1) : ℝ) + 1) < t (k + 1) := by
        rw [t_eq (by omega)]
        push_cast
        exact Int.lt_floor_add_one _
      rw [div_lt_iff₀ hlb] at hfl
      rw [hlamb]
      simp only [Kb, K, tb, θhat]
      push_cast
      nlinarith
    obtain ⟨⟨hsub', h0'⟩, hstep⟩ := witness_step hsub h0 ht
      (by exact_mod_cast lamBar_nonneg (k + 1) : (0 : ℝ) ≤ lamBar (k + 1)) hθbar hw htb hd hwin1
      hwin2
    -- (6) "Moreover, the function `g'` of the corollary is `g_k`: for `S ⊆ E_{k−1}`, …
    -- `g(S ∪ {k}) = g(S) + K_k − ∑_{i∈S} d_i^{(k)} = g(S) + K_k − d(S)`" (`g_insert`).
    have hgk : ∀ X : Finset (Fin (k + 1)),
        gE (k + 1) X =
          extG (gE k) (fun i => θhat - lhat * tE k i) Kb (X.map (ext k).symm.toEmbedding) := by
      intro X
      set T := X.map (ext k).symm.toEmbedding with hT_def
      have hX : X = T.map (ext k).toEmbedding := by simp [T, map_map]
      rw [show gE (k + 1) X = g ((T.map (ext k).toEmbedding).map (emb (k + 1))) by rw [← hX]; rfl]
      by_cases hT : none ∈ T
      · rw [eq_insertNone hT, map_ext_insertNone, g_insert fun i hi => (lt_of_mem_map_emb hi).2]
        simp only [extG, none_mem_insertNone, ↓reduceIte, eraseNone_insertNone, gE, hdvec, Kb]
        push_cast
        rw [sum_map]
      · rw [eq_map_some hT, map_ext_some]
        have hn : none ∉ (eraseNone T).map Function.Embedding.some := by simp
        simp only [extG, gE, eraseNone_map_some, hn, ↓reduceIte]
    -- (7) "By the corollary, `g_k` is submodular with `g_k(∅) = 0`, every `S ⊆ E_{k−1}` has the
    -- witness `(λ_S, θ_S)` for `g_k`, and `S ∪ {k}` has the witness
    -- `(λ_S, θ_S) + (λ_k, θ_k) = (λ_{S∪{k}}, θ_{S∪{k}})`."
    have htE : ∀ b, tE (k + 1) b = extT (tE k) tb ((ext k).symm b) := fun b => by
      obtain ⟨o, rfl⟩ := (ext k).surjective b
      rcases o with _ | i
      · simp only [tE, extT, Equiv.symm_apply_apply, Option.elim]
        rw [emb_ext_none]
      · simp only [tE, extT, Equiv.symm_apply_apply, Option.elim]
        rw [emb_ext_some]
    refine ⟨⟨fun X Y => ?_, ?_⟩, fun S => ?_⟩
    · rw [hgk, hgk, hgk, hgk, map_union, map_inter]
      exact hsub' _ _
    · rw [hgk]
      simpa using h0'
    · set T := S.map (ext k).symm.toEmbedding with hT_def
      have hS : S = T.map (ext k).toEmbedding := by simp [T, map_map]
      by_cases hT : none ∈ T
      · have hw' : wit (k + 1) ((insertNone (eraseNone T)).map (ext k).toEmbedding) =
            wit k (eraseNone T) + (lhat, θhat) := by
          have hk : k + 1 ∉ (eraseNone T).map (emb k) := fun h =>
            lt_irrefl (k + 1) (lt_of_mem_map_emb h).2
          rw [wit, map_ext_insertNone, sum_insert hk, add_comm]
          rfl
        rw [hS, eq_insertNone hT, hw']
        exact isWitness_map (ext k) hgk htE (hstep _ trivial).2
      · have hw' : wit (k + 1) (((eraseNone T).map Function.Embedding.some).map
            (ext k).toEmbedding) = wit k (eraseNone T) := by
          rw [wit, map_ext_some]
          rfl
        rw [hS, eq_map_some hT, hw']
        exact isWitness_map (ext k) hgk htE (hstep _ trivial).1

/-- **`prop:witness`** (Proposition B.16, statement `stoc-sections/appC-bits.tex:126-152`, proof
`appC-bits.tex:154-219`). Let `n ≥ 1`, let the integers `λ_k`, `λ̄_k`, `θ_k`, `θ̄_k`, `d_i^{(k)}`,
`D_k`, `t_k` and `K_k` be defined recursively for `k = 1, …, n` (`lam`, `lamBar`, `theta`,
`thetaBar`, `d`, `D`, `t` with `t_eq`, `K`), let `E = {1, …, n}` (here `Fin n`, the element `i`
being the paper's `i + 1`) and `g(S) = ∑_{k∈S} K_k − ∑_{i,k∈S, i<k} d_i^{(k)}` (`g`, on `E`:
`gE n`). Then
(i) `2 = t_1 < t_2 < ⋯ < t_n ≤ 2(2n + 2)^{n−1}`, and `d_i^{(k)} ≥ 0` for all `i < k`;
(ii) `g` is submodular with `g(∅) = 0`, and every `S ⊆ E` has the witness
`(λ_S, θ_S) = ∑_{k∈S} (λ_k, θ_k)` (`wit n S`) for `g` with respect to `t = (t_1, …, t_n)`.

The paper's steps: (i) by induction on `k ∈ {1, …, n}` (`claim_i`): `t_1 = 2` (`t_one`), and for
`k ∈ {2, …, n}` from `t_1 < ⋯ < t_{k−1}` follow `d_i^{(k)} ≥ 0` and `t_{k−1} < t_k` (`step_i`); then
the upper bound `t_k ≤ (2k + 2) t_{k−1}` for `k ∈ {2, …, n}` (`t_le_mul`) and
`t_n ≤ t_1 ∏_{k=2}^n (2k + 2) ≤ 2(2n + 2)^{n−1}` (`t_le_pow`); (ii) the claim `(C_k)` (`ClaimC k`)
for all `k ∈ {0, …, n}`, by induction on `k` over `E_k = {1, …, k}` with `cor:witness`, from (i)
(`claim_ii`), and as `E_n = E` and `g_n = g` (in the Lean by definition: `Fin n` and `gE n`), the
claim `(C_n)` is (ii). -/
theorem witness (n : ℕ) (hn : 1 ≤ n) :
    (t 1 = 2 ∧ (∀ k, 1 ≤ k → k < n → t k < t (k + 1)) ∧ t n ≤ 2 * (2 * n + 2) ^ (n - 1) ∧
      ∀ i k, 1 ≤ i → i < k → k ≤ n → 0 ≤ d i k) ∧
    ((Submodular (gE n) ∧ gE n ∅ = 0) ∧
      ∀ S : Finset (Fin n), IsWitness (gE n) (tE n) (wit n S) S) := by
  -- (i) "We first prove (i), by induction on `k`" (`claim_i` for `k = n`): `2 = t_1 < ⋯ < t_n`
  -- and `d_i^{(k)} ≥ 0` for all `i < k ≤ n`; "For the upper bound, let `k ∈ {2, …, n}`. … Hence
  -- `t_n ≤ t_1 ∏_{k=2}^n (2k + 2) ≤ 2(2n + 2)^{n−1}`, which completes the proof of (i)."
  -- (`t_le_mul`, `t_le_pow`)
  obtain ⟨h1, hchain, hd⟩ := claim_i hn le_rfl
  refine ⟨⟨h1, hchain, t_le_pow hn, hd⟩, ?_⟩
  -- (ii) "We prove `(C_k)` for all `k ∈ {0, …, n}` by induction on `k`" (`claim_ii`). "This proves
  -- `(C_k)` for all `k ∈ {0, …, n}`. As `E_n = E` and `g_n = g`, the claim `(C_n)` is (ii)."
  exact claim_ii ⟨h1, hchain, hd⟩ n le_rfl

/-! ### The facts of `prop:witness` (i) that the proof of `thm:polybits` uses

Where the proof of `thm:polybits` uses that `t > 0`, `d ≥ 0` or `θ ≥ 0` without citing
`prop:witness`, these facts are read off `witness` (for `n = k`). -/

/-- `t_k ≥ 2` for `k ≥ 1`: `2 = t_1 < ⋯ < t_k` by `prop:witness` (i) (`witness` for `n = k`). -/
lemma two_le_t {k : ℕ} (hk : 1 ≤ k) : 2 ≤ t k := by
  obtain ⟨h1, hchain, -, -⟩ := (witness k hk).1
  rcases hk.lt_or_eq with h | rfl
  · have := chain_lt hchain le_rfl h le_rfl
    linarith
  · exact h1.ge

/-- `d_i^{(k)} ≥ 0` for `1 ≤ i < k`, by `prop:witness` (i) (`witness` for `n = k`). -/
lemma d_nonneg {i k : ℕ} (hi : 1 ≤ i) (hik : i < k) : 0 ≤ d i k :=
  (witness k (by omega)).1.2.2.2 i k hi hik le_rfl

/-- `θ_k ≥ 0` for `k ≥ 1`: `θ_1 = 0`, and `θ_k = λ_k t_{k−1}` with `t_{k−1} ≥ 2` by
`prop:witness` (i) (`two_le_t`). -/
lemma theta_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ theta k := by
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · rw [theta_one]
  · rw [theta_of_two_le hk2]
    exact mul_nonneg (lam_pos k).le (by linarith [two_le_t (k := k - 1) (by omega)])

end Construction

end Witness

end Stoc
