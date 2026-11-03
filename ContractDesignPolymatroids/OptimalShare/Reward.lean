-- stamp r8 2026-11-03
import ContractDesignPolymatroids.BestResponse.Quadratic

/-!
# The principal's utility and the reward of the best response

The STOC version, Section 2 (`stoc-sections/02-preliminaries.tex`): the principal's utility at the
best response, `U_P(α) = U_P(x*(α) | α) = (1 − α) r(x*(α))`, with `r(x*(α)) = ∑ m_e x*_e(α)`
(`Stoc.grossValue`) and `U_P(α) = Stoc.profit (grossValue f m β) α`.

Section 3 (`stoc-sections/06-optimal-share.tex:29-31`), Lemma `lem:monreward`, with its proof in
Appendix B.2 (`stoc-sections/appB-quadratic.tex:276-287`): for every cost function `c`, all shares
`0 ≤ α < α'`, and any maximizers `x` of `U_A(· | α) = α r − c` and `x'` of `U_A(· | α')` over
`P₊(f)`, `r(x) ≤ r(x')`. The exact statement is `Stoc.monreward`. Its proof is that of
`Stoc.monreward_aux`, the same claim for any action set and any shares `α < α'` (the proof opens
with "The argument uses only the optimality of `x` and `x'`, not the form of `c`",
`appB-quadratic.tex:277`, and it uses neither `P₊(f)` nor `α ≥ 0`), in the STOC version's steps:
(1) the two inequalities that say that `x` and `x'` are maximizers, (2) their sum
`(α' − α)(r(x') − r(x)) ≥ 0`, (3) division by `α' − α > 0`. `monreward_aux` is also used for the
arbitrary action sets of `ContractDesignPolymatroids/Approximation/Scheme.lean`. The quadratic costs `c(x) = ∑ β_e/2 x_e²`
give the corollaries `IsBestResponse.reward_mono` (best responses on any action set, through
`U_A(x | α) = α r(x) − c(x)`, `utility_eq_reward_sub`) and `grossValue_monotone` (`α ↦ r(x*(α))` is
nondecreasing).

The utility, best responses, their first-order condition and `x*(α)` are defined in
`ContractDesignPolymatroids/BestResponse/Quadratic.lean`. Until 2026-10-17 these declarations were part of
`CDP/StarShaped.lean` and `CDP/HalfRule.lean`, next to the star-shapedness of `r(x*(α))` and the
half rule of the research series. Those were not in the long paper; the research library has
them (`Research/S05/StarShaped.lean`, `Research/S05/HalfRule.lean`).

Taken over on 2026-10-20 from `Paper/FixedShare/Reward.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version. Reworked on 2026-10-25:
`lem:monreward` has one exact statement and one proof here (it was in
`ContractDesignPolymatroids/Approximation/Scheme.lean`), and the quadratic forms are derived from it.
-/

namespace Stoc

open Finset

variable {E : Type*} [Fintype E]

/-- The principal's utility `U_P(α) = (1 − α) S(α)` for a function `S` of the share; at the best
response `S(α) = r(x*(α))` (`grossValue`). -/
def profit (S : ℝ → ℝ) (α : ℝ) : ℝ := (1 - α) * S α

/-! ### `lem:monreward` -/

/-- The proof of `lem:monreward` (`stoc-sections/appB-quadratic.tex:276-287`), for any action set
`C` and any shares `α < α'` (the proof uses neither `P₊(f)` nor `α ≥ 0`, nor the form of `c`): if
`x` maximizes `α r − c` and `x'` maximizes `α' r − c` over `C`, then `r(x) ≤ r(x')`. The steps:
(1) the two optimality inequalities; (2) adding them gives `(α' − α)(r(x') − r(x)) ≥ 0`; (3) so
`r(x') ≥ r(x)`, as `α' − α > 0`. -/
theorem monreward_aux {C : Set (E → ℝ)} (m : E → ℝ) (c : (E → ℝ) → ℝ) {α α' : ℝ} (h : α < α')
    {x x' : E → ℝ} (hx : x ∈ C) (hx' : x' ∈ C)
    (hmax : ∀ y ∈ C, α * reward m y - c y ≤ α * reward m x - c x)
    (hmax' : ∀ y ∈ C, α' * reward m y - c y ≤ α' * reward m x' - c x') :
    reward m x ≤ reward m x' := by
  -- "The argument uses only the optimality of `x` and `x'`, not the form of `c`": so `C` and `c`
  -- are arbitrary here.
  -- (1) "As `x` maximizes `U_A(· | α)` and `x'` maximizes `U_A(· | α')` over `P₊(f)`, we have
  -- `α r(x) − c(x) ≥ α r(x') − c(x')` and `α' r(x') − c(x') ≥ α' r(x) − c(x)`."
  have h1 : α * reward m x - c x ≥ α * reward m x' - c x' := hmax x' hx'
  have h2 : α' * reward m x' - c x' ≥ α' * reward m x - c x := hmax' x hx
  -- (2) "Adding the two inequalities gives `(α' − α)(r(x') − r(x)) ≥ 0`,"
  have h3 : (α' - α) * (reward m x' - reward m x) ≥ 0 := by linarith
  -- (3) "so `r(x') ≥ r(x)`."
  have h4 := (mul_nonneg_iff_of_pos_left (sub_pos.2 h)).1 h3
  linarith

/-- **`lem:monreward`** (Lemma 3.5, statement `stoc-sections/06-optimal-share.tex:29-31`, proof
`stoc-sections/appB-quadratic.tex:276-287`), under the standing assumptions of the model
(`stoc-sections/02-preliminaries.tex:4, 12`: `f` is a rank function, `m ≥ 0`, and the cost function
`c : ℝ^E_{≥0} → ℝ_{≥0}` has `c(0) = 0`): for every cost function `c`, all shares `0 ≤ α < α'`, and
any maximizers `x` of `U_A(· | α) = α r − c` and `x'` of `U_A(· | α')` over `P₊(f)`,
`r(x) ≤ r(x')`. The proof, with the paper's steps (1)-(3), is `monreward_aux`, which uses only the
optimality of `x` and `x'`. -/
theorem monreward [DecidableEq E] {f : Finset E → ℝ} (_hf : IsRankFunction f) {m : E → ℝ}
    (_hm : ∀ e, 0 ≤ m e) {c : (E → ℝ) → ℝ} (_hc : ∀ x : E → ℝ, 0 ≤ x → 0 ≤ c x)
    (_hc0 : c 0 = 0) {α α' : ℝ} (_hα : 0 ≤ α) (h : α < α') {x x' : E → ℝ}
    (hx : x ∈ indepPoly f) (hx' : x' ∈ indepPoly f)
    (hmax : ∀ y ∈ indepPoly f, α * reward m y - c y ≤ α * reward m x - c x)
    (hmax' : ∀ y ∈ indepPoly f, α' * reward m y - c y ≤ α' * reward m x' - c x') :
    reward m x ≤ reward m x' :=
  monreward_aux m c h hx hx' hmax hmax'

/-! ### The quadratic case -/

/-- The agent's utility is the share times the reward minus the cost:
`U_A(x | α) = α r(x) − c(x)` with `c(x) = ∑ β_e x_e²/2`. -/
theorem utility_eq_reward_sub (m β : E → ℝ) (α : ℝ) (x : E → ℝ) :
    utility m β α x = α * reward m x - ∑ e, β e / 2 * x e ^ 2 :=
  rfl

/-- `lem:monreward` for the quadratic costs `c(x) = ∑ β_e x_e²/2` and best responses on any action
set (a corollary of `monreward_aux`, as `U_A(x | α) = α r(x) − c(x)`): the reward is nondecreasing
in the share. -/
theorem IsBestResponse.reward_mono {C : Set (E → ℝ)} {m β : E → ℝ} {α α' : ℝ} (hαα' : α < α')
    {a b : E → ℝ} (ha : IsBestResponse C m β α a) (hb : IsBestResponse C m β α' b) :
    reward m a ≤ reward m b := by
  refine monreward_aux m (fun x => ∑ e, β e / 2 * x e ^ 2) hαα' ha.1 hb.1 (fun y hy => ?_)
    fun y hy => ?_
  · have := ha.2 y hy
    rwa [utility_eq_reward_sub, utility_eq_reward_sub] at this
  · have := hb.2 y hy
    rwa [utility_eq_reward_sub, utility_eq_reward_sub] at this

/-! ### The reward of the best response -/

/-- The reward `r(x*(α)) = ∑ m_e x*_e(α)` of the best response. -/
noncomputable def grossValue (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : ℝ :=
  reward m (bestResponse f m β α)

/-- `lem:monreward` for the quadratic costs and the best response `x*` (a corollary of
`monreward_aux`, through `IsBestResponse.reward_mono`): `α ↦ r(x*(α))` is nondecreasing. -/
theorem grossValue_monotone [DecidableEq E] {f : Finset E → ℝ} (hf : IsRankFunction f)
    (m β : E → ℝ) : Monotone (grossValue f m β) := by
  intro α α' h
  rcases h.lt_or_eq with h | h
  · exact (isBestResponse_bestResponse hf m β α).reward_mono h
      (isBestResponse_bestResponse hf m β α')
  · rw [h]

/-- The sentence of Section 3 after `lem:monreward` (`stoc-sections/06-optimal-share.tex:33`): "In
the quadratic setting, `lem:monreward` implies `r¹_I ≥ 0` on every piece." If the reward of the
best response is `r(x*(α)) = r⁰_I + r¹_I α` on a piece `I = [a, b]`, `a < b` (the notation of
`06-optimal-share.tex:25`), then `r¹_I ≥ 0`, as `α ↦ r(x*(α))` is nondecreasing
(`grossValue_monotone`). -/
theorem reward_slope_nonneg [DecidableEq E] {f : Finset E → ℝ} (hf : IsRankFunction f)
    (m β : E → ℝ) {a b r0 r1 : ℝ} (hab : a < b)
    (h : ∀ α ∈ Set.Icc a b, grossValue f m β α = r0 + r1 * α) : 0 ≤ r1 := by
  have hmono := grossValue_monotone hf m β hab.le
  rw [h a (Set.left_mem_Icc.2 hab.le), h b (Set.right_mem_Icc.2 hab.le)] at hmono
  nlinarith

end Stoc
