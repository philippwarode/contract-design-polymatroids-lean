-- stamp r9 2026-11-03
import ContractDesignPolymatroids.Approximation.Scheme

/-!
# Convex costs: the setting, the value and the shift

The STOC version's Section 5.2 (`sec:convex`, `stoc-sections/08c-convex.tex`) and Appendix D.3
(`app:convex`, `stoc-sections/appF-convex.tex`): the settings, the agent's value `V`, the reward
`r(x*(α))` of the best response with the largest reward, `U_P`, the welfare `W`, `δ`-optimal
responses, and `lem:shift`.

* `Setting P m c rb`: the assumptions of `prop:approxresponses` and `prop:convexscheme`, "Under the
  assumptions on `K`, `c`, `r`, and the response oracle at the start of `app:convex`"
  (appF-convex.tex:82). The start of `app:convex` states them (appF-convex.tex:9): "For the oracle
  analysis, let `K ⊆ ℝ^E_{≥0}` be compact with `0 ∈ K`, and let `c : K → ℝ_{≥0}` be continuous
  with `c(0) = 0`. We use the reward bound `r̄` and the approximate best-response oracle of
  `sec:convex`." Section 5.2 gives "`r̄ > 0` a known reward bound" (08c-convex.tex:5) of the reward
  `r(x) = mᵀx` with `m ≥ 0` of the model (02-preliminaries.tex:12); the introduction states the
  setting of `prop:approxresponses` so: "The underlying scheme applies to any compact action set
  containing zero, with continuous nonnegative costs vanishing at zero" (01-introduction.tex:26).
  The action set is called `P` here, as `K` is the last round of the welfare loop in
  `ContractDesignPolymatroids/Convex/Scheme.lean`, and `r̄` is `rb`.
* `PolySetting f m c g G rb` (08c-convex.tex:13, 17), the setting of `thm:convexfptas` and of
  `lem:ellipsoid`: the action set `P₊(f)` of a polymatroid, rewards `m ≥ 0` with the model's reward
  of success `r̄ > 0`, `r ≤ r̄` on `P₊(f)` (02-preliminaries.tex:12), a cost of the model that is
  convex on `P₊(f)`, and a cost oracle that returns the value `c(x)` and a subgradient `g(x)` of `c`
  on `P₊(f)` with `‖g(x)‖_∞ ≤ G`. Such costs are continuous on `P₊(f)` (`abs_cost_sub_le`,
  `PolySetting.continuousOn`, not in the paper), so a `PolySetting` gives a `Setting` on `P₊(f)`
  (`PolySetting.toSetting`).
* Best responses exist and `x*(α)`, a point of `X*(α)` with the largest reward, exists
  (`Setting.exists_favourable`); "Then `V(0) = 0` and `V(1) = W`" (appF-convex.tex:9;
  `Setting.V_zero`, `V_one`), and `V(α) ≥ U_A(0 | α) = 0`, which the proof of `lem:welfare` uses
  (`Setting.V_nonneg`, not in the paper).
* `V` (`max_{x ∈ K} U_A(x | α)`), `S` (`r(x*(α))`), `profit` (`U_P(α) = (1 − α) r(x*(α))`),
  `welfare` (`W = max_{x ∈ K} (r(x) − c(x))`, 08c-convex.tex:5); `OPT` is
  `Stoc.OPT (profit P m c)`.
* appF-convex.tex:100, "`lem:monreward`, which holds for all maximizers": `r(x*(α))` is
  nondecreasing in the share (`Setting.monotoneOn_S`), so that the proof of `prop:convexscheme`
  can apply `thm:fptas` to the best responses `x*(α)` (in the form `Stoc.fptas_aux`).
* `IsDeltaOpt`: `δ`-optimal responses (08c-convex.tex:3, and `app:convex`).
* `lem:shift` (`shift`).

Taken over on 2026-10-20 from `Research/S14/Model.lean` (series 14 r6 and the draft
`section-convex.tex` d3) for the STOC version (`stoc.tex`); from then on this copy follows the
STOC version.
-/

namespace Stoc.Convex

open Set Filter Topology

variable {E : Type*} [Fintype E]

/-- The setting of `prop:approxresponses` and `prop:convexscheme`, "the assumptions on `K`, `c`,
`r`, and the response oracle at the start of `app:convex`" (appF-convex.tex:82): "For the oracle
analysis, let `K ⊆ ℝ^E_{≥0}` be compact with `0 ∈ K`, and let `c : K → ℝ_{≥0}` be continuous with
`c(0) = 0`. We use the reward bound `r̄` and the approximate best-response oracle of `sec:convex`."
(appF-convex.tex:9). The reward bound is "`r̄ > 0` a known reward bound" (08c-convex.tex:5), so
`r(x) ≤ r̄` on `K` for the reward `r(x) = mᵀx` with `m ≥ 0` of the model (02-preliminaries.tex:12)
(the introduction: "any compact action set containing zero, with continuous nonnegative costs
vanishing at zero", 01-introduction.tex:26). Here the action set is `P` and `r̄` is `rb`; `0 ≤ r` on
`P` follows from `m ≥ 0` and `P ⊆ ℝ^E_{≥0}`. The response oracle is a hypothesis where a result uses
it. -/
structure Setting (P : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ) (rb : ℝ) : Prop where
  compact : IsCompact P
  nonneg : ∀ x ∈ P, 0 ≤ x
  zero_mem : (0 : E → ℝ) ∈ P
  continuousOn : ContinuousOn c P
  c_nonneg : ∀ x ∈ P, 0 ≤ c x
  c_zero : c 0 = 0
  m_nonneg : ∀ e, 0 ≤ m e
  rbar_pos : 0 < rb
  reward_le : ∀ x ∈ P, reward m x ≤ rb

/-- The setting of `thm:convexfptas` ("For convex costs on `P₊(f)`", 08c-convex.tex:17) and of
`lem:ellipsoid` (`sec:F-ellipsoid`), with the model of `sec:model` (02-preliminaries.tex:12): a
polymatroid with rank function `f`, rewards `m ≥ 0`, the given reward of success `r̄ > 0` (`rb`)
with `r(x) ≤ r̄` for every `x ∈ P₊(f)`, a cost `c : ℝ^E_{≥0} → ℝ_{≥0}` with `c(0) = 0` that is
convex on `P₊(f)`, and "a cost oracle that returns `c(x)` and a subgradient `g(x)` with
`‖g(x)‖_∞ ≤ G` for a known `G`" (08c-convex.tex:13), here for every `x ∈ P₊(f)`, of `c` on `P₊(f)`.
As in the computational model of 08c-convex.tex:13 ("The cost oracle accepts feasible real inputs
and returns exact values"), `c` and `g` are exact functions of `x ∈ P₊(f)`; the model's counting of
operations is not formalised. -/
structure PolySetting [DecidableEq E] (f : Finset E → ℝ) (m : E → ℝ) (c : (E → ℝ) → ℝ)
    (g : (E → ℝ) → E → ℝ) (G : ℝ) (rb : ℝ) : Prop where
  rank : IsRankFunction f
  m_nonneg : ∀ e, 0 ≤ m e
  rbar_pos : 0 < rb
  reward_le : ∀ x ∈ indepPoly f, reward m x ≤ rb
  cost : IsCost c
  convexOn : ConvexOn ℝ (indepPoly f) c
  subgrad : ∀ x ∈ indepPoly f, ∀ y ∈ indepPoly f, c x + ∑ e, g x e * (y e - x e) ≤ c y
  bound : ∀ x ∈ indepPoly f, ∀ e, |g x e| ≤ G

section Defs

variable (P : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ)

/-- The agent's value: "Write `V(α) := max_{x ∈ K} U_A(x | α)`" (appF-convex.tex:9), which the
proofs of `lem:welfare` and `lem:ellipsoid` use (appF-convex.tex:39-49, 136). -/
noncomputable def V (α : ℝ) : ℝ :=
  sSup (util m c α '' P)

/-- `r(x*(α))` for the best response `x*(α)` of the model, which breaks ties in favor of the
principal (02-preliminaries.tex:17): a point of `X*(α)`, "the set of maximizers"
(appF-convex.tex:9), with the largest reward. For `α < 1` this is the model's tie-breaking; at
`α = 1`, where `U_P(x | 1) = 0` for every `x`, all of `X*(1)` ties, and `S` takes the largest
reward. -/
noncomputable def S (α : ℝ) : ℝ :=
  sSup (reward m '' bestResponses P m c α)

/-- The principal's utility `U_P(α) = (1 − α) r(x*(α))` (02-preliminaries.tex:17). -/
noncomputable def profit (α : ℝ) : ℝ :=
  (1 - α) * S P m c α

/-- The welfare `W = max_{x ∈ K} (r(x) − c(x))` (08c-convex.tex:5). -/
noncomputable def welfare : ℝ :=
  sSup ((fun x => reward m x - c x) '' P)

/-- `x` is a *`δ`-optimal response* at the share `α` (08c-convex.tex:3): "an action `x̃ ∈ K` is a
`δ`-optimal response if `U_A(x̃ | α) ≥ max_{x ∈ K} U_A(x | α) − δ`", that is,
`U_A(x | α) ≥ V(α) − δ`; `app:convex` uses the term throughout (appF-convex.tex:11, 14, 56). -/
def IsDeltaOpt (α δ : ℝ) (x : E → ℝ) : Prop :=
  x ∈ P ∧ V P m c α - δ ≤ util m c α x

end Defs

variable {m : E → ℝ} {c : (E → ℝ) → ℝ}

/-- "`c(y) − c(x) ≥ g(x)ᵀ(y − x) ≥ −G ‖y − x‖₁` for all `x, y ∈ P₊(f)`, and exchanging `x` and `y`
gives `|c(y) − c(x)| ≤ G ‖y − x‖₁`" (not in the paper: the final version has this argument only in a
comment, appF-convex.tex:119; the proof of `thm:convexfptas` applies `prop:convexscheme`, which
assumes a continuous cost, on `P₊(f)`). -/
theorem abs_cost_sub_le {G : ℝ} {x y gx gy : E → ℝ}
    (hx : c x + ∑ e, gx e * (y e - x e) ≤ c y) (hy : c y + ∑ e, gy e * (x e - y e) ≤ c x)
    (hgx : ∀ e, |gx e| ≤ G) (hgy : ∀ e, |gy e| ≤ G) :
    |c y - c x| ≤ G * ∑ e, |y e - x e| := by
  have k1 : -(G * ∑ e, |y e - x e|) ≤ ∑ e, gx e * (y e - x e) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have := neg_abs_le (gx e * (y e - x e))
    rw [abs_mul] at this
    nlinarith [abs_nonneg (y e - x e), hgx e]
  have k2 : -(G * ∑ e, |y e - x e|) ≤ ∑ e, gy e * (x e - y e) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have := neg_abs_le (gy e * (x e - y e))
    rw [abs_mul, abs_sub_comm] at this
    nlinarith [abs_nonneg (y e - x e), hgy e]
  rw [abs_le]
  constructor <;> linarith

namespace PolySetting

variable [DecidableEq E] {f : Finset E → ℝ} {g : (E → ℝ) → E → ℝ} {G rb : ℝ}
  (h : PolySetting f m c g G rb)
include h

/-- "These costs satisfy the continuity assumption above", on `P₊(f)`, by `abs_cost_sub_le` (not in
the paper: a comment of the final version, appF-convex.tex:119). -/
theorem continuousOn : ContinuousOn c (indepPoly f) := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun y : E → ℝ => G * ∑ e, |y e - x e|) (𝓝[indepPoly f] x) (𝓝 0) := by
    have hcont : Continuous fun y : E → ℝ => G * ∑ e, |y e - x e| :=
      continuous_const.mul (continuous_finsetSum _ fun e _ =>
        ((continuous_apply e).sub continuous_const).abs)
    have := hcont.tendsto x
    simp only [sub_self, abs_zero, Finset.sum_const_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.norm_eq_abs]
  exact abs_cost_sub_le (h.subgrad x hx y hy) (h.subgrad y hy x hx) (h.bound x hx) (h.bound y hy)

/-- The cost is nonnegative on `P₊(f)`. -/
lemma c_nonneg {x : E → ℝ} (hx : x ∈ indepPoly f) : 0 ≤ c x :=
  h.cost.nonneg x hx.1

/-- The setting of `thm:convexfptas` lies in that of `prop:convexscheme`, with `K = P₊(f)`: `P₊(f)`
is compact, contains `0` and lies in `ℝ^E_{≥0}`, and the costs are continuous on it (`continuousOn`,
not in the paper: the proof of `thm:convexfptas` runs `alg:convex` on `P₊(f)` and cites
`prop:convexscheme` there, appF-convex.tex:144). -/
theorem toSetting : Setting (indepPoly f) m c rb where
  compact := isCompact_indepPoly f
  nonneg _ hx := hx.1
  zero_mem := zero_mem_indepPoly h.rank
  continuousOn := h.continuousOn
  c_nonneg _ hx := h.c_nonneg hx
  c_zero := h.cost.zero
  m_nonneg := h.m_nonneg
  rbar_pos := h.rbar_pos
  reward_le := h.reward_le

end PolySetting

namespace Setting

variable {P : Set (E → ℝ)} {rb : ℝ} (h : Setting P m c rb)
include h

/-- Best responses exist: "We assume that this maximum is attained … Both hold when `c` is
continuous on the compact set" (02-preliminaries.tex:17), and `K` is compact and `c` continuous on
it (appF-convex.tex:9). -/
lemma exists_isBR (α : ℝ) : ∃ x, IsBR P m c α x :=
  Stoc.Convex.exists_isBR h.compact ⟨0, h.zero_mem⟩ h.continuousOn α

omit h in
/-- At a best response, `V(α) = U_A(x | α)`. -/
lemma _root_.Stoc.Convex.IsBR.V_eq {α : ℝ} {x : E → ℝ} (hx : IsBR P m c α x) :
    V P m c α = util m c α x :=
  IsGreatest.csSup_eq ⟨mem_image_of_mem _ hx.1, by rintro _ ⟨z, hz, rfl⟩; exact hx.2 z hz⟩

/-- `U_A(z | α) ≤ V(α)` for `z ∈ K`: the maximum `V(α)` is attained. -/
lemma util_le_V {α : ℝ} {z : E → ℝ} (hz : z ∈ P) : util m c α z ≤ V P m c α := by
  obtain ⟨x, hx⟩ := h.exists_isBR α
  rw [hx.V_eq]
  exact hx.2 z hz

/-- `x*(α)`, a point of `X*(α)` with the largest reward, exists ("when using this tie-breaking rule,
… the reward attains its maximum over the set of best responses. Both hold when `c` is continuous on
the compact set", 02-preliminaries.tex:17; `K` is compact and `c` continuous on it,
appF-convex.tex:9). -/
lemma isGreatest_S (α : ℝ) :
    IsGreatest (reward m '' bestResponses P m c α) (S P m c α) := by
  obtain ⟨x₀, hx₀⟩ := h.exists_isBR α
  obtain ⟨y, hy, hmax⟩ := (isCompact_bestResponses h.compact h.continuousOn
    α).exists_isMaxOn ⟨x₀, hx₀⟩ (continuous_reward m).continuousOn
  have hg : IsGreatest (reward m '' bestResponses P m c α) (reward m y) :=
    ⟨mem_image_of_mem _ hy, by rintro _ ⟨z, hz, rfl⟩; exact isMaxOn_iff.1 hmax z hz⟩
  rw [S, hg.csSup_eq]
  exact hg

lemma exists_favourable (α : ℝ) : ∃ y, IsBR P m c α y ∧ reward m y = S P m c α := by
  obtain ⟨⟨y, hy, hyS⟩, -⟩ := h.isGreatest_S α
  exact ⟨y, hy, hyS⟩

lemma S_nonneg (α : ℝ) : 0 ≤ S P m c α := by
  obtain ⟨y, hy, hyS⟩ := h.exists_favourable α
  rw [← hyS]
  exact reward_nonneg_of_nonneg h.m_nonneg (h.nonneg y hy.1)

lemma S_le_rbar (α : ℝ) : S P m c α ≤ rb := by
  obtain ⟨y, hy, hyS⟩ := h.exists_favourable α
  rw [← hyS]
  exact h.reward_le y hy.1

/-- `V(α) ≥ U_A(0 | α) = 0`, as `0 ∈ K` and `c(0) = 0` (not in the paper: the proof of
`lem:welfare` uses it without proof, "as `V(α) ≥ 0`", appF-convex.tex:39). -/
lemma V_nonneg (α : ℝ) : 0 ≤ V P m c α := by
  have h0 := h.util_le_V (α := α) h.zero_mem
  have : util m c α 0 = 0 := by simp [util, reward, h.c_zero]
  linarith

/-- "Then `V(0) = 0`" (appF-convex.tex:9), as `c ≥ 0 = c(0)`; the proof of `lem:welfare` uses it
in `W = V(1) − V(0)` (appF-convex.tex:47). -/
lemma V_zero : V P m c 0 = 0 := by
  refine le_antisymm (csSup_le ⟨_, mem_image_of_mem _ h.zero_mem⟩ ?_) (h.V_nonneg 0)
  rintro _ ⟨z, hz, rfl⟩
  simp only [util, zero_mul, zero_sub, neg_nonpos]
  exact h.c_nonneg z hz

omit h in
/-- "and `V(1) = W`" (appF-convex.tex:9) for the welfare `W := max_{x ∈ K} (r(x) − c(x))`
(08c-convex.tex:5); the proof of `lem:welfare` uses it in `W = V(1) − V(0)` (appF-convex.tex:47). -/
lemma _root_.Stoc.Convex.V_one : V P m c 1 = welfare P m c := by
  unfold V welfare
  congr 1
  exact Set.image_congr fun x _ => by simp only [util, one_mul]

/-- `U_P` is bounded above on `[0, 1]` (not in the paper: it takes `OPT` as given). -/
lemma bddAbove_profit : BddAbove (profit P m c '' Icc 0 1) :=
  ⟨rb, by
    rintro _ ⟨α, hα, rfl⟩
    have := h.S_le_rbar α
    have := h.S_nonneg α
    unfold profit
    nlinarith [hα.1, hα.2]⟩

/-- `U_P(α) ≤ OPT` for `α ∈ [0, 1]`. -/
lemma profit_le_OPT {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) : profit P m c α ≤ OPT (profit P m c) :=
  le_csSup h.bddAbove_profit (mem_image_of_mem _ hα)

/-- `OPT ≥ 0` (not in the paper: it uses this tacitly in the last paragraph of the proof of
`prop:convexscheme`, "Finally, we show that some `Ũ_j` is large", whose last inequality needs
`ε² OPT/8 ≥ 0` (appF-convex.tex:100-107), and in the proof of `thm:convexfptas`, where "`OPT = 0`
by `lem:welfare`" needs `OPT ≥ 0` besides `OPT ≤ W` (appF-convex.tex:144)). -/
lemma OPT_nonneg : 0 ≤ OPT (profit P m c) :=
  (mul_nonneg (by norm_num) (h.S_nonneg 0)).trans
    (h.profit_le_OPT (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩))

/-- appF-convex.tex:100, "`lem:monreward`, which holds for all maximizers": the reward
`r(x*(α))` of the best responses `x*(α)` of the largest reward is nondecreasing in the share, by
`lem:monreward` on any action set (`monotoneOn_reward_of_isBR`), as every `x*(α)` is a maximizer.
So `thm:fptas` applies to them in the form `fptas_aux` ("so the theorem applies to the best
responses `x*(α)`"). -/
lemma monotoneOn_S : MonotoneOn (S P m c) (Icc 0 1) := by
  choose xs hxs hxsS using h.exists_favourable
  have hmono := monotoneOn_reward_of_isBR (I := Icc 0 1) fun α _ => hxs α
  intro α hα α' hα' hle
  rw [← hxsS α, ← hxsS α']
  exact hmono hα hα' hle

end Setting

/-! ### `lem:shift` -/

/-- **`lem:shift`** (Lemma D.5, appF-convex.tex:13-18, proof 20-28): let `0 ≤ α'' < α < α'`, let
`δ ≥ 0`, and let `x̃` be a `δ`-optimal response at `α`. Then every `y'' ∈ X*(α'')` and every
`y' ∈ X*(α')` satisfy `r(y'') − δ/(α − α'') ≤ r(x̃) ≤ r(y') + δ/(α' − α)` (the left-hand inequality
for every `y''`, and the right-hand one for every `y'`). In the setting of `prop:convexscheme`
(`Setting`).

The proof, in the STOC version's order (as in the proof of `lem:monreward`, two inequalities are
added): (1) `y'` is a best response at `α'` and `x̃` is `δ`-optimal at `α`, which gives two
inequalities; (2) adding them gives the right-hand inequality; (3) the same with `α''` and `y''`
gives the left-hand one. It uses neither `α'' ≥ 0` nor `δ ≥ 0`. -/
theorem shift {P : Set (E → ℝ)} {rb : ℝ} (h : Setting P m c rb) {α'' α α' δ : ℝ}
    (_hα'' : 0 ≤ α'') (hα''α : α'' < α) (hαα' : α < α') (_hδ : 0 ≤ δ) {x : E → ℝ}
    (hx : IsDeltaOpt P m c α δ x) :
    (∀ y'' ∈ bestResponses P m c α'', reward m y'' - δ / (α - α'') ≤ reward m x) ∧
      ∀ y' ∈ bestResponses P m c α', reward m x ≤ reward m y' + δ / (α' - α) := by
  have hright : ∀ y' ∈ bestResponses P m c α', reward m x ≤ reward m y' + δ / (α' - α) := by
    intro y' hy'
    -- (1) "As `y'` is a best response at `α'` and `x̃` is `δ`-optimal at `α`,
    -- `α'r(y') − c(y') ≥ α'r(x̃) − c(x̃)` and `αr(x̃) − c(x̃) ≥ αr(y') − c(y') − δ`."
    have h1 : α' * reward m x - c x ≤ α' * reward m y' - c y' := hy'.2 x hx.1
    have h2 : α * reward m y' - c y' - δ ≤ α * reward m x - c x := by
      have := h.util_le_V (α := α) hy'.1
      have := hx.2
      simp only [util] at *
      linarith
    -- (2) "Adding them gives `(α' − α)(r(y') − r(x̃)) ≥ −δ`, which is the right-hand inequality."
    have h3 : -δ ≤ (α' - α) * (reward m y' - reward m x) := by linarith
    rw [← sub_le_iff_le_add', le_div_iff₀ (sub_pos.2 hαα')]
    linarith
  -- (3) "In the same way, `α''r(y'') − c(y'') ≥ α''r(x̃) − c(x̃)` and
  -- `αr(x̃) − c(x̃) ≥ αr(y'') − c(y'') − δ` give `(α − α'')(r(x̃) − r(y'')) ≥ −δ`, which is the
  -- left-hand inequality."
  have hleft : ∀ y'' ∈ bestResponses P m c α'', reward m y'' - δ / (α - α'') ≤ reward m x := by
    intro y'' hy''
    have h1 : α'' * reward m x - c x ≤ α'' * reward m y'' - c y'' := hy''.2 x hx.1
    have h2 : α * reward m y'' - c y'' - δ ≤ α * reward m x - c x := by
      have := h.util_le_V (α := α) hy''.1
      have := hx.2
      simp only [util] at *
      linarith
    have h3 : -δ ≤ (α - α'') * (reward m x - reward m y'') := by linarith
    rw [sub_le_iff_le_add', ← sub_le_iff_le_add, le_div_iff₀ (sub_pos.2 hα''α)]
    linarith
  exact ⟨hleft, hright⟩

end Stoc.Convex
