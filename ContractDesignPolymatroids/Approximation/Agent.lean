-- stamp r7 2026-11-02
import ContractDesignPolymatroids.OptimalShare.Reward

/-!
# The agent's problem for an arbitrary cost

The model of the STOC version (`sec:model`, `stoc-sections/02-preliminaries.tex:11-17`) for an
arbitrary cost function, as Section 5 and Appendix D use it. The agent chooses an action `x` in an
action set `P` (the STOC version's `P₊(f)`; Section 5 and Appendix D replace it by an action set
`K`), its utility is `U_A(x | α) = α r(x) − c(x)` (`util`), and it plays a maximizer of `U_A(· | α)`
over `P` (`IsBR`). `X*(α)` is the set of maximizers (`bestResponses`). Unless stated otherwise,
ties are broken in favor of the principal (02-preliminaries.tex:17): among the maximizers the agent
plays one with the largest `U_P(x | α) = (1 − α) r(x)` (`IsPBR`).

* `IsCost`: the costs of the model, `c : ℝ^E_{≥0} → ℝ_{≥0}` with `c(0) = 0`
  (02-preliminaries.tex:12).
* The reward of success: "a given reward `r̄ > 0`, where `r(x) ≤ r̄` for every `x ∈ P₊(f)`"
  (02-preliminaries.tex:12), a number `R` with `0 < R` and `r ≤ R` on `P₊(f)` where a statement uses
  it. Its footnote: "If `r` vanishes on `P₊(f)`, every share is optimal"
  (`isMaxOn_of_reward_eq_zero`); "Otherwise, one convenient choice is `r̄ = ∑_e m_e f({e})`, since
  `x_e ≤ f({e})` for every feasible action" (`rbar`, `reward_le_rbar`, `rbar_valid`); "Any
  positive upper bound on the feasible expected rewards gives the same expected utilities below"
  (`linear_contract_utils`). "Success occurs with probability `r(x)/r̄`": that it lies in `[0, 1]`
  is not in the paper (`reward_div_mem`, with `reward_nonneg_of_mem`).
* `linear_contracts`: `lem:linear-contracts` (appA-proofs.tex:8-20), to which
  02-preliminaries.tex:13 points: a contract that pays `t₀ ≥ 0` for failure and `t₁ ≥ 0` for success
  can be replaced by a linear contract with a share in `[0, 1]` without decreasing the principal's
  expected utility (`contractAgent`, `contractPrincipal`, `IsContractBR`).
* `quadCost`: the quadratic costs of 05-best-response.tex:4, for which `IsBR` is the quadratic
  model's `IsBestResponse` (`isBR_quadCost_iff`), and the quadratic model's best response `x*(α)`
  (`Stoc.bestResponse`, unique as `β > 0`) is the model's best response (`isPBR_bestResponse`).
* `exists_isBR`, `exists_isPBR`: the two assumptions of 02-preliminaries.tex:17 (the agent's maximum
  and the largest reward among the maximizers are attained) hold when `c` is continuous on a compact
  action set ("Both hold when `c` is continuous on the compact set `P₊(f)`").
* The unit of work of Section 5, the best-response oracle call ("Their running time is measured in
  best-response oracle calls", 08-approximation.tex:4), is not a Lean object: the Lean counts the
  shares at which best responses are computed (`Stoc.fptas`, `Stoc.probe`, `Stoc.fptashom`,
  `Stoc.fptasquad`, `Stoc.Lower.querylb`).

The names lie in the namespace `Stoc.Convex`, that of the convex costs, where they were first
needed.
-/

namespace Stoc.Convex

open Set

variable {E : Type*} [Fintype E]

/-! ### Utility and best responses -/

/-- The agent's utility `U_A(x | α) = α r(x) − c(x)` at the share `α` (02-preliminaries.tex:15). -/
def util (m : E → ℝ) (c : (E → ℝ) → ℝ) (α : ℝ) (x : E → ℝ) : ℝ :=
  α * reward m x - c x

/-- `x` is a best response at the share `α` on the action set `P`:
`x ∈ argmax_{z ∈ P} U_A(z | α)`. -/
def IsBR (P : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ) (α : ℝ) (x : E → ℝ) : Prop :=
  x ∈ P ∧ ∀ z ∈ P, util m c α z ≤ util m c α x

/-- The set `X*(α)` of best responses. -/
def bestResponses (P : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ) (α : ℝ) : Set (E → ℝ) :=
  {x | IsBR P m c α x}

/-- `x` is the best response of the model at the share `α` (02-preliminaries.tex:17): a maximizer of
`U_A(· | α)` over `P` that breaks ties in favor of the principal, that is, it maximizes
`U_P(· | α) = (1 − α) r` among the maximizers. -/
def IsPBR (P : Set (E → ℝ)) (m : E → ℝ) (c : (E → ℝ) → ℝ) (α : ℝ) (x : E → ℝ) : Prop :=
  IsBR P m c α x ∧ ∀ y, IsBR P m c α y → (1 - α) * reward m y ≤ (1 - α) * reward m x

/-- The costs of the model (02-preliminaries.tex:12): `c : ℝ^E_{≥0} → ℝ_{≥0}` with `c(0) = 0`. -/
structure IsCost (c : (E → ℝ) → ℝ) : Prop where
  nonneg : ∀ x : E → ℝ, 0 ≤ x → 0 ≤ c x
  zero : c 0 = 0

variable {P : Set (E → ℝ)} {m : E → ℝ} {c : (E → ℝ) → ℝ}

lemma IsPBR.isBR {α : ℝ} {x : E → ℝ} (h : IsPBR P m c α x) : IsBR P m c α x := h.1

lemma continuous_reward (m : E → ℝ) : Continuous (reward m) := by
  unfold reward
  fun_prop

lemma continuousOn_util (hc : ContinuousOn c P) (α : ℝ) : ContinuousOn (util m c α) P :=
  ((continuous_const.mul (continuous_reward m)).continuousOn).sub hc

/-- 02-preliminaries.tex:17: if `c` is continuous on the compact nonempty action set `P`, the
agent's maximum is attained at every share. -/
theorem exists_isBR (hP : IsCompact P) (hne : P.Nonempty) (hc : ContinuousOn c P) (α : ℝ) :
    ∃ x, IsBR P m c α x := by
  obtain ⟨x, hx, hmax⟩ := hP.exists_isMaxOn hne (continuousOn_util hc α)
  exact ⟨x, hx, isMaxOn_iff.1 hmax⟩

/-- `X*(α)` is compact when `c` is continuous on the compact action set `P`. -/
lemma isCompact_bestResponses (hP : IsCompact P) (hc : ContinuousOn c P) (α : ℝ) :
    IsCompact (bestResponses P m c α) := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · have : bestResponses (∅ : Set (E → ℝ)) m c α = ∅ := by
      ext x
      simp [bestResponses, IsBR]
    rw [this]
    exact isCompact_empty
  obtain ⟨x₀, hx₀⟩ := exists_isBR hP hne hc α
  have hset : bestResponses P m c α = P ∩ util m c α ⁻¹' Ici (util m c α x₀) := by
    ext x
    refine ⟨fun hx => ⟨hx.1, hx.2 x₀ hx₀.1⟩, fun hx => ⟨hx.1, fun z hz => ?_⟩⟩
    exact (hx₀.2 z hz).trans hx.2
  rw [hset]
  exact hP.of_isClosed_subset ((continuousOn_util hc α).preimage_isClosed_of_isClosed
    hP.isClosed isClosed_Ici) inter_subset_left

/-- 02-preliminaries.tex:17: if `c` is continuous on the compact nonempty action set `P`, the
reward attains its maximum over the set of agent-optimal actions, so the best response of the model
exists. -/
theorem exists_isPBR (hP : IsCompact P) (hne : P.Nonempty) (hc : ContinuousOn c P) (α : ℝ) :
    ∃ x, IsPBR P m c α x := by
  obtain ⟨x₀, hx₀⟩ := exists_isBR hP hne hc α
  obtain ⟨y, hy, hmax⟩ := (isCompact_bestResponses hP hc α).exists_isMaxOn ⟨x₀, hx₀⟩
    ((continuous_const.mul (continuous_reward m)).continuousOn :
      ContinuousOn (fun x => (1 - α) * reward m x) _)
  exact ⟨y, hy, fun z hz => isMaxOn_iff.1 hmax z hz⟩

/-! ### Quadratic costs as a special case -/

/-- The quadratic cost `c(x) = ∑_e β_e x_e²/2` (05-best-response.tex:4). -/
noncomputable def quadCost (β : E → ℝ) (x : E → ℝ) : ℝ :=
  ∑ e, β e / 2 * x e ^ 2

/-- With the quadratic cost, `U_A` is the quadratic model's utility (`Stoc.utility`). -/
lemma util_quadCost (m β : E → ℝ) (α : ℝ) (x : E → ℝ) :
    util m (quadCost β) α x = utility m β α x :=
  rfl

/-- With the quadratic cost, best responses are those of the quadratic model
(`Stoc.IsBestResponse`). -/
lemma isBR_quadCost_iff {C : Set (E → ℝ)} {m β : E → ℝ} {α : ℝ} {x : E → ℝ} :
    IsBR C m (quadCost β) α x ↔ IsBestResponse C m β α x := by
  simp only [IsBR, IsBestResponse, util_quadCost]

end Stoc.Convex

namespace Stoc

variable {E : Type*} [Fintype E]

/-- The footnote's "one convenient choice" of the reward of success, `r̄ = ∑_e m_e f({e})`
(02-preliminaries.tex:12; the model takes `r̄ > 0` as given, with `r(x) ≤ r̄` on `P₊(f)`). -/
def rbar (f : Finset E → ℝ) (m : E → ℝ) : ℝ :=
  reward m fun e => f {e}

/-- For `m ≥ 0` and `x ≥ 0`, `r(x) ≥ 0` (not in the paper: it uses this tacitly). -/
lemma reward_nonneg_of_nonneg {m x : E → ℝ} (hm : ∀ e, 0 ≤ m e) (hx : 0 ≤ x) : 0 ≤ reward m x :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hm e) (hx e)

/-- For `m ≥ 0`, the reward is nonnegative on `P₊(f)`, as `0 ≤ x_e` there (not in the paper:
02-preliminaries.tex:12 uses it tacitly). -/
lemma reward_nonneg_of_mem {f : Finset E → ℝ} {m : E → ℝ} (hm : ∀ e, 0 ≤ m e) {x : E → ℝ}
    (hx : x ∈ indepPoly f) : 0 ≤ reward m x :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hm e) (hx.1 e)

/-- The footnote of 02-preliminaries.tex:12: for `m ≥ 0`, `r(x) ≤ ∑_e m_e f({e})` on `P₊(f)`,
"since `x_e ≤ f({e})` for every feasible action". -/
lemma reward_le_rbar {f : Finset E → ℝ} {m : E → ℝ} (hm : ∀ e, 0 ≤ m e) {x : E → ℝ}
    (hx : x ∈ indepPoly f) : reward m x ≤ rbar f m :=
  Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (by simpa using hx.2 {e}) (hm e)

/-- The footnote of 02-preliminaries.tex:12, "Otherwise, one convenient choice is
`r̄ = ∑_e m_e f({e})`, since `x_e ≤ f({e})` for every feasible action": if `r` does not vanish on
`P₊(f)`, this `r̄` is a reward of success as the model requires, positive and at least `r(x)` for
every `x ∈ P₊(f)` (`reward_le_rbar`; its positivity is not in the paper). -/
theorem rbar_valid {f : Finset E → ℝ} {m : E → ℝ} (hm : ∀ e, 0 ≤ m e)
    (hr : ∃ x ∈ indepPoly f, reward m x ≠ 0) :
    0 < rbar f m ∧ ∀ x ∈ indepPoly f, reward m x ≤ rbar f m := by
  obtain ⟨x, hx, hne⟩ := hr
  exact ⟨lt_of_lt_of_le (lt_of_le_of_ne (reward_nonneg_of_mem hm hx) hne.symm)
    (reward_le_rbar hm hx), fun y hy => reward_le_rbar hm hy⟩

/-- 02-preliminaries.tex:12: for a reward of success `R > 0` with `r(x) ≤ R` on `P₊(f)`, "Success
occurs with probability `r(x)/r̄`", which lies in `[0, 1]` as `0 ≤ r(x) ≤ R` on `P₊(f)`
(`reward_nonneg_of_mem`; not in the paper). -/
lemma reward_div_mem {f : Finset E → ℝ} {m : E → ℝ} (hm : ∀ e, 0 ≤ m e) {R : ℝ} (hR : 0 < R)
    (hRb : ∀ x ∈ indepPoly f, reward m x ≤ R) {x : E → ℝ} (hx : x ∈ indepPoly f) :
    reward m x / R ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (reward_nonneg_of_mem hm hx) hR.le, (div_le_one hR).2 (hRb x hx)⟩

/-- The footnote of 02-preliminaries.tex:12, "If `r` vanishes on `P₊(f)`, every share is optimal":
for every choice of actions `xs(α) ∈ P₊(f)`, for instance best responses,
`U_P(α) = (1 − α) r(xs(α)) = 0`, and every share `α ∈ [0, 1]` maximizes `U_P` over `[0, 1]`. -/
theorem isMaxOn_of_reward_eq_zero {f : Finset E → ℝ} {m : E → ℝ}
    (h0 : ∀ x ∈ indepPoly f, reward m x = 0) (xs : ℝ → E → ℝ)
    (hxs : ∀ α ∈ Set.Icc (0 : ℝ) 1, xs α ∈ indepPoly f) :
    ∀ α ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (profit fun α => reward m (xs α)) (Set.Icc 0 1) α :=
  fun α hα => isMaxOn_iff.2 fun β hβ => by
    simp only [profit, h0 _ (hxs β hβ), h0 _ (hxs α hα), mul_zero, le_refl]

/-! ### Linear contracts -/

/-- The agent's expected utility under the contract that pays `t₀` for failure and `t₁` for success
(02-preliminaries.tex:12-13, `lem:linear-contracts`), with the reward `R` of success: success occurs
with probability `r(x)/R`, so the expected payment is `(1 − r(x)/R) t₀ + (r(x)/R) t₁`, and the agent
bears the cost `c(x)`. -/
noncomputable def contractAgent (R : ℝ) (m : E → ℝ) (c : (E → ℝ) → ℝ) (t₀ t₁ : ℝ) (x : E → ℝ) :
    ℝ :=
  (1 - reward m x / R) * t₀ + reward m x / R * t₁ - c x

/-- The principal's expected utility under the contract that pays `t₀` for failure and `t₁` for
success: the reward `R` of success, which occurs with probability `r(x)/R`, minus the expected
payment. -/
noncomputable def contractPrincipal (R : ℝ) (m : E → ℝ) (t₀ t₁ : ℝ) (x : E → ℝ) : ℝ :=
  reward m x / R * R - ((1 - reward m x / R) * t₀ + reward m x / R * t₁)

/-- A best response of the agent to the contract: a maximizer of its expected utility over
`P₊(f)`. -/
def IsContractBR (f : Finset E → ℝ) (R : ℝ) (m : E → ℝ) (c : (E → ℝ) → ℝ) (t₀ t₁ : ℝ)
    (x : E → ℝ) : Prop :=
  x ∈ indepPoly f ∧ ∀ z ∈ indepPoly f, contractAgent R m c t₀ t₁ z ≤ contractAgent R m c t₀ t₁ x

/-- The footnote of 02-preliminaries.tex:12, "Any positive upper bound on the feasible expected
rewards gives the same expected utilities below": for every reward of success `R > 0`, the linear
contract with share `α`, which "pays `0` for failure and `α r̄` for success"
(02-preliminaries.tex:13), gives the agent `U_A(x | α) = α r(x) − c(x)` and the principal
`U_P(x | α) = (1 − α) r(x)` (02-preliminaries.tex:14-16), whatever `R` is. -/
theorem linear_contract_utils {R : ℝ} (hR : 0 < R) (m : E → ℝ) (c : (E → ℝ) → ℝ) (α : ℝ)
    (x : E → ℝ) :
    contractAgent R m c 0 (α * R) x = Convex.util m c α x ∧
      contractPrincipal R m 0 (α * R) x = (1 - α) * reward m x := by
  have hR0 : R ≠ 0 := hR.ne'
  refine ⟨?_, ?_⟩
  · simp only [contractAgent, Convex.util]
    field_simp
    ring
  · simp only [contractPrincipal]
    field_simp
    ring

/-- **`lem:linear-contracts`** (Lemma A.1, appA-proofs.tex:8-10, proof 12-20): "Every contract with
nonnegative outcome payments that admits a best response can be replaced by a linear contract with
share `α ∈ [0, 1]` without decreasing the principal's expected utility, with ties broken in favor of
the principal", in the binary-outcome model of `sec:model` (02-preliminaries.tex:12-13), the setting
of Appendix A.1. Here: for a contract that pays `t₀ ≥ 0` for failure and `t₁ ≥ 0` for success, there
is a share `α ∈ [0, 1]` such that for every best response `x` to the contract and every best
response `x'` at `α` that breaks ties in favor of the principal (`Convex.IsPBR`), the principal's
expected utility under the contract is at most `(1 − α) r(x')`, its expected utility under the
linear contract.

The hypotheses are those of the model (02-preliminaries.tex:12): `f` a rank function, `m ≥ 0`, a
cost `c` with `c ≥ 0` and `c(0) = 0`, and the given reward of success `R = r̄ > 0` with `r ≤ R` on
`P₊(f)`; the bound `r ≤ R` and `t₁ ≥ 0` are not used. The proof, numbered (1)-(5) here: (1) with
`α' = (t₁ − t₀)/r̄`, the agent's and the principal's expected utilities from `x ∈ P₊(f)` are
`t₀ + α' r(x) − c(x)` and `(1 − α') r(x) − t₀`; (2) if `α' ∈ [0, 1]`, the linear contract with share
`α'` has the same set of best responses, the principal's utility under it is larger by `t₀` for each
such response, and principal-favoring tie-breaking preserves this improvement; (3) if `α' > 1`, the
principal's utility under the original contract is at most `0`; (4) if `α' < 0`, every best response
`x` satisfies `α' r(x) − c(x) ≥ 0`, so `r(x) = 0` and the principal's utility is `−t₀ ≤ 0`; (5) in
both cases, the linear contract with share `0` is at least as good, as it gives the principal
`r(x*(0)) ≥ 0`. -/
theorem linear_contracts [DecidableEq E] {f : Finset E → ℝ} (hf : IsRankFunction f) {m : E → ℝ}
    (hm : ∀ e, 0 ≤ m e) {c : (E → ℝ) → ℝ} (hc : Convex.IsCost c) {R : ℝ} (hR : 0 < R)
    (_hRb : ∀ x ∈ indepPoly f, reward m x ≤ R) {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (_ht₁ : 0 ≤ t₁) :
    ∃ α ∈ Set.Icc (0 : ℝ) 1, ∀ x x', IsContractBR f R m c t₀ t₁ x →
      Convex.IsPBR (indepPoly f) m c α x' →
        contractPrincipal R m t₀ t₁ x ≤ (1 - α) * reward m x' := by
  -- (1) "Let the original contract pay `t₀ ≥ 0` for failure and `t₁ ≥ 0` for success, and set
  -- `α' := (t₁ − t₀)/r̄`. Since success occurs with probability `r(x)/r̄`, the agent's and the
  -- principal's expected utilities from an action `x ∈ P₊(f)` are, respectively,
  -- `t₀ + α'r(x) − c(x)`, `(1 − α')r(x) − t₀`."
  set α' := (t₁ - t₀) / R with hα'
  have hR0 : R ≠ 0 := hR.ne'
  have h1 : ∀ x, contractAgent R m c t₀ t₁ x = t₀ + Convex.util m c α' x := fun x => by
    simp only [contractAgent, Convex.util, hα']
    field_simp
    ring
  have h1' : ∀ x, contractPrincipal R m t₀ t₁ x = (1 - α') * reward m x - t₀ := fun x => by
    simp only [contractPrincipal, hα']
    field_simp
    ring
  rcases le_or_gt 0 α' with h0 | h0
  · rcases le_or_gt α' 1 with h1le | h1gt
    · -- (2) "If `α' ∈ [0, 1]`, the linear contract with share `α'` has the same set of best
      -- responses, since the agent's utilities differ only by the constant `t₀`."
      have hsame : ∀ x, IsContractBR f R m c t₀ t₁ x ↔ Convex.IsBR (indepPoly f) m c α' x :=
        fun x => by
          simp only [IsContractBR, Convex.IsBR, h1]
          constructor
          · rintro ⟨hx, h⟩
            exact ⟨hx, fun z hz => by linarith [h z hz]⟩
          · rintro ⟨hx, h⟩
            exact ⟨hx, fun z hz => by linarith [h z hz]⟩
      refine ⟨α', ⟨h0, h1le⟩, fun x x' hx hx' => ?_⟩
      -- (2) "For each such response, the principal's utility under the linear contract is larger
      -- by `t₀`. Principal-favoring tie-breaking therefore preserves this improvement."
      have hle := hx'.2 x ((hsame x).1 hx)
      rw [h1']
      linarith
    · -- (3) "If `α' > 1`, the principal's utility under the original contract is at most `0`,
      -- since `r(x) ≥ 0` and `t₀ ≥ 0`."
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, fun x x' hx hx' => ?_⟩
      have hle : contractPrincipal R m t₀ t₁ x ≤ 0 := by
        rw [h1']
        have := reward_nonneg_of_mem hm hx.1
        nlinarith
      -- (5) "In both cases, the linear contract with share `0` is at least as good, since it
      -- gives the principal utility `r(x*(0)) ≥ 0`."
      have := reward_nonneg_of_mem hm hx'.1.1
      linarith
  · -- (4) "If `α' < 0`, every best response `x` satisfies `α'r(x) − c(x) ≥ 0`, since choosing
    -- `x = 0` gives the agent utility `t₀`. As `r(x) ≥ 0` and `c(x) ≥ 0`, this implies `r(x) = 0`,
    -- so the principal's utility is `−t₀ ≤ 0`."
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, fun x x' hx hx' => ?_⟩
    have hz : contractAgent R m c t₀ t₁ 0 = t₀ := by
      rw [h1, Convex.util, show reward m (0 : E → ℝ) = 0 by simp [reward], hc.zero]
      ring
    have hge : 0 ≤ α' * reward m x - c x := by
      have := hx.2 0 (zero_mem_indepPoly hf)
      rw [hz, h1, Convex.util] at this
      linarith
    have hrx := reward_nonneg_of_mem hm hx.1
    have hcx := hc.nonneg x fun e => hx.1.1 e
    have hrx0 : reward m x = 0 := by nlinarith
    have hle : contractPrincipal R m t₀ t₁ x ≤ 0 := by
      rw [h1', hrx0]
      linarith
    -- (5) "In both cases, the linear contract with share `0` is at least as good, since it gives
    -- the principal utility `r(x*(0)) ≥ 0`."
    have := reward_nonneg_of_mem hm hx'.1.1
    linarith

/-- The best response `x*(α)` of the quadratic model is the model's best response for the cost
`∑_e β_e/2 x_e²`: it maximizes `U_A(· | α)` over `P₊(f)`, and for `β > 0` it is the only maximizer
(05-best-response.tex:10), so the tie-breaking does not matter. -/
lemma isPBR_bestResponse [DecidableEq E] {f : Finset E → ℝ} (hf : IsRankFunction f)
    {m β : E → ℝ} (hβ : ∀ e, 0 < β e) (α : ℝ) :
    Convex.IsPBR (indepPoly f) m (Convex.quadCost β) α (bestResponse f m β α) := by
  have hbr := isBestResponse_bestResponse hf m β α
  refine ⟨Convex.isBR_quadCost_iff.2 hbr, fun y hy => ?_⟩
  rw [(Convex.isBR_quadCost_iff.1 hy).unique (convex_indepPoly f) hβ hbr]

/-! ### One element -/

/-- The rank function of one element `e` with `f({e}) = T`. -/
def oneF (T : ℝ) (S : Finset Unit) : ℝ := T * S.card

lemma isRankFunction_oneF {T : ℝ} (hT : 0 ≤ T) : IsRankFunction (oneF T) where
  empty := by simp [oneF]
  mono S S' h := by
    simp only [oneF]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card h) hT
  submod S S' := by
    simp only [oneF]
    have h := Finset.card_union_add_card_inter S S'
    have h' : ((S ∪ S').card : ℝ) + (S ∩ S').card = S.card + S'.card := by exact_mod_cast h
    nlinarith

lemma mem_indepPoly_oneF {T : ℝ} {x : Unit → ℝ} :
    x ∈ indepPoly (oneF T) ↔ 0 ≤ x () ∧ x () ≤ T := by
  constructor
  · rintro ⟨h0, hS⟩
    refine ⟨h0 (), ?_⟩
    simpa [oneF] using hS Finset.univ
  · rintro ⟨h0, h1⟩
    refine ⟨fun e => h0, fun S => ?_⟩
    rcases Finset.eq_empty_or_nonempty S with rfl | hS
    · simp [oneF]
    · have : S = Finset.univ := Finset.eq_univ_of_forall fun u => by
        obtain ⟨v, hv⟩ := hS
        exact hv
      subst this
      simpa [oneF] using h1

lemma reward_one_unit (x : Unit → ℝ) : reward 1 x = x () := by
  simp [reward]

/-- For one element with `m_e = 1` and `f({e}) = T`, the footnote's choice `r̄ = ∑_e m_e f({e})`
(`rbar`, 02-preliminaries.tex:12) is `T`. -/
lemma rbar_oneF (T : ℝ) : rbar (oneF T) 1 = T := by
  simp [rbar, reward, oneF]

end Stoc
