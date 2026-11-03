-- stamp r9 2026-11-03
import ContractDesignPolymatroids.BestResponse.Quadratic
import ContractDesignPolymatroids.BestResponse.LayerCake
import ContractDesignPolymatroids.Preliminaries.Greedy

/-!
# Level sets of the marginals

The STOC version, Section 3, Proposition `prop:optchar` and Theorem `thm:levelsets`
(`stoc-sections/05-best-response.tex`), with the proofs in Appendix B.1 (`sec:A-bestresponse`,
`stoc-sections/appB-quadratic.tex`), and Theorem `thm:monmarg`, which Appendix B.1 states and proves
(paragraph "Level sets and monotone marginals", `appB-quadratic.tex:215-248`).

* `optchar`: `prop:optchar`. Its proof is the STOC version's, in `isBestResponse_iff_levelSets`,
  the same statement with the hypothesis `α m ≥ 0` of step (1) in place of `m ≥ 0` and `α ≥ 0`:
  (1) at an optimum `x ≤ z(α)`, so `ρ(x) ≥ 0` (`IsBestResponse.le_z`,
  `IsBestResponse.marg_nonneg`); (2) by concavity, `x` is optimal if and only if it maximizes
  `ρ(x)ᵀy` over `P₊(f)` (`isBestResponse_iff_maximises`); (3)-(6) for `ρ(x) ≥ 0`, over the distinct
  positive values `θ_1 > ⋯ > θ_k` of `ρ(x)` and `A_i = A_{θ_i}(x)`: the layer-cake identity
  (`Stoc.layerCake`), the maximum `∑_i (θ_i − θ_{i+1}) f(A_i)` by Edmonds' greedy theorem
  [Edm03, (19)] (`Stoc.greedy_pos`), attained at `x`
  exactly when every `A_i` is tight, and these are all nonempty positive level sets
  (`Stoc.levelSet_eq_theta`). `IsBestResponse.levelSet_tight` is its "only if".
* `rho` and `optLevelSet`: the optimal marginals `ρ_e(α)` and their level sets `A_θ(α)`, and
  `levelFun`: `F_{α,θ}` (`stoc-sections/05-best-response.tex:30-31`).
* `levelsets` (and `IsBestResponse.levelSet_isMaxMinimiser`): `thm:levelsets`.
* `monmarg` (and `IsBestResponse.marg_le`): `thm:monmarg`, with `subset_of_isMinimiser`, the form
  of Topkis's monotonicity theorem that the STOC version cites.

Taken over on 2026-10-20 from `Paper/FixedShare/LevelSets.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version. The proofs of
`prop:optchar`, `thm:levelsets` and `thm:monmarg` were rewritten on 2026-10-25 to take the STOC
version's steps. On 2026-11-02 the steps (3)-(6) of the proof of `prop:optchar`, a lemma for every
`ρ ≥ 0` until then, moved into the proof, for `ρ(x)` as in the STOC version.
-/

namespace Stoc

open Finset Function

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {f : Finset E → ℝ} {m β : E → ℝ} {α : ℝ} {x : E → ℝ}

/-- The level set `A_θ(x) = {e | ρ_e(x) ≥ θ}` of the marginals at `x`
(`stoc-sections/05-best-response.tex:16`). -/
def levelSet (m β : E → ℝ) (α : ℝ) (x : E → ℝ) (θ : ℝ) : Finset E :=
  univ.filter fun e => θ ≤ marg m β α x e

/-! ### `prop:optchar` -/

omit [DecidableEq E] in
/-- Step (2) of the proof of `prop:optchar` (`stoc-sections/appB-quadratic.tex:15-22`): "By
concavity, `x` is optimal if and only if it maximizes the linear objective `ρ(x)ᵀy` over
`y ∈ P₊(f)`: necessity follows by taking directional derivatives towards feasible points"
(`IsBestResponse.foc`), "and sufficiency from concavity, which yields
`U_A(y | α) − U_A(x | α) ≤ ρ(x)ᵀ(y − x)`" (`isBestResponse_of_foc`). -/
theorem isBestResponse_iff_maximises (hβ : ∀ e, 0 < β e) (hx : x ∈ indepPoly f) :
    IsBestResponse (indepPoly f) m β α x ↔
      ∀ y ∈ indepPoly f, ∑ e, marg m β α x e * y e ≤ ∑ e, marg m β α x e * x e := by
  have hsplit : ∀ y : E → ℝ, ∑ e, marg m β α x e * (y e - x e) =
      ∑ e, marg m β α x e * y e - ∑ e, marg m β α x e * x e := fun y => by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  constructor
  · intro hopt y hy
    have h := hopt.foc (convex_indepPoly f) hy
    rw [hsplit] at h
    linarith
  · intro hmax
    refine isBestResponse_of_foc (fun e => (hβ e).le) hx fun y hy => ?_
    rw [hsplit]
    linarith [hmax y hy]

/-- `prop:optchar` with the hypothesis `α m_e ≥ 0` of its first step (the form that the proofs of
`lem:velocity` and `lem:continuation` (Appendix B.4), `thm:bitlength` (Appendix B.3) and
`thm:polybits` (Appendix B.7), `lem:fullplane`(g) (Appendix B.6.1) and `lem:exactbr` (Appendix C.8)
use; `thm:waterfilling` uses `optchar`): for `β > 0`, a point is the best response if and only if
it lies in `P₊(f)`, its marginals are nonnegative and its level sets `A_θ`, `θ > 0`, are tight.

The STOC version's proof (`stoc-sections/appB-quadratic.tex:13-30`), in its order: (1) at an
optimum `x_e ≤ z_e(α)`, hence `ρ(x) ≥ 0` (`IsBestResponse.marg_nonneg`); (2) `x` is optimal if and
only if it maximizes `ρ(x)ᵀy` over `P₊(f)` (`isBestResponse_iff_maximises`); (3)-(6) for
`ρ(x) ≥ 0` and `x ∈ P₊(f)`: (3) for the distinct positive values `θ_1 > ⋯ > θ_k > 0` of `ρ(x)`,
`θ_{k+1} := 0` and `A_i := A_{θ_i}(x)`, `ρ(x)ᵀy = ∑_{i=1}^k (θ_i − θ_{i+1}) y(A_i)`
(`Stoc.layerCake` with level `0`; indices from 0, `theta ρ(x) 0 i` is `θ_{i+1}`); (4) by
Edmonds' greedy theorem [Edm03, (19)], the maximum over `P₊(f)` is
`∑_{i=1}^k (θ_i − θ_{i+1}) f(A_i)`: the vector `x̄` of Edmonds' greedy theorem (`greedy_pos`) for
`ρ(x)`, in an order with `ρ(x)` nonincreasing, maximizes `ρ(x)ᵀy`, and
`x̄(A_i) = f(A_i)` as `A_i` is a prefix of the order; (5) so it is attained at `x` exactly when
every `A_i` is tight; (6) these are all nonempty positive level sets (`Stoc.levelSet_eq_theta`; an
empty one is tight); if `k = 0`, the condition is vacuous. Together: a best response has
`ρ(x) ≥ 0` by (1), and for `x ∈ P₊(f)` with `ρ(x) ≥ 0`, (2) and (3)-(6) show that `x` is the best
response if and only if its level sets `A_θ(x)`, `θ > 0`, are tight. -/
theorem isBestResponse_iff_levelSets (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    (hm : ∀ e, 0 ≤ α * m e) :
    IsBestResponse (indepPoly f) m β α x ↔ x ∈ indepPoly f ∧ (∀ e, 0 ≤ marg m β α x e) ∧
      ∀ θ > 0, IsTight f x (levelSet m β α x θ) := by
  -- (1) "At an optimum, `x_e ≤ z_e(α)`: otherwise reducing `x_e` to `z_e(α)` preserves
  -- feasibility and increases the utility. Hence `ρ(x) ≥ 0`."
  have h1 : IsBestResponse (indepPoly f) m β α x → ∀ e, 0 ≤ marg m β α x e :=
    fun hopt => hopt.marg_nonneg hβ hm
  -- (2) "By concavity, `x` is optimal if and only if it maximizes the linear objective
  -- `ρ(x)ᵀy` over `y ∈ P₊(f)`: necessity follows by taking directional derivatives towards
  -- feasible points, and sufficiency from concavity, which yields
  -- `U_A(y | α) − U_A(x | α) ≤ ρ(x)ᵀ(y − x)`."
  have h2 : x ∈ indepPoly f → (IsBestResponse (indepPoly f) m β α x ↔
      ∀ y ∈ indepPoly f, ∑ e, marg m β α x e * y e ≤ ∑ e, marg m β α x e * x e) :=
    isBestResponse_iff_maximises hβ
  -- (3)-(6), for `ρ(x) ≥ 0` and `x ∈ P₊(f)`: `x` maximizes `ρ(x)ᵀy` over `P₊(f)` if and only if
  -- every level set `A_θ(x)`, `θ > 0`, is tight.
  have h36 : x ∈ indepPoly f → (∀ e, 0 ≤ marg m β α x e) →
      ((∀ y ∈ indepPoly f, ∑ e, marg m β α x e * y e ≤ ∑ e, marg m β α x e * x e) ↔
        ∀ θ > 0, IsTight f x (levelSet m β α x θ)) := by
    intro hx hρ
    set ρ := marg m β α x with hρdef
    -- (3) "For `ρ(x) ≥ 0`, let `θ_1 > ⋯ > θ_k > 0` be its distinct positive values, set
    -- `θ_{k+1} := 0`, and put `A_i := A_{θ_i}(x)`. Then
    -- `ρ(x)ᵀy = ∑_{i=1}^k (θ_i − θ_{i+1}) y(A_i)`."
    set k := numVals ρ 0 with hk
    set A : ℕ → Finset E := fun i => levelSet m β α x (theta ρ 0 i) with hA
    have h3 : ∀ y : E → ℝ,
        ∑ e, ρ e * y e = ∑ i ∈ range k, (theta ρ 0 i - theta ρ 0 (i + 1)) * ∑ e ∈ A i, y e := by
      intro y
      have h := layerCake hρ y
      simp only [sub_zero] at h
      exact h
    -- (4) "By Edmonds' greedy theorem [Edm03, (19)], the maximum over `P₊(f)` is
    -- `∑_{i=1}^k (θ_i − θ_{i+1}) f(A_i)`, …"
    set V := ∑ i ∈ range k, (theta ρ 0 i - theta ρ 0 (i + 1)) * f (A i) with hV
    have h4 : (∀ y ∈ indepPoly f, ∑ e, ρ e * y e ≤ V) ∧
        ∃ y ∈ indepPoly f, ∑ e, ρ e * y e = V := by
      -- An order of `E` with `ρ(x)` nonincreasing (ties broken by an enumeration of `E`).
      set κ : E → ℝ ×ₗ Fin (Fintype.card E) := fun e => toLex (-ρ e, Fintype.equivFin E e)
        with hκdef
      have hκ : Injective κ := fun e e' h => by
        simp only [κ, toLex_inj, Prod.mk.injEq] at h
        exact (Fintype.equivFin E).injective h.2
      have hκρ : ∀ e e', κ e < κ e' → ρ e' ≤ ρ e := fun e e' h => by
        simp only [κ, Prod.Lex.toLex_lt_toLex, neg_lt_neg_iff] at h
        rcases h with h | ⟨h, _⟩
        · exact h.le
        · linarith
      set σ := sortEquiv κ hκ with hσ
      have hanti : Antitone (ρ ∘ σ) := antitone_comp_sortEquiv hκ hκρ
      obtain ⟨hxb, hmax⟩ := greedy_pos hf σ ρ hanti
      set xb := edmondsVec f σ #(univ.filter fun e => 0 < ρ e) with hxbdef
      -- `x̄(A_i) = f(A_i)`: `A_i` is a prefix of the order, of elements with `ρ_e(x) > 0`.
      have hxbA : ∀ i < k, ∑ e ∈ A i, xb e = f (A i) := by
        intro i hi
        have hpre : A i = prefixSet σ #(A i) := by
          refine eq_prefixSet_card σ fun e he e' he' => ?_
          simp only [A, levelSet, mem_filter, mem_univ, true_and] at he ⊢
          refine he.trans ?_
          have h := hanti he'
          simp only [comp_apply, Equiv.apply_symm_apply] at h
          exact h
        have hsub : A i ⊆ univ.filter fun e => 0 < ρ e := fun e he => by
          simp only [A, levelSet, mem_filter, mem_univ, true_and] at he ⊢
          exact (c_lt_theta hi).trans_le he
        rw [hpre]
        exact sum_prefixSet_edmondsVec hf.empty σ (card_le_card hsub) (card_le_univ _)
      have hval : ∑ e, ρ e * xb e = V := by
        rw [h3 xb]
        exact sum_congr rfl fun i hi => by rw [hxbA i (mem_range.1 hi)]
      exact ⟨fun y hy => hval ▸ hmax y hy, xb, hxb, hval⟩
    -- (5) "… so it is attained at `x` exactly when every `A_i` is tight": termwise, as
    -- `θ_i − θ_{i+1} > 0` and `x(A_i) ≤ f(A_i)`.
    have hgap : ∀ i < k, 0 < theta ρ 0 i - theta ρ 0 (i + 1) := fun i hi =>
      sub_pos.2 (theta_lt_theta (Nat.lt_succ_self i) hi)
    have h5 : ∑ e, ρ e * x e = V ↔ ∀ i < k, IsTight f x (A i) := by
      have hterm : ∀ i ∈ range k,
          0 ≤ (theta ρ 0 i - theta ρ 0 (i + 1)) * (f (A i) - ∑ e ∈ A i, x e) := fun i hi =>
        mul_nonneg (hgap i (mem_range.1 hi)).le (sub_nonneg.2 (hx.2 (A i)))
      have hdiff : V - ∑ e, ρ e * x e =
          ∑ i ∈ range k, (theta ρ 0 i - theta ρ 0 (i + 1)) * (f (A i) - ∑ e ∈ A i, x e) := by
        rw [h3 x, hV, ← sum_sub_distrib]
        exact sum_congr rfl fun i _ => by ring
      constructor
      · intro hxV i hi
        have hz := (sum_eq_zero_iff_of_nonneg hterm).1 (by rw [← hdiff]; linarith) i
          (mem_range.2 hi)
        have h0 := (mul_eq_zero.1 hz).resolve_left (hgap i hi).ne'
        show ∑ e ∈ A i, x e = f (A i)
        linarith
      · intro ht
        have hz : ∑ i ∈ range k,
            (theta ρ 0 i - theta ρ 0 (i + 1)) * (f (A i) - ∑ e ∈ A i, x e) = 0 :=
          sum_eq_zero fun i hi => by
            rw [(ht i (mem_range.1 hi) : ∑ e ∈ A i, x e = f (A i)), sub_self, mul_zero]
        linarith
    -- (6) "These are all nonempty positive level sets. If `k = 0`, the condition is vacuous."
    have h6 : (∀ i < k, IsTight f x (A i)) ↔ ∀ θ > 0, IsTight f x (levelSet m β α x θ) := by
      constructor
      · intro hAi θ hθ
        rcases levelSet_eq_theta (ρ := ρ) hθ with hemp | ⟨i, hi, heq⟩
        · show ∑ e ∈ levelSet m β α x θ, x e = f (levelSet m β α x θ)
          rw [show levelSet m β α x θ = ∅ from hemp, sum_empty, hf.empty]
        · rw [show levelSet m β α x θ = A i from heq]
          exact hAi i hi
      · intro hL i hi
        exact hL _ (c_lt_theta hi)
    -- `x` maximizes `ρ(x)ᵀy` ⟺ the maximum is attained at `x` ⟺ every `A_i` is tight ⟺ every
    -- `A_θ(x)`, `θ > 0`, is tight.
    rw [← h6, ← h5]
    constructor
    · intro hmax
      obtain ⟨y, hy, hyV⟩ := h4.2
      exact le_antisymm (h4.1 x hx) (hyV ▸ hmax y hy)
    · intro hxV y hy
      rw [hxV]
      exact h4.1 y hy
  -- "only if" by (1), (2) and (3)-(6); "if" by (3)-(6) and (2).
  exact ⟨fun hopt => ⟨hopt.1, h1 hopt, (h36 hopt.1 (h1 hopt)).1 ((h2 hopt.1).1 hopt)⟩,
    fun ⟨hx, hρ, ht⟩ => (h2 hx).2 ((h36 hx hρ).2 ht)⟩

/-- **`prop:optchar`** (Proposition 3.1, statement `stoc-sections/05-best-response.tex:19-21`, proof
`stoc-sections/appB-quadratic.tex:13-30`): for quadratic costs with `β > 0`, rewards `m ≥ 0` and a
share `α ≥ 0`, a point `x ∈ P₊(f)` is the best response to `α` if and only if `ρ(x) ≥ 0` and
every level set `A_θ(x)`, `θ > 0`, is tight, i.e., `x(A_θ(x)) = f(A_θ(x))`. In particular,
`0 ≤ x*_e(α) ≤ α t_e` for all `e`.
The proof is that of `isBestResponse_iff_levelSets`; the last sentence is its step (1) for
`x*(α)` (`IsBestResponse.le_z`). -/
theorem optchar (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hα : 0 ≤ α)
    (hx : x ∈ indepPoly f) :
    (IsBestResponse (indepPoly f) m β α x ↔
      (∀ e, 0 ≤ marg m β α x e) ∧ ∀ θ > 0, IsTight f x (levelSet m β α x θ)) ∧
      ∀ e, 0 ≤ bestResponse f m β α e ∧ bestResponse f m β α e ≤ α * (m e / β e) := by
  have hαm : ∀ e, 0 ≤ α * m e := fun e => mul_nonneg hα (hm e)
  refine ⟨?_, fun e => ?_⟩
  · rw [isBestResponse_iff_levelSets hf hβ hαm]
    exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  · -- "In particular, `0 ≤ x*_e(α) ≤ α t_e`": step (1) for `x*(α)`, with `z_e(α) = α t_e`.
    exact (isBestResponse_bestResponse hf m β α).le_z hβ hαm e

/-- `prop:optchar`, "only if": every level set `A_θ`, `θ > 0`, of the best response is tight. -/
theorem IsBestResponse.levelSet_tight (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    (hm : ∀ e, 0 ≤ α * m e) (hx : IsBestResponse (indepPoly f) m β α x) {θ : ℝ} (hθ : 0 < θ) :
    IsTight f x (levelSet m β α x θ) :=
  ((isBestResponse_iff_levelSets hf hβ hm).1 hx).2.2 θ hθ

/-! ### `thm:levelsets` -/

/-- The marginals at the best response, `ρ(α) := ρ(x*(α))` (`stoc-sections/05-best-response.tex:30`,
with `eq:marg`), that is, the optimal marginals `ρ_e(α) = α m_e − β_e x*_e(α)`
(`stoc-sections/appB-quadratic.tex:216-218`). -/
def rho (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) (e : E) : ℝ :=
  marg m β α (bestResponse f m β α) e

/-- The level sets at the best response, `A_θ(α) := A_θ(x*(α))`
(`stoc-sections/05-best-response.tex:30`), that is, `A_θ(α) = {e | ρ_e(α) ≥ θ}`
(`stoc-sections/appB-quadratic.tex:216-218`). -/
def optLevelSet (f : Finset E → ℝ) (m β : E → ℝ) (α θ : ℝ) : Finset E :=
  univ.filter fun e => θ ≤ rho f m β α e

/-- `F_{α,θ}(S) = f(S) − α t(S) + θ β⁻¹(S)`, with `t_e = m_e/β_e`, `t(S) = ∑_{e∈S} t_e`, and
`β⁻¹(S) = ∑_{e∈S} 1/β_e` (`stoc-sections/05-best-response.tex:12, 31`). -/
def levelFun (f : Finset E → ℝ) (m β : E → ℝ) (α θ : ℝ) (S : Finset E) : ℝ :=
  f S - α * ∑ e ∈ S, m e / β e + θ * ∑ e ∈ S, 1 / β e

omit [Fintype E] in
/-- `F_{α,θ}` is submodular (not in the paper: the STOC version uses this without proof, when it
applies Topkis's monotonicity theorem to `F_{α,θ}` and `F_{α',θ}` in the proof of `thm:monmarg`,
`stoc-sections/appB-quadratic.tex:241-244`): `f` is, and the other two terms are modular. -/
theorem levelFun_submodular (hf : Submodular f) (m β : E → ℝ) (α θ : ℝ) :
    Submodular (levelFun f m β α θ) := by
  intro S T
  unfold levelFun
  have h1 := sum_union_inter (s₁ := S) (s₂ := T) (f := fun e => m e / β e)
  have h2 := sum_union_inter (s₁ := S) (s₂ := T) (f := fun e => 1 / β e)
  have e1 : α * ∑ e ∈ S ∪ T, m e / β e + α * ∑ e ∈ S ∩ T, m e / β e =
      α * ∑ e ∈ S, m e / β e + α * ∑ e ∈ T, m e / β e := by
    rw [← mul_add, ← mul_add, h1]
  have e2 : θ * ∑ e ∈ S ∪ T, 1 / β e + θ * ∑ e ∈ S ∩ T, 1 / β e =
      θ * ∑ e ∈ S, 1 / β e + θ * ∑ e ∈ T, 1 / β e := by
    rw [← mul_add, ← mul_add, h2]
  have h3 := hf S T
  linarith

/-- `thm:levelsets` for a best response `x` (with the hypothesis `α m_e ≥ 0` of `prop:optchar`):
for every `θ > 0`, the level set `A = A_θ` minimizes `F_{α,θ}` and contains every minimizer.

The STOC version's proof (`stoc-sections/appB-quadratic.tex:221-233`): (1) as
`x_e = α t_e − β_e⁻¹ ρ_e`, `F_{α,θ}(S) = f(S) − x(S) + ∑_{e∈S} β_e⁻¹(θ − ρ_e)`; (2)
`F_{α,θ}(S) ≥ ∑_{e∈S} β_e⁻¹(θ − ρ_e)`, as `x ∈ P₊(f)`, with equality if and only if `S` is tight;
(3) `∑_{e∈S} β_e⁻¹(θ − ρ_e) ≥ ∑_{e : ρ_e > θ} β_e⁻¹(θ − ρ_e)`, with equality if and only if
`{e | ρ_e > θ} ⊆ S ⊆ A`; (4) as `A` is tight (`prop:optchar`), it attains the lower bound, so it
is a minimizer, and every minimizer is contained in `A`. -/
theorem IsBestResponse.levelSet_isMaxMinimiser (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    (hm : ∀ e, 0 ≤ α * m e) (hx : IsBestResponse (indepPoly f) m β α x) {θ : ℝ} (hθ : 0 < θ) :
    (∀ S, levelFun f m β α θ (levelSet m β α x θ) ≤ levelFun f m β α θ S) ∧
      ∀ S, levelFun f m β α θ S ≤ levelFun f m β α θ (levelSet m β α x θ) →
        S ⊆ levelSet m β α x θ := by
  set A := levelSet m β α x θ with hA
  set ρ := marg m β α x with hρ
  set w : E → ℝ := fun e => (θ - ρ e) / β e with hw
  -- (1) "As `x_e = α t_e − β_e⁻¹ ρ_e` for every `e ∈ E`, every `S ⊆ E` satisfies
  -- `F_{α,θ}(S) = f(S) − x(S) + ∑_{e∈S} β_e⁻¹(θ − ρ_e)
  -- ≥ ∑_{e∈S} β_e⁻¹(θ − ρ_e) ≥ ∑_{e∈E : ρ_e>θ} β_e⁻¹(θ − ρ_e)`."
  -- Here the equality; the two inequalities are steps (2) and (3).
  have h1 : ∀ S, levelFun f m β α θ S = (f S - ∑ e ∈ S, x e) + ∑ e ∈ S, w e := by
    intro S
    have key : ∀ e, -(α * (m e / β e)) + θ * (1 / β e) = -x e + w e := by
      intro e
      simp only [w, ρ, marg]
      have := (hβ e).ne'
      field_simp
      ring
    unfold levelFun
    rw [mul_sum, mul_sum]
    have : f S - ∑ e ∈ S, α * (m e / β e) + ∑ e ∈ S, θ * (1 / β e) =
        f S + ∑ e ∈ S, (-(α * (m e / β e)) + θ * (1 / β e)) := by
      rw [sum_add_distrib, sum_neg_distrib]
      ring
    rw [this, sum_congr rfl fun e _ => key e, sum_add_distrib, sum_neg_distrib]
    ring
  -- (2) "The first inequality holds as `x ∈ P₊(f)`, with equality if and only if `S` is
  -- tight, …"
  have h2 : ∀ S, 0 ≤ f S - ∑ e ∈ S, x e ∧ (f S - ∑ e ∈ S, x e = 0 ↔ IsTight f x S) := by
    intro S
    refine ⟨sub_nonneg.2 (hx.1.2 S), ?_⟩
    unfold IsTight
    constructor <;> intro h <;> linarith
  -- (3) "… and the second holds with equality if and only if `{e : ρ_e > θ} ⊆ S ⊆ A`."
  set P := univ.filter fun e => θ < ρ e with hP
  set LB := ∑ e ∈ P, w e with hLB
  have hwneg : ∀ e, w e < 0 ↔ θ < ρ e := fun e => by
    simp only [w]
    rw [div_neg_iff]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_lt.2 (hβ e).le)
      · linarith
    · intro h
      exact Or.inr ⟨by linarith, hβ e⟩
  have hwA : ∀ e, e ∈ A ↔ w e ≤ 0 := fun e => by
    simp only [A, levelSet, mem_filter, mem_univ, true_and, w]
    rw [div_nonpos_iff]
    constructor
    · intro h
      exact Or.inr ⟨by rw [← hρ] at h; linarith, (hβ e).le⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_le.2 (hβ e))
      · rw [← hρ]
        linarith
  have h3 : ∀ S : Finset E, LB ≤ ∑ e ∈ S, w e ∧ (∑ e ∈ S, w e = LB ↔ P ⊆ S ∧ S ⊆ A) := by
    intro S
    -- `∑_S w − LB = ∑_{S ∖ P} w − ∑_{P ∖ S} w`, with `w ≥ 0` on `S ∖ P` and `w < 0` on `P ∖ S`.
    have hS := sum_inter_add_sum_sdiff S P w
    have hPs := sum_inter_add_sum_sdiff P S w
    rw [inter_comm] at hPs
    have hpos : ∀ e ∈ S \ P, 0 ≤ w e := fun e he => by
      have : ¬ θ < ρ e := fun h => (mem_sdiff.1 he).2 (mem_filter.2 ⟨mem_univ e, h⟩)
      exact not_lt.1 fun h => this ((hwneg e).1 h)
    have hneg : ∀ e ∈ P \ S, w e < 0 := fun e he => (hwneg e).2 (mem_filter.1 (mem_sdiff.1 he).1).2
    have hA0 : 0 ≤ ∑ e ∈ S \ P, w e := sum_nonneg hpos
    have hB0 : ∑ e ∈ P \ S, w e ≤ 0 := sum_nonpos fun e he => (hneg e he).le
    refine ⟨by linarith, ⟨fun heq => ?_, fun ⟨hPS, hSA⟩ => ?_⟩⟩
    · have hA' : ∑ e ∈ S \ P, w e = 0 := by linarith
      have hB' : ∑ e ∈ P \ S, w e = 0 := by linarith
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · by_contra heS
        have := (sum_eq_zero_iff_of_nonpos fun e he => (hneg e he).le).1 hB' e
          (mem_sdiff.2 ⟨he, heS⟩)
        exact absurd this (hneg e (mem_sdiff.2 ⟨he, heS⟩)).ne
      · rw [hwA]
        by_cases heP : e ∈ P
        · exact ((hwneg e).2 (mem_filter.1 heP).2).le
        · exact ((sum_eq_zero_iff_of_nonneg hpos).1 hA' e (mem_sdiff.2 ⟨he, heP⟩)).le
    · have hA' : ∑ e ∈ S \ P, w e = 0 := sum_eq_zero fun e he => le_antisymm
        ((hwA e).1 (hSA (mem_sdiff.1 he).1)) (hpos e he)
      have hB' : P \ S = ∅ := sdiff_eq_empty_iff_subset.2 hPS
      rw [hB', sum_empty] at hPs
      linarith
  -- (4) "As `A` is tight (`prop:optchar`), it attains the lower bound, so it is a minimizer, and
  -- every minimizer is contained in `A`."
  have hAt : IsTight f x A := hx.levelSet_tight hf hβ hm hθ
  have hPA : P ⊆ A := fun e he => by
    simp only [P, mem_filter, mem_univ, true_and] at he
    simp only [A, levelSet, mem_filter, mem_univ, true_and]
    rw [← hρ]
    exact he.le
  have hFA : levelFun f m β α θ A = LB := by
    rw [h1, ((h2 A).2).2 hAt, zero_add]
    exact ((h3 A).2).2 ⟨hPA, Subset.rfl⟩
  refine ⟨fun S => ?_, fun S hS => ?_⟩
  · rw [hFA, h1]
    linarith [(h2 S).1, (h3 S).1]
  · rw [hFA, h1] at hS
    have hS2 := (h2 S).1
    have hS3 := (h3 S).1
    exact (((h3 S).2).1 (by linarith)).2

/-- **`thm:levelsets`** (Theorem 3.3, statement `stoc-sections/05-best-response.tex:35-37`, proof
`stoc-sections/appB-quadratic.tex:221-233`): for all `α ≥ 0`, `θ > 0`, the level set `A_θ(α)` of
the best response `x*(α)` is the unique maximal minimizer of `F_{α,θ}`: it minimizes `F_{α,θ}`
and contains every minimizer. Proof: `IsBestResponse.levelSet_isMaxMinimiser`. -/
theorem levelsets (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (hα : 0 ≤ α)
    {θ : ℝ} (hθ : 0 < θ) :
    (∀ S, levelFun f m β α θ (optLevelSet f m β α θ) ≤ levelFun f m β α θ S) ∧
      ∀ S, levelFun f m β α θ S ≤ levelFun f m β α θ (optLevelSet f m β α θ) →
        S ⊆ optLevelSet f m β α θ :=
  (isBestResponse_bestResponse hf m β α).levelSet_isMaxMinimiser hf hβ
    (fun e => mul_nonneg hα (hm e)) hθ

/-! ### `thm:monmarg` -/

omit [Fintype E] in
/-- Topkis's monotonicity theorem in the form the STOC version uses (not in the paper: it cites
[Top78, Thms. 6.1–6.2], `stoc-sections/appB-quadratic.tex:244`): if `A` minimizes a submodular `F`,
every `S` with `G(S) ≤ G(A')` lies in `A'` (for instance, `A'` is the maximal minimizer of `G`), and
`G − F` is nonincreasing under inclusion, then `A ⊆ A'`. -/
theorem subset_of_isMinimiser {F G : Finset E → ℝ} (hF : Submodular F)
    (hGF : ∀ S T : Finset E, S ⊆ T → G T - F T ≤ G S - F S) {A A' : Finset E}
    (hA : ∀ S, F A ≤ F S) (hmax : ∀ S, G S ≤ G A' → S ⊆ A') : A ⊆ A' := by
  have h1 := hF A A'
  have h2 := hA (A ∩ A')
  have h3 := hGF A' (A ∪ A') subset_union_right
  have h4 : G (A ∪ A') ≤ G A' := by linarith
  exact subset_union_left.trans (hmax _ h4)

/-- `thm:monmarg` for best responses: for `0 ≤ α ≤ α'`, every marginal of the best response at
`α` is at most the one at `α'`.

The STOC version's proof (`stoc-sections/appB-quadratic.tex:240-248`): (1) for `θ > 0`,
`F_{α',θ} − F_{α,θ} = −(α' − α) t` is modular and nonincreasing under inclusion, (2) so
`A_θ(α) ⊆ A_θ(α')` by `thm:levelsets` and Topkis's monotonicity theorem [Top78, Thms. 6.1–6.2]
(`subset_of_isMinimiser`); (3) if `ρ_e(α) > ρ_e(α')`, a `θ` with `ρ_e(α) > θ > ρ_e(α') ≥ 0`
gives `e ∈ A_θ(α) ∖ A_θ(α')`, a contradiction. -/
theorem IsBestResponse.marg_le (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e)
    {α α' : ℝ} {x x' : E → ℝ} (hα : 0 ≤ α) (hle : α ≤ α')
    (hx : IsBestResponse (indepPoly f) m β α x) (hx' : IsBestResponse (indepPoly f) m β α' x')
    (e : E) : marg m β α x e ≤ marg m β α' x' e := by
  have hαm : ∀ e, 0 ≤ α * m e := fun e => mul_nonneg hα (hm e)
  have hα'm : ∀ e, 0 ≤ α' * m e := fun e => mul_nonneg (hα.trans hle) (hm e)
  -- "Let `0 ≤ α < α'` and `θ > 0`."
  -- The Lean takes `0 ≤ α ≤ α'` (`hα`, `hle`), and every `θ > 0` in (1) and (2).
  -- (1) "The difference `F_{α',θ} − F_{α,θ} = −(α' − α) t` is modular and nonincreasing under
  -- inclusion, …"
  have h1 : ∀ θ S, levelFun f m β α' θ S - levelFun f m β α θ S =
      -((α' - α) * ∑ e ∈ S, m e / β e) := by
    intro θ S
    unfold levelFun
    ring
  have h1' : ∀ θ, ∀ S T : Finset E, S ⊆ T →
      levelFun f m β α' θ T - levelFun f m β α θ T ≤
        levelFun f m β α' θ S - levelFun f m β α θ S := by
    intro θ S T hST
    rw [h1, h1]
    have : ∑ e ∈ S, m e / β e ≤ ∑ e ∈ T, m e / β e :=
      sum_le_sum_of_subset_of_nonneg hST fun e _ _ => div_nonneg (hm e) (hβ e).le
    nlinarith
  -- (2) "… so `A_θ(α) ⊆ A_θ(α')` by `thm:levelsets` and Topkis's monotonicity theorem
  -- [Top78, Thms. 6.1–6.2]."
  have h2 : ∀ θ > 0, levelSet m β α x θ ⊆ levelSet m β α' x' θ := fun θ hθ =>
    subset_of_isMinimiser (levelFun_submodular hf.submod m β α θ) (h1' θ)
      (hx.levelSet_isMaxMinimiser hf hβ hαm hθ).1 (hx'.levelSet_isMaxMinimiser hf hβ hα'm hθ).2
  -- (3) "If `ρ_e(α) > ρ_e(α')` for some `e`, then a `θ` with `ρ_e(α) > θ > ρ_e(α') ≥ 0` gives
  -- `e ∈ A_θ(α) ∖ A_θ(α')`, a contradiction."
  by_contra hlt
  rw [not_le] at hlt
  have h0 : 0 ≤ marg m β α' x' e := hx'.marg_nonneg hβ hα'm e
  set θ := (marg m β α x e + marg m β α' x' e) / 2 with hθdef
  have hθ : 0 < θ := by
    rw [hθdef]
    linarith
  have heA : e ∈ levelSet m β α x θ := by
    simp only [levelSet, mem_filter, mem_univ, true_and, hθdef]
    linarith
  have := h2 θ hθ heA
  simp only [levelSet, mem_filter, mem_univ, true_and, hθdef] at this
  linarith

/-- **`thm:monmarg`** (Theorem B.4, statement `stoc-sections/appB-quadratic.tex:237-239`, proof
`stoc-sections/appB-quadratic.tex:240-248`): for every `e ∈ E`, the marginal
`α ↦ ρ_e(α) = α m_e − β_e x*_e(α)` is nondecreasing on `[0, ∞)`. Proof:
`IsBestResponse.marg_le`. -/
theorem monmarg (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) (e : E) :
    MonotoneOn (fun α => rho f m β α e) (Set.Ici 0) :=
  fun α hα α' _ hle => (isBestResponse_bestResponse hf m β α).marg_le hf hβ hm hα hle
    (isBestResponse_bestResponse hf m β α') e

end

end Stoc
