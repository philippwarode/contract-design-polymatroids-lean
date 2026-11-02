-- stamp r9 2026-11-02
import Stoc.OptimalShare.Reward
import Stoc.Hardness.FullPlane

/-!
# Three operations on instances

The STOC version's `lem:ops` (Appendix B.2, `stoc-sections/appB-quadratic.tex`: the direct sum at
line 293, the statement at lines 295-302, the proof at lines 304-337):

* `ops_a`, part (a): if `f = f_1 ⊕ f_2` for rank functions `f_1, f_2`, then `x* = (x*_1, x*_2)`
  and `r(x*(α)) = r_1(x*_1(α)) + r_2(x*_2(α))`;
* `ops_b`, part (b): for `σ > 0`, `(f, m/σ, β)` has the best response `α ↦ x*(α/σ)` and the
  reward `r(x*(α/σ))/σ` under it;
* `ops_c`, part (c): for `C, α_∘ > 0`, adding an element `e` as a direct summand with
  `f({e}) = C`, `m_e = 1` and `β_e = α_∘/C`, a capped linear summand, adds the capped linear
  function `C min(α/α_∘, 1)` to the reward under the best response;
* `ops`: the statement of the lemma, the conjunction of (a)–(c), each part with its own instance
  (that of (a) is the direct sum itself), proved by the three parts, in the order of the proof
  ("We first show (a).", "We next show (b).", "Finally, we show (c).").

The direct sum `f_1 ⊕ f_2` on disjoint ground sets `E_1`, `E_2` is `dsum f₁ f₂` on the type
`E₁ ⊕ E₂`, with `(f_1 ⊕ f_2)(S) = f_1(S ∩ E_1) + f_2(S ∩ E_2)` and `S ∩ E_1 = S.toLeft`. The
rewards and curvatures of the direct sum are `Sum.elim m₁ m₂` and `Sum.elim β₁ β₂`, so that `m₁`
is `m|_{E_1}`. The reward `r(x*(α))` of an instance under its best response is `Stoc.grossValue`.
The rank function of an instance with a capped linear summand is `knob f C` (`knob` is the name of
the earlier versions of the paper, which called a capped linear summand a "knob"; the STOC
version's `α_∘` is `αk` in the Lean).
The added steps (not in the paper) are the lemmas `isRankFunction_dsum` (the direct sum of two
rank functions is one), `isRankFunction_single` (so is the function of one element with capacity
`C`) and `bestResponse_single` (the maximizer of the one-dimensional problem of (c)).
`lem:fullplane`(f), the direct sum in the full plane, is `fullplane_f` (`xi_dirSum`) of
`Stoc/Hardness/FullPlane.lean`.

Taken over on 2026-10-20 from `Paper/Hardness/Operations.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### Direct sums -/

section DirectSum

variable {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂] [DecidableEq E₁] [DecidableEq E₂]

/-- The direct sum `(f_1 ⊕ f_2)(S) := f_1(S ∩ E_1) + f_2(S ∩ E_2)` on `E₁ ⊕ E₂`
(`stoc-sections/appB-quadratic.tex:291`). -/
def dsum (f₁ : Finset E₁ → ℝ) (f₂ : Finset E₂ → ℝ) (T : Finset (E₁ ⊕ E₂)) : ℝ :=
  f₁ T.toLeft + f₂ T.toRight

variable {f₁ : Finset E₁ → ℝ} {f₂ : Finset E₂ → ℝ}

omit [Fintype E₁] [Fintype E₂] in
/-- The direct sum of two polymatroid rank functions is one (not in the paper: in `lem:ops`(a),
`f = f_1 ⊕ f_2` is the rank function of the instance `(f, m, β)`, so the paper takes it as
given). -/
theorem isRankFunction_dsum (h₁ : IsRankFunction f₁) (h₂ : IsRankFunction f₂) :
    IsRankFunction (dsum f₁ f₂) where
  empty := by
    have a : (∅ : Finset (E₁ ⊕ E₂)).toLeft = ∅ := by ext; simp
    have b : (∅ : Finset (E₁ ⊕ E₂)).toRight = ∅ := by ext; simp
    simp only [Hardness.dsum, a, b, h₁.empty, h₂.empty, add_zero]
  mono S T hST := add_le_add (h₁.mono (toLeft_subset_toLeft hST))
    (h₂.mono (toRight_subset_toRight hST))
  submod S T := by
    have a := h₁.submod S.toLeft T.toLeft
    have b := h₂.submod S.toRight T.toRight
    simp only [Hardness.dsum, toLeft_union, toLeft_inter, toRight_union, toRight_inter]
    linarith

omit [Fintype E₁] [Fintype E₂] [DecidableEq E₁] [DecidableEq E₂] in
/-- `lem:ops`(a), the first two steps: `P₊(f_1 ⊕ f_2) = P₊(f_1) × P₊(f_2)`. -/
theorem mem_indepPoly_dsum (h₁ : f₁ ∅ = 0) (h₂ : f₂ ∅ = 0) {x : E₁ ⊕ E₂ → ℝ} :
    x ∈ indepPoly (dsum f₁ f₂) ↔
      (fun e => x (Sum.inl e)) ∈ indepPoly f₁ ∧ (fun e => x (Sum.inr e)) ∈ indepPoly f₂ := by
  constructor
  · -- (1) "If `x ∈ P₊(f)` and `S ⊆ E_i`, then `x(S) ≤ f(S) = f_i(S)`, as the other summand
    -- vanishes on the empty set, so `x|_{E_i} ∈ P₊(f_i)`."
    rintro ⟨hx0, hx⟩
    refine ⟨⟨fun e => hx0 _, fun S => ?_⟩, ⟨fun e => hx0 _, fun S => ?_⟩⟩
    · have := hx (S.disjSum ∅)
      rw [sum_disjSum, sum_empty, add_zero] at this
      simpa only [Hardness.dsum, toLeft_disjSum, toRight_disjSum, h₂, add_zero] using this
    · have := hx ((∅ : Finset E₁).disjSum S)
      rw [sum_disjSum, sum_empty, zero_add] at this
      simpa only [Hardness.dsum, toLeft_disjSum, toRight_disjSum, h₁, zero_add] using this
  · -- (2) "Conversely, if `x|_{E_i} ∈ P₊(f_i)` for `i = 1, 2`, then `x ≥ 0` and
    -- `x(S) = x(S ∩ E_1) + x(S ∩ E_2) ≤ f_1(S ∩ E_1) + f_2(S ∩ E_2) = f(S)` for every
    -- `S ⊆ E`."
    rintro ⟨⟨hx1, hS1⟩, ⟨hx2, hS2⟩⟩
    refine ⟨fun e => ?_, fun T => ?_⟩
    · rcases e with e | e
      · exact hx1 e
      · exact hx2 e
    · rw [← toLeft_disjSum_toRight (u := T), sum_disjSum]
      simp only [Hardness.dsum, toLeft_disjSum, toRight_disjSum]
      exact add_le_add (hS1 _) (hS2 _)

omit [DecidableEq E₁] [DecidableEq E₂] in
/-- `lem:ops`(a), the third step: the agent's utility is separable, the sum of the utilities of
the two summands at `x|_{E_1}` and `x|_{E_2}`. -/
lemma utility_sumElim (m₁ β₁ : E₁ → ℝ) (m₂ β₂ : E₂ → ℝ) (α : ℝ) (x : E₁ ⊕ E₂ → ℝ) :
    utility (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α x =
      utility m₁ β₁ α (fun e => x (Sum.inl e)) + utility m₂ β₂ α (fun e => x (Sum.inr e)) := by
  simp only [utility_eq_sum]
  rw [Fintype.sum_sum_type]
  rfl

/-- `lem:ops`(a) without the model's `m ≥ 0`, which its proof does not use: the form that
`ops_c` and `lem:combsum`(b) take. The paper's statement of (a) is `ops_a`, a part of `ops`. -/
theorem ops_a_aux (h₁ : IsRankFunction f₁) (h₂ : IsRankFunction f₂) {m₁ β₁ : E₁ → ℝ}
    {m₂ β₂ : E₂ → ℝ} (hβ₁ : ∀ e, 0 < β₁ e) (hβ₂ : ∀ e, 0 < β₂ e) :
    (∀ α, 0 ≤ α → bestResponse (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α =
      Sum.elim (bestResponse f₁ m₁ β₁ α) (bestResponse f₂ m₂ β₂ α)) ∧
    ∀ α, 0 ≤ α → grossValue (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α =
      grossValue f₁ m₁ β₁ α + grossValue f₂ m₂ β₂ α := by
  have hβ : ∀ e, 0 < Sum.elim β₁ β₂ e := fun e => by
    rcases e with e | e
    · exact hβ₁ e
    · exact hβ₂ e
  -- (1), (2) "So `P₊(f) = P₊(f_1) × P₊(f_2)`."
  have hprod := fun x => mem_indepPoly_dsum (x := x) h₁.empty h₂.empty
  -- (3) "The agent's utility `U_A(x | α)` is separable: it is the sum of the agent's utilities in
  -- the two instances `(f_i, m|_{E_i}, β|_{E_i})` at `x|_{E_1}` and `x|_{E_2}`, respectively. So,
  -- for every share `α ≥ 0`, its maximizer over the product `P₊(f)` is the pair of the two
  -- maximizers, that is, `x*(α) = (x*_1(α), x*_2(α))`."
  have hpair : ∀ α, bestResponse (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α =
      Sum.elim (bestResponse f₁ m₁ β₁ α) (bestResponse f₂ m₂ β₂ α) := by
    intro α
    have hb1 := isBestResponse_bestResponse h₁ m₁ β₁ α
    have hb2 := isBestResponse_bestResponse h₂ m₂ β₂ α
    have key : IsBestResponse (indepPoly (dsum f₁ f₂)) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α
        (Sum.elim (bestResponse f₁ m₁ β₁ α) (bestResponse f₂ m₂ β₂ α)) := by
      refine ⟨(hprod _).2 ⟨hb1.1, hb2.1⟩, fun z hz => ?_⟩
      obtain ⟨hz1, hz2⟩ := (hprod z).1 hz
      rw [utility_sumElim, utility_sumElim]
      exact add_le_add (hb1.2 _ hz1) (hb2.2 _ hz2)
    exact (key.eq_bestResponse hβ (isRankFunction_dsum h₁ h₂)).symm
  refine ⟨fun α _ => hpair α, fun α _ => ?_⟩
  -- (4) "As `r(x) = m^⊤x = (m|_{E_1})^⊤x|_{E_1} + (m|_{E_2})^⊤x|_{E_2}`, this gives
  -- `r(x*(α)) = r_1(x*_1(α)) + r_2(x*_2(α))`."
  unfold grossValue reward
  rw [hpair α, Fintype.sum_sum_type]
  rfl

/-- **`lem:ops`(a)** (Lemma B.5, `stoc-sections/appB-quadratic.tex:296`, proof lines 303-315): if
`f = f_1 ⊕ f_2` for rank functions `f_1, f_2`, then `x* = (x*_1, x*_2)` and
`r(x*(α)) = r_1(x*_1(α)) + r_2(x*_2(α))`, at every share `α ≥ 0`, where `x*_i` and `r_i` belong to
`(f_i, m|_{E_i}, β|_{E_i})`.

The proof's steps: (1) `x ∈ P₊(f)` restricts to `x|_{E_i} ∈ P₊(f_i)`, (2) and conversely, so
`P₊(f) = P₊(f_1) × P₊(f_2)` (`mem_indepPoly_dsum`); (3) the utility is separable
(`utility_sumElim`), so its maximizer over the product is the pair of the maximizers; (4) the
reward is additive. The steps are in `ops_a_aux`, which does not use the model's `m ≥ 0`. -/
theorem ops_a (h₁ : IsRankFunction f₁) (h₂ : IsRankFunction f₂) {m₁ β₁ : E₁ → ℝ}
    {m₂ β₂ : E₂ → ℝ} (_hm₁ : ∀ e, 0 ≤ m₁ e) (_hm₂ : ∀ e, 0 ≤ m₂ e) (hβ₁ : ∀ e, 0 < β₁ e)
    (hβ₂ : ∀ e, 0 < β₂ e) :
    (∀ α, 0 ≤ α → bestResponse (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α =
      Sum.elim (bestResponse f₁ m₁ β₁ α) (bestResponse f₂ m₂ β₂ α)) ∧
    ∀ α, 0 ≤ α → grossValue (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α =
      grossValue f₁ m₁ β₁ α + grossValue f₂ m₂ β₂ α :=
  ops_a_aux h₁ h₂ hβ₁ hβ₂

end DirectSum

/-! ### Dilations -/

section Dilation

variable {E : Type*} [Fintype E]

/-- `lem:ops`(b), the first step: the agent's utility in `(f, m/σ, β)` at `α` is
`U_A(x | α/σ)` in `(f, m, β)`. -/
lemma utility_dilate (m β : E → ℝ) {σ : ℝ} (hσ : σ ≠ 0) (α : ℝ) :
    utility (fun e => m e / σ) β α = utility m β (α / σ) := by
  funext x
  simp only [utility_eq_sum]
  refine sum_congr rfl fun e _ => ?_
  field_simp

/-- `lem:ops`(b), the first step at every share: for `σ ≠ 0`, the best response of
`(f, m/σ, β)` at `α` is `x*(α/σ)`, as the agent maximizes the same utility over the same
polyhedron (`utility_dilate`). The proof of `lem:ops`(b), `ops_b_aux`, uses it. -/
lemma bestResponse_dilate (f : Finset E → ℝ) (m β : E → ℝ) {σ : ℝ} (hσ : σ ≠ 0) (α : ℝ) :
    bestResponse f (fun e => m e / σ) β α = bestResponse f m β (α / σ) := by
  unfold bestResponse IsBestResponse
  rw [utility_dilate m β hσ]

/-- `lem:ops`(b) without the model's assumptions on the instance (a rank function, `m ≥ 0`,
`β > 0`), which its proof does not use: the form that `lem:combsum`(a), `thm:expbp` and
`thm:polybits` take. The paper's statement of (b) is `ops_b`, a part of `ops`. -/
theorem ops_b_aux (f : Finset E → ℝ) (m β : E → ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∀ α, 0 ≤ α → bestResponse f (fun e => m e / σ) β α = bestResponse f m β (α / σ)) ∧
      ∀ α, 0 ≤ α → grossValue f (fun e => m e / σ) β α = grossValue f m β (α / σ) / σ := by
  -- (1) "At the share `α ≥ 0`, the agent's utility in the instance `(f, m/σ, β)` is
  -- `∑_{e∈E}(α(m_e/σ)x_e − (β_e/2)x_e²) = U_A(x | α/σ)`, the agent's utility in `(f, m, β)` at
  -- the share `α/σ`, over the same polyhedron `P₊(f)`. So the best response of `(f, m/σ, β)` at
  -- `α` is `x*(α/σ)`."
  have hbr : ∀ α, bestResponse f (fun e => m e / σ) β α = bestResponse f m β (α / σ) :=
    bestResponse_dilate f m β hσ.ne'
  refine ⟨fun α _ => hbr α, fun α _ => ?_⟩
  -- (2) "The reward of the new instance is measured with `m/σ`, so its reward under the best
  -- response is `(m/σ)^⊤x*(α/σ) = r(x*(α/σ))/σ`."
  unfold grossValue reward
  rw [hbr α, sum_div]
  refine sum_congr rfl fun e _ => ?_
  ring

/-- **`lem:ops`(b)** (`stoc-sections/appB-quadratic.tex:297`, proof lines 317-329): for `σ > 0`, the
instance `(f, m/σ, β)` has the best response `α ↦ x*(α/σ)` and the reward `r(x*(α/σ))/σ` under it,
at every share `α ≥ 0`.

The proof's steps: (1) the utility of `(f, m/σ, β)` at `α` is `U_A(x | α/σ)` over the same
polyhedron `P₊(f)` (`utility_dilate`), so the best response at `α` is `x*(α/σ)`
(`bestResponse_dilate`); (2) its reward is
`(m/σ)^⊤x*(α/σ) = r(x*(α/σ))/σ`. The steps are in `ops_b_aux`, which does not use the assumptions
on the instance (a rank function, `m ≥ 0`, `β > 0`). -/
theorem ops_b [DecidableEq E] (f : Finset E → ℝ) (m β : E → ℝ) (_hf : IsRankFunction f)
    (_hm : ∀ e, 0 ≤ m e) (_hβ : ∀ e, 0 < β e) {σ : ℝ} (hσ : 0 < σ) :
    (∀ α, 0 ≤ α → bestResponse f (fun e => m e / σ) β α = bestResponse f m β (α / σ)) ∧
      ∀ α, 0 ≤ α → grossValue f (fun e => m e / σ) β α = grossValue f m β (α / σ) / σ :=
  ops_b_aux f m β hσ

end Dilation

/-! ### Capped linear summands -/

/-- The function of one element with capacity `C`, `π_C(∅) = 0` and `π_C({e}) = C`. -/
def single (C : ℝ) (T : Finset Unit) : ℝ := if T.Nonempty then C else 0

lemma finset_unit (T : Finset Unit) : T = ∅ ∨ T = univ := by
  rcases T.eq_empty_or_nonempty with h | ⟨u, hu⟩
  · exact Or.inl h
  · right
    ext v
    simp only [mem_univ, iff_true]
    rwa [Subsingleton.elim v u]

/-- The function of one element with capacity `C ≥ 0` is a polymatroid rank function (not in the
paper: `lem:ops`(c) takes the instance with the capped linear summand for an instance). -/
theorem isRankFunction_single {C : ℝ} (hC : 0 ≤ C) : IsRankFunction (single C) where
  empty := by simp [single]
  mono S T hST := by
    rcases finset_unit S with rfl | rfl <;> rcases finset_unit T with rfl | rfl <;>
      simp [single, hC]
    exact absurd (hST (mem_univ ())) (notMem_empty _)
  submod S T := by
    rcases finset_unit S with rfl | rfl <;> rcases finset_unit T with rfl | rfl <;>
      simp [single]

/-- The one-dimensional maximizer of `lem:ops`(c): for `C, α_∘ > 0` (`αk`) and `α ≥ 0`, the point
`y = min(α C/α_∘, C)` maximizes `α y − α_∘ y²/(2C)` over `[0, C] = P₊(π_C)` (not in the paper: the
STOC version states the maximizer without proof, `appB-quadratic.tex:331-333`). -/
theorem bestResponse_single {C αk : ℝ} (hC : 0 < C) (hαk : 0 < αk) {α : ℝ} (hα : 0 ≤ α) :
    bestResponse (single C) (fun _ => 1) (fun _ => αk / C) α =
      fun _ => min (α * C / αk) C := by
  set y := min (α * C / αk) C
  have hb : 0 < αk / C := div_pos hαk hC
  have hy0 : 0 ≤ y := le_min (by positivity) hC.le
  have hyC : y ≤ C := min_le_right _ _
  have hmem : (fun _ : Unit => y) ∈ indepPoly (single C) := by
    refine ⟨fun _ => hy0, fun S => ?_⟩
    rcases finset_unit S with rfl | rfl
    · simp [single]
    · simpa [single] using hyC
  have key : IsBestResponse (indepPoly (single C)) (fun _ => 1) (fun _ => αk / C) α
      (fun _ => y) := by
    refine ⟨hmem, fun z hz => ?_⟩
    have hz0 : 0 ≤ z () := hz.1 ()
    have hzC : z () ≤ C := by simpa [single] using hz.2 univ
    simp only [utility_eq_sum, Finset.univ_unique, Finset.sum_singleton]
    -- the first-order condition `(α − (α_∘/C) y)(z − y) ≤ 0` at `y`
    have hfoc : (α - αk / C * y) * (z () - y) ≤ 0 := by
      rcases le_total (α * C / αk) C with h | h
      · have : y = α * C / αk := min_eq_left h
        have e : α - αk / C * y = 0 := by rw [this]; field_simp; ring
        rw [e, zero_mul]
      · have : y = C := min_eq_right h
        have e : 0 ≤ α - αk / C * y := by
          rw [this, div_mul_cancel₀ _ hC.ne']
          rw [le_div_iff₀ hαk] at h
          nlinarith
        rw [this]
        exact mul_nonpos_of_nonneg_of_nonpos (by rwa [this] at e) (by linarith)
    nlinarith [sq_nonneg (z () - y), mul_nonneg hb.le (sq_nonneg (z () - y))]
  exact (key.eq_bestResponse (fun _ => hb) (isRankFunction_single hC.le)).symm

/-- The capped linear summand of `lem:ops`(c): `f` plus a new direct summand `e` with
`f({e}) = C` (the rank function; the rewards are `Sum.elim m (fun _ => 1)` and the curvatures
`Sum.elim β (fun _ => α_∘/C)`). The name `knob` is that of the earlier versions of the paper. -/
def knob {E : Type*} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (C : ℝ) :
    Finset (E ⊕ Unit) → ℝ :=
  dsum f (single C)

/-- `lem:ops`(c) without the model's `m ≥ 0`, which its proof does not use: the form that the
proofs of `thm:gadget` and `prop:correct` take. The paper's statement of (c) is `ops_c`, a part of
`ops`. -/
theorem ops_c_aux {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ}
    (hf : IsRankFunction f) {m β : E → ℝ} (hβ : ∀ e, 0 < β e) {C αk : ℝ} (hC : 0 < C)
    (hαk : 0 < αk) {α : ℝ} (hα : 0 ≤ α) :
    grossValue (knob f C) (Sum.elim m fun _ => 1) (Sum.elim β fun _ => αk / C) α =
      grossValue f m β α + C * min (α / αk) 1 := by
  obtain ⟨-, hr⟩ := ops_a_aux (m₁ := m) (m₂ := fun _ => 1) hf (isRankFunction_single hC.le) hβ
    (fun _ => div_pos hαk hC)
  -- (1) "By (a), the new coordinate `y` maximizes `α y − α_∘ y²/(2C)` over `[0, C]`, so
  -- `y = min(α C/α_∘, C) = C min(α/α_∘, 1)`."
  have hy : bestResponse (single C) (fun _ => 1) (fun _ => αk / C) α =
      fun _ => C * min (α / αk) 1 := by
    rw [bestResponse_single hC hαk hα]
    funext u
    rw [mul_min_of_nonneg _ _ hC.le, mul_one]
    congr 1
    field_simp
  -- (2) "As `m_e = 1`, the new element adds `y` to the reward."
  unfold knob
  rw [hr α hα]
  congr 1
  unfold grossValue reward
  rw [hy]
  simp

/-- **`lem:ops`(c)** (`stoc-sections/appB-quadratic.tex:298`, proof lines 331-334): let `C, α_∘ > 0`
(`αk`). Adding an element `e` as a direct summand with `f({e}) = C`, `m_e = 1` and `β_e = α_∘/C`, a
capped linear summand (`knob f C`), adds the capped linear function `C min(α/α_∘, 1)` to the reward
under the best response.

The proof's steps: (1) by (a), the new coordinate `y` maximizes `α y − α_∘ y²/(2C)` over `[0, C]`,
so `y = min(α C/α_∘, C) = C min(α/α_∘, 1)` (`bestResponse_single`); (2) as `m_e = 1`, the new
element adds `y` to the reward. The steps are in `ops_c_aux`, which does not use the model's
`m ≥ 0`. -/
theorem ops_c {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ}
    (hf : IsRankFunction f) {m β : E → ℝ} (_hm : ∀ e, 0 ≤ m e) (hβ : ∀ e, 0 < β e) {C αk : ℝ}
    (hC : 0 < C) (hαk : 0 < αk) {α : ℝ} (hα : 0 ≤ α) :
    grossValue (knob f C) (Sum.elim m fun _ => 1) (Sum.elim β fun _ => αk / C) α =
      grossValue f m β α + C * min (α / αk) 1 :=
  ops_c_aux hf hβ hC hαk hα

/-- **`lem:ops`** (Lemma B.5, `stoc-sections/appB-quadratic.tex:293-300`, proof lines 302-335): let
`(f, m, β)` be an instance with best response `x*`. (a) If `f = f_1 ⊕ f_2` for rank functions
`f_1, f_2`, then `x* = (x*_1, x*_2)` and `r(x*(α)) = r_1(x*_1(α)) + r_2(x*_2(α))`, where `x*_i` and
`r_i` belong to `(f_i, m|_{E_i}, β|_{E_i})`. (b) For `σ > 0`, the instance `(f, m/σ, β)` has the
best response `α ↦ x*(α/σ)` and the reward `r(x*(α/σ))/σ` under it. (c) Let `C, α_∘ > 0` (`αk`).
Adding an element `e` as a direct summand with `f({e}) := C`, `m_e := 1` and `β_e := α_∘/C`, a
capped linear summand (`knob f C`), adds the capped linear function `C min(α/α_∘, 1)` to the reward
under the best response.

The instance of (a) is the direct sum itself, on `E₁ ⊕ E₂`, so each part quantifies over its own
instance, with the model's hypotheses (a rank function, `m ≥ 0`, `β > 0`); the identities hold at
every share `α ≥ 0`. Its parts are `ops_a`, `ops_b` and `ops_c`; their docstrings give the paper's
steps. -/
theorem ops :
    -- (a) direct sums
    (∀ {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂] [DecidableEq E₁] [DecidableEq E₂]
      {f₁ : Finset E₁ → ℝ} {f₂ : Finset E₂ → ℝ}, IsRankFunction f₁ → IsRankFunction f₂ →
      ∀ {m₁ β₁ : E₁ → ℝ} {m₂ β₂ : E₂ → ℝ}, (∀ e, 0 ≤ m₁ e) → (∀ e, 0 ≤ m₂ e) →
      (∀ e, 0 < β₁ e) → (∀ e, 0 < β₂ e) →
      (∀ α, 0 ≤ α → bestResponse (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α =
        Sum.elim (bestResponse f₁ m₁ β₁ α) (bestResponse f₂ m₂ β₂ α)) ∧
      ∀ α, 0 ≤ α → grossValue (dsum f₁ f₂) (Sum.elim m₁ m₂) (Sum.elim β₁ β₂) α =
        grossValue f₁ m₁ β₁ α + grossValue f₂ m₂ β₂ α) ∧
    -- (b) dilations
    (∀ {E : Type*} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (m β : E → ℝ),
      IsRankFunction f → (∀ e, 0 ≤ m e) → (∀ e, 0 < β e) → ∀ {σ : ℝ}, 0 < σ →
      (∀ α, 0 ≤ α → bestResponse f (fun e => m e / σ) β α = bestResponse f m β (α / σ)) ∧
        ∀ α, 0 ≤ α → grossValue f (fun e => m e / σ) β α = grossValue f m β (α / σ) / σ) ∧
    -- (c) capped linear summands
    ∀ {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ}, IsRankFunction f →
      ∀ {m β : E → ℝ}, (∀ e, 0 ≤ m e) → (∀ e, 0 < β e) → ∀ {C αk : ℝ}, 0 < C → 0 < αk →
      ∀ {α : ℝ}, 0 ≤ α →
      grossValue (knob f C) (Sum.elim m fun _ => 1) (Sum.elim β fun _ => αk / C) α =
        grossValue f m β α + C * min (α / αk) 1 := by
  -- (1) "We first show (a)." (`ops_a`)
  refine ⟨ops_a, ?_, ?_⟩
  -- (2) "We next show (b)." (`ops_b`)
  · exact ops_b
  -- (3) "Finally, we show (c)." (`ops_c`)
  · exact ops_c

end

end Hardness

end Stoc
