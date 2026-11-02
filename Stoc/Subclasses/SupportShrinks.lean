-- stamp r8 2026-11-02
import Stoc.OptimalShare.Velocity

/-!
# The support of the best response shrinks

The STOC version, Appendix B.8 (`sec:A-subclasses`), Lemma `lem:supportmon`
(`stoc-sections/appB-quadratic.tex:610-642`), which holds for every polymatroid: if `x*_e(α) = 0`
for shares `0 < α < α'`, then `x*_e(α') = 0`. So the support of `x*` is nonincreasing in `α` and
changes at no more than `n` shares.

*  `bestResponse_eq_zero_of_lt`: the first statement, with the STOC version's steps (1)-(8).
*  `supportmon`: the whole lemma. The support is `brSupport`, the shares at which it changes are
  `supportChanges`, and step (9), "every element leaves the support at most once", is
  `supportChanges_subset`: the support changes only at the shares `s_e` at which an element leaves
  it (`leaveShare`).

Steps the STOC version uses without proof, each in its own lemma (D3):
`exists_levelSets_const_right` (step (4), "after shrinking `h`, the chain of positive level sets of
`ρ`, the zero set `Z` and the free set `Φ` are constant on `J`") and `stateConstOn_of_levelSets`
(step (4), "so the state of `sec:A-structure` is constant on `J`"), with the blocks constant by
`blocks_const_of_levelSets` and its reason `rho_eq_iff_levelSets`. Also not in the paper:
`brSupport_eq_of_noChange`, the support is the same at two shares with no change of the support
between them, which the STOC version leaves implicit for the pinning intervals of `thm:laminar`.
Step (2), "then `m_e > 0`, as `0 < x*_e(α') ≤ α' t_e` by `prop:optchar`", cites `prop:optchar`
(`Stoc.optchar`) at its place.

The share `α_` (`\underline\alpha`) of the STOC version is `α₁` here, the share `α̃` is `γ`. The
block `D` of `e` on `J`, the elements `g` with `ρ_g = ρ_e` on `J`, is the block of `e` at a share
`α₃ ∈ J`, `blockOf f m β α₃ e` (the state is constant on `J`), and `Z` is `zeroSet f m β α₃`; the
mean `m̄_D = t(D ∖ Z)/β⁻¹(D ∖ Z)` of `lem:velocity` is `meanReward f m β α₃ e`, a sum over
`blockNZ f m β α₃ e = D ∖ Z` (`Stoc/OptimalShare/Velocity.lean`).

Taken over on 2026-10-21 from `Paper/Subclasses/SupportShrinks.lean` (the long paper's
`lem:support-shrinks`, whose proof the STOC version takes over) for the STOC version (`stoc.tex`);
from then on this copy follows the STOC version.
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {f : Finset E → ℝ} {m β : E → ℝ}

/-! ### The support, its changes, and the state -/

/-- The support `{e | x*_e(α) > 0}` of the best response. -/
def brSupport (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : Finset E :=
  univ.filter fun e => 0 < bestResponse f m β α e

/-- The shares `α > 0` at which the support of `x*` changes: it is not constant on any
neighborhood of `α`. -/
def supportChanges (f : Finset E → ℝ) (m β : E → ℝ) : Set ℝ :=
  {α | 0 < α ∧ ¬ ∀ᶠ α' in 𝓝 α, brSupport f m β α' = brSupport f m β α}

open Classical in
/-- The chain of positive level sets of the marginals at the share `α`: the sets
`A_θ(α) = {e | ρ_e(α) ≥ θ}`, `θ > 0`. -/
def posLevelSets (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : Finset (Finset E) :=
  univ.filter fun S => ∃ θ > 0, S = levelSet m β α (bestResponse f m β α) θ

omit [DecidableEq E] in
theorem mem_brSupport {α : ℝ} {e : E} :
    e ∈ brSupport f m β α ↔ 0 < bestResponse f m β α e := by
  simp [brSupport]

omit [DecidableEq E] in
theorem mem_posLevelSets {α : ℝ} {S : Finset E} :
    S ∈ posLevelSets f m β α ↔ ∃ θ > 0, S = levelSet m β α (bestResponse f m β α) θ := by
  classical
  simp [posLevelSets]

omit [DecidableEq E] in
theorem mem_levelSet_iff_le {α θ : ℝ} {x : E → ℝ} {g : E} :
    g ∈ levelSet m β α x θ ↔ θ ≤ marg m β α x g := by
  simp [levelSet]

omit [DecidableEq E] in
/-- (Not in the paper: a step of `blocks_const_of_levelSets`.) Two elements with positive marginal
have equal marginals exactly when they lie in the same level sets `A_θ(α)`, `θ > 0`. -/
theorem rho_eq_iff_levelSets {α : ℝ} {e e' : E} (he : 0 < rho f m β α e)
    (he' : 0 < rho f m β α e') :
    rho f m β α e = rho f m β α e' ↔
      ∀ S ∈ posLevelSets f m β α, (e ∈ S ↔ e' ∈ S) := by
  have hmem : ∀ θ g, g ∈ levelSet m β α (bestResponse f m β α) θ ↔ θ ≤ rho f m β α g :=
    fun θ g => mem_levelSet_iff_le
  constructor
  · intro h S hS
    obtain ⟨θ, -, rfl⟩ := mem_posLevelSets.1 hS
    rw [hmem, hmem, h]
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · -- `A_{ρ_{e'}}(α)` contains `e'` but not `e`
      have hS : levelSet m β α (bestResponse f m β α) (rho f m β α e') ∈
          posLevelSets f m β α := mem_posLevelSets.2 ⟨_, he', rfl⟩
      have := (h _ hS).2 ((hmem _ e').2 le_rfl)
      rw [hmem] at this
      linarith
    · -- `A_{ρ_e}(α)` contains `e` but not `e'`
      have hS : levelSet m β α (bestResponse f m β α) (rho f m β α e) ∈
          posLevelSets f m β α := mem_posLevelSets.2 ⟨_, he, rfl⟩
      have := (h _ hS).1 ((hmem _ e).2 le_rfl)
      rw [hmem] at this
      linarith

/-- (Not in the paper: step (4) of `lem:supportmon` uses this without proof, in "so the state of
`sec:A-structure` is constant on `J`", `stateConstOn_of_levelSets`.) On a set `J ⊆ (0, ∞)` on which
the family of positive level sets `A_θ(α)` and the free set are constant, the blocks are constant
as well, since two elements with positive marginal have equal marginals exactly when they lie in
the same level sets (`rho_eq_iff_levelSets`); the marginals are nonnegative (`prop:optchar`), so an
element with zero marginal is free, and the free set is constant. -/
theorem blocks_const_of_levelSets (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    (hm : ∀ e, 0 ≤ m e) {J : Set ℝ} (hJ : ∀ α ∈ J, 0 < α)
    (hlev : ∀ α ∈ J, ∀ α' ∈ J, posLevelSets f m β α = posLevelSets f m β α')
    (hΦ : ∀ α ∈ J, ∀ α' ∈ J, ∀ e, rho f m β α e = 0 ↔ rho f m β α' e = 0) :
    ∀ α ∈ J, ∀ α' ∈ J, ∀ e e',
      rho f m β α e = rho f m β α e' ↔ rho f m β α' e = rho f m β α' e' := by
  intro α hα α' hα' e e'
  have hρ0 : ∀ γ ∈ J, ∀ g, 0 ≤ rho f m β γ g := fun γ hγ g =>
    (isBestResponse_bestResponse hf m β γ).marg_nonneg hβ
      (fun g => mul_nonneg (hJ γ hγ).le (hm g)) g
  -- an element has a positive marginal at `α` exactly when it has one at `α'`
  have hpos : ∀ g, 0 < rho f m β α g ↔ 0 < rho f m β α' g := fun g => by
    rw [(hρ0 α hα g).lt_iff_ne', (hρ0 α' hα' g).lt_iff_ne', Ne, Ne, hΦ α hα α' hα' g]
  by_cases he : 0 < rho f m β α e <;> by_cases he' : 0 < rho f m β α e'
  · -- both marginals positive: the same level sets at `α` and at `α'`
    rw [rho_eq_iff_levelSets he he', rho_eq_iff_levelSets ((hpos e).1 he) ((hpos e').1 he'),
      hlev α hα α' hα']
  · -- `e` positive, `e'` free: unequal marginals at `α` and at `α'`
    have h1 : rho f m β α e' = 0 := le_antisymm (not_lt.1 he') (hρ0 α hα e')
    have h2 : rho f m β α' e' = 0 := (hΦ α hα α' hα' e').1 h1
    rw [h1, h2]
    exact ⟨fun h => absurd h he.ne', fun h => absurd h ((hpos e).1 he).ne'⟩
  · -- `e` free, `e'` positive
    have h1 : rho f m β α e = 0 := le_antisymm (not_lt.1 he) (hρ0 α hα e)
    have h2 : rho f m β α' e = 0 := (hΦ α hα α' hα' e).1 h1
    rw [h1, h2]
    exact ⟨fun h => absurd h.symm he'.ne', fun h => absurd h.symm ((hpos e').1 he').ne'⟩
  · -- both free: equal marginals `0` at `α` and at `α'`
    have h1 : rho f m β α e = 0 := le_antisymm (not_lt.1 he) (hρ0 α hα e)
    have h2 : rho f m β α e' = 0 := le_antisymm (not_lt.1 he') (hρ0 α hα e')
    rw [h1, h2, (hΦ α hα α' hα' e).1 h1, (hΦ α hα α' hα' e').1 h2]

/-- (Not in the paper: step (4) of `lem:supportmon` uses this without proof, "so the state of
`sec:A-structure` is constant on `J`".) On a set `J ⊆ (0, ∞)` on which the chain of positive level
sets, the zero set and the free set are constant, the state of `sec:A-structure` is constant: the
blocks are constant by `blocks_const_of_levelSets`. -/
theorem stateConstOn_of_levelSets (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    (hm : ∀ e, 0 ≤ m e) {J : Set ℝ} (hJ : ∀ α ∈ J, 0 < α)
    (hlev : ∀ α ∈ J, ∀ α' ∈ J, posLevelSets f m β α = posLevelSets f m β α')
    (hZ : ∀ α ∈ J, ∀ α' ∈ J, ∀ e, bestResponse f m β α e = 0 ↔ bestResponse f m β α' e = 0)
    (hΦ : ∀ α ∈ J, ∀ α' ∈ J, ∀ e, rho f m β α e = 0 ↔ rho f m β α' e = 0) :
    StateConstOn f m β J :=
  ⟨hΦ, hZ, blocks_const_of_levelSets hf hβ hm hJ hlev hΦ⟩

/-! ### Steps of `lem:supportmon` that the STOC version uses without proof -/

omit [Fintype E] [DecidableEq E] in
/-- (Not in the paper: a step of the proof of `exists_levelSets_const_right`.) An affine function
`γ ↦ c + γ d` keeps its sign just right of `α₁`. -/
theorem exists_sign_const_right (c d α₁ : ℝ) :
    ∃ u > α₁, ∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u,
      (0 < c + γ * d ↔ 0 < c + γ' * d) ∧ (c + γ * d = 0 ↔ c + γ' * d = 0) := by
  by_cases hd : d = 0
  · exact ⟨α₁ + 1, by linarith, fun γ _ γ' _ => by simp [hd]⟩
  -- `u`: the zero `r = −c/d` if it lies right of `α₁`; there is no zero in `(α₁, u)`.
  set r := -c / d with hr
  have hzero : ∀ γ, c + γ * d = 0 ↔ γ = r := by
    intro γ
    rw [hr, eq_div_iff hd]
    constructor <;> intro h <;> linarith
  set u := if α₁ < r then r else α₁ + 1
  have hu : α₁ < u := by
    simp only [u]
    split_ifs with h
    · exact h
    · linarith
  have hnz : ∀ γ ∈ Set.Ioo α₁ u, c + γ * d ≠ 0 := by
    intro γ hγ h0
    rw [hzero] at h0
    subst h0
    simp only [u] at hγ
    split_ifs at hγ with h
    · exact lt_irrefl _ hγ.2
    · exact h hγ.1
  -- An affine function that is positive at `γ` and not positive at `γ'` vanishes between them.
  have hpos : ∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u, 0 < c + γ * d → 0 < c + γ' * d := by
    intro γ hγ γ' hγ' h
    by_contra h'
    rw [not_lt] at h'
    have hcont : ContinuousOn (fun x : ℝ => c + x * d) (Set.uIcc γ γ') := by fun_prop
    obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hcont
      (show (0 : ℝ) ∈ Set.uIcc (c + γ * d) (c + γ' * d) from Set.mem_uIcc.2 (Or.inr ⟨h', h.le⟩))
    have hxJ : x ∈ Set.Ioo α₁ u := Set.OrdConnected.uIcc_subset inferInstance hγ hγ' hx
    exact hnz x hxJ hx0
  exact ⟨u, hu, fun γ hγ γ' hγ' => ⟨⟨hpos γ hγ γ' hγ', hpos γ' hγ' γ hγ⟩,
    ⟨fun h => absurd h (hnz γ hγ), fun h => absurd h (hnz γ' hγ')⟩⟩⟩

omit [DecidableEq E] in
/-- (Not in the paper: step (4) of `lem:supportmon`, "After shrinking `h`, …", is used without
proof.) If `x*` is affine on `[α₁, α₂]`, then on some interval `(α₁, u)`, `u ≤ α₂`, the chain of
positive level sets of `ρ`, the zero set and the free set are constant: each of `x*_g`, `ρ_g` and
`ρ_g − ρ_{g'}` is affine there and keeps its sign just right of `α₁`. -/
theorem exists_levelSets_const_right {α₁ α₂ : ℝ} (h12 : α₁ < α₂) {p w : E → ℝ}
    (haff : ∀ γ ∈ Set.Icc α₁ α₂, bestResponse f m β γ = fun e => p e + γ * w e) :
    ∃ u, α₁ < u ∧ u ≤ α₂ ∧
      (∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u, posLevelSets f m β γ = posLevelSets f m β γ') ∧
      (∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u, ∀ e,
        bestResponse f m β γ e = 0 ↔ bestResponse f m β γ' e = 0) ∧
      (∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u, ∀ e, rho f m β γ e = 0 ↔ rho f m β γ' e = 0) := by
  classical
  -- The affine functions `x*_g`, `ρ_g` and `ρ_g − ρ_{g'}` on `[α₁, α₂]`.
  set c : E → ℝ := fun e => -(β e * p e)
  set d : E → ℝ := fun e => m e - β e * w e
  choose ux hux hx using fun e => exists_sign_const_right (p e) (w e) α₁
  choose uρ huρ hρ using fun e => exists_sign_const_right (c e) (d e) α₁
  choose uρρ huρρ hρρ using fun q : E × E =>
    exists_sign_const_right (c q.1 - c q.2) (d q.1 - d q.2) α₁
  -- `u`: the smallest of these and `α₂`.
  set U : Finset ℝ := insert α₂ ((univ.image ux) ∪ (univ.image uρ) ∪ (univ.image uρρ))
  have hUne : U.Nonempty := insert_nonempty _ _
  set u := U.min' hUne
  have hUgt : ∀ v ∈ U, α₁ < v := by
    intro v hv
    simp only [U, mem_insert, mem_union, mem_image, mem_univ, true_and] at hv
    rcases hv with rfl | ((⟨e, rfl⟩ | ⟨e, rfl⟩) | ⟨q, rfl⟩)
    · exact h12
    · exact hux e
    · exact huρ e
    · exact huρρ q
  have hu : α₁ < u := hUgt _ (min'_mem U hUne)
  have hule : ∀ v ∈ U, u ≤ v := fun v hv => min'_le U v hv
  have huα₂ : u ≤ α₂ := hule α₂ (mem_insert_self _ _)
  have hsub : ∀ v ∈ U, ∀ γ ∈ Set.Ioo α₁ u, γ ∈ Set.Ioo α₁ v :=
    fun v hv γ hγ => ⟨hγ.1, hγ.2.trans_le (hule v hv)⟩
  have hmemx : ∀ e, ux e ∈ U := fun e => by simp [U]
  have hmemρ : ∀ e, uρ e ∈ U := fun e => by simp [U]
  have hmemρρ : ∀ q, uρρ q ∈ U := fun q => by simp [U]
  -- On `(α₁, u)`, `x*` and `ρ` are the affine functions.
  have hxγ : ∀ γ ∈ Set.Ioo α₁ u, ∀ e, bestResponse f m β γ e = p e + γ * w e := by
    intro γ hγ e
    rw [haff γ ⟨hγ.1.le, (hγ.2.trans_le huα₂).le⟩]
  have hργ : ∀ γ ∈ Set.Ioo α₁ u, ∀ e, rho f m β γ e = c e + γ * d e := by
    intro γ hγ e
    simp only [rho, marg, hxγ γ hγ e, c, d]
    ring
  -- The comparisons `ρ_{g'}(γ) ≤ ρ_g(γ)` and the signs of the `ρ_g(γ)` do not depend on `γ`.
  have hcmp : ∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u, ∀ g g',
      (rho f m β γ g' ≤ rho f m β γ g ↔ rho f m β γ' g' ≤ rho f m β γ' g) := by
    intro γ hγ γ' hγ' g g'
    have h := hρρ (g, g') γ (hsub _ (hmemρρ _) γ hγ) γ' (hsub _ (hmemρρ _) γ' hγ')
    simp only at h
    have hφ : ∀ x ∈ Set.Ioo α₁ u, rho f m β x g' ≤ rho f m β x g ↔
        0 ≤ c g - c g' + x * (d g - d g') := by
      intro x hx
      rw [hργ x hx, hργ x hx]
      constructor <;> intro h' <;> linarith
    rw [hφ γ hγ, hφ γ' hγ']
    constructor
    · intro hle
      rcases hle.lt_or_eq with hlt | heq
      · exact (h.1.1 hlt).le
      · exact (h.2.1 heq.symm).symm.le
    · intro hle
      rcases hle.lt_or_eq with hlt | heq
      · exact (h.1.2 hlt).le
      · exact (h.2.2 heq.symm).symm.le
  have hsgn : ∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u, ∀ g,
      (0 < rho f m β γ g ↔ 0 < rho f m β γ' g) := by
    intro γ hγ γ' hγ' g
    rw [hργ γ hγ, hργ γ' hγ']
    exact (hρ g γ (hsub _ (hmemρ g) γ hγ) γ' (hsub _ (hmemρ g) γ' hγ')).1
  -- So the positive level sets at `γ` are those at `γ'`.
  have hlev : ∀ γ ∈ Set.Ioo α₁ u, ∀ γ' ∈ Set.Ioo α₁ u,
      posLevelSets f m β γ ⊆ posLevelSets f m β γ' := by
    intro γ hγ γ' hγ' S hS
    obtain ⟨θ, hθ, rfl⟩ := mem_posLevelSets.1 hS
    have hmem : ∀ x θ g, g ∈ levelSet m β x (bestResponse f m β x) θ ↔ θ ≤ rho f m β x g :=
      fun x θ g => mem_levelSet_iff_le
    by_cases hne : (levelSet m β γ (bestResponse f m β γ) θ).Nonempty
    · -- `A_θ(γ) = {g | ρ_g ≥ ρ_{g₀}}` for its element `g₀` with the least marginal.
      obtain ⟨g₀, hg₀, hmin⟩ := exists_min_image _ (fun g => rho f m β γ g) hne
      have hθg₀ : θ ≤ rho f m β γ g₀ := (hmem γ θ g₀).1 hg₀
      refine mem_posLevelSets.2 ⟨rho f m β γ' g₀, (hsgn γ hγ γ' hγ' g₀).1 (by linarith), ?_⟩
      ext g
      rw [hmem γ' _ g, hmem γ θ g, ← hcmp γ hγ γ' hγ' g g₀]
      constructor
      · intro h
        exact hmin g ((hmem γ θ g).2 h)
      · intro h
        linarith
    · -- `A_θ(γ) = ∅ = A_{θ'}(γ')` for `θ'` above all marginals at `γ'`.
      rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]
      set θ' := 1 + ∑ g, |rho f m β γ' g|
      have hθ' : ∀ g, rho f m β γ' g < θ' := by
        intro g
        have h1 := single_le_sum (f := fun g => |rho f m β γ' g|) (fun g _ => abs_nonneg _)
          (mem_univ g)
        have h2 := le_abs_self (rho f m β γ' g)
        simp only [θ']
        linarith
      have hθ'0 : 0 < θ' := by
        have := sum_nonneg fun g (_ : g ∈ univ) => abs_nonneg (rho f m β γ' g)
        simp only [θ']
        linarith
      refine mem_posLevelSets.2 ⟨θ', hθ'0, ?_⟩
      ext g
      rw [hmem γ' θ' g]
      simp only [notMem_empty, false_iff, not_le]
      exact hθ' g
  refine ⟨u, hu, huα₂, fun γ hγ γ' hγ' => Subset.antisymm (hlev γ hγ γ' hγ')
    (hlev γ' hγ' γ hγ), fun γ hγ γ' hγ' e => ?_, fun γ hγ γ' hγ' e => ?_⟩
  · rw [hxγ γ hγ, hxγ γ' hγ']
    exact (hx e γ (hsub _ (hmemx e) γ hγ) γ' (hsub _ (hmemx e) γ' hγ')).2
  · rw [hργ γ hγ, hργ γ' hγ']
    exact (hρ e γ (hsub _ (hmemρ e) γ hγ) γ' (hsub _ (hmemρ e) γ' hγ')).2

/-! ### The lemma -/

/-- **`lem:supportmon`**, first statement (`stoc-sections/appB-quadratic.tex:610-642`): if
`0 < α < α'` and `x*_e(α) = 0`, then `x*_e(α') = 0`. The STOC version's steps: (1) `x*` is
continuous with finitely many affine pieces (`lem:pwaffine`), and `x*_e = 0` iff `ρ_e = α̃ m_e`;
(2) if `x*_e(α') > 0`, then `m_e > 0`, as `0 < x*_e(α') ≤ α' t_e` by `prop:optchar`;
(3) `α_ = inf {α̃ > α | x*_e(α̃) > 0}` has `x*_e(α_) = 0` by continuity, so `ρ_e(α_) = α_ m_e > 0`;
(4) `x*`, and hence `ρ`, is affine on `J = (α_, α_ + h)`, and after shrinking `h` the state is
constant on `J` and `ρ_e > 0` on `J`; (5) `x*_e > 0` on `J`; (6) for the block `D` of `e` on `J`,
`ρ_e` has the slope `m̄_D = t(D ∖ Z)/β⁻¹(D ∖ Z)` on `J` by `lem:velocity`; (7) every `g ∈ D ∖ Z`
has `m_g ≥ m_e`; (8) so the slope is at least `m_e`, `ρ_e(α̃) ≥ α̃ m_e` and `x*_e(α̃) ≤ 0` for
`α̃ ∈ J`, a contradiction. -/
theorem bestResponse_eq_zero_of_lt (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    (hm : ∀ e, 0 ≤ m e) {α α' : ℝ} (hα : 0 < α) (hαα' : α < α') {e : E}
    (h0 : bestResponse f m β α e = 0) : bestResponse f m β α' e = 0 := by
  -- (1) "By `lem:pwaffine`, `x*` is continuous and has finitely many affine pieces. Recall
  -- `ρ_e(α̃) = α̃ m_e − β_e x*_e(α̃)`, so that `x*_e(α̃) = 0` if and only if `ρ_e(α̃) = α̃ m_e`."
  have hcont : ∀ γ, 0 < γ → ContinuousAt (fun γ => bestResponse f m β γ e) γ := fun γ hγ =>
    ((continuous_apply e).comp_continuousOn (pwaffine ⟨hf, hβ, hm⟩).1).continuousAt
      (Ici_mem_nhds hγ)
  have hρcont : ∀ γ, 0 < γ → ContinuousAt (fun γ => rho f m β γ e) γ := fun γ hγ =>
    (continuousAt_id.mul continuousAt_const).sub (continuousAt_const.mul (hcont γ hγ))
  have hzero : ∀ γ, bestResponse f m β γ e = 0 ↔ rho f m β γ e = γ * m e := by
    intro γ
    simp only [rho, marg]
    constructor
    · intro h
      rw [h, mul_zero, sub_zero]
    · intro h
      have h' : β e * bestResponse f m β γ e = 0 := by linarith
      exact (mul_eq_zero.1 h').resolve_left (hβ e).ne'
  have hx0 : ∀ γ, 0 ≤ bestResponse f m β γ e := fun γ =>
    (isBestResponse_bestResponse hf m β γ).1.1 e
  by_contra hne
  have hpos' : 0 < bestResponse f m β α' e := lt_of_le_of_ne (hx0 α') (Ne.symm hne)
  -- (2) "Suppose that `x*_e(α) = 0` and `x*_e(α') > 0` for some `0 < α < α'`. Then `m_e > 0`, as
  -- `0 < x*_e(α') ≤ α' t_e` by `prop:optchar`."
  have hme : 0 < m e := by
    have hle : bestResponse f m β α' e ≤ α' * (m e / β e) :=
      ((optchar hf hβ hm (hα.trans hαα').le (isBestResponse_bestResponse hf m β α').1).2 e).2
    have ht : 0 < α' * (m e / β e) := hpos'.trans_le hle
    exact (div_pos_iff_of_pos_right (hβ e)).1 (pos_of_mul_pos_right ht (hα.trans hαα').le)
  -- (3) "Let `α_ := inf {α̃ > α : x*_e(α̃) > 0}`. By continuity, `x*_e(α_) = 0`, that is,
  -- `ρ_e(α_) = α_ m_e > 0`."
  set S := {γ : ℝ | α < γ ∧ 0 < bestResponse f m β γ e}
  have hSne : S.Nonempty := ⟨α', hαα', hpos'⟩
  have hSbdd : BddBelow S := ⟨α, fun γ hγ => hγ.1.le⟩
  set α₁ := sInf S
  have hαα₁ : α ≤ α₁ := le_csInf hSne fun γ hγ => hγ.1.le
  have hα₁pos : 0 < α₁ := lt_of_lt_of_le hα hαα₁
  have hx₁ : bestResponse f m β α₁ e = 0 := by
    by_contra h₁
    have h₁pos : 0 < bestResponse f m β α₁ e := lt_of_le_of_ne (hx0 α₁) (Ne.symm h₁)
    have hαlt : α < α₁ := lt_of_le_of_ne hαα₁ fun h => h₁ (h ▸ h0)
    have hev : ∀ᶠ γ in 𝓝[<] α₁, α < γ ∧ 0 < bestResponse f m β γ e :=
      ((eventually_gt_nhds hαlt).and ((hcont α₁ hα₁pos).eventually
        (lt_mem_nhds h₁pos))).filter_mono nhdsWithin_le_nhds
    obtain ⟨γ, hγS, hγlt⟩ := (hev.and eventually_mem_nhdsWithin).exists
    exact absurd (csInf_le hSbdd hγS) (not_le.2 hγlt)
  have hρ₁ : rho f m β α₁ e = α₁ * m e := (hzero α₁).1 hx₁
  have hρ₁pos : 0 < rho f m β α₁ e := by
    rw [hρ₁]
    exact mul_pos hα₁pos hme
  -- (4) "Choose `h > 0` such that `x*`, and hence `ρ`, is affine on `J := (α_, α_ + h)`."
  -- The Lean takes an interval `[α_, α₂]` on which `x*` is affine, from the finitely many affine
  -- pieces of `lem:pwaffine` (`exists_affine_right`).
  obtain ⟨α₂, h12, -, p, w, haff⟩ := exists_affine_right (m := m) hf hβ hα₁pos.le
    (show α₁ < α₁ + 1 by linarith)
  have hρaff : ∀ γ ∈ Set.Icc α₁ α₂,
      rho f m β γ e = rho f m β α₁ e + (γ - α₁) * (m e - β e * w e) := by
    intro γ hγ
    simp only [rho, marg, haff γ hγ, haff α₁ ⟨le_rfl, h12.le⟩]
    ring
  -- (4) "After shrinking `h`, the chain of positive level sets of `ρ`, the zero set `Z` and the
  -- free set `Φ` are constant on `J` (so the state of `sec:A-structure` is constant on `J`), and
  -- `ρ_e > 0` on `J`."
  obtain ⟨u₁, hu₁, hu₁2, hlev, hZ, hΦ⟩ := exists_levelSets_const_right h12 haff
  obtain ⟨u₂, hu₂, hρu₂⟩ : ∃ u₂ > α₁, ∀ γ ∈ Set.Ioo α₁ u₂, 0 < rho f m β γ e := by
    have hev : ∀ᶠ γ in 𝓝 α₁, 0 < rho f m β γ e :=
      (hρcont α₁ hα₁pos).eventually (lt_mem_nhds hρ₁pos)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    refine ⟨α₁ + ε, by linarith, fun γ hγ => hball γ ?_⟩
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [hγ.1], hγ.2⟩
  set u := min u₁ u₂
  have hu : α₁ < u := lt_min hu₁ hu₂
  set J := Set.Ioo α₁ u
  have hJ1 : ∀ γ ∈ J, γ ∈ Set.Ioo α₁ u₁ := fun γ hγ => ⟨hγ.1, hγ.2.trans_le (min_le_left _ _)⟩
  have hJ2 : ∀ γ ∈ J, γ ∈ Set.Ioo α₁ u₂ := fun γ hγ => ⟨hγ.1, hγ.2.trans_le (min_le_right _ _)⟩
  have hJα₂ : ∀ γ ∈ J, γ ∈ Set.Icc α₁ α₂ := fun γ hγ =>
    ⟨hγ.1.le, ((hJ1 γ hγ).2.trans_le hu₁2).le⟩
  have hS : StateConstOn f m β J :=
    stateConstOn_of_levelSets hf hβ hm (fun γ hγ => hα₁pos.trans hγ.1)
      (fun γ hγ γ' hγ' => hlev γ (hJ1 γ hγ) γ' (hJ1 γ' hγ'))
      (fun γ hγ γ' hγ' => hZ γ (hJ1 γ hγ) γ' (hJ1 γ' hγ'))
      (fun γ hγ γ' hγ' => hΦ γ (hJ1 γ hγ) γ' (hJ1 γ' hγ'))
  have hρJ : ∀ γ ∈ J, 0 < rho f m β γ e := fun γ hγ => hρu₂ γ (hJ2 γ hγ)
  -- (5) "Moreover, `x*_e > 0` on `J`, because `x*_e` is affine on `J`, vanishes at `α_` and is
  -- positive somewhere in `J`."
  have hxe : ∀ γ ∈ Set.Icc α₁ α₂, bestResponse f m β γ e = (γ - α₁) * w e := by
    intro γ hγ
    have h1 := congrFun (haff γ hγ) e
    have h2 := congrFun (haff α₁ ⟨le_rfl, h12.le⟩) e
    rw [hx₁] at h2
    rw [h1]
    linarith
  have hwe : 0 < w e := by
    obtain ⟨γ, hγS, hγlt⟩ := exists_lt_of_csInf_lt hSne hu
    have hγ1 : α₁ < γ := lt_of_le_of_ne (csInf_le hSbdd hγS) fun h => by
      have h2 := hγS.2
      rw [← h, hx₁] at h2
      exact lt_irrefl 0 h2
    have hγpos := hγS.2
    rw [hxe γ (hJα₂ γ ⟨hγ1, hγlt⟩)] at hγpos
    exact pos_of_mul_pos_right hγpos (by linarith)
  have hxpos : ∀ γ ∈ J, 0 < bestResponse f m β γ e := fun γ hγ => by
    rw [hxe γ (hJα₂ γ hγ)]
    exact mul_pos (by linarith [hγ.1]) hwe
  -- (6) "Let `D` be the block of `e` on `J`, that is, the set of elements `g` with `ρ_g = ρ_e` on
  -- `J`."
  -- The Lean takes the block of `e` at a share `α₃ ∈ J`, as the state is constant on `J`.
  set α₃ := (α₁ + u) / 2
  have hα₃ : α₃ ∈ J := ⟨by simp only [α₃]; linarith, by simp only [α₃]; linarith⟩
  set D := blockOf f m β α₃ e
  set Z := zeroSet f m β α₃
  have hD : ∀ g, g ∈ D ↔ ∀ γ ∈ J, rho f m β γ g = rho f m β γ e := fun g => by
    simp only [D, blockOf, mem_filter, mem_univ, true_and]
    exact ⟨fun h γ hγ => (hS.block α₃ hα₃ γ hγ g e).1 h, fun h => h α₃ hα₃⟩
  have hDZ : blockNZ f m β α₃ e = D \ Z := by
    ext g
    simp [blockNZ, D, Z, blockOf, zeroSet]
  -- (6) "By `lem:velocity`, `ρ_e = α̃ m_e − β_e x*_e` has slope `m̄_D = t(D ∖ Z)/β⁻¹(D ∖ Z)` on
  -- `J`, which is the mean of the rewards `m_g`, `g ∈ D ∖ Z`, weighted by `β_g⁻¹`."
  -- So the slope `m_e − β_e w_e` of step (4) is `m̄_D`.
  have hvel := (velocity_lemma ⟨hf, hβ, hm⟩ hα₁pos.le (stateConstOn_iff.1 hS) hα₃).2 e
    (ne_of_gt (hρJ α₃ hα₃)) (ne_of_gt (hxpos α₃ hα₃))
  have hslope : m e - β e * w e = meanReward f m β α₃ e := by
    refine sub_eq_zero.1 (slope_eq_zero_of_const hu (p := rho f m β α₁ e -
      α₁ * (m e - β e * w e) - rho f m β α₃ e + α₃ * meanReward f m β α₃ e) fun γ hγ => ?_)
    have h1 := hρaff γ (hJα₂ γ hγ)
    have h2 := hvel γ hγ
    linear_combination h1.symm.trans h2
  -- (7) "Each `g ∈ D ∖ Z` satisfies `x*_g > 0`, hence `ρ_e = ρ_g < α̃ m_g` for `α̃ ∈ J`. Letting
  -- `α̃ ↓ α_` gives `α_ m_e ≤ α_ m_g`, that is, `m_g ≥ m_e`."
  have hDm : ∀ g ∈ D \ Z, m e ≤ m g := by
    intro g hg
    obtain ⟨hgD, hgZ⟩ := mem_sdiff.1 hg
    have hlt : ∀ γ ∈ J, rho f m β γ e < γ * m g := by
      intro γ hγ
      have heq : rho f m β γ g = rho f m β γ e := (hD g).1 hgD γ hγ
      have hxg : bestResponse f m β γ g ≠ 0 := fun h => hgZ (by
        simp only [Z, zeroSet, mem_filter, mem_univ, true_and]
        exact (hS.zero α₃ hα₃ γ hγ g).2 h)
      have hxg' : 0 < bestResponse f m β γ g :=
        lt_of_le_of_ne ((isBestResponse_bestResponse hf m β γ).1.1 g) (Ne.symm hxg)
      rw [← heq]
      simp only [rho, marg]
      have := mul_pos (hβ g) hxg'
      linarith
    have hlim : Tendsto (fun γ => γ * m g - rho f m β γ e) (𝓝[>] α₁)
        (𝓝 (α₁ * m g - rho f m β α₁ e)) :=
      ((continuousAt_id.mul continuousAt_const).sub (hρcont α₁ hα₁pos)).tendsto.mono_left
        nhdsWithin_le_nhds
    have hge : 0 ≤ α₁ * m g - rho f m β α₁ e :=
      ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT hu) fun γ hγ =>
        (sub_pos.2 (hlt γ hγ)).le)
    rw [hρ₁] at hge
    by_contra hlt'
    rw [not_le] at hlt'
    have := mul_pos hα₁pos (sub_pos.2 hlt')
    linarith
  -- (8) "So the slope of `ρ_e` on `J` is at least `m_e`, and
  -- `ρ_e(α̃) ≥ α_ m_e + (α̃ − α_) m_e = α̃ m_e` for `α̃ ∈ J`. This means `x*_e(α̃) ≤ 0` on `J`, a
  -- contradiction."
  have heDZ : e ∈ D \ Z := mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ e, rfl⟩,
    fun h => ne_of_gt (hxpos α₃ hα₃) (mem_filter.1 h).2⟩
  have hsum1 : 0 < ∑ g ∈ D \ Z, 1 / β g := sum_pos (fun g _ => one_div_pos.2 (hβ g)) ⟨e, heDZ⟩
  have hmean : m e ≤ meanReward f m β α₃ e := by
    rw [meanReward, hDZ, le_div_iff₀ hsum1, mul_sum]
    refine sum_le_sum fun g hg => ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hDm g hg) (hβ g).le
  have hρge : ∀ γ ∈ J, γ * m e ≤ rho f m β γ e := by
    intro γ hγ
    rw [hρaff γ (hJα₂ γ hγ), hρ₁, hslope]
    calc γ * m e = α₁ * m e + (γ - α₁) * m e := by ring
      _ ≤ α₁ * m e + (γ - α₁) * meanReward f m β α₃ e := by
        have : 0 ≤ γ - α₁ := by linarith [hγ.1]
        gcongr
  have hxle : ∀ γ ∈ J, bestResponse f m β γ e ≤ 0 := by
    intro γ hγ
    have h1 : rho f m β γ e = γ * m e - β e * bestResponse f m β γ e := rfl
    have h2 : 0 ≤ β e * (-bestResponse f m β γ e) := by linarith [hρge γ hγ]
    have := (mul_nonneg_iff_of_pos_left (hβ e)).1 h2
    linarith
  exact absurd (hxpos α₃ hα₃) (not_lt.2 (hxle α₃ hα₃))

/-- The share at which `e` leaves the support: `s_e = sup {α > 0 | x*_e(α) > 0}`. -/
def leaveShare (f : Finset E → ℝ) (m β : E → ℝ) (e : E) : ℝ :=
  sSup {α | 0 < α ∧ 0 < bestResponse f m β α e}

/-- `lem:supportmon`, step (9): "The last statement holds since every element leaves the support at
most once." By the first
statement, `{α > 0 | x*_e(α) > 0}` lies below every share at which `x*_e` vanishes, so `e` leaves
the support only at `s_e`, and the support changes only at the shares `s_e`. -/
theorem supportChanges_subset (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) :
    supportChanges f m β ⊆ Set.range (leaveShare f m β) := by
  rintro α₀ ⟨hα₀, hnot⟩
  by_contra hrange
  apply hnot
  -- Each element is in the support near `α₀` exactly when it is at `α₀`.
  have he : ∀ e, ∀ᶠ α' in 𝓝 α₀,
      (0 < bestResponse f m β α' e ↔ 0 < bestResponse f m β α₀ e) := by
    intro e
    -- `x*_e` is continuous at `α₀` (`lem:pwaffine`)
    have hcont : ContinuousAt (fun γ => bestResponse f m β γ e) α₀ :=
      ((continuous_apply e).comp_continuousOn (pwaffine ⟨hf, hβ, hm⟩).1).continuousAt
        (Ici_mem_nhds hα₀)
    by_cases hpos : 0 < bestResponse f m β α₀ e
    · filter_upwards [hcont.eventually (lt_mem_nhds hpos)] with α' hα'
      exact ⟨fun _ => hpos, fun _ => hα'⟩
    · have h0 : bestResponse f m β α₀ e = 0 :=
        le_antisymm (not_lt.1 hpos) ((isBestResponse_bestResponse hf m β α₀).1.1 e)
      set P := {α | 0 < α ∧ 0 < bestResponse f m β α e}
      -- `P` lies below `α₀`, by the first statement.
      have hPlt : ∀ γ ∈ P, γ < α₀ := by
        intro γ hγ
        by_contra hge
        rw [not_lt] at hge
        rcases hge.lt_or_eq with hlt | heq
        · have h2 := hγ.2
          rw [bestResponse_eq_zero_of_lt hf hβ hm hα₀ hlt h0] at h2
          exact lt_irrefl 0 h2
        · have h2 := hγ.2
          rw [← heq, h0] at h2
          exact lt_irrefl 0 h2
      by_cases hPne : P.Nonempty
      · -- `s_e < α₀`, and right of `s_e` the element is not in the support.
        have hs : leaveShare f m β e ≤ α₀ := csSup_le hPne fun γ hγ => (hPlt γ hγ).le
        have hs' : leaveShare f m β e < α₀ :=
          lt_of_le_of_ne hs fun h => hrange ⟨e, h⟩
        filter_upwards [eventually_gt_nhds hs', eventually_gt_nhds hα₀] with α' hα' hα'0
        refine ⟨fun h => absurd (le_csSup ⟨α₀, fun γ hγ => (hPlt γ hγ).le⟩
          (show α' ∈ P from ⟨hα'0, h⟩)) (not_le.2 hα'), fun h => absurd h hpos⟩
      · filter_upwards [eventually_gt_nhds hα₀] with α' hα'
        exact ⟨fun h => absurd (show α' ∈ P from ⟨hα', h⟩) (fun h' => hPne ⟨α', h'⟩),
          fun h => absurd h hpos⟩
  filter_upwards [eventually_all.2 he] with α' hα'
  ext e
  rw [mem_brSupport, mem_brSupport, hα' e]

/-- **`lem:supportmon`** (Lemma B.17, `stoc-sections/appB-quadratic.tex:610-642`): for
`0 < α < α'`, `x*_e(α) = 0` implies `x*_e(α') = 0` (`bestResponse_eq_zero_of_lt`, steps (1)-(8)). So
the support of `x*` is nonincreasing in `α` and changes at no more than `n` shares (step (9),
`supportChanges_subset`). -/
theorem supportmon (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) :
    (∀ α α', 0 < α → α < α' → ∀ e, bestResponse f m β α e = 0 → bestResponse f m β α' e = 0) ∧
      (∀ α α', 0 < α → α ≤ α' → brSupport f m β α' ⊆ brSupport f m β α) ∧
      (supportChanges f m β).Finite ∧ (supportChanges f m β).ncard ≤ Fintype.card E := by
  refine ⟨fun α α' hα hαα' e h0 => bestResponse_eq_zero_of_lt hf hβ hm hα hαα' h0,
    fun α α' hα hαα' e he => ?_, ?_, ?_⟩
  · -- "So the support of `x*` is nonincreasing in `α` …", by the first statement.
    rw [mem_brSupport] at he ⊢
    by_contra hne
    have h0 : bestResponse f m β α e = 0 :=
      le_antisymm (not_lt.1 hne) ((isBestResponse_bestResponse hf m β α).1.1 e)
    rcases hαα'.lt_or_eq with hlt | heq
    · rw [bestResponse_eq_zero_of_lt hf hβ hm hα hlt h0] at he
      exact lt_irrefl 0 he
    · rw [heq] at hne
      exact hne he
  · exact (Set.finite_range _).subset (supportChanges_subset hf hβ hm)
  · have hrange : Set.range (leaveShare f m β) =
        ((univ.image (leaveShare f m β) : Finset ℝ) : Set ℝ) := by
      ext s
      simp
    refine (Set.ncard_le_ncard (supportChanges_subset hf hβ hm) (Set.finite_range _)).trans ?_
    rw [hrange, Set.ncard_coe_finset]
    exact card_image_le.trans_eq card_univ

/-- (Not in the paper: the STOC version leaves this implicit, for the pinning intervals of the setup
of `thm:laminar`, on which the support is constant.) Between two shares with no change of the
support in between, the support is the same: by `lem:supportmon`, an element that leaves the
support between `α` and `α'` leaves it at the share `s_e ∈ [α, α')`, at which the support
changes. -/
theorem brSupport_eq_of_noChange (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e)
    {α α' : ℝ} (hα : 0 < α) (hαα' : α ≤ α')
    (hno : ∀ τ ∈ supportChanges f m β, τ ∉ Set.Icc α α') :
    brSupport f m β α' = brSupport f m β α := by
  refine Subset.antisymm ((supportmon hf hβ hm).2.1 α α' hα hαα') fun e he => ?_
  by_contra he'
  rw [mem_brSupport] at he he'
  have h0 : bestResponse f m β α' e = 0 :=
    le_antisymm (not_lt.1 he') ((isBestResponse_bestResponse hf m β α').1.1 e)
  -- `P = {γ > 0 | x*_e(γ) > 0}` contains `α` and lies below `α'`, and `s_e = sup P`.
  set P := {γ | 0 < γ ∧ 0 < bestResponse f m β γ e}
  have hPlt : ∀ γ ∈ P, γ < α' := by
    intro γ hγ
    by_contra hge
    rw [not_lt] at hge
    rcases hge.lt_or_eq with hlt | heq
    · have h2 := hγ.2
      rw [bestResponse_eq_zero_of_lt hf hβ hm (hα.trans_le hαα') hlt h0] at h2
      exact lt_irrefl 0 h2
    · have h2 := hγ.2
      rw [← heq, h0] at h2
      exact lt_irrefl 0 h2
  have hbdd : BddAbove P := ⟨α', fun γ hγ => (hPlt γ hγ).le⟩
  have hαP : α ∈ P := ⟨hα, he⟩
  have hs1 : α ≤ leaveShare f m β e := le_csSup hbdd hαP
  have hs2 : leaveShare f m β e ≤ α' := csSup_le ⟨α, hαP⟩ fun γ hγ => (hPlt γ hγ).le
  -- The support changes at `s_e`: left of it `e` is in the support, at and right of it not.
  refine hno (leaveShare f m β e) ⟨hα.trans_le hs1, fun hev => ?_⟩ ⟨hs1, hs2⟩
  set s := leaveShare f m β e
  -- `x*_e` is continuous at `s` (`lem:pwaffine`)
  have hcont : ContinuousAt (fun γ => bestResponse f m β γ e) s :=
    ((continuous_apply e).comp_continuousOn (pwaffine ⟨hf, hβ, hm⟩).1).continuousAt
      (Ici_mem_nhds (hα.trans_le hs1))
  have hsP : s ∉ P := by
    intro hsP
    -- `P` is open, so it contains points right of `s`.
    have hev' : ∀ᶠ γ in 𝓝 s, γ ∈ P :=
      ((eventually_gt_nhds hsP.1).and (hcont.eventually (lt_mem_nhds hsP.2)))
    obtain ⟨γ, hγP, hγs⟩ := ((hev'.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi s ∈ 𝓝[>] s)).exists
    exact absurd (le_csSup hbdd hγP) (not_le.2 hγs)
  have hes : e ∉ brSupport f m β s := fun h => hsP ⟨hα.trans_le hs1, mem_brSupport.1 h⟩
  -- Left of `s` there are points of `P`, at which `e` is in the support.
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨γ, hγP, hγ⟩ := exists_lt_of_lt_csSup ⟨α, hαP⟩ (show s - ε < s by linarith)
  have hγs : γ ≤ s := le_csSup hbdd hγP
  have hγball : γ ∈ Metric.ball s ε := by
    rw [Real.ball_eq_Ioo]
    exact ⟨hγ, by linarith⟩
  have := hball γ hγball
  exact hes (this ▸ mem_brSupport.2 hγP.2)

end

end Stoc
