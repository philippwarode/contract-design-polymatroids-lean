-- stamp r8 2026-11-02
import ContractDesignPolymatroids.BestResponse.LevelSets
import ContractDesignPolymatroids.BestResponse.LayerCake
import ContractDesignPolymatroids.OptimalShare.PiecewiseAffine

/-!
# The slope of the best response

The STOC version: the state, defined at the end of Appendix B.2 (`sec:A-structure`,
`stoc-sections/appB-quadratic.tex:337-343`), and in Appendix B.4 (`sec:A-pieces`) the velocity of a
state (`eq:velocity`, `appB-quadratic.tex:357-367`) and Lemma `lem:velocity` (statement :369-373,
proof :375-385).

At a share `α > 0`, the free set is `Φ(α) = {e | ρ_e(α) = 0}` (`freeSet`), the zero set is
`Z(α) = {e | x*_e(α) = 0}` (`zeroSet`), and `E ∖ Φ(α)` is partitioned into the blocks `𝒫(α)` of
equal positive marginal (`blockOf`, `blockPartition`); the triple is the state (`state`). For a
state, (`eq:velocity`) assigns the vector `v` (`velocity`): `v_e = t_e` on `Φ`, `v_e = 0` on
`Z ∖ Φ`, and `v_e = β_e⁻¹ (m_e − m̄_D)` on `D ∖ Z` for a block `D`, where
`m̄_D = t(D ∖ Z)/β⁻¹(D ∖ Z)` (`meanReward`, with `D ∖ Z` the set `blockNZ`).

`lem:velocity` (`velocity_lemma`): on every open interval with constant state, `x*` is affine with
slope `v`, and for `e ∈ D ∖ Z` the marginal `ρ_e` has slope `m̄_D`. The proof follows the STOC
version's:

1. continuity keeps the blocks in the same order of marginal values (`StateConstOn.rho_le_iff`);
2. their cumulative unions are tight level sets, so `x*(D)` is constant for every block `D`; the
   blocks in decreasing order of marginal are indexed by the distinct positive marginals
   `θ_0 > θ_1 > ⋯` (`theta` of `ContractDesignPolymatroids/BestResponse/LayerCake.lean`, indices from 0), and their
   cumulative unions are the level sets `L_i = {g | ρ_g ≥ θ_i}`;
3. `x*(D) = α t(D ∖ Z) − ρ_D(α) β⁻¹(D ∖ Z)`;
4. if `D ∖ Z ≠ ∅`, this makes `ρ_D` affine with slope `m̄_D` and gives the slope of `x*`;
5. on free and zero coordinates, `x*_e = α t_e` and `x*_e = 0`.

That the state is constant on an interval is also encoded as the structure `StateConstOn` (the
free set and the zero set are constant, and so is the relation "equal marginal", which determines
the blocks), which other files use; `stateConstOn_iff` proves the two forms equivalent.
`slope_eq_zero_of_const` (an affine function that vanishes on an interval has slope `0`) serves
`lem:supportmon`.

Step 1 is stated without proof in the STOC version; the Lean proves it by the intermediate value
theorem (`StateConstOn.rho_le_iff`, marked "not in the paper").

Taken over on 2026-10-20 from `Paper/OptimalShare/Velocity.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version. Reworked on
2026-10-25: the cumulative union of the blocks above a block is tight as a level set, as in the
STOC version, and the state and the second sentence of the lemma are stated as in the paper.
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {f : Finset E → ℝ} {m β : E → ℝ}

/-! ### States and velocities -/

/-- The free set `Φ(α) = {e | ρ_e(α) = 0}`. -/
def freeSet (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : Finset E :=
  univ.filter fun e => rho f m β α e = 0

/-- The zero set `Z(α) = {e | x*_e(α) = 0}`. -/
def zeroSet (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : Finset E :=
  univ.filter fun e => bestResponse f m β α e = 0

/-- The block of `e` at `α`: the elements with the marginal of `e`. -/
def blockOf (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) (e : E) : Finset E :=
  univ.filter fun g => rho f m β α g = rho f m β α e

/-- The partition `𝒫(α)` of `E ∖ Φ(α)` into blocks of equal positive marginal. -/
def blockPartition (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : Finset (Finset E) :=
  (univ.filter fun e => rho f m β α e ≠ 0).image (blockOf f m β α)

/-- The state `(Φ(α), Z(α), 𝒫(α))` at the share `α`. -/
def state (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : Finset E × Finset E × Finset (Finset E) :=
  (freeSet f m β α, zeroSet f m β α, blockPartition f m β α)

/-- `D ∖ Z` for the block `D` of `e` at the share `α`. -/
def blockNZ (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) (e : E) : Finset E :=
  univ.filter fun g => rho f m β α g = rho f m β α e ∧ bestResponse f m β α g ≠ 0

/-- The mean `m̄_D = t(D ∖ Z)/β⁻¹(D ∖ Z)` of (`eq:velocity`) for the block `D` of `e` at `α`, with
`t(S) = ∑_{g ∈ S} m_g/β_g` and `β⁻¹(S) = ∑_{g ∈ S} 1/β_g`. -/
def meanReward (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) (e : E) : ℝ :=
  (∑ g ∈ blockNZ f m β α e, m g / β g) / ∑ g ∈ blockNZ f m β α e, 1 / β g

/-- The vector `v` that (`eq:velocity`) assigns to the state at `α`: `v_e = t_e` for `e ∈ Φ`,
`v_e = 0` for `e ∈ Z ∖ Φ`, and `v_e = β_e⁻¹ (m_e − m̄_D)` for `e ∈ D ∖ Z`, with the mean `m̄_D`
(`meanReward`) written out. -/
def velocity (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) (e : E) : ℝ :=
  if rho f m β α e = 0 then m e / β e
  else if bestResponse f m β α e = 0 then 0
  else (m e - (∑ g ∈ blockNZ f m β α e, m g / β g) / (∑ g ∈ blockNZ f m β α e, 1 / β g)) / β e

omit [DecidableEq E] in
/-- (`eq:velocity`) for `e ∈ D ∖ Z`: `v_e = β_e⁻¹ (m_e − m̄_D)`. -/
lemma velocity_eq_of_mem {α : ℝ} {e : E} (hfree : rho f m β α e ≠ 0)
    (hz : bestResponse f m β α e ≠ 0) :
    velocity f m β α e = (m e - meanReward f m β α e) / β e := by
  unfold velocity meanReward
  rw [ite_eq_right hfree, ite_eq_right hz]

/-- The state is constant on `J`, in the form other files use: the free set, the zero set and the
relation "equal marginal", which determines the blocks, do not change on `J`
(`stateConstOn_iff`: the same as `state f m β α = state f m β α'` for all `α, α' ∈ J`). -/
structure StateConstOn (f : Finset E → ℝ) (m β : E → ℝ) (J : Set ℝ) : Prop where
  free : ∀ α ∈ J, ∀ α' ∈ J, ∀ e, rho f m β α e = 0 ↔ rho f m β α' e = 0
  zero : ∀ α ∈ J, ∀ α' ∈ J, ∀ e, bestResponse f m β α e = 0 ↔ bestResponse f m β α' e = 0
  block : ∀ α ∈ J, ∀ α' ∈ J, ∀ e e',
    rho f m β α e = rho f m β α e' ↔ rho f m β α' e = rho f m β α' e'

/-- The two forms of "the state is constant on `J`" agree (plumbing). -/
theorem stateConstOn_iff {J : Set ℝ} :
    StateConstOn f m β J ↔ ∀ α ∈ J, ∀ α' ∈ J, state f m β α = state f m β α' := by
  classical
  constructor
  · intro hS α hα α' hα'
    have hfree : freeSet f m β α = freeSet f m β α' := by
      ext e
      simp only [freeSet, mem_filter, mem_univ, true_and]
      exact hS.free α hα α' hα' e
    have hblk : ∀ e, blockOf f m β α e = blockOf f m β α' e := by
      intro e
      ext g
      simp only [blockOf, mem_filter, mem_univ, true_and]
      exact hS.block α hα α' hα' g e
    refine Prod.ext hfree (Prod.ext ?_ ?_)
    · show zeroSet f m β α = zeroSet f m β α'
      ext e
      simp only [zeroSet, mem_filter, mem_univ, true_and]
      exact hS.zero α hα α' hα' e
    · show (univ.filter fun e => rho f m β α e ≠ 0).image (blockOf f m β α) =
        (univ.filter fun e => rho f m β α' e ≠ 0).image (blockOf f m β α')
      have hnf : (univ.filter fun e => rho f m β α e ≠ 0) =
          univ.filter fun e => rho f m β α' e ≠ 0 := by
        ext e
        simp only [mem_filter, mem_univ, true_and, ne_eq]
        rw [hS.free α hα α' hα' e]
      rw [hnf]
      exact Finset.image_congr fun e _ => hblk e
  · intro hS
    have hfree : ∀ α ∈ J, ∀ α' ∈ J, ∀ e, rho f m β α e = 0 ↔ rho f m β α' e = 0 := by
      intro α hα α' hα' e
      have h := congrArg (fun s => e ∈ s.1) (hS α hα α' hα')
      simpa [state, freeSet] using h
    refine ⟨hfree, fun α hα α' hα' e => ?_, fun α hα α' hα' e e' => ?_⟩
    · have h := congrArg (fun s => e ∈ s.2.1) (hS α hα α' hα')
      simpa [state, zeroSet] using h
    · by_cases he : rho f m β α e = 0
      · -- `e` is free at `α` and at `α'`: equal marginals means `e'` is free too
        have he' : rho f m β α' e = 0 := (hfree α hα α' hα' e).1 he
        rw [he, he', eq_comm, (eq_comm (a := (0 : ℝ))), hfree α hα α' hα' e']
      · -- the block of `e` at `α` is a block at `α'`, which contains `e`, so it is its block
        have hmem : blockOf f m β α e ∈ blockPartition f m β α' := by
          have h : blockPartition f m β α = blockPartition f m β α' :=
            congrArg (fun s => s.2.2) (hS α hα α' hα')
          rw [← h]
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ e, he⟩)
        obtain ⟨e'', -, he''⟩ := Finset.mem_image.1 hmem
        have hee : e ∈ blockOf f m β α e := by simp [blockOf]
        rw [← he''] at hee
        have h1 : rho f m β α' e = rho f m β α' e'' := by simpa [blockOf] using hee
        have h2 := Finset.ext_iff.1 he'' e'
        simp only [blockOf, mem_filter, mem_univ, true_and] at h2
        rw [eq_comm (a := rho f m β α e), ← h2, h1, eq_comm]

/-! ### Step (1): the order of the blocks -/

theorem continuous_rho (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) (e : E) :
    Continuous fun α => rho f m β α e := by
  have h := (continuous_apply e).comp (continuous_bestResponse (m := m) hf hβ)
  unfold rho marg
  exact (continuous_id.mul continuous_const).sub (continuous_const.mul h)

/-- Step (1) of the proof of `lem:velocity` (not in the paper: the STOC version says without proof
that continuity keeps the blocks in the same order of marginal values throughout the interval): on
an open interval with constant state, the order of the marginals is constant, as `ρ_{e'} − ρ_e` is
continuous and has no zero there unless it vanishes throughout (intermediate value theorem). -/
theorem StateConstOn.rho_le_iff (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e) {a b : ℝ}
    (hS : StateConstOn f m β (Set.Ioo a b)) {α α' : ℝ} (hα : α ∈ Set.Ioo a b)
    (hα' : α' ∈ Set.Ioo a b) (e e' : E) :
    rho f m β α e ≤ rho f m β α e' ↔ rho f m β α' e ≤ rho f m β α' e' := by
  by_cases heq : rho f m β α e = rho f m β α e'
  · have heq' := (hS.block α hα α' hα' e e').1 heq
    rw [heq, heq']
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  · have hne' : rho f m β α' e ≠ rho f m β α' e' := fun h => heq ((hS.block α hα α' hα' e e').2 h)
    set h : ℝ → ℝ := fun γ => rho f m β γ e' - rho f m β γ e
    have hcont : Continuous h := (continuous_rho hf hβ e').sub (continuous_rho hf hβ e)
    -- `h` has no zero on `[α, α']`, so it does not change sign there.
    have hnz : ∀ γ ∈ Set.uIcc α α', h γ ≠ 0 := by
      intro γ hγ h0
      have hγJ : γ ∈ Set.Ioo a b := Set.OrdConnected.uIcc_subset inferInstance hα hα' hγ
      have : rho f m β γ e = rho f m β γ e' := by simp only [h] at h0; linarith
      exact heq ((hS.block γ hγJ α hα e e').1 this)
    have hsign : 0 < h α ↔ 0 < h α' := by
      constructor
      · intro hpos
        by_contra hneg
        rw [not_lt] at hneg
        obtain ⟨γ, hγ, h0⟩ := intermediate_value_uIcc hcont.continuousOn
          (show (0 : ℝ) ∈ Set.uIcc (h α) (h α') from Set.mem_uIcc.2 (Or.inr ⟨hneg, hpos.le⟩))
        exact hnz γ hγ h0
      · intro hpos
        by_contra hneg
        rw [not_lt] at hneg
        obtain ⟨γ, hγ, h0⟩ := intermediate_value_uIcc hcont.continuousOn
          (show (0 : ℝ) ∈ Set.uIcc (h α) (h α') from Set.mem_uIcc.2 (Or.inl ⟨hneg, hpos.le⟩))
        exact hnz γ hγ h0
    simp only [h, sub_pos] at hsign
    constructor
    · intro hle
      exact (hsign.1 (lt_of_le_of_ne hle heq)).le
    · intro hle
      exact (hsign.2 (lt_of_le_of_ne hle hne')).le

/-! ### `lem:velocity` -/

/-- **`lem:velocity`** (Lemma B.6, statement `stoc-sections/appB-quadratic.tex:369-373`, proof
:375-385): on every open interval `J = (a, b)`, `a ≥ 0`, with constant state, `x*` is affine with
slope `v` from (`eq:velocity`), `x*(α) = x*(α₀) + (α − α₀) v` for `α, α₀ ∈ J`; and for `e ∈ D ∖ Z`
(that is, `ρ_e ≠ 0` and `x*_e ≠ 0`), the marginal `ρ_e` has slope `m̄_D`. Steps: (1) the blocks keep
their order; (2) their cumulative unions are tight level sets, so `x*(D)` is constant; (3)
`x*(D) = α t(D ∖ Z) − ρ_D(α) β⁻¹(D ∖ Z)`; (4) so `ρ_D` is affine with slope `m̄_D`, and `x*_e`
has slope `β_e⁻¹ (m_e − m̄_D)`; (5) the free and zero coordinates. -/
theorem velocity_lemma (H : Tracing.Hyp f m β) {a b : ℝ} (ha : 0 ≤ a)
    (hS : ∀ α ∈ Set.Ioo a b, ∀ α' ∈ Set.Ioo a b, state f m β α = state f m β α')
    {α₀ : ℝ} (hα₀ : α₀ ∈ Set.Ioo a b) :
    (∀ α ∈ Set.Ioo a b, bestResponse f m β α =
      fun e => bestResponse f m β α₀ e + (α - α₀) * velocity f m β α₀ e) ∧
    ∀ e, rho f m β α₀ e ≠ 0 → bestResponse f m β α₀ e ≠ 0 →
      ∀ α ∈ Set.Ioo a b, rho f m β α e = rho f m β α₀ e + (α - α₀) * meanReward f m β α₀ e := by
  have hS' : StateConstOn f m β (Set.Ioo a b) := stateConstOn_iff.2 hS
  set J := Set.Ioo a b
  -- The marginals are nonnegative on `J` (`prop:optchar`), and `x*_g = (γ m_g − ρ_g)/β_g`.
  have hρ0 : ∀ γ ∈ J, ∀ e, 0 ≤ rho f m β γ e := fun γ hγ e =>
    (isBestResponse_bestResponse H.rank m β γ).marg_nonneg H.beta
      (fun e => mul_nonneg (by linarith [hγ.1]) (H.reward e)) e
  have hx : ∀ γ g, bestResponse f m β γ g = (γ * m g - rho f m β γ g) / β g := fun γ g => by
    simp only [rho, marg]
    field_simp [(H.beta g).ne']
    ring
  have hpos : ∀ γ ∈ J, ∀ g, rho f m β α₀ g ≠ 0 → 0 < rho f m β γ g := fun γ hγ g hg =>
    lt_of_le_of_ne (hρ0 γ hγ g) (Ne.symm fun h => hg ((hS'.free α₀ hα₀ γ hγ g).2 h))
  -- (1) "Continuity keeps the blocks in the same order of marginal values throughout the
  -- interval."
  have h1 : ∀ γ ∈ J, ∀ g g', rho f m β α₀ g ≤ rho f m β α₀ g' ↔ rho f m β γ g ≤ rho f m β γ g' :=
    fun γ hγ g g' => hS'.rho_le_iff H.rank H.beta hα₀ hγ g g'
  -- The blocks in decreasing order of marginal: the distinct positive marginals
  -- `θ_0 > θ_1 > ⋯ > θ_{k−1}` at `α₀`, the blocks `{g | ρ_g(α₀) = θ_i}`, and their cumulative
  -- unions `L_i = {g | ρ_g(α₀) ≥ θ_i}`.
  set θ := theta (rho f m β α₀) 0
  set k := numVals (rho f m β α₀) 0
  set L : ℕ → Finset E := fun i => univ.filter fun g => θ i ≤ rho f m β α₀ g
  -- (2) "Their cumulative unions are tight level sets, …": at every `γ ∈ J`, `L_i` is the level set
  -- `A_{ρ_g(γ)}(γ)` for an element `g` of the `i`-th block, at a positive level, so it is tight
  -- (`prop:optchar`).
  have h2 : ∀ γ ∈ J, ∀ i < k, IsTight f (bestResponse f m β γ) (L i) := by
    intro γ hγ i hi
    obtain ⟨g, -, hg⟩ := Finset.mem_image.1 (Finset.mem_filter.1 (theta_mem hi)).1
    have hg : rho f m β α₀ g = θ i := hg
    have hgpos : 0 < rho f m β γ g := hpos γ hγ g (by rw [hg]; exact (c_lt_theta hi).ne')
    have hL : L i = univ.filter fun g' => rho f m β γ g ≤ rho f m β γ g' := by
      ext g'
      simp only [L, mem_filter, mem_univ, true_and]
      rw [← hg]
      exact h1 γ hγ g g'
    rw [hL]
    have hm : ∀ e, 0 ≤ γ * m e := fun e => mul_nonneg (by linarith [hγ.1]) (H.reward e)
    exact ((isBestResponse_iff_levelSets H.rank H.beta hm).1
      (isBestResponse_bestResponse H.rank m β γ)).2.2 _ hgpos
  -- (2)-(4) for the block `D` of an element `e ∈ D ∖ Z`, which gives the second sentence of the
  -- lemma.
  have hblock : ∀ e, rho f m β α₀ e ≠ 0 → bestResponse f m β α₀ e ≠ 0 →
      ∀ γ ∈ J, rho f m β γ e = rho f m β α₀ e + (γ - α₀) * meanReward f m β α₀ e := by
    intro e hfree hz
    obtain ⟨j, hj, hθj⟩ := exists_theta_eq (lt_of_le_of_ne (hρ0 α₀ hα₀ e) (Ne.symm hfree))
    have hθj : θ j = rho f m β α₀ e := hθj
    -- the cumulative union of the blocks above `D` is `L_{j−1}`, or empty for `j = 0`
    set Lm := univ.filter fun g => θ j < rho f m β α₀ g
    have hLm : ∀ γ ∈ J, IsTight f (bestResponse f m β γ) Lm := by
      intro γ hγ
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · have hempty : Lm = ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun g _ hg => ?_
          obtain ⟨i, hi, hθi⟩ := exists_theta_eq ((c_lt_theta hj).trans hg)
          have hθi : θ i = rho f m β α₀ g := hθi
          rw [← hθi] at hg
          subst hj0
          exact absurd ((theta_le_theta_iff hi hj).2 (Nat.zero_le i)) (not_le.2 hg)
        rw [hempty]
        simp [IsTight, H.rank.empty]
      · have hLj : Lm = L (j - 1) := by
          ext g
          simp only [Lm, L, mem_filter, mem_univ, true_and]
          constructor
          · intro hg
            obtain ⟨i, hi, hθi⟩ := exists_theta_eq ((c_lt_theta hj).trans hg)
            have hθi : θ i = rho f m β α₀ g := hθi
            rw [← hθi] at hg ⊢
            have hij : i < j := by
              by_contra hji
              exact absurd ((theta_le_theta_iff hi hj).2 (not_lt.1 hji)) (not_le.2 hg)
            exact (theta_le_theta_iff (i := j - 1) (j := i) (by omega) hi).2 (by omega)
          · intro hg
            exact lt_of_lt_of_le (theta_lt_theta (by omega) hj.le) hg
        rw [hLj]
        exact h2 γ hγ (j - 1) (by omega)
    have hsub : Lm ⊆ L j := fun g hg => by
      simp only [Lm, L, mem_filter, mem_univ, true_and] at hg ⊢
      exact hg.le
    -- "… so `x*(D)` is constant for every block `D`": `x*(D) = f(L_j) − f(L_{j−1})`
    have hD : ∀ γ ∈ J, ∑ g ∈ L j \ Lm, bestResponse f m β γ g = f (L j) - f Lm := by
      intro γ hγ
      rw [sum_sdiff_eq_sub hsub, h2 γ hγ j hj, hLm γ hγ]
    -- (3) "Writing `ρ_D` for its common marginal gives
    -- `x*(D) = α t(D ∖ Z) − ρ_D(α) β⁻¹(D ∖ Z)`."
    set B := blockNZ f m β α₀ e
    have hBsub : B ⊆ L j \ Lm := fun g hg => by
      simp only [B, blockNZ, mem_filter, mem_univ, true_and] at hg
      simp only [L, Lm, Finset.mem_sdiff, mem_filter, mem_univ, true_and, not_lt]
      have hgj : rho f m β α₀ g = θ j := hg.1.trans hθj.symm
      rw [hgj]
      exact ⟨le_rfl, le_rfl⟩
    have h3 : ∀ γ ∈ J, ∑ g ∈ L j \ Lm, bestResponse f m β γ g =
        γ * ∑ g ∈ B, m g / β g - rho f m β γ e * ∑ g ∈ B, 1 / β g := by
      intro γ hγ
      rw [← sum_sdiff hBsub]
      have h0 : ∑ g ∈ (L j \ Lm) \ B, bestResponse f m β γ g = 0 := sum_eq_zero fun g hg => by
        simp only [B, blockNZ, L, Lm, Finset.mem_sdiff, mem_filter, mem_univ, true_and,
          not_lt, not_and, not_not] at hg
        have hge : rho f m β α₀ g = rho f m β α₀ e := by
          rw [hθj] at hg
          exact le_antisymm hg.1.2 hg.1.1
        exact (hS'.zero α₀ hα₀ γ hγ g).1 (hg.2 hge)
      rw [h0, zero_add, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun g hg => ?_
      simp only [B, blockNZ, mem_filter, mem_univ, true_and] at hg
      rw [hx γ g, (hS'.block α₀ hα₀ γ hγ g e).1 hg.1]
      field_simp [(H.beta g).ne']
    -- (4) "If `D ∖ Z ≠ ∅`, this makes `ρ_D` affine with slope `m̄_D` …"
    have hsum1 : 0 < ∑ g ∈ B, 1 / β g :=
      sum_pos (fun g _ => one_div_pos.2 (H.beta g)) ⟨e, by simp [B, blockNZ, hz]⟩
    have hρe : ∀ γ ∈ J, rho f m β γ e =
        (γ * ∑ g ∈ B, m g / β g - (f (L j) - f Lm)) / ∑ g ∈ B, 1 / β g := by
      intro γ hγ
      rw [eq_div_iff hsum1.ne']
      linarith [hD γ hγ, h3 γ hγ]
    intro γ hγ
    have hmean : meanReward f m β α₀ e = (∑ g ∈ B, m g / β g) / ∑ g ∈ B, 1 / β g := rfl
    rw [hρe γ hγ, hρe α₀ hα₀, hmean]
    field_simp
    ring
  refine ⟨fun α hα => ?_, hblock⟩
  funext e
  show bestResponse f m β α e = bestResponse f m β α₀ e + (α - α₀) * velocity f m β α₀ e
  -- (5) "For free and zero coordinates, the claim follows from `x*_e = α t_e` and `x*_e = 0`,
  -- respectively."
  by_cases hfree : rho f m β α₀ e = 0
  · -- the free coordinates, from `x*_e = α t_e`
    unfold velocity
    rw [ite_eq_left hfree, hx α e, hx α₀ e, (hS'.free α₀ hα₀ α hα e).1 hfree, hfree]
    field_simp [(H.beta e).ne']
    ring
  by_cases hz : bestResponse f m β α₀ e = 0
  · -- the zero coordinates, from `x*_e = 0`
    unfold velocity
    rw [ite_eq_right hfree, ite_eq_left hz, hz, (hS'.zero α₀ hα₀ α hα e).1 hz]
    ring
  -- (4) "… and gives the stated slope of `x*`": `x*_e = (α m_e − ρ_D)/β_e`.
  rw [velocity_eq_of_mem hfree hz, hx α e, hx α₀ e, hblock e hfree hz α hα]
  field_simp [(H.beta e).ne']
  ring

/-- Two values of an affine function at distinct points that agree force its slope to vanish. -/
theorem slope_eq_zero_of_const {c d : ℝ} (hcd : c < d) {p w : ℝ}
    (h : ∀ α ∈ Set.Ioo c d, p + α * w = 0) : w = 0 := by
  have h1 := h ((2 * c + d) / 3) ⟨by linarith, by linarith⟩
  have h2 := h ((c + 2 * d) / 3) ⟨by linarith, by linarith⟩
  have : (c + 2 * d) / 3 - (2 * c + d) / 3 ≠ 0 := by linarith
  have h3 : ((c + 2 * d) / 3 - (2 * c + d) / 3) * w = 0 := by linarith
  exact (mul_eq_zero.1 h3).resolve_left this

end

end Stoc
