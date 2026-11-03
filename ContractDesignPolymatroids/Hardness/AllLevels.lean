-- stamp r10 2026-11-03
import ContractDesignPolymatroids.Hardness.OneStep

/-!
# All levels: `thm:alllevels`

The STOC version's `thm:alllevels` (Appendix C.7, `sec:D-alllevels`, "Every level works",
`stoc-sections/appD-hardness.tex:1492-1503`, proof lines 1505-1537), for the levels of `def:tower`
built by the parameter rule.

* `κT`: `κ = min(1, ε_0/δ)`; `HypH`: the property `(H_j)` of a level;
* `alllevels_zero`: `(H_0)`, from (B2) of `prop:base`; `alllevels_step`: the derivation of
  `(H_{j+1})` from `(H_j)` in the proof;
* `alllevels`: `thm:alllevels`.

Taken over on 2026-10-20 from `Paper/Hardness/AllLevels.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### Distances to translated and larger sets -/

/-- `min(dist(α, Γ'), δ) ≤ min(dist(α, Γ), δ)` for `Γ ⊆ Γ'` (not in the paper: the proof of
`thm:alllevels` uses without proof that the distance to a larger set is smaller). -/
lemma minDist_anti {α δ : ℝ} {Γ Γ' : Finset ℝ} (h : Γ ⊆ Γ') :
    minDist α Γ' δ ≤ minDist α Γ δ := by
  have h1 := minDist_coe (α := α) (Γ := Γ') (δ := δ)
  have h2 := minDist_coe (α := α) (Γ := Γ) (δ := δ)
  have hd : distTo α Γ' ≤ distTo α Γ := inf_mono h
  have : (minDist α Γ' δ : WithTop ℝ) ≤ minDist α Γ δ := by
    rw [h1, h2]
    exact min_le_min_right _ hd
  exact_mod_cast this

/-- `min(dist(α, Γ + μ), δ) = min(dist(α − μ, Γ), δ)` (not in the paper: the proof of
`thm:alllevels` uses without proof that `dist(α, Γ + μ) = dist(α − μ, Γ)`). -/
lemma minDist_translate {α δ μ : ℝ} {Γ : Finset ℝ} :
    minDist α (Γ.image (· + μ)) δ = minDist (α - μ) Γ δ := by
  have hd : distTo α (Γ.image (· + μ)) = distTo (α - μ) Γ := by
    unfold distTo
    rw [inf_image]
    refine inf_congr rfl fun γ _ => ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  unfold minDist
  rw [hd]

section Tower

variable (μin : ℕ → ℕ)

/-- `κ = min(1, ε_0/δ)`, the dip of the combs of `thm:alllevels`. -/
def κT : ℝ := min 1 (ε₀ / δT μin)

/-- The property `(H_j)` of `thm:alllevels`: `L_j(α) − r(ξ^{(j)}(α)) ≥ κ min(dist(α, Γ_j), δ)` for
all `α ≥ R_0`, and `r(ξ^{(j)}(γ)) = L_j(γ)` for every `γ ∈ Γ_j` (the gap `gapT μin j α` is
`L_j(α) − r(ξ^{(j)}(α))`, and `curve` is the reward `r(ξ^{(j)}(α))`). -/
def HypH (j : ℕ) : Prop :=
  (∀ α, R0 ≤ α → κT μin * minDist α (ΓT μin j) (δT μin) ≤ gapT μin j α) ∧
  ∀ γ ∈ ΓT μin j, curve (gT μin j) (mT μin j) (βT μin j) γ = (lvl μin j).p + (lvl μin j).q * γ

variable {μin}

/-- `Γ_0 = {ζ_1, ζ_2}`, as `μ_0 = 1/3 = ζ_2 − ζ_1` (`def:tower`). -/
lemma ΓT_zero (h0 : 0 < μin 0) : ΓT μin 0 = {ζ₁, ζ₂} := by
  have hp : (range 1).powerset = ({∅, {0}} : Finset (Finset ℕ)) := by decide
  rw [ΓT, hp, image_insert, image_singleton, sum_empty, sum_singleton, μT_zero h0, add_zero]
  congr 2
  unfold ζ₁ ζ₂
  norm_num

/-- `Γ_j ⊆ 𝓡_j = [R_0, R_1^{(j)}]` (not in the paper: the proof of `thm:alllevels` uses this
without proof, "Finally, `Γ_j ⊆ 𝓡_j`"). -/
lemma ΓT_subset (j : ℕ) {γ : ℝ} (hγ : γ ∈ ΓT μin j) : γ ∈ Set.Icc R0 (R1T μin j) := by
  obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hγ
  have hQ' : Q ⊆ range (j + 1) := mem_powerset.1 hQ
  have h1 : 0 ≤ ∑ i ∈ Q, μT μin i := sum_nonneg fun i _ => μT_nonneg i
  have h2 : ∑ i ∈ Q, μT μin i ≤ ∑ i ∈ range (j + 1), μT μin i :=
    sum_le_sum_of_subset_of_nonneg hQ' fun i _ _ => μT_nonneg i
  have := ε₀_pos
  refine ⟨?_, ?_⟩
  · unfold R0
    linarith
  · unfold R1T
    linarith

/-- The gap of level `j` vanishes at `γ` exactly if `r(ξ^{(j)}(γ)) = L_j(γ)`. -/
lemma gapT_eq_zero_iff {j : ℕ} {γ : ℝ} :
    gapT μin j γ = 0 ↔
      curve (gT μin j) (mT μin j) (βT μin j) γ = (lvl μin j).p + (lvl μin j).q * γ := by
  unfold gapT gap
  constructor <;> intro h <;> linarith

/-- `(H_0)` (the proof of `thm:alllevels`, `stoc-sections/appD-hardness.tex:1506-1507`):
"`(H_0)` is (B2) of `prop:base`, since `κ ≤ 1` and `Γ_0 = {ζ_1, ζ_2}`". -/
theorem alllevels_zero (h0 : 0 < μin 0) : HypH μin 0 := by
  obtain ⟨-, -, -, -, ⟨hB2, -, hdist, -, -⟩, -⟩ := Base.base
  have hδ : 0 < δT μin := by
    have : (0 : ℝ) < μin 0 := by exact_mod_cast h0
    unfold δT
    positivity
  have hκ : κT μin ≤ 1 := min_le_left _ _
  rw [HypH, ΓT_zero h0]
  refine ⟨fun α hα => ?_, fun γ hγ => ?_⟩
  · have h1 : (minDist α {ζ₁, ζ₂} (δT μin) : WithTop ℝ) ≤
        ((L₀ α - curve Base.f₀ Base.m Base.β α : ℝ) : WithTop ℝ) :=
      minDist_le_distTo.trans (hdist α hα)
    have h2 : minDist α {ζ₁, ζ₂} (δT μin) ≤ L₀ α - curve Base.f₀ Base.m Base.β α := by
      exact_mod_cast h1
    have h3 := minDist_nonneg (α := α) (Γ := {ζ₁, ζ₂}) hδ.le
    have h4 : κT μin * minDist α {ζ₁, ζ₂} (δT μin) ≤ minDist α {ζ₁, ζ₂} (δT μin) := by
      nlinarith
    show _ ≤ L₀ α - curve Base.f₀ Base.m Base.β α
    linarith
  · have hγ' : γ = ζ₁ ∨ γ = ζ₂ := by simpa using hγ
    have hle : -1 / 6 ≤ γ := by
      rcases hγ' with rfl | rfl <;> norm_num [ζ₁, ζ₂]
    exact ((hB2 γ hle).2.2 hγ')

/-- The derivation of `(H_{j+1})` from `(H_j)` in the proof of `thm:alllevels`
(`stoc-sections/appD-hardness.tex:1509-1536`), for `μ^in ∈ 𝔉` of length at least `j + 2`, given
the hypotheses of `lem:onelevel` at the steps `0 → 1, …, j → j + 1` and those of `thm:transition`
at the step `j → j + 1` for some `(e_t, e_l)`.

The step's sentences: (1) by `thm:transition`, the gap of level `j + 1` is at least `ε_0 ≥ κδ` on
the transition `[R_1^{(j)}, R_0 + μ_{j+1}]`; (2) on `𝓡_j`, `lem:onelevel`(b) and `(H_j)` give
`L_{j+1}(α) − r(ξ^{(j+1)}(α)) = L_j(α) − r(ξ^{(j)}(α)) ≥ κ min(dist(α, Γ_j), δ)`; (3) on
`[R_0 + μ_{j+1}, ∞)`, as `ψ_{j+1} > 0` and `α − μ_{j+1} ≥ R_0`, they give
`L_{j+1}(α) − r(ξ^{(j+1)}(α)) ≥ L_j(α − μ_{j+1}) − r(ξ^{(j)}(α − μ_{j+1}))
≥ κ min(dist(α, Γ_j + μ_{j+1}), δ)`; (4) as `Γ_{j+1} = Γ_j ∪ (Γ_j + μ_{j+1})` and these three
intervals cover `[R_0, ∞)`, this gives the inequality of `(H_{j+1})`; (5) finally, `Γ_j ⊆ 𝓡_j`,
and `Γ_j + μ_{j+1}` lies in `𝓡_j + μ_{j+1}`, which is contained in the interval
`[R_0 + μ_{j+1}, α_{τ_2}]` of `lem:onelevel`(b); so, by the first two cases of `lem:onelevel`(b) and
by `(H_j)`, the gap vanishes on `Γ_j` and on `Γ_j + μ_{j+1}`. -/
theorem alllevels_step {K : ℕ} (hF : InF μin K) {j : ℕ} (hK : j + 2 ≤ K) {et el : Gr j}
    (hyp : ∀ i ≤ j, OneLevelHyp μin i) (hT : TransitionHyp μin j et el) (hH : HypH μin j) :
    HypH μin (j + 1) := by
  have hj := hyp j le_rfl
  have hδ : 0 < δT μin := by
    have : (0 : ℝ) < μin 0 := by exact_mod_cast μin0_pos hF
    unfold δT
    positivity
  have hκ0 : 0 ≤ κT μin := le_min zero_le_one (by positivity)
  obtain ⟨hb1, hb2, hb3⟩ := onelevel_b hF hK hj
  have hατ₂ := (onelevel_a hF hK hj).1
  -- (1) "By `thm:transition`, with `(e_t, e_l) = (C_0, C_0)` for `j = 0` and `(b_j, τ_{2,j})` for
  -- `j ≥ 1`, whose hypotheses hold by `prop:level1` and `thm:onestep`,
  -- `L_{j+1}(α) − r(ξ^{(j+1)}(α)) ≥ ε_0 ≥ κδ` on the transition `[R_1^{(j)}, R_0 + μ_{j+1}]`."
  -- The Lean: for any pair `(e_t, e_l)` with the hypotheses of `thm:transition` (`hT`); `alllevels`
  -- gives the paper's pairs.
  have htr := transition hF hK hyp hT
  have hκδ : κT μin * δT μin ≤ ε₀ := by
    have : κT μin ≤ ε₀ / δT μin := min_le_right _ _
    calc κT μin * δT μin ≤ ε₀ / δT μin * δT μin := mul_le_mul_of_nonneg_right this hδ.le
      _ = ε₀ := div_mul_cancel₀ ε₀ hδ.ne'
  -- (2) "On `𝓡_j`, `lem:onelevel`(b) and `(H_j)` give
  -- `L_{j+1}(α) − r(ξ^{(j+1)}(α)) = L_j(α) − r(ξ^{(j)}(α)) ≥ κ min(dist(α, Γ_j), δ)`."
  have h2 : ∀ α ∈ Set.Icc R0 (R1T μin j),
      κT μin * minDist α (ΓT μin j) (δT μin) ≤ gapT μin (j + 1) α := fun α hα => by
    rw [hb1 α hα]
    exact hH.1 α hα.1
  -- (3) "On `[R_0 + μ_{j+1}, ∞)`, as `ψ_{j+1} > 0` and `α − μ_{j+1} ≥ R_0`, they give
  -- `L_{j+1}(α) − r(ξ^{(j+1)}(α)) ≥ L_j(α − μ_{j+1}) − r(ξ^{(j)}(α − μ_{j+1}))
  -- ≥ κ min(dist(α, Γ_j + μ_{j+1}), δ)`."
  have h3 : ∀ α, R0 + μT μin (j + 1) ≤ α →
      κT μin * minDist α ((ΓT μin j).image (· + μT μin (j + 1))) (δT μin) ≤
        gapT μin (j + 1) α := fun α hα => by
    have hge : gapT μin j (α - μT μin (j + 1)) ≤ gapT μin (j + 1) α := by
      rcases le_or_gt α (ατ₂ μin j) with h | h
      · rw [hb2 α ⟨hα, h⟩]
      · rw [hb3 α h.le]
        have := mul_nonneg (ψ_nonneg (μin := μin) j) (sub_nonneg.2 h.le)
        linarith
    rw [minDist_translate]
    exact (hH.1 _ (by linarith)).trans hge
  refine ⟨fun α hα => ?_, fun γ hγ => ?_⟩
  · -- (4) "As `Γ_{j+1} = Γ_j ∪ (Γ_j + μ_{j+1})` and these three intervals cover `[R_0, ∞)`, this
    -- gives the inequality of `(H_{j+1})`."
    rw [ΓT_succ]
    rcases le_or_gt α (R1T μin j) with h | h
    · exact (mul_le_mul_of_nonneg_left (minDist_anti subset_union_left) hκ0).trans
        (h2 α ⟨hα, h⟩)
    rcases le_or_gt α (R0 + μT μin (j + 1)) with h' | h'
    · have hm := minDist_le_right (α := α) (Γ := ΓT μin j ∪
        (ΓT μin j).image (· + μT μin (j + 1))) (δ := δT μin)
      have := mul_le_mul_of_nonneg_left hm hκ0
      have := htr α ⟨h.le, h'⟩
      linarith
    · exact (mul_le_mul_of_nonneg_left (minDist_anti subset_union_right) hκ0).trans
        (h3 α h'.le)
  · -- (5) "Finally, `Γ_j ⊆ 𝓡_j`, and `Γ_j + μ_{j+1}` lies in `𝓡_j + μ_{j+1}`, which is contained
    -- in the interval `[R_0 + μ_{j+1}, α_{τ_2}]` of `lem:onelevel`(b). So, by the first two cases
    -- of `lem:onelevel`(b) and by `(H_j)`, `L_{j+1}(α) − r(ξ^{(j+1)}(α))` vanishes on `Γ_j` and on
    -- `Γ_j + μ_{j+1}`."
    rw [← gapT_eq_zero_iff]
    rw [ΓT_succ] at hγ
    rcases mem_union.1 hγ with hγ | hγ
    · rw [hb1 γ (ΓT_subset j hγ)]
      exact gapT_eq_zero_iff.2 (hH.2 γ hγ)
    · obtain ⟨γ', hγ', rfl⟩ := mem_image.1 hγ
      have hw := ΓT_subset (μin := μin) j hγ'
      rw [hb2 _ ⟨by linarith [hw.1], by linarith [hw.2]⟩, add_sub_cancel_right]
      exact gapT_eq_zero_iff.2 (hH.2 γ' hγ')

/-- **`thm:alllevels`** (Theorem C.23, `stoc-sections/appD-hardness.tex:1492-1503`, proof lines
1505-1537): let `μ^in ∈ 𝔉` have length `k` (here `K`), build the levels `0, …, k − 1` by the
parameter rule, and let `κ := min(1, ε_0/δ)`. Then every level `j ≤ k − 1` satisfies `(H_j)`
(`HypH`), and for `j ≥ 1` the hypotheses of `lem:onelevel` hold at the step `j − 1 → j`
(`OneLevelHyp μin (j − 1)`).

The proof's steps: by induction on `j` (the induction hypothesis at `j` is the theorem's claim for
the levels `0, …, j`): (1) `(H_0)` is (B2) of `prop:base` (`alllevels_zero`); (2) the assertions
on level `1` are `prop:level1`, and for `j ≥ 1` those on level `j + 1` follow from `thm:onestep`
at the step `j → j + 1`; (3) `(H_{j+1})` follows from `(H_j)` (`alllevels_step`), by
`thm:transition` with `(e_t, e_l) = (C_0, C_0)` for `j = 0` and `(b_j, τ_{2,j})` for `j ≥ 1`, whose
hypotheses hold by `prop:level1` and `thm:onestep`. -/
theorem alllevels {K : ℕ} (hF : InF μin K) :
    (∀ j, j < K → HypH μin j) ∧ (∀ j, 1 ≤ j → j < K → OneLevelHyp μin (j - 1)) := by
  have h0 := μin0_pos hF
  have key : ∀ j, j < K → HypH μin j ∧ ∀ i < j, OneLevelHyp μin i := by
    -- "By induction on `j`."
    intro j
    induction j with
    | zero =>
      -- (1) "`(H_0)` is (B2) of `prop:base`, since `κ ≤ 1` and `Γ_0 = {ζ_1, ζ_2}`."
      intro _
      exact ⟨alllevels_zero h0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ j ih =>
      intro hj
      obtain ⟨hH, hprev⟩ := ih (by omega)
      -- (2) "The assertions on level `1` are `prop:level1`, and for `j ≥ 1` those on level `j + 1`
      -- follow from `thm:onestep` at the step `j → j + 1`."
      have hstep : OneLevelHyp μin j ∧ ∃ et el : Gr j, TransitionHyp μin j et el := by
        rcases j with _ | j
        · obtain ⟨-, -, h1, h2⟩ := level1 hF (by omega)
          exact ⟨h1, _, _, h2⟩
        · obtain ⟨h1, h2⟩ := onestep (j := j) hF (by omega) fun i hi => hprev i (by omega)
          exact ⟨h1, _, _, h2⟩
      obtain ⟨hcur, et, el, hT⟩ := hstep
      have hyp : ∀ i ≤ j, OneLevelHyp μin i := fun i hi => by
        rcases hi.lt_or_eq with hi | rfl
        · exact hprev i hi
        · exact hcur
      -- (3) "It remains to derive `(H_{j+1})` from `(H_j)`."
      exact ⟨alllevels_step hF (by omega) hyp hT hH, fun i hi => hyp i (by omega)⟩
  refine ⟨fun j hj => (key j hj).1, fun j hj1 hj => (key j hj).2 (j - 1) (by omega)⟩

end Tower

end

end Hardness

end Stoc
