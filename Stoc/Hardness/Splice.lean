-- stamp r8 2026-11-02
import Stoc.Hardness.Translation

/-!
# One-element extensions: the splice theorem and the windows

The STOC version's Appendix B.6.3 (`sec:B-extensions`, "One-element extensions and the splice",
`stoc-sections/appB-tools.tex:304-456`): `thm:splice`, the configurations and `lem:windows`.

Setting (`appB-tools.tex:313-324`): `f` is submodular with `f(∅) = 0` on `E`, `m, β > 0`, `d ≥ 0`
is modular, `h = f − d` (`Stoc.Hardness.subMod f d`), `K ∈ ℝ`, and the extension `f'` of `f` by the
new element `b = none` of `Option E` is `Stoc.Hardness.extend f d K`; `m` and `β` are extended by
`m_b` and `β_b` through `m', β' : Option E → ℝ` (`m = m' ∘ some`, `β = β' ∘ some`). The marginals
`ρ' = ρ^{f'}` are `rhoPrime`, the best response `ξ' = ξ^{f'}` is `xiPrime`, and the marginal
`θ_b = ρ'_b` of the new element is `thetaB`. The extension is submodular with `f'(∅) = 0` by the
proof of
`lem:translation`(a) (`Stoc.Hardness.FPHyp.extend`); the "direct check" of the same fact in the
setting (`appB-tools.tex:323`), a second argument, is not formalised.

The paper's objects: `clamp`, `med` (the median of three numbers), `clampTerm`
(`c_e = clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)`), `bigY` (`Y(θ)`), `IsF1` (`θ` solves `eq:splice`),
`spliceDiff` (the difference of the two sides of `eq:splice`), `splicePoint` (the vector `y` of the
proof of (b) and (c)), `configU` and `configW` (the configuration), `blockUW` (the block
`D = (W ∖ U) ∪ {b}`), `IsWeakConfig` (a weak configuration), `bigX` (`X_{U,W}`), `thetaUW`
(`θ_{U,W}`).

The exact statements: `splice` (`thm:splice`), `config_spec` (the paragraph "Configurations"),
`isWeakConfig_of_levelSets`, `isWeakConfig_config` and `windows_mass_marginal` (the three claims of
`lem:windows` between its definitions and (a), `appB-tools.tex:409-411`), `windows_a`, `windows_b`,
`windows_c`, and `windows`, the statement of `lem:windows`: the conjunction of the three claims
before (a) and of (a)–(c), proved by these six declarations, which are its parts. Each carries all
hypotheses of the paper. Those of `thm:splice` and `lem:windows`(a)-(c) are derived from auxiliary
lemmas with the paper's proofs under `FPHyp` (no `m > 0`): `splice_aux`, `windows_a_aux` (with its
first steps in `windows_a_block`, which `windows_mass_marginal` also uses), `windows_b_aux`,
`windows_c_aux`; `config_spec`, `isWeakConfig_of_levelSets` and `isWeakConfig_config` carry their
proofs themselves.

The elementary facts on clamps and medians that the paper uses without proof are lemmas of their
own, marked "not in the paper". Besides the exact statements and the auxiliary lemmas, the later
files use `rho_le_rho_subMod` (the proof of `thm:splice`(a)), the median lemmas
`med_eq_min_max`, `med_eq_left` and `le_med_iff_of_le`.

Taken over on 2026-10-20 from `Paper/Hardness/Splice.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {f : Finset E → ℝ} {d : E → ℝ} {K : ℝ} {m β : E → ℝ} {m' β' : Option E → ℝ}

/-! ### The setting (`appB-tools.tex:313-324`) -/

variable (f d K m' β')

/-- `ρ' = ρ^{f'}` (`appB-tools.tex:324`): the full-plane marginals of the extension `f'` of `f` by
`b`, taken with respect to `m` and `β` extended by `m_b` and `β_b` (that is, `m'` and `β'`). -/
def rhoPrime (α : ℝ) : Option E → ℝ :=
  rho (extend f d K) m' β' α

/-- `ξ' = ξ^{f'}` (`appB-tools.tex:324`): the full-plane best response of the extension `f'`. -/
def xiPrime (α : ℝ) : Option E → ℝ :=
  xi (extend f d K) m' β' α

/-- `θ_b = ρ'_b` (`appB-tools.tex:324`): the marginal of the new element `b = none`. -/
def thetaB (α : ℝ) : ℝ :=
  rhoPrime f d K m' β' α none

variable {f d K m' β'}

/-- `ρ'(α) = ρ(ξ'(α))`: the full-plane marginals are the marginals `α m − β ξ'(α)` at the full-plane
best response (their definition, `appB-tools.tex:38`). -/
lemma rhoPrime_eq_marg (α : ℝ) (o : Option E) :
    rhoPrime f d K m' β' α o = marg m' β' α (xiPrime f d K m' β' α) o :=
  rfl

/-! ### `thm:splice`(a) -/

/-- `thm:splice`, the proof of (a) (`appB-tools.tex:345-353`, "We first prove property (a)."): for
every `θ`, `A = A^f_θ(α)` lies in `A' = A^h_θ(α)`. Steps: (1) `F^h_{α,θ} = F^f_{α,θ} − d`, and
`d ≥ 0`; (2) the submodularity of `F^f_{α,θ}` and the minimality of `A` (`lem:fullplane`(b)) give
`F^h(A ∪ A') − F^h(A') = F^f(A ∪ A') − F^f(A') − d(A ∖ A') ≤ F^f(A ∪ A') − F^f(A')
≤ F^f(A) − F^f(A ∩ A') ≤ 0`; (3) so `A ∪ A'` minimizes `F^h_{α,θ}`, as `A'` does, and `A ⊆ A'` by
`lem:fullplane`(b). -/
theorem levelSet_subset_subMod (H : FPHyp f β) (hd : ∀ e, 0 ≤ d e) (α θ : ℝ) :
    levelSet m β α (xi f m β α) θ ⊆ levelSet m β α (xi (subMod f d) m β α) θ := by
  -- (1) "Fix `θ ∈ ℝ`, and let `A := A^f_θ(α)` and `A' := A^h_θ(α)`. As `F^h_{α,θ} = F^f_{α,θ} − d`
  -- and `d ≥ 0`, …"
  set A := levelSet m β α (xi f m β α) θ
  set A' := levelSet m β α (xi (subMod f d) m β α) θ
  set Ff := levelFun f m β α θ
  set Fh := levelFun (subMod f d) m β α θ
  have hFh : ∀ S, Fh S = Ff S - ∑ e ∈ S, d e := fun S => by
    simp only [Fh, Ff, levelFun, Hardness.subMod]
    ring
  have hdA : ∑ e ∈ A ∪ A', d e = ∑ e ∈ A', d e + ∑ e ∈ A \ A', d e := by
    rw [← sum_union disjoint_sdiff, union_sdiff_self_eq_union, union_comm]
  have hdnn : 0 ≤ ∑ e ∈ A \ A', d e := sum_nonneg fun e _ => hd e
  -- (2) "… the submodularity of `F^f_{α,θ}` and the minimality of `A` (`lem:fullplane`(b)) give
  -- `F^h_{α,θ}(A ∪ A') − F^h_{α,θ}(A') = F^f_{α,θ}(A ∪ A') − F^f_{α,θ}(A') − d(A ∖ A')`
  -- `≤ F^f_{α,θ}(A ∪ A') − F^f_{α,θ}(A')`
  -- `≤ F^f_{α,θ}(A) − F^f_{α,θ}(A ∩ A') ≤ 0`."
  have hsub := levelFun_submodular H.submod m β α θ A A'
  have hmin := (levelSet_isMaxMinimiser H m α θ).1 (A ∩ A')
  have hcalc : Fh (A ∪ A') - Fh A' ≤ 0 :=
    calc Fh (A ∪ A') - Fh A' = Ff (A ∪ A') - Ff A' - ∑ e ∈ A \ A', d e := by
          rw [hFh, hFh, hdA]
          ring
      _ ≤ Ff (A ∪ A') - Ff A' := by linarith
      _ ≤ Ff A - Ff (A ∩ A') := by linarith
      _ ≤ 0 := by linarith
  -- (3) "So `A ∪ A'` minimizes `F^h_{α,θ}`, as `A'` does, and `A ⊆ A'` by `lem:fullplane`(b)."
  exact subset_union_left.trans ((levelSet_isMaxMinimiser (H.subMod d) m α θ).2 _ (by linarith))

/-- `thm:splice`(a), first part, auxiliary form (`appB-tools.tex:354`): `ρ^f ≤ ρ^h`. As
`levelSet_subset_subMod` holds for every `θ`, an element `e` with `ρ^f_e > ρ^h_e` would lie in `A`
but not in `A'` for `θ := ρ^f_e`. -/
theorem rho_le_rho_subMod (H : FPHyp f β) (hd : ∀ e, 0 ≤ d e) (α : ℝ) (e : E) :
    rho f m β α e ≤ rho (subMod f d) m β α e := by
  -- (1) "As this holds for every `θ`, `ρ^f ≤ ρ^h`: an element `e` with `ρ^f_e > ρ^h_e` would lie in
  -- `A` but not in `A'` for `θ := ρ^f_e`."
  by_contra hlt
  rw [not_le] at hlt
  have hA : e ∈ levelSet m β α (xi f m β α) (rho f m β α e) := by
    unfold levelSet
    rw [mem_filter]
    exact ⟨mem_univ e, le_rfl⟩
  have hA' := levelSet_subset_subMod H hd α (rho f m β α e) hA
  unfold levelSet at hA'
  rw [mem_filter] at hA'
  exact absurd hA'.2 (not_le.2 hlt)

/-- `thm:splice`(a), second part, auxiliary form (`appB-tools.tex:355-358`): the set `E` is tight
for `ξ^f(α)` and `ξ^h(α)`, and `ρ^h_e − ρ^f_e = β_e (ξ^f_e − ξ^h_e)`, so
`∑_e (ρ^h_e − ρ^f_e)/β_e = ∑_e (ξ^f_e − ξ^h_e) = f(E) − h(E) = d(E)`. -/
theorem sum_rho_subMod_sub (H : FPHyp f β) (d : E → ℝ) (α : ℝ) :
    ∑ e, (rho (subMod f d) m β α e - rho f m β α e) / β e = ∑ e, d e := by
  -- (1) "The set `E` is tight for `ξ^f(α)` and for `ξ^h(α)`, …"
  have h1 := (xi_mem_fpBase H m α).2
  have h2 := (xi_mem_fpBase (H.subMod d) m α).2
  -- "… and `ρ^h_e − ρ^f_e = β_e(ξ^f_e − ξ^h_e)`, so
  -- `∑_{e∈E} (ρ^h_e − ρ^f_e)/β_e = ∑_{e∈E} (ξ^f_e − ξ^h_e) = f(E) − h(E) = d(E)`."
  have : ∀ e, (rho (subMod f d) m β α e - rho f m β α e) / β e =
      xi f m β α e - xi (subMod f d) m β α e := by
    intro e
    have := (H.pos e).ne'
    simp only [rho, marg]
    field_simp
    ring
  rw [sum_congr rfl fun e _ => this e, sum_sub_distrib, h1, h2]
  simp [Hardness.subMod]

/-! ### Clamps and medians -/

/-- `clamp(v, a, a') = min(max(v, a), a')` (for `a ≤ a'`). -/
def clamp (v a a' : ℝ) : ℝ :=
  min (max v a) a'

/-- The median `med(a, b, c)` of three numbers. -/
def med (a b c : ℝ) : ℝ :=
  max (min a b) (min (max a b) c)

/-- The clamp `c_e = clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)` of the splice, for `a = ρ^f_e` and
`b = ρ^h_e`. -/
def clampTerm (a b θ : ℝ) : ℝ :=
  clamp (θ - a) 0 (b - a)

/-! The elementary facts about clamps and medians below are used without proof in the paper (not in
the paper: their proofs). -/

section Clamp

variable {a b θ θ' : ℝ}

/-- The median of `a ≤ b` and `θ` is `min(max(a, θ), b)` (`appB-tools.tex:386`; not in the paper:
the paper uses this without proof). -/
lemma med_eq_min_max (hab : a ≤ b) : med a θ b = min (max a θ) b := by
  unfold med
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- `c_e ≥ 0`, which is well defined by `ρ^f_e ≤ ρ^h_e` (`appB-tools.tex:365, 369`; not in the
paper: the paper uses this without proof). -/
lemma clampTerm_nonneg (hab : a ≤ b) : 0 ≤ clampTerm a b θ :=
  le_min (le_max_right _ _) (sub_nonneg.2 hab)

/-- `c_e ≤ ρ^h_e − ρ^f_e` (`appB-tools.tex:369`; not in the paper: the paper uses this without
proof). -/
lemma clampTerm_le : clampTerm a b θ ≤ b - a :=
  min_le_right _ _

/-- `a + clamp(θ − a, 0, b − a) = med(a, θ, b)` for `a ≤ b` (`appB-tools.tex:367`; not in the paper:
the paper uses this without proof). -/
lemma add_clampTerm_eq_med (hab : a ≤ b) : a + clampTerm a b θ = med a θ b := by
  rw [med_eq_min_max hab]
  unfold clampTerm clamp
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- The clamp is `0` for `θ ≤ a` (`appB-tools.tex:383, 440`; not in the paper: the paper uses this
without proof). -/
lemma clampTerm_eq_zero (hab : a ≤ b) (h : θ ≤ a) : clampTerm a b θ = 0 := by
  unfold clampTerm clamp
  rw [max_eq_right (by linarith), min_eq_left (by linarith)]

/-- The clamp is `b − a` for `b ≤ θ` (`appB-tools.tex:388, 440`; not in the paper: the paper uses
this without proof). -/
lemma clampTerm_eq_sub (h : b ≤ θ) (hab : a ≤ b) : clampTerm a b θ = b - a := by
  unfold clampTerm clamp
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

/-- The clamp is `θ − a` for `a ≤ θ ≤ b` (`appB-tools.tex:440`; not in the paper: the paper uses
this without proof). -/
lemma clampTerm_eq_mid (h1 : a ≤ θ) (h2 : θ ≤ b) : clampTerm a b θ = θ - a := by
  unfold clampTerm clamp
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

/-- `med(a, θ, b) = a` for `θ ≤ a ≤ b` (`appB-tools.tex:399, 428`; not in the paper: the paper uses
this without proof). -/
lemma med_eq_left (hab : a ≤ b) (h : θ ≤ a) : med a θ b = a := by
  rw [← add_clampTerm_eq_med hab, clampTerm_eq_zero hab h, add_zero]

/-- `med(a, θ, b) = θ` for `a ≤ θ ≤ b` (`appB-tools.tex:399, 428`; not in the paper: the paper uses
this without proof). -/
lemma med_eq_mid (h1 : a ≤ θ) (h2 : θ ≤ b) : med a θ b = θ := by
  rw [← add_clampTerm_eq_med (h1.trans h2), clampTerm_eq_mid h1 h2]
  ring

/-- `med(a, θ, b) = b` for `a ≤ b ≤ θ` (`appB-tools.tex:399, 428`; not in the paper: the paper uses
this without proof). -/
lemma med_eq_right (hab : a ≤ b) (h : b ≤ θ) : med a θ b = b := by
  rw [← add_clampTerm_eq_med hab, clampTerm_eq_sub h hab]
  ring

/-- For `θ' > θ` (`appB-tools.tex:382`): the median `med(a, θ, b)` exceeds `θ` exactly if
`a > θ`, and then it equals `a`; so it is at least `θ'` exactly if `a ≥ θ'` (the paper states this
without proof). -/
lemma le_med_iff_of_lt (hab : a ≤ b) (h : θ < θ') : θ' ≤ med a θ b ↔ θ' ≤ a := by
  have hexc : θ < med a θ b ↔ θ < a := by
    rw [med_eq_min_max hab]
    constructor
    · intro h'
      by_contra ha
      rw [not_lt] at ha
      rw [max_eq_right ha] at h'
      exact absurd (min_le_left θ b) (not_le.2 h')
    · intro ha
      exact lt_min (lt_max_of_lt_left ha) (ha.trans_le hab)
  have heq : θ < a → med a θ b = a := fun ha => by
    rw [med_eq_min_max hab, max_eq_left ha.le, min_eq_left hab]
  constructor
  · intro h'
    have ha := hexc.1 (h.trans_le h')
    rwa [heq ha] at h'
  · intro h'
    rw [heq (h.trans_le h')]
    exact h'

/-- For `θ' ≤ θ` (`appB-tools.tex:386`): the median `min(max(a, θ), b)` is at least `θ'` exactly if
`b ≥ θ'` (the paper states this without proof). -/
lemma le_med_iff_of_le (hab : a ≤ b) (h : θ' ≤ θ) : θ' ≤ med a θ b ↔ θ' ≤ b := by
  rw [med_eq_min_max hab, le_min_iff]
  exact ⟨fun h' => h'.2, fun h' => ⟨h.trans (le_max_right _ _), h'⟩⟩

/-- The clamp `clamp(θ − a, 0, b − a)` of the affine function `θ − a` is continuous in `θ` (not in
the paper: the paper uses this without proof, in "as `Y` is a sum of clamps of affine functions",
`appB-tools.tex:362`). -/
lemma continuous_clampTerm (a b : ℝ) : Continuous fun θ => clampTerm a b θ := by
  unfold clampTerm clamp
  fun_prop

/-- The clamp is nondecreasing in `θ` (`appB-tools.tex:362`; not in the paper: the paper uses this
without proof, in "as `Y` is nondecreasing"). -/
lemma monotone_clampTerm (a b : ℝ) : Monotone fun θ => clampTerm a b θ := by
  intro θ₁ θ₂ h
  unfold clampTerm clamp
  exact min_le_min_right _ (max_le_max_right _ (by linarith))

end Clamp

/-! ### `thm:splice`(b) and (c) -/

variable (f d K m' β')

/-- `Y(θ) = ∑_{e∈E} clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)/β_e`, with the old instance
`(m' ∘ some, β' ∘ some)`. -/
def bigY (α θ : ℝ) : ℝ :=
  ∑ e, clampTerm (rho f (fun e => m' (some e)) (fun e => β' (some e)) α e)
    (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) θ / β' (some e)

/-- `θ` solves (`eq:splice`): `(α m_b − θ)/β_b = K − d(E) + Y(θ)`. -/
def IsF1 (α θ : ℝ) : Prop :=
  (α * m' none - θ) / β' none = K - ∑ e, d e + bigY f d m' β' α θ

/-- The difference `(α m_b − θ)/β_b − (K − d(E) + Y(θ))` of the two sides of (`eq:splice`), as a
function of `θ` (the proof of (b) and (c), `appB-tools.tex:362-364`). -/
def spliceDiff (α θ : ℝ) : ℝ :=
  (α * m' none - θ) / β' none - (K - ∑ e, d e + bigY f d m' β' α θ)

/-- The vector `y` of the proof of (b) and (c) (`appB-tools.tex:366`) for the solution `θ` of
(`eq:splice`): `y_b = (α m_b − θ)/β_b` and `y_e = ξ^f_e − c_e/β_e` for `e ∈ E`. -/
def splicePoint (α θ : ℝ) : Option E → ℝ := fun o =>
  Option.elim o ((α * m' none - θ) / β' none) fun e =>
    xi f (fun e => m' (some e)) (fun e => β' (some e)) α e -
      clampTerm (rho f (fun e => m' (some e)) (fun e => β' (some e)) α e)
        (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) θ / β' (some e)

variable {f d K m' β'}

omit [DecidableEq E] in
/-- `θ` solves (`eq:splice`) exactly if the difference of its two sides vanishes. -/
lemma isF1_iff_spliceDiff {α θ : ℝ} :
    IsF1 f d K m' β' α θ ↔ spliceDiff f d K m' β' α θ = 0 := by
  unfold IsF1 spliceDiff
  exact sub_eq_zero.symm

/-- `Y(θ) ∈ [0, d(E)]` (`appB-tools.tex:338`), by (a): each clamp lies in
`[0, ρ^h_e − ρ^f_e]`, and `∑_e (ρ^h_e − ρ^f_e)/β_e = d(E)`. -/
theorem bigY_mem (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e) (α θ : ℝ) :
    0 ≤ bigY f d m' β' α θ ∧ bigY f d m' β' α θ ≤ ∑ e, d e := by
  have hle := rho_le_rho_subMod (m := fun e => m' (some e)) H hd α
  refine ⟨sum_nonneg fun e _ => div_nonneg (clampTerm_nonneg (hle e)) (H.pos e).le, ?_⟩
  rw [← sum_rho_subMod_sub H d α (m := fun e => m' (some e))]
  exact sum_le_sum fun e _ => div_le_div_of_nonneg_right clampTerm_le (H.pos e).le

/-- `Y` is nondecreasing, as each clamp is nondecreasing in `θ` (`monotone_clampTerm`; not in the
paper: the paper uses this without proof, in "as `Y` is nondecreasing", `appB-tools.tex:362`). -/
theorem bigY_mono (H : FPHyp f fun e => β' (some e)) (α : ℝ) : Monotone (bigY f d m' β' α) :=
  fun _ _ h => sum_le_sum fun e _ =>
    div_le_div_of_nonneg_right (monotone_clampTerm _ _ h) (H.pos e).le

omit [DecidableEq E] in
/-- The proof of (b) and (c) (`appB-tools.tex:362`): the difference of the two sides of
(`eq:splice`) is continuous in `θ`, as `Y` is a sum of clamps of affine functions
(`continuous_clampTerm`). -/
theorem continuous_spliceDiff (α : ℝ) : Continuous (spliceDiff f d K m' β' α) := by
  unfold spliceDiff bigY
  refine ((continuous_const.sub continuous_id).div_const _).sub
    (continuous_const.add (continuous_finsetSum _ fun e _ => ?_))
  exact (continuous_clampTerm _ _).div_const _

/-- The proof of (b) and (c) (`appB-tools.tex:362`): the difference of the two sides of
(`eq:splice`) is strictly decreasing in `θ`, as `Y` is nondecreasing (`bigY_mono`). -/
theorem strictAnti_spliceDiff (H : FPHyp f fun e => β' (some e)) (hb : 0 < β' none) (α : ℝ) :
    StrictAnti (spliceDiff f d K m' β' α) := by
  intro θ₁ θ₂ h
  have h1 : (α * m' none - θ₂) / β' none < (α * m' none - θ₁) / β' none :=
    div_lt_div_of_pos_right (by linarith) hb
  have h2 := bigY_mono (d := d) (m' := m') H α h.le
  unfold spliceDiff
  linarith

/-- The proof of (b) and (c) (`appB-tools.tex:363`): as `0 ≤ Y ≤ d(E)` by (a) (`bigY_mem`), the
difference of the two sides of (`eq:splice`) is nonnegative at `θ = α m_b − β_b K` and nonpositive
at `θ = α m_b − β_b (K − d(E))`. -/
theorem spliceDiff_signs (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) (α : ℝ) :
    0 ≤ spliceDiff f d K m' β' α (α * m' none - β' none * K) ∧
      spliceDiff f d K m' β' α (α * m' none - β' none * (K - ∑ e, d e)) ≤ 0 := by
  have := hb.ne'
  constructor
  · have h1 : (α * m' none - (α * m' none - β' none * K)) / β' none = K := by
      field_simp
      ring
    unfold spliceDiff
    rw [h1]
    linarith [(bigY_mem (m' := m') H hd α (α * m' none - β' none * K)).2]
  · have h1 : (α * m' none - (α * m' none - β' none * (K - ∑ e, d e))) / β' none =
        K - ∑ e, d e := by
      field_simp
      ring
    unfold spliceDiff
    rw [h1]
    linarith [(bigY_mem (m' := m') H hd α (α * m' none - β' none * (K - ∑ e, d e))).1]

/-- The proof of (b) and (c) (`appB-tools.tex:367`): at the share `α`, the marginals (`eq:marg`) of
the vector `y` (`splicePoint`) are `ρ_b(y) = θ` and `ρ_e(y) = ρ^f_e + c_e = med(ρ^f_e, θ, ρ^h_e)`
for `e ∈ E` (the last step as `ρ^f ≤ ρ^h` by (a), `add_clampTerm_eq_med`). -/
theorem marg_splicePoint (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) (α θ : ℝ) :
    marg m' β' α (splicePoint f d m' β' α θ) none = θ ∧
      ∀ e, marg m' β' α (splicePoint f d m' β' α θ) (some e) =
        med (rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) θ
          (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) := by
  have hle := rho_le_rho_subMod (m := fun e => m' (some e)) H hd α
  constructor
  · -- (1) "At the share `α`, its marginals (`eq:marg`) are `ρ_b(y) = θ` …"
    -- Here `ρ_b(y) = α m_b − β_b (α m_b − θ)/β_b`.
    have := hb.ne'
    simp only [marg, splicePoint, Option.elim]
    field_simp
    ring
  · -- "… and `ρ_e(y) = ρ^f_e + c_e = med(ρ^f_e, θ, ρ^h_e)` for `e ∈ E`."
    -- Here `ρ_e(y) = α m_e − β_e (ξ^f_e − c_e/β_e)`, and the median uses `ρ^f_e ≤ ρ^h_e`.
    intro e
    rw [← add_clampTerm_eq_med (hle e)]
    have := (H.pos e).ne'
    simp only [marg, splicePoint, Option.elim, rho]
    field_simp
    ring

/-- `thm:splice`, the construction in the proof of (b) and (c) (`appB-tools.tex:365-393`): for the
solution `θ` of (`eq:splice`), `ξ^{f'}(α)` is the vector `y` with `y_b = (α m_b − θ)/β_b` and
`y_e = ξ^f_e − c_e/β_e`, `c_e = clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)`. (It holds for every solution;
the proof uses only that `θ` solves (`eq:splice`).) Steps: (1) at the share `α`, its marginals are
`ρ_b(y) = θ` and `ρ_e(y) = ρ^f_e + c_e = med(ρ^f_e, θ, ρ^h_e)` (`marg_splicePoint`); (2) with
`π_e = (ρ^h_e − ρ^f_e)/β_e = ξ^f_e − ξ^h_e`, `π_e ≥ c_e/β_e ≥ 0`, `∑_e π_e = d(E)`, and
`y_b = K − d(E) + ∑_e c_e/β_e` by (`eq:splice`), every `S ⊆ E` satisfies
`y(S) ≤ ξ^f(S) ≤ f(S)` and `y(S) + y_b = K + ξ^h(S) − ∑_{e∈E∖S} (π_e − c_e/β_e) ≤ K + h(S)`
(`eq:B-feas`), so `y(S') ≤ f'(S')` for every `S' ⊆ E ∪ {b}`; (3) for `θ' > θ`, the level set
`{ρ(y) ≥ θ'}` is `{e ∈ E : ρ^f_e ≥ θ'}`, on which `c = 0`, tight for `ξ^f(α)` by
`lem:fullplane`(a); (4) for `θ' ≤ θ`, it is `A ∪ {b}` with `A = {e ∈ E : ρ^h_e ≥ θ'}`, every
`e ∈ E ∖ A` has `c_e/β_e = π_e`, so the sum in (`eq:B-feas`) vanishes for `S = A`, and as `A` is
tight for `ξ^h(α)` by `lem:fullplane`(a), `y(A) + y_b = K + ξ^h(A) = K + h(A) = f'(A ∪ {b})`;
(5) by `lem:fullplane`(a), `y = ξ'(α)`. -/
theorem xi_extend_of_isF1 (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) {α θ : ℝ} (hθ : IsF1 f d K m' β' α θ) :
    xiPrime f d K m' β' α = splicePoint f d m' β' α θ := by
  symm
  set m : E → ℝ := fun e => m' (some e)
  set β : E → ℝ := fun e => β' (some e)
  set ξf := xi f m β α
  set ξh := xi (subMod f d) m β α
  set ρf := rho f m β α
  set ρh := rho (subMod f d) m β α
  set c : E → ℝ := fun e => clampTerm (ρf e) (ρh e) θ
  set π : E → ℝ := fun e => (ρh e - ρf e) / β e
  set y := splicePoint f d m' β' α θ
  have hβ := H.pos
  have hle : ∀ e, ρf e ≤ ρh e := rho_le_rho_subMod H hd α
  -- (1) "At the share `α`, its marginals (`eq:marg`) are `ρ_b(y) = θ` and
  -- `ρ_e(y) = ρ^f_e + c_e = med(ρ^f_e, θ, ρ^h_e)` for `e ∈ E`." (`marg_splicePoint`)
  have hmarg_none : marg m' β' α y none = θ := (marg_splicePoint H hd hb α θ).1
  have hmarg_some : ∀ e, marg m' β' α y (some e) = med (ρf e) θ (ρh e) :=
    (marg_splicePoint H hd hb α θ).2
  -- (2) "Let `π_e := (ρ^h_e − ρ^f_e)/β_e = ξ^f_e − ξ^h_e` for `e ∈ E`. Then `π_e ≥ c_e/β_e ≥ 0`,
  -- and `∑_{e∈E} π_e = d(E)` by (a)."
  have hξ : ∀ e, ξf e = ξh e + π e := by
    intro e
    have := (hβ e).ne'
    simp only [ξf, ξh, π, ρf, ρh, rho, marg]
    field_simp
    ring
  have hcπ : ∀ e, c e / β e ≤ π e := fun e =>
    div_le_div_of_nonneg_right clampTerm_le (hβ e).le
  have hc0 : ∀ e, 0 ≤ c e / β e := fun e =>
    div_nonneg (clampTerm_nonneg (hle e)) (hβ e).le
  have hπE : ∑ e, π e = ∑ e, d e := sum_rho_subMod_sub H d α
  -- "By (`eq:splice`), `y_b = K − d(E) + ∑_{e∈E} c_e/β_e`."
  have hy_none : y none = K - ∑ e, d e + ∑ e, c e / β e := hθ
  have hsum : ∀ T : Finset (Option E), ∑ o ∈ T, y o =
      (if none ∈ T then y none else 0) + ∑ e ∈ eraseNone T, (ξf e - c e / β e) :=
    fun T => sum_option_finset T y
  -- "With `ξ^f(S) = ξ^h(S) + ∑_{e∈S} π_e`, every `S ⊆ E` therefore satisfies
  -- `y(S) ≤ ξ^f(S) ≤ f(S)`,
  -- `y(S) + y_b = K + ξ^h(S) − ∑_{e∈E∖S} (π_e − c_e/β_e) ≤ K + h(S)` (`eq:B-feas`), …"
  -- Here the Lean proves the equality of the second line; the inequalities follow below.
  have hfeas : ∀ S : Finset E, ∑ e ∈ S, (ξf e - c e / β e) + y none =
      K + ∑ e ∈ S, ξh e - ∑ e ∈ Sᶜ, (π e - c e / β e) := by
    intro S
    have h1 : ∑ e ∈ S, (ξf e - c e / β e) = ∑ e ∈ S, ξh e + ∑ e ∈ S, π e - ∑ e ∈ S, c e / β e := by
      rw [← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun e _ => by rw [hξ e]
    have h3 := sum_add_sum_compl S fun e => c e / β e
    have h4 := sum_add_sum_compl S π
    rw [h1, hy_none, sum_sub_distrib]
    linarith
  have hfE := xi_mem_fpBase H m α
  have hhE := xi_mem_fpBase (H.subMod d) m α
  -- "… so `y(S') ≤ f'(S')` for every `S' ⊆ E ∪ {b}`."
  -- The Lean proves the two inequalities of (`eq:B-feas`) here, for `S' = S` and `S' = S ∪ {b}`.
  have hyP : y ∈ fpPoly (extend f d K) := fun T => by
    rw [hsum]
    set T' := eraseNone T
    by_cases hT : none ∈ T
    · simp only [hT, ↓reduceIte, extend, Hardness.subMod]
      have h1 := hhE.1 T'
      have h5 : 0 ≤ ∑ e ∈ T'ᶜ, (π e - c e / β e) :=
        sum_nonneg fun e _ => sub_nonneg.2 (hcπ e)
      have h6 := hfeas T'
      simp only [Hardness.subMod] at h1
      linarith
    · simp only [hT, ↓reduceIte, extend, zero_add]
      have h1 := hfE.1 T'
      have h2 : ∑ e ∈ T', (ξf e - c e / β e) ≤ ∑ e ∈ T', ξf e :=
        sum_le_sum fun e _ => by linarith [hc0 e]
      linarith
  -- "We now show that every upper level set `{e ∈ E ∪ {b} : ρ_e(y) ≥ θ'}`, `θ' ∈ ℝ`, is tight for
  -- `y` with respect to `f'`, using `ρ^f ≤ ρ^h` throughout."
  have hyt : ∀ θ', IsTight (extend f d K) y (levelSet m' β' α y θ') := fun θ' => by
    unfold IsTight
    rw [hsum]
    set L := levelSet m' β' α y θ'
    rcases lt_or_ge θ θ' with hlt | hge
    · -- (3) "Let `θ' > θ`. For `e ∈ E`, the median `med(ρ^f_e, θ, ρ^h_e)` exceeds `θ` exactly if
      -- `ρ^f_e > θ`, and then it equals `ρ^f_e`. As `ρ_b(y) = θ < θ'`, the level set is therefore
      -- `{e ∈ E : ρ^f_e ≥ θ'}`, on which `c = 0`, that is, `y = ξ^f`. This set is tight for
      -- `ξ^f(α)` by `lem:fullplane`(a), hence for `y`, as `f' = f` on subsets of `E`."
      have hnone : none ∉ L := by
        simp only [L, levelSet, mem_filter, mem_univ, true_and, hmarg_none, not_le]
        exact hlt
      have hL : eraseNone L = levelSet m β α ξf θ' := by
        ext e
        rw [mem_eraseNone]
        simp only [L, levelSet, mem_filter, mem_univ, true_and, hmarg_some]
        exact le_med_iff_of_lt (hle e) hlt
      have hc : ∀ e ∈ eraseNone L, c e = 0 := by
        intro e he
        rw [hL] at he
        simp only [levelSet, mem_filter, mem_univ, true_and] at he
        exact clampTerm_eq_zero (hle e) (by
          show θ ≤ ρf e
          have : marg m β α ξf e = ρf e := rfl
          linarith)
      have ht := xi_levelSet_tight H m α θ'
      unfold IsTight at ht
      simp only [hnone, ↓reduceIte, zero_add, extend]
      rw [sum_congr rfl fun e he => by rw [hc e he, zero_div, sub_zero], hL, ht]
    · -- (4) "Now let `θ' ≤ θ`. For `e ∈ E`, the median
      -- `med(ρ^f_e, θ, ρ^h_e) = min(max(ρ^f_e, θ), ρ^h_e)` is at least `θ'` exactly if
      -- `ρ^h_e ≥ θ'`, and `ρ_b(y) = θ ≥ θ'`. So the level set is `A ∪ {b}` with
      -- `A := {e ∈ E : ρ^h_e ≥ θ'}`. Every `e ∈ E ∖ A` has `ρ^h_e < θ' ≤ θ`, so
      -- `c_e = ρ^h_e − ρ^f_e`, that is, `c_e/β_e = π_e`. So the sum in (`eq:B-feas`) vanishes for
      -- `S = A`, and as `A` is tight for `ξ^h(α)` by `lem:fullplane`(a),
      -- `y(A) + y_b = K + ξ^h(A) = K + h(A) = f'(A ∪ {b})`."
      have hnone : none ∈ L := by
        simp only [L, levelSet, mem_filter, mem_univ, true_and, hmarg_none]
        exact hge
      set A := levelSet m β α ξh θ'
      have hL : eraseNone L = A := by
        ext e
        rw [mem_eraseNone]
        simp only [L, A, levelSet, mem_filter, mem_univ, true_and, hmarg_some]
        exact le_med_iff_of_le (hle e) hge
      have hc : ∀ e ∈ Aᶜ, π e - c e / β e = 0 := by
        intro e he
        simp only [A, levelSet, mem_compl, mem_filter, mem_univ, true_and, not_le] at he
        have : marg m β α ξh e = ρh e := rfl
        simp only [c, π]
        rw [clampTerm_eq_sub (by linarith) (hle e), sub_self]
      have ht := xi_levelSet_tight (H.subMod d) m α θ'
      unfold IsTight at ht
      simp only [hnone, ↓reduceIte, extend, Hardness.subMod] at ht ⊢
      rw [hL]
      have h1 := hfeas A
      rw [sum_eq_zero hc, sub_zero] at h1
      linarith
  -- (5) "By `lem:fullplane`(a), `y = ξ'(α)`."
  exact eq_xi_of_levelSets (H.extend hd hb K) hyP hyt

/-- `thm:splice`(c), the last step (`appB-tools.tex:394`): for the solution `θ` of (`eq:splice`),
`θ_b = ρ_b(y) = θ`, as `y = ξ'(α)` (`xi_extend_of_isF1`) and `ρ_b(y) = θ` (`marg_splicePoint`). -/
theorem rho_none_of_isF1 (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) {α θ : ℝ} (hθ : IsF1 f d K m' β' α θ) :
    thetaB f d K m' β' α = θ := by
  rw [thetaB, rhoPrime_eq_marg, xi_extend_of_isF1 H hd hb hθ]
  exact (marg_splicePoint H hd hb α θ).1

/-- `thm:splice`, auxiliary form (`appB-tools.tex:344-395`, under `FPHyp` and `d ≥ 0`, `β_b > 0`):
(a) `ρ^f ≤ ρ^h` and `∑_e (ρ^h_e − ρ^f_e)/β_e = d(E)`; (b) `ρ'_e = med(ρ^f_e, θ_b, ρ^h_e)`; (c) `θ_b`
is the unique solution of (`eq:splice`), and `Y(θ) ∈ [0, d(E)]`. The proof first proves property
(a): (1) for every `θ`, `A^f_θ(α) ⊆ A^h_θ(α)` (`levelSet_subset_subMod`), so `ρ^f ≤ ρ^h`
(`rho_le_rho_subMod`); (2) `E` is tight for `ξ^f(α)` and `ξ^h(α)`, and
`ρ^h_e − ρ^f_e = β_e (ξ^f_e − ξ^h_e)`, which gives the sum (`sum_rho_subMod_sub`). Then it proves
properties (b) and (c): (3) the difference of the two sides of (`eq:splice`) (`spliceDiff`) is
continuous in `θ`, as `Y` is a sum of clamps of affine functions (`continuous_spliceDiff`), and
strictly decreasing, as `Y` is nondecreasing (`strictAnti_spliceDiff`); (4) as `0 ≤ Y ≤ d(E)` by
(a), the difference is nonnegative at `θ = α m_b − β_b K` and nonpositive at
`θ = α m_b − β_b (K − d(E))` (`spliceDiff_signs`); (5) so, by the intermediate value theorem,
(`eq:splice`) has a solution `θ`, and it is unique, as the difference is strictly decreasing;
(6) with `c_e = clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)`, the vector `y` with `y_b = (α m_b − θ)/β_b`
and `y_e = ξ^f_e − c_e/β_e` is `ξ'(α)` by `lem:fullplane`(a) (`xi_extend_of_isF1`); (7) this proves
(b), as `ρ'_e = ρ_e(y) = med(ρ^f_e, θ, ρ^h_e)` (`marg_splicePoint`), and (c) with
`θ_b = ρ_b(y) = θ` (`rho_none_of_isF1`). -/
theorem splice_aux (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e) (hb : 0 < β' none)
    (α : ℝ) :
    ((∀ e, rho f (fun e => m' (some e)) (fun e => β' (some e)) α e ≤
        rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      ∑ e, (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e -
        rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) / β' (some e) = ∑ e, d e) ∧
    (∀ e, rhoPrime f d K m' β' α (some e) =
      med (rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) (thetaB f d K m' β' α)
        (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e)) ∧
    ((IsF1 f d K m' β' α (thetaB f d K m' β' α) ∧
        ∀ θ, IsF1 f d K m' β' α θ → θ = thetaB f d K m' β' α) ∧
      ∀ θ, 0 ≤ bigY f d m' β' α θ ∧ bigY f d m' β' α θ ≤ ∑ e, d e) := by
  -- (1) "We first prove property (a). … As this holds for every `θ`, `ρ^f ≤ ρ^h`: …"
  -- The omitted sentences (`appB-tools.tex:346-353`) are `levelSet_subset_subMod`, and the quoted
  -- sentence after them is `rho_le_rho_subMod`.
  have ha1 := rho_le_rho_subMod (m := fun e => m' (some e)) H hd α
  -- (2) "The set `E` is tight for `ξ^f(α)` and for `ξ^h(α)`, … This proves (a)."
  -- (`sum_rho_subMod_sub`)
  have ha2 := sum_rho_subMod_sub (m := fun e => m' (some e)) H d α
  -- (3) "Now we prove properties (b) and (c). The difference of the two sides of (`eq:splice`) is
  -- continuous in `θ`, as `Y` is a sum of clamps of affine functions, and strictly decreasing, as
  -- `Y` is nondecreasing."
  have hcont := continuous_spliceDiff (f := f) (d := d) (K := K) (m' := m') (β' := β') α
  have hanti := strictAnti_spliceDiff (K := K) (d := d) (m' := m') H hb α
  -- (4) "As `0 ≤ Y ≤ d(E)` by (a), the difference is nonnegative at `θ = α m_b − β_b K` and
  -- nonpositive at `θ = α m_b − β_b(K − d(E))`."
  obtain ⟨hlo, hhi⟩ := spliceDiff_signs (K := K) (m' := m') H hd hb α
  -- (5) "So, by the intermediate value theorem, (`eq:splice`) has a solution `θ`, and it is
  -- unique, as the difference is strictly decreasing."
  have hlohi : α * m' none - β' none * K ≤ α * m' none - β' none * (K - ∑ e, d e) := by
    have := mul_nonneg hb.le (sum_nonneg fun e (_ : e ∈ univ) => hd e)
    nlinarith
  obtain ⟨θ, -, hθ0⟩ := intermediate_value_Icc' hlohi hcont.continuousOn ⟨hhi, hlo⟩
  have hθ : IsF1 f d K m' β' α θ := isF1_iff_spliceDiff.2 hθ0
  have huniq : ∀ θ', IsF1 f d K m' β' α θ' → θ' = θ := fun θ' h' =>
    hanti.injective ((isF1_iff_spliceDiff.1 h').trans hθ0.symm)
  -- (6) "For `e ∈ E`, write `c_e := clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)`, which is well defined by
  -- (a). Define `y ∈ ℝ^{E∪{b}}` by `y_b := (α m_b − θ)/β_b` and `y_e := ξ^f_e − c_e/β_e` for
  -- `e ∈ E`. … By `lem:fullplane`(a), `y = ξ'(α)`."
  -- These sentences (`appB-tools.tex:365-393`) are `xi_extend_of_isF1`.
  have hξ' : xiPrime f d K m' β' α = splicePoint f d m' β' α θ := xi_extend_of_isF1 H hd hb hθ
  -- (7) "This proves (b), and (c) with `θ_b = ρ_b(y) = θ`."
  -- For (b), the Lean uses `ρ'_e = ρ_e(y) = med(ρ^f_e, θ, ρ^h_e)` (`marg_splicePoint`).
  have hθb : thetaB f d K m' β' α = θ := rho_none_of_isF1 H hd hb hθ
  have hmed : ∀ e, rhoPrime f d K m' β' α (some e) =
      med (rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) θ
        (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) := fun e => by
    rw [rhoPrime_eq_marg, hξ']
    exact (marg_splicePoint H hd hb α θ).2 e
  refine ⟨⟨ha1, ha2⟩, fun e => ?_, ⟨⟨by rw [hθb]; exact hθ, fun θ' h => ?_⟩, bigY_mem H hd α⟩⟩
  · rw [hmed e, hθb]
  · rw [hθb]
    exact huniq θ' h

/-- **`thm:splice`** (Theorem B.12, `appB-tools.tex:326-342`, proof
`appB-tools.tex:344-395`): let `f` be submodular with `f(∅) = 0`, `m, β > 0`, `d ≥ 0`, `K ∈ ℝ`,
`b ∉ E` with `m_b, β_b > 0`, `h = f − d` and `f'` the extension of `f` by `b`; fix `α ∈ ℝ`. Then (a)
`ρ^f_e ≤ ρ^h_e` for every `e ∈ E`, and `∑_{e∈E} (ρ^h_e − ρ^f_e)/β_e = d(E)`; (b)
`ρ'_e = med(ρ^f_e, θ_b, ρ^h_e)` for every `e ∈ E`; (c) `θ_b` is the unique solution `θ` of
(`eq:splice`) `(α m_b − θ)/β_b = K − d(E) + Y(θ)` (`IsF1`), where
`Y(θ) = ∑_{e∈E} clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)/β_e ∈ [0, d(E)]`. Steps (in `splice_aux`): the
proof first proves property (a): (1) for every `θ`, `A^f_θ(α) ⊆ A^h_θ(α)` by the submodularity of
`F^f_{α,θ}` and the minimality of `A^f_θ(α)`, hence `ρ^f ≤ ρ^h` (`levelSet_subset_subMod`,
`rho_le_rho_subMod`); (2) `E` is tight for `ξ^f(α)` and `ξ^h(α)`, which gives the sum
(`sum_rho_subMod_sub`). Then it proves properties (b) and (c): (3) the difference of the two sides
of (`eq:splice`) is continuous in `θ`, as `Y` is a sum of clamps of affine functions, and strictly
decreasing, as `Y` is nondecreasing; (4) as `0 ≤ Y ≤ d(E)` by (a), it is nonnegative at
`θ = α m_b − β_b K` and nonpositive at `θ = α m_b − β_b (K − d(E))`; (5) so, by the intermediate
value theorem, (`eq:splice`) has a solution `θ`, and it is unique, as the difference is strictly
decreasing; (6) the vector `y` with `y_b = (α m_b − θ)/β_b` and `y_e = ξ^f_e − c_e/β_e` satisfies
`y ≤ f'` and has tight upper level sets, so `y = ξ'(α)` by `lem:fullplane`(a)
(`xi_extend_of_isF1`); (7) this proves (b), and (c) with `θ_b = ρ_b(y) = θ`. The hypothesis
`m > 0` is not used. -/
theorem splice (hf : Submodular f) (hf0 : f ∅ = 0) (_hm : ∀ o, 0 < m' o) (hβ : ∀ o, 0 < β' o)
    (hd : ∀ e, 0 ≤ d e) (K α : ℝ) :
    ((∀ e, rho f (fun e => m' (some e)) (fun e => β' (some e)) α e ≤
        rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      ∑ e, (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e -
        rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) / β' (some e) = ∑ e, d e) ∧
    (∀ e, rhoPrime f d K m' β' α (some e) =
      med (rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) (thetaB f d K m' β' α)
        (rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e)) ∧
    ((IsF1 f d K m' β' α (thetaB f d K m' β' α) ∧
        ∀ θ, IsF1 f d K m' β' α θ → θ = thetaB f d K m' β' α) ∧
      ∀ θ, 0 ≤ bigY f d m' β' α θ ∧ bigY f d m' β' α θ ≤ ∑ e, d e) :=
  splice_aux ⟨hf, hf0, fun e => hβ (some e)⟩ hd (hβ none) α

/-! ### Configurations (`appB-tools.tex:397-401`) -/

variable (f d K m' β')

/-- The configuration at `α`, first set: `U = {e ∈ E : ρ^f_e(α) > θ_b(α)}`. -/
def configU (α : ℝ) : Finset E :=
  univ.filter fun e => thetaB f d K m' β' α <
    rho f (fun e => m' (some e)) (fun e => β' (some e)) α e

/-- The configuration at `α`, second set: `W = {e ∈ E : ρ^h_e(α) ≥ θ_b(α)}`. -/
def configW (α : ℝ) : Finset E :=
  univ.filter fun e => thetaB f d K m' β' α ≤
    rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e

/-- The block `D = (W ∖ U) ∪ {b}` (`appB-tools.tex:400`, `417`), with `b = none`; for the
configuration, the set of elements of `E ∪ {b}` with the marginal `θ_b`. -/
def blockUW (U W : Finset E) : Finset (Option E) :=
  insertNone (W \ U)

variable {f d K m' β'}

/-- The paragraph "Configurations" (`appB-tools.tex:397-400`), for the configuration `(U, W)` at
`α`: by `thm:splice`, `U ⊆ W`, and `ρ' = ρ^f > θ_b` on `U`, `ρ' = θ_b` on `W ∖ U` and
`ρ' = ρ^h < θ_b` on `E ∖ W`; so the block of `b`, the set of elements of `E ∪ {b}` with the
marginal `θ_b`, is `D = (W ∖ U) ∪ {b}`. (For `f` submodular with `f(∅) = 0`, `m, β > 0` and
`d ≥ 0`; the hypothesis `m > 0` is not used.) -/
theorem config_spec (hf : Submodular f) (hf0 : f ∅ = 0) (_hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (hd : ∀ e, 0 ≤ d e) (α : ℝ) :
    configU f d K m' β' α ⊆ configW f d K m' β' α ∧
      (∀ e ∈ configU f d K m' β' α, rhoPrime f d K m' β' α (some e) =
          rho f (fun e => m' (some e)) (fun e => β' (some e)) α e ∧
        thetaB f d K m' β' α < rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      (∀ e ∈ configW f d K m' β' α \ configU f d K m' β' α,
        rhoPrime f d K m' β' α (some e) = thetaB f d K m' β' α) ∧
      (∀ e ∉ configW f d K m' β' α, rhoPrime f d K m' β' α (some e) =
          rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e ∧
        rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e <
          thetaB f d K m' β' α) ∧
      univ.filter (fun o => rhoPrime f d K m' β' α o = thetaB f d K m' β' α) =
        blockUW (configU f d K m' β' α) (configW f d K m' β' α) := by
  have H : FPHyp f fun e => β' (some e) := ⟨hf, hf0, fun e => hβ (some e)⟩
  -- `thm:splice`(a) and (b): `ρ^f ≤ ρ^h` and `ρ'_e = med(ρ^f_e, θ_b, ρ^h_e)`
  obtain ⟨⟨hle, -⟩, hmed, -⟩ := splice_aux (K := K) H hd (hβ none) α
  set θb := thetaB f d K m' β' α
  have hU : ∀ e, e ∈ configU f d K m' β' α ↔
      θb < rho f (fun e => m' (some e)) (fun e => β' (some e)) α e := fun e => by
    simp [configU, θb]
  have hW : ∀ e, e ∈ configW f d K m' β' α ↔
      θb ≤ rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e := fun e => by
    simp [configW, θb]
  -- `U ⊆ W`, as `ρ^f ≤ ρ^h`
  have hUW : configU f d K m' β' α ⊆ configW f d K m' β' α := fun e he =>
    (hW e).2 (((hU e).1 he).le.trans (hle e))
  -- `ρ' = ρ^f > θ_b` on `U`, `ρ' = θ_b` on `W ∖ U` and `ρ' = ρ^h < θ_b` on `E ∖ W`
  have honU : ∀ e ∈ configU f d K m' β' α, rhoPrime f d K m' β' α (some e) =
      rho f (fun e => m' (some e)) (fun e => β' (some e)) α e := fun e he => by
    rw [hmed e, med_eq_left (hle e) ((hU e).1 he).le]
  have honWU : ∀ e ∈ configW f d K m' β' α \ configU f d K m' β' α,
      rhoPrime f d K m' β' α (some e) = θb := fun e he => by
    rw [mem_sdiff] at he
    rw [hmed e, med_eq_mid (not_lt.1 fun h => he.2 ((hU e).2 h)) ((hW e).1 he.1)]
  have honW : ∀ e ∉ configW f d K m' β' α, rhoPrime f d K m' β' α (some e) =
      rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e := fun e he => by
    rw [hmed e, med_eq_right (hle e) (not_le.1 fun h => he ((hW e).2 h)).le]
  refine ⟨hUW, fun e he => ⟨honU e he, (hU e).1 he⟩, honWU,
    fun e he => ⟨honW e he, not_le.1 fun h => he ((hW e).2 h)⟩, ?_⟩
  -- so the block of `b`, the set of elements with the marginal `θ_b`, is `D = (W ∖ U) ∪ {b}`
  ext o
  rw [mem_filter, blockUW, mem_insertNone]
  rcases o with _ | e
  · constructor
    · intro _ a ha
      exact absurd ha (by simp)
    · intro _
      exact ⟨mem_univ _, rfl⟩
  · simp only [mem_univ, true_and, Option.mem_def, Option.some.injEq, forall_eq']
    constructor
    · intro h
      by_contra hn
      rw [mem_sdiff, not_and, not_not] at hn
      by_cases heW : e ∈ configW f d K m' β' α
      · have heU := hn heW
        rw [honU e heU] at h
        exact absurd h ((hU e).1 heU).ne'
      · rw [honW e heW] at h
        exact absurd h (not_le.1 fun h' => heW ((hW e).2 h')).ne
    · intro he
      exact honWU e he

/-! ### `lem:windows` -/

variable (f d K m' β')

/-- `X_{U,W} = K + h(W) − f(U)` of `lem:windows` (`appB-tools.tex:406`); at a weak configuration, it
is the mass `ξ'(D)` of `D` (`windows_mass_marginal`). -/
def bigX (U W : Finset E) : ℝ :=
  K + subMod f d W - f U

/-- `θ_{U,W} = (α t(D) − X_{U,W})/β⁻¹(D)` of `lem:windows` (`appB-tools.tex:406`), for
`D = (W ∖ U) ∪ {b}`; at a weak configuration, it is `θ_b`, the common marginal of the elements of
`D` (`windows_mass_marginal`). -/
def thetaUW (α : ℝ) (U W : Finset E) : ℝ :=
  (α * ∑ o ∈ blockUW U W, m' o / β' o - bigX f d K U W) / ∑ o ∈ blockUW U W, 1 / β' o

/-- `(U, W)` is a weak configuration at `α` (`lem:windows`, `appB-tools.tex:408`): at `α`,
`ρ^f_e ≥ θ_b` for `e ∈ U`, `ρ^f_e ≤ θ_b ≤ ρ^h_e` for `e ∈ W ∖ U` and `ρ^h_e ≤ θ_b` for `e ∈ E ∖ W`,
and `U` is tight for `ξ^f(α)` and `W` is tight for `ξ^h(α)`. -/
def IsWeakConfig (α : ℝ) (U W : Finset E) : Prop :=
  (∀ e ∈ U, thetaB f d K m' β' α ≤ rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
    (∀ e ∈ W \ U, rho f (fun e => m' (some e)) (fun e => β' (some e)) α e ≤
        thetaB f d K m' β' α ∧
      thetaB f d K m' β' α ≤ rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
    (∀ e ∉ W, rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e ≤
      thetaB f d K m' β' α) ∧
    IsTight f (xi f (fun e => m' (some e)) (fun e => β' (some e)) α) U ∧
    IsTight (subMod f d) (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α) W

variable {f d K m' β'}

/-- `lem:windows`, before (a) (`appB-tools.tex:409`): the last two conditions of a weak
configuration hold if `U` is an upper level set of `ρ^f(α)` and `W` one of `ρ^h(α)`, strict or not
(`lem:fullplane`(a)). (For `f` submodular with `f(∅) = 0`, `m, β > 0`, `d ≥ 0`; `m > 0` and
`d ≥ 0` are not used.) -/
theorem isWeakConfig_of_levelSets (hf : Submodular f) (hf0 : f ∅ = 0) (_hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (_hd : ∀ e, 0 ≤ d e) (α : ℝ) {U W : Finset E}
    (hU : ∃ θ, U = levelSet (fun e => m' (some e)) (fun e => β' (some e)) α
        (xi f (fun e => m' (some e)) (fun e => β' (some e)) α) θ ∨
      U = univ.filter fun e => θ < rho f (fun e => m' (some e)) (fun e => β' (some e)) α e)
    (hW : ∃ θ, W = levelSet (fun e => m' (some e)) (fun e => β' (some e)) α
        (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α) θ ∨
      W = univ.filter fun e => θ < rho (subMod f d) (fun e => m' (some e))
        (fun e => β' (some e)) α e) :
    IsTight f (xi f (fun e => m' (some e)) (fun e => β' (some e)) α) U ∧
      IsTight (subMod f d) (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α) W := by
  have H : FPHyp f fun e => β' (some e) := ⟨hf, hf0, fun e => hβ (some e)⟩
  -- (1) "The last two conditions hold if `U` is an upper level set of `ρ^f(α)` and `W` one of
  -- `ρ^h(α)`, strict or not (`lem:fullplane`(a))."
  obtain ⟨θ, hU | hU⟩ := hU <;> obtain ⟨θ', hW | hW⟩ := hW <;> rw [hU, hW] <;>
    first
    | exact ⟨xi_levelSet_tight H _ α θ, xi_levelSet_tight (H.subMod d) _ α θ'⟩
    | exact ⟨xi_levelSet_tight H _ α θ, xi_strictLevelSet_tight (H.subMod d) _ α θ'⟩
    | exact ⟨xi_strictLevelSet_tight H _ α θ, xi_levelSet_tight (H.subMod d) _ α θ'⟩
    | exact ⟨xi_strictLevelSet_tight H _ α θ, xi_strictLevelSet_tight (H.subMod d) _ α θ'⟩

/-- `lem:windows`, before (a) (`appB-tools.tex:410`): the configuration at `α` is a weak
configuration (for `f` submodular with `f(∅) = 0`, `m, β > 0` and `d ≥ 0`). -/
theorem isWeakConfig_config (hf : Submodular f) (hf0 : f ∅ = 0) (hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (hd : ∀ e, 0 ≤ d e) (α : ℝ) :
    IsWeakConfig f d K m' β' α (configU f d K m' β' α) (configW f d K m' β' α) := by
  -- (1) "In particular, the configuration at `α` is a weak configuration."
  -- Its inequalities are those of the paragraph "Configurations" (`config_spec`).
  obtain ⟨-, hU, -, hW, -⟩ := config_spec (K := K) hf hf0 hm hβ hd α
  -- Its tightness holds as `U` is a strict upper level set of `ρ^f(α)` and `W` an upper level set
  -- of `ρ^h(α)` (`isWeakConfig_of_levelSets`).
  have ht := isWeakConfig_of_levelSets hf hf0 hm hβ hd α (U := configU f d K m' β' α)
    (W := configW f d K m' β' α) ⟨thetaB f d K m' β' α, Or.inr rfl⟩
    ⟨thetaB f d K m' β' α, Or.inl (by
      ext e
      unfold configW levelSet
      rw [mem_filter, mem_filter]
      rfl)⟩
  refine ⟨fun e he => (hU e he).2.le, fun e he => ⟨?_, ?_⟩, fun e he => (hW e he).2.le, ht⟩
  · have he' := mem_sdiff.1 he
    exact not_lt.1 fun h => he'.2 (by simpa [configU] using h)
  · have he' := mem_sdiff.1 he
    simpa [configW] using he'.1

/-- `lem:windows`(a), the first steps of its proof (`appB-tools.tex:427-435`), auxiliary form
(under `FPHyp`, `d ≥ 0`, `β_b > 0`): if `(U, W)` is a weak configuration at `α`, `U ⊆ W` and
`D = (W ∖ U) ∪ {b}`, then `ξ'(α) = ξ^f(α)` on `U`, `ξ'(α) = ξ^h(α)` on `E ∖ W`, all elements of `D`
have the marginal `θ_b`, `ξ'(D) = X_{U,W}` and `θ_b = θ_{U,W}`. Steps: (1) by `thm:splice`(b),
`ρ'_e = med(ρ^f_e, θ_b, ρ^h_e)`, which by the inequalities of a weak configuration and `ρ^f ≤ ρ^h`
is `ρ^f_e` on `U`, `θ_b` on `W ∖ U` and `ρ^h_e` on `E ∖ W`; as `ξ_e = α t_e − ρ_e/β_e` for each of
`ξ'`, `ξ^f`, `ξ^h`, `ξ' = ξ^f` on `U` and `ξ' = ξ^h` on `E ∖ W`; (2) `E ∪ {b}` is tight for `ξ'`,
`U` for `ξ^f`, `W` and `E` for `ξ^h`, so
`ξ'(D) = f'(E ∪ {b}) − ξ^f(U) − ξ^h(E ∖ W) = K + h(E) − f(U) − h(E) + h(W) = X_{U,W}`; all elements
of `D` have the marginal `θ_b`, so `ξ'(D) = α t(D) − θ_b β⁻¹(D)`, which gives `θ_b = θ_{U,W}`. -/
theorem windows_a_block (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) {α : ℝ} {U W : Finset E} (hUW : U ⊆ W)
    (hconf : IsWeakConfig f d K m' β' α U W) :
    (∀ e ∈ U, xiPrime f d K m' β' α (some e) =
        xi f (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      (∀ e ∉ W, xiPrime f d K m' β' α (some e) =
        xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      (∀ o ∈ blockUW U W, rhoPrime f d K m' β' α o = thetaB f d K m' β' α) ∧
      ∑ o ∈ blockUW U W, xiPrime f d K m' β' α o = bigX f d K U W ∧
      thetaB f d K m' β' α = thetaUW f d K m' β' α U W := by
  obtain ⟨hU, hWU, hW, htU, htW⟩ := hconf
  set m : E → ℝ := fun e => m' (some e)
  set β : E → ℝ := fun e => β' (some e)
  set θb := thetaB f d K m' β' α
  set ξf := xi f m β α
  set ξh := xi (subMod f d) m β α
  set ξ' := xiPrime f d K m' β' α
  set D := blockUW U W
  have H' := H.extend hd hb K
  have hβ' := H'.pos
  -- (1) "By `thm:splice`(b), `ρ'_e = med(ρ^f_e, θ_b, ρ^h_e)`. By the inequalities of a weak
  -- configuration and as `ρ^f ≤ ρ^h`, this is `ρ^f_e` for `e ∈ U`, `θ_b` for `e ∈ W ∖ U` and
  -- `ρ^h_e` for `e ∈ E ∖ W`."
  obtain ⟨⟨hle, -⟩, hmed, -⟩ := splice_aux (K := K) H hd hb α
  have hρU : ∀ e ∈ U, rhoPrime f d K m' β' α (some e) = rho f m β α e := fun e he => by
    rw [hmed e, med_eq_left (hle e) (hU e he)]
  have hρWU : ∀ e ∈ W \ U, rhoPrime f d K m' β' α (some e) = θb := fun e he => by
    rw [hmed e, med_eq_mid (hWU e he).1 (hWU e he).2]
  have hρW : ∀ e ∉ W, rhoPrime f d K m' β' α (some e) = rho (subMod f d) m β α e :=
    fun e he => by rw [hmed e, med_eq_right (hle e) (hW e he)]
  -- "As `ξ_e = α t_e − ρ_e/β_e` for each of the three best responses `ξ'`, `ξ^f`, `ξ^h` and their
  -- marginals, `ξ' = ξ^f` on `U` and `ξ' = ξ^h` on `E ∖ W`."
  have hξ' : ∀ o, ξ' o = (α * m' o - rhoPrime f d K m' β' α o) / β' o := fun o => xi_eq H' o
  have hξf : ∀ e, ξf e = (α * m e - rho f m β α e) / β e := fun e => xi_eq H e
  have hξh : ∀ e, ξh e = (α * m e - rho (subMod f d) m β α e) / β e :=
    fun e => xi_eq (H.subMod d) e
  have hξU : ∀ e ∈ U, ξ' (some e) = ξf e := fun e he => by
    rw [hξ' (some e), hρU e he, hξf e]
  have hξW : ∀ e ∉ W, ξ' (some e) = ξh e := fun e he => by
    rw [hξ' (some e), hρW e he, hξh e]
  -- (2) "The set `E ∪ {b}` is tight for `ξ'`, `U` is tight for `ξ^f`, and `W` and `E` are tight
  -- for `ξ^h`, so `ξ'(D) = f'(E ∪ {b}) − ξ^f(U) − ξ^h(E ∖ W)`
  -- `= K + h(E) − f(U) − h(E) + h(W) = X_{U,W}`."
  have hsplit : ∀ y : E → ℝ, ∑ e, y e = ∑ e ∈ U, y e + ∑ e ∈ W \ U, y e + ∑ e ∈ Wᶜ, y e := by
    intro y
    rw [← sum_add_sum_compl W, ← sum_sdiff hUW]
    ring
  have hsumD : ∀ y : Option E → ℝ, ∑ o ∈ D, y o = y none + ∑ e ∈ W \ U, y (some e) :=
    fun y => sum_insertNone y (W \ U)
  have hXD : ∑ o ∈ D, ξ' o = bigX f d K U W := by
    have htot : ∑ o, ξ' o = extend f d K univ := (xi_mem_fpBase H' m' α).2
    rw [Fintype.sum_option] at htot
    simp only [extend, mem_univ, ↓reduceIte, eraseNone_univ', Hardness.subMod] at htot
    rw [hsplit fun e => ξ' (some e), sum_congr rfl hξU,
      sum_congr rfl fun e he => hξW e (mem_compl.1 he)] at htot
    have hfU : ∑ e ∈ U, ξf e = f U := htU
    have hhW := htW
    unfold IsTight Hardness.subMod at hhW
    have hhE := (xi_mem_fpBase (H.subMod d) m α).2
    simp only [Hardness.subMod] at hhE
    have hcompl := sum_add_sum_compl W ξh
    rw [hsumD]
    unfold bigX Hardness.subMod
    linarith
  -- "All elements of `D` have the marginal `θ_b`, so `ξ'(D) = α t(D) − θ_b β⁻¹(D)`, …"
  have hρD : ∀ o ∈ D, rhoPrime f d K m' β' α o = θb := by
    intro o ho
    cases o with
    | none => rfl
    | some e => exact hρWU e (by simpa [D, blockUW, mem_insertNone] using ho)
  have hD : ∑ o ∈ D, ξ' o = α * ∑ o ∈ D, m' o / β' o - θb * ∑ o ∈ D, 1 / β' o := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun o ho => ?_
    rw [hξ' o, hρD o ho]
    have := (hβ' o).ne'
    field_simp
  -- "… which gives `θ_b = θ_{U,W}`."
  have hDpos : 0 < ∑ o ∈ D, 1 / β' o :=
    sum_pos (fun o _ => one_div_pos.2 (hβ' o)) ⟨none, by simp [D, blockUW, mem_insertNone]⟩
  have hθ : θb = thetaUW f d K m' β' α U W := by
    unfold thetaUW
    rw [eq_div_iff hDpos.ne']
    linarith
  exact ⟨hξU, hξW, hρD, hXD, hθ⟩

/-- **`lem:windows`, before (a), its third claim** (`appB-tools.tex:411`): in the setting of
`thm:splice` (`f` submodular with `f(∅) = 0`, `m, β > 0`, `d ≥ 0`, `K`, `b` with
`m_b, β_b > 0`), for `α ∈ ℝ`, `U ⊆ W ⊆ E` and `D = (W ∖ U) ∪ {b}`: at a weak configuration,
`X_{U,W} = ξ'(D)` is the mass of `D` and `θ_{U,W} = θ_b` is the common marginal of its elements,
by (a) (the steps of its proof that show this, `windows_a_block`), and for the configuration, `D`
is the block of `b`, the set of elements of `E ∪ {b}` with the marginal `θ_b` (the paragraph
"Configurations", `config_spec`). -/
theorem windows_mass_marginal (hf : Submodular f) (hf0 : f ∅ = 0) (hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (hd : ∀ e, 0 ≤ d e) {α : ℝ} {U W : Finset E} (hUW : U ⊆ W) :
    (IsWeakConfig f d K m' β' α U W →
      bigX f d K U W = ∑ o ∈ blockUW U W, xiPrime f d K m' β' α o ∧
        thetaUW f d K m' β' α U W = thetaB f d K m' β' α ∧
        ∀ o ∈ blockUW U W, rhoPrime f d K m' β' α o = thetaB f d K m' β' α) ∧
    (U = configU f d K m' β' α → W = configW f d K m' β' α →
      univ.filter (fun o => rhoPrime f d K m' β' α o = thetaB f d K m' β' α) = blockUW U W) := by
  have H : FPHyp f fun e => β' (some e) := ⟨hf, hf0, fun e => hβ (some e)⟩
  refine ⟨fun hconf => ?_, fun hU hW => ?_⟩
  · -- (1) "At a weak configuration, `X_{U,W} = ξ'(D)` is the mass of `D` and `θ_{U,W} = θ_b` is
    -- the common marginal of its elements, by (a), …" (`windows_a_block`)
    obtain ⟨-, -, hρD, hXD, hθ⟩ := windows_a_block H hd (hβ none) hUW hconf
    exact ⟨hXD.symm, hθ.symm, hρD⟩
  · -- (2) "… and for the configuration, `D` is the block of `b`."
    -- This is the paragraph "Configurations" (`config_spec`).
    subst hU hW
    exact (config_spec hf hf0 hm hβ hd α).2.2.2.2

/-- `lem:windows`(a), auxiliary form (`appB-tools.tex:427-436`, under `FPHyp`, `d ≥ 0`, `β_b > 0`):
if `(U, W)` is a weak configuration at `α`, `U ⊆ W`, then `θ_b(α) = θ_{U,W}`, `ξ'(α) = ξ^f(α)` on
`U`, `ξ'(α) = ξ^h(α)` on `E ∖ W`, and (`eq:windows`)
`r(ξ'(α)) = ∑_{e∈U} m_e ξ^f_e + ∑_{e∈E∖W} m_e ξ^h_e + α SS(D) + X_{U,W} m̄_D`. Steps: (1), (2) of
`windows_a_block`: by `thm:splice`(b) and the inequalities of a weak configuration, `ξ' = ξ^f` on
`U` and `ξ' = ξ^h` on `E ∖ W`; by the tightness of `E ∪ {b}`, `U`, `W` and `E`, `ξ'(D) = X_{U,W}`,
and as all elements of `D` have the marginal `θ_b`, `θ_b = θ_{U,W}`; (3) by `lem:fullplane`(e),
`∑_{e∈D} m_e ξ'_e = α SS(D) + X_{U,W} m̄_D`, and adding the sums of `m_e ξ'_e` over `U` and over
`E ∖ W` gives (`eq:windows`). -/
theorem windows_a_aux (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) {α : ℝ} {U W : Finset E} (hUW : U ⊆ W)
    (hconf : IsWeakConfig f d K m' β' α U W) :
    thetaB f d K m' β' α = thetaUW f d K m' β' α U W ∧
      (∀ e ∈ U, xiPrime f d K m' β' α (some e) =
        xi f (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      (∀ e ∉ W, xiPrime f d K m' β' α (some e) =
        xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      reward m' (xiPrime f d K m' β' α) =
        ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) α e +
        ∑ e ∈ Wᶜ, m' (some e) * xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e +
        α * SS m' β' (blockUW U W) + bigX f d K U W * mbar m' β' (blockUW U W) := by
  -- (1), (2) "By `thm:splice`(b), `ρ'_e = med(ρ^f_e, θ_b, ρ^h_e)`. … All elements of `D` have the
  -- marginal `θ_b`, so `ξ'(D) = α t(D) − θ_b β⁻¹(D)`, which gives `θ_b = θ_{U,W}`."
  -- These sentences (`appB-tools.tex:427-435`) are `windows_a_block`.
  obtain ⟨hξU, hξW, hρD, hXD, hθ⟩ := windows_a_block H hd hb hUW hconf
  refine ⟨hθ, hξU, hξW, ?_⟩
  set m : E → ℝ := fun e => m' (some e)
  set β : E → ℝ := fun e => β' (some e)
  set ξf := xi f m β α
  set ξh := xi (subMod f d) m β α
  set ξ' := xiPrime f d K m' β' α
  set D := blockUW U W
  have hβ' := (H.extend hd hb K).pos
  -- (3) "By `lem:fullplane`(e), `∑_{e∈D} m_e ξ'_e = α SS(D) + X_{U,W} m̄_D`, and adding the sums
  -- of `m_e ξ'_e` over `U` and over `E ∖ W` gives (`eq:windows`)."
  have hsplit : ∀ y : E → ℝ, ∑ e, y e = ∑ e ∈ U, y e + ∑ e ∈ W \ U, y e + ∑ e ∈ Wᶜ, y e := by
    intro y
    rw [← sum_add_sum_compl W, ← sum_sdiff hUW]
    ring
  have hsumD : ∀ y : Option E → ℝ, ∑ o ∈ D, y o = y none + ∑ e ∈ W \ U, y (some e) :=
    fun y => sum_insertNone y (W \ U)
  have he : ∑ o ∈ D, m' o * ξ' o = α * SS m' β' D + (∑ o ∈ D, ξ' o) * mbar m' β' D :=
    sum_mul_xi_of_rho_eq (g := extend f d K) (m := m') hβ' α
      ⟨none, by simp [D, blockUW, mem_insertNone]⟩
      fun o ho o' ho' => (hρD o ho).trans (hρD o' ho').symm
  rw [hXD, hsumD] at he
  have hreward : reward m' ξ' = m' none * ξ' none + ∑ e, m' (some e) * ξ' (some e) := by
    simp only [reward, Fintype.sum_option]
  have s1 : ∑ e ∈ U, m' (some e) * ξ' (some e) = ∑ e ∈ U, m' (some e) * ξf e :=
    sum_congr rfl fun e he => by rw [hξU e he]
  have s2 : ∑ e ∈ Wᶜ, m' (some e) * ξ' (some e) = ∑ e ∈ Wᶜ, m' (some e) * ξh e :=
    sum_congr rfl fun e he => by rw [hξW e (mem_compl.1 he)]
  rw [hreward, hsplit fun e => m' (some e) * ξ' (some e), s1, s2]
  linarith

/-- **`lem:windows`(a)** (Lemma B.13, `appB-tools.tex:413-416`, proof `appB-tools.tex:427-436`): in
the setting of `thm:splice` (`f` submodular with `f(∅) = 0`, `m, β > 0`, `d ≥ 0`, `K`, `b` with
`m_b, β_b > 0`), for `α ∈ ℝ`, `U ⊆ W ⊆ E` and `D = (W ∖ U) ∪ {b}`: if `(U, W)` is a weak
configuration at `α`, then `θ_b(α) = θ_{U,W}`, `ξ'(α) = ξ^f(α)` on `U`, `ξ'(α) = ξ^h(α)` on
`E ∖ W`, and (`eq:windows`)
`r(ξ^{f'}(α)) = ∑_{e∈U} m_e ξ^f_e(α) + ∑_{e∈E∖W} m_e ξ^h_e(α) + α SS(D) + X_{U,W} m̄_D`. Steps (in
`windows_a_block` and `windows_a_aux`): (1) by `thm:splice`(b) and the inequalities of a weak
configuration, `ρ' = ρ^f` on `U`, `θ_b` on `W ∖ U` and `ρ^h` on `E ∖ W`, and as
`ξ_e = α t_e − ρ_e/β_e`, `ξ' = ξ^f` on `U` and `ξ' = ξ^h` on `E ∖ W`; (2) by the tightness of
`E ∪ {b}`, `U`, `W` and `E`, `ξ'(D) = X_{U,W}`, and as all elements of `D` have the marginal `θ_b`,
`θ_b = θ_{U,W}`; (3) by `lem:fullplane`(e), `∑_{e∈D} m_e ξ'_e = α SS(D) + X_{U,W} m̄_D`, which with
the sums over `U` and over `E ∖ W` gives (`eq:windows`). The hypothesis `m > 0` is not used. -/
theorem windows_a (hf : Submodular f) (hf0 : f ∅ = 0) (_hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (hd : ∀ e, 0 ≤ d e) {α : ℝ} {U W : Finset E} (hUW : U ⊆ W)
    (hconf : IsWeakConfig f d K m' β' α U W) :
    thetaB f d K m' β' α = thetaUW f d K m' β' α U W ∧
      (∀ e ∈ U, xiPrime f d K m' β' α (some e) =
        xi f (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      (∀ e ∉ W, xiPrime f d K m' β' α (some e) =
        xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      reward m' (xiPrime f d K m' β' α) =
        ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) α e +
        ∑ e ∈ Wᶜ, m' (some e) * xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e +
        α * SS m' β' (blockUW U W) + bigX f d K U W * mbar m' β' (blockUW U W) :=
  windows_a_aux ⟨hf, hf0, fun e => hβ (some e)⟩ hd (hβ none) hUW hconf

/-- `lem:windows`(b), auxiliary form (`appB-tools.tex:438-447`, under `FPHyp`, `d ≥ 0`, `β_b > 0`):
for `U ⊆ W ⊆ E` (the standing assumption of `lem:windows`, `appB-tools.tex:404`) and
`θ = θ_{U,W}`, if `U = {ρ^f > θ}` and `W = {ρ^h ≥ θ}`, then `θ` solves (`eq:splice`), so
`θ_b = θ` by the uniqueness in `thm:splice`(c). Steps: (1) the clamp of `e` in `Y(θ)` is `0` for
`e ∈ U`, `θ − ρ^f_e` for `e ∈ W ∖ U` and `ρ^h_e − ρ^f_e` for `e ∈ E ∖ W`; with
`ρ^f_e/β_e = α t_e − ξ^f_e`,
`ρ^h_e/β_e = α t_e − ξ^h_e` and `(W ∖ U) ∪ (E ∖ W) = E ∖ U`,
`Y(θ) = θ β⁻¹(W ∖ U) − α t(W ∖ U) + ξ^f(E ∖ U) − ξ^h(E ∖ W)`; (2) `E`, `U` and `W` are upper level
sets, so `ξ^f(E ∖ U) = f(E) − f(U)` and `ξ^h(E ∖ W) = h(E) − h(W)` by `lem:fullplane`(a), and
`f(E) − h(E) = d(E)`; hence `K − d(E) + Y(θ) = X_{U,W} + θ β⁻¹(W ∖ U) − α t(W ∖ U)`; (3) the
left-hand side of (`eq:splice`) is `α t_b − θ/β_b`, so (`eq:splice`) becomes
`α t(D) − θ β⁻¹(D) = X_{U,W}`, the definition of `θ_{U,W}`; (4) so `θ_b = θ` by the uniqueness in
`thm:splice`(c). -/
theorem windows_b_aux (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) {α : ℝ} {U W : Finset E} (hUW : U ⊆ W)
    (hU : ∀ e, e ∈ U ↔ thetaUW f d K m' β' α U W <
      rho f (fun e => m' (some e)) (fun e => β' (some e)) α e)
    (hW : ∀ e, e ∈ W ↔ thetaUW f d K m' β' α U W ≤
      rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) :
    thetaB f d K m' β' α = thetaUW f d K m' β' α U W := by
  set θ := thetaUW f d K m' β' α U W with hθdef
  set m : E → ℝ := fun e => m' (some e)
  set β : E → ℝ := fun e => β' (some e)
  set ξf := xi f m β α
  set ξh := xi (subMod f d) m β α
  set ρf := rho f m β α
  set ρh := rho (subMod f d) m β α
  have hβ := H.pos
  have hle : ∀ e, ρf e ≤ ρh e := rho_le_rho_subMod H hd α
  -- (1) "We show that `θ := θ_{U,W}` solves (`eq:splice`). … By the hypotheses, the clamp of `e`
  -- in `Y(θ)` is `0` for `e ∈ U`, `θ − ρ^f_e` for `e ∈ W ∖ U` and `ρ^h_e − ρ^f_e` for `e ∈ E ∖ W`.
  -- With `ρ^f_e/β_e = α t_e − ξ^f_e` and `ρ^h_e/β_e = α t_e − ξ^h_e`, …"
  -- The omitted sentence (`appB-tools.tex:439`) is step (4), which the Lean takes last.
  have hc : ∀ e, clampTerm (ρf e) (ρh e) θ / β e =
      if e ∈ U then 0 else if e ∈ W then θ / β e - α * (m e / β e) + ξf e else ξf e - ξh e := by
    intro e
    have := (hβ e).ne'
    by_cases heU : e ∈ U
    · rw [ite_eq_left heU, clampTerm_eq_zero (hle e) ((hU e).1 heU).le, zero_div]
    · rw [ite_eq_right heU]
      have h1 : ρf e ≤ θ := not_lt.1 fun h => heU ((hU e).2 h)
      by_cases heW : e ∈ W
      · rw [ite_eq_left heW, clampTerm_eq_mid h1 ((hW e).1 heW)]
        simp only [ξf, ρf, rho, marg]
        field_simp
        ring
      · rw [ite_eq_right heW, clampTerm_eq_sub (not_le.1 fun h => heW ((hW e).2 h)).le (hle e)]
        simp only [ξf, ξh, ρf, ρh, rho, marg]
        field_simp
        ring
  -- "… and as `(W ∖ U) ∪ (E ∖ W) = E ∖ U`, this gives
  -- `Y(θ) = θ β⁻¹(W ∖ U) − α t(W ∖ U) + ξ^f(E ∖ U) − ξ^h(E ∖ W)`."
  have hY : bigY f d m' β' α θ = θ * ∑ e ∈ W \ U, 1 / β e - α * ∑ e ∈ W \ U, m e / β e +
      ∑ e ∈ Uᶜ, ξf e - ∑ e ∈ Wᶜ, ξh e := by
    unfold bigY
    rw [sum_congr rfl fun e _ => hc e]
    rw [← sum_add_sum_compl W, ← sum_sdiff hUW]
    have h1 : ∑ e ∈ U, (if e ∈ U then (0 : ℝ) else if e ∈ W then θ / β e - α * (m e / β e) + ξf e
        else ξf e - ξh e) = 0 := sum_eq_zero fun e he => by rw [ite_eq_left he]
    have h2 : ∑ e ∈ W \ U, (if e ∈ U then (0 : ℝ) else if e ∈ W then θ / β e - α * (m e / β e) +
        ξf e else ξf e - ξh e) = ∑ e ∈ W \ U, (θ / β e - α * (m e / β e) + ξf e) :=
      sum_congr rfl fun e he => by
        rw [ite_eq_right (mem_sdiff.1 he).2, ite_eq_left (mem_sdiff.1 he).1]
    have h3 : ∑ e ∈ Wᶜ, (if e ∈ U then (0 : ℝ) else if e ∈ W then θ / β e - α * (m e / β e) +
        ξf e else ξf e - ξh e) = ∑ e ∈ Wᶜ, (ξf e - ξh e) := by
      refine sum_congr rfl fun e he => ?_
      have heW := mem_compl.1 he
      rw [ite_eq_right fun h => heW (hUW h), ite_eq_right heW]
    rw [h1, h2, h3]
    have hUc : ∑ e ∈ Uᶜ, ξf e = ∑ e ∈ W \ U, ξf e + ∑ e ∈ Wᶜ, ξf e := by
      have h4 := sum_add_sum_compl U ξf
      have h5 := sum_add_sum_compl W ξf
      have h6 := sum_sdiff hUW (f := ξf)
      linarith
    rw [hUc, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, mul_sum, mul_sum]
    have : ∀ e ∈ W \ U, θ / β e = θ * (1 / β e) := fun e _ => by ring
    rw [sum_congr rfl this]
    ring
  -- (2) "The sets `E`, `U = {e ∈ E : ρ^f_e > θ}` and `W = {e ∈ E : ρ^h_e ≥ θ}` are upper level
  -- sets, so `ξ^f(E ∖ U) = f(E) − f(U)` and `ξ^h(E ∖ W) = h(E) − h(W)` by `lem:fullplane`(a), …"
  have htU : ∑ e ∈ U, ξf e = f U := by
    have h := xi_strictLevelSet_tight H m α θ
    have hU' : U = univ.filter fun e => θ < rho f m β α e := by
      ext e
      simp [hU e, ρf]
    rw [hU']
    exact h
  have htW : ∑ e ∈ W, ξh e = subMod f d W := by
    have h := xi_levelSet_tight (H.subMod d) m α θ
    have hW' : W = levelSet m β α ξh θ := by
      ext e
      simp only [levelSet, mem_filter, mem_univ, true_and, hW e]
      rfl
    rw [hW']
    exact h
  have hfU : ∑ e ∈ Uᶜ, ξf e = f univ - f U := by
    have h1 := (xi_mem_fpBase H m α).2
    have h2 := sum_add_sum_compl U ξf
    linarith
  have hhW : ∑ e ∈ Wᶜ, ξh e = subMod f d univ - subMod f d W := by
    have h1 := (xi_mem_fpBase (H.subMod d) m α).2
    have h2 := sum_add_sum_compl W ξh
    linarith
  -- "… and `f(E) − h(E) = d(E)`. Hence `K − d(E) + Y(θ) = X_{U,W} + θ β⁻¹(W ∖ U) − α t(W ∖ U)`."
  have hfh : f univ - subMod f d univ = ∑ e, d e := by
    simp only [Hardness.subMod]
    ring
  have hKY : K - ∑ e, d e + bigY f d m' β' α θ =
      bigX f d K U W + θ * ∑ e ∈ W \ U, 1 / β e - α * ∑ e ∈ W \ U, m e / β e := by
    rw [hY, hfU, hhW]
    unfold bigX
    linarith
  -- (3) "The left-hand side of (`eq:splice`) is `α t_b − θ/β_b`, so (`eq:splice`) becomes
  -- `α t(D) − θ β⁻¹(D) = X_{U,W}`, which is the definition of `θ_{U,W}`."
  have hθF1 : IsF1 f d K m' β' α θ := by
    have hβ' := (H.extend hd hb K).pos
    have hDpos : 0 < ∑ o ∈ blockUW U W, 1 / β' o :=
      sum_pos (fun o _ => one_div_pos.2 (hβ' o)) ⟨none, by simp [blockUW, mem_insertNone]⟩
    have hθD : θ * ∑ o ∈ blockUW U W, 1 / β' o =
        α * ∑ o ∈ blockUW U W, m' o / β' o - bigX f d K U W := by
      rw [hθdef, thetaUW, div_mul_cancel₀ _ hDpos.ne']
    rw [blockUW, sum_insertNone, sum_insertNone] at hθD
    have := hb.ne'
    have e1 : (α * m' none - θ) / β' none = α * (m' none / β' none) - θ * (1 / β' none) := by
      field_simp
    unfold IsF1
    rw [hKY, e1]
    simp only [m, β] at hθD ⊢
    linarith
  -- (4) "Then `θ_b = θ` by the uniqueness in `thm:splice`(c), …"
  -- The paper says this right after the first sentence of step (1); the Lean applies it last.
  exact ((splice_aux (K := K) H hd hb α).2.2.1.2 θ hθF1).symm

/-- **`lem:windows`(b)** (`appB-tools.tex:417`, proof `appB-tools.tex:438-447`): in the setting of
`thm:splice` (`f` submodular with `f(∅) = 0`, `m, β > 0`, `d ≥ 0`, `K`, `b` with `m_b, β_b > 0`),
for `α ∈ ℝ` and `U ⊆ W ⊆ E`: if `ρ^f_e(α) > θ_{U,W}` for `e ∈ U`, `ρ^f_e(α) ≤ θ_{U,W}` for
`e ∈ E ∖ U`, `ρ^h_e(α) ≥ θ_{U,W}` for `e ∈ W` and `ρ^h_e(α) < θ_{U,W}` for `e ∈ E ∖ W`, then
`(U, W)` is the configuration at `α`. Steps: (1)–(3) `θ = θ_{U,W}` solves (`eq:splice`): the
clamps of `Y(θ)`, the tight sets `E`, `U`, `W` (`lem:fullplane`(a)), and the left-hand side
`α t_b − θ/β_b` (`windows_b_aux`); (4) so `θ_b = θ` by the uniqueness in `thm:splice`(c), and the
hypotheses say that `U = {e : ρ^f_e > θ_b}` and `W = {e : ρ^h_e ≥ θ_b}`. The hypothesis `m > 0` is
not used. -/
theorem windows_b (hf : Submodular f) (hf0 : f ∅ = 0) (_hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (hd : ∀ e, 0 ≤ d e) {α : ℝ} {U W : Finset E} (hUW : U ⊆ W)
    (hU : ∀ e ∈ U, thetaUW f d K m' β' α U W <
      rho f (fun e => m' (some e)) (fun e => β' (some e)) α e)
    (hUc : ∀ e ∉ U, rho f (fun e => m' (some e)) (fun e => β' (some e)) α e ≤
      thetaUW f d K m' β' α U W)
    (hW : ∀ e ∈ W, thetaUW f d K m' β' α U W ≤
      rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e)
    (hWc : ∀ e ∉ W, rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e <
      thetaUW f d K m' β' α U W) :
    U = configU f d K m' β' α ∧ W = configW f d K m' β' α := by
  -- The hypotheses in the form `U = {e ∈ E : ρ^f_e > θ_{U,W}}` and `W = {e ∈ E : ρ^h_e ≥ θ_{U,W}}`,
  -- which `windows_b_aux` takes.
  have hU' : ∀ e, e ∈ U ↔ thetaUW f d K m' β' α U W <
      rho f (fun e => m' (some e)) (fun e => β' (some e)) α e :=
    fun e => ⟨hU e, fun h => by_contra fun he => absurd (hUc e he) (not_le.2 h)⟩
  have hW' : ∀ e, e ∈ W ↔ thetaUW f d K m' β' α U W ≤
      rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e :=
    fun e => ⟨hW e, fun h => by_contra fun he => absurd (hWc e he) (not_lt.2 h)⟩
  -- (1)–(4) "We show that `θ := θ_{U,W}` solves (`eq:splice`). Then `θ_b = θ` by the uniqueness in
  -- `thm:splice`(c), …" (`windows_b_aux`)
  have hθb := windows_b_aux (K := K) ⟨hf, hf0, fun e => hβ (some e)⟩ hd (hβ none) hUW hU' hW'
  -- "… and the hypotheses say that `U = {e ∈ E : ρ^f_e > θ_b}` and `W = {e ∈ E : ρ^h_e ≥ θ_b}`."
  constructor
  · ext e
    simp only [configU, mem_filter, mem_univ, true_and, hθb]
    exact hU' e
  · ext e
    simp only [configW, mem_filter, mem_univ, true_and, hθb]
    exact hW' e

/-- `lem:windows`(c), auxiliary form (`appB-tools.tex:449-455`): if `(U, W)` is a weak
configuration at `a` and at `a' ≥ a`, then
`r(ξ'(a')) − r(ξ'(a)) = [∑_{e∈U} m_e ξ^f_e]_a^{a'} + [∑_{e∈E∖W} m_e ξ^h_e]_a^{a'} + (a' − a) SS(D)`,
the first bracket in `[0, r(ξ^f(a')) − r(ξ^f(a))]` and the second in
`[0, r(ξ^h(a')) − r(ξ^h(a))]`. Steps: (1) subtract (`eq:windows`) at `a` from (`eq:windows`) at
`a'`; `X_{U,W}` and `m̄_D` do not depend on the share; (2) `U` is tight for `ξ^f(a)` and `ξ^f(a')`,
so by `lem:fullplane`(d) the sums over `U` and over `E ∖ U` both grow, and their increments add up
to `r(ξ^f(a')) − r(ξ^f(a))`; (3) likewise for `W`, `ξ^h` and the complement `E ∖ W`. -/
theorem windows_c_aux (H : FPHyp f fun e => β' (some e)) (hd : ∀ e, 0 ≤ d e)
    (hb : 0 < β' none) {U W : Finset E} (hUW : U ⊆ W) {a a' : ℝ} (haa : a ≤ a')
    (ha : IsWeakConfig f d K m' β' a U W) (ha' : IsWeakConfig f d K m' β' a' U W) :
    reward m' (xiPrime f d K m' β' a') - reward m' (xiPrime f d K m' β' a) =
        (∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e) +
        (∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e) +
        (a' - a) * SS m' β' (blockUW U W) ∧
      (0 ≤ ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e ∧
        ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e ≤
        reward (fun e => m' (some e)) (xi f (fun e => m' (some e)) (fun e => β' (some e)) a') -
          reward (fun e => m' (some e)) (xi f (fun e => m' (some e)) (fun e => β' (some e)) a)) ∧
      (0 ≤ ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e ∧
        ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e ≤
        reward (fun e => m' (some e))
            (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a') -
          reward (fun e => m' (some e))
            (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a)) := by
  set m : E → ℝ := fun e => m' (some e)
  set β : E → ℝ := fun e => β' (some e)
  -- (1) "Subtract (`eq:windows`) at `a` from (`eq:windows`) at `a'`. The numbers `X_{U,W}` and
  -- `m̄_D` do not depend on the share, so the last two terms give `(a' − a) SS(D)`."
  have hra := (windows_a_aux H hd hb hUW ha).2.2.2
  have hra' := (windows_a_aux H hd hb hUW ha').2.2.2
  refine ⟨by rw [hra, hra']; ring, ?_, ?_⟩
  · -- (2) "By the definition of a weak configuration at `a` and at `a'`, the set `U` is tight for
    -- `ξ^f(a)` and for `ξ^f(a')`. So, by `lem:fullplane`(d), the sums `∑_{e∈U} m_e ξ^f_e` and
    -- `∑_{e∈E∖U} m_e ξ^f_e` are both at least as large at `a'` as at `a`. Their increments add up
    -- to `r(ξ^f(a')) − r(ξ^f(a))`, so the first bracket lies in `[0, r(ξ^f(a')) − r(ξ^f(a))]`."
    have h1 := sum_mul_xi_mono (m := m) H haa ha.2.2.2.1 ha'.2.2.2.1
    have e1 := sum_add_sum_compl U fun e => m e * xi f m β a e
    have e2 := sum_add_sum_compl U fun e => m e * xi f m β a' e
    refine ⟨by linarith [h1.1], ?_⟩
    simp only [reward]
    linarith [h1.2]
  · -- (3) "Likewise, the set `W` is tight for `ξ^h(a)` and for `ξ^h(a')`, so, by
    -- `lem:fullplane`(d), the sums `∑_{e∈W} m_e ξ^h_e` and `∑_{e∈E∖W} m_e ξ^h_e` are both at least
    -- as large at `a'` as at `a`. The second bracket is the increment of the sum over the
    -- complement `E ∖ W`, so it lies in `[0, r(ξ^h(a')) − r(ξ^h(a))]`."
    have h3 := sum_mul_xi_mono (m := m) (H.subMod d) haa ha.2.2.2.2 ha'.2.2.2.2
    have e1 := sum_add_sum_compl W fun e => m e * xi (subMod f d) m β a e
    have e2 := sum_add_sum_compl W fun e => m e * xi (subMod f d) m β a' e
    refine ⟨by linarith [h3.2], ?_⟩
    simp only [reward]
    linarith [h3.1]

/-- **`lem:windows`(c)** (`appB-tools.tex:418-422`, proof `appB-tools.tex:449-455`): in the setting
of `thm:splice` (`f` submodular with `f(∅) = 0`, `m, β > 0`, `d ≥ 0`, `K`, `b` with
`m_b, β_b > 0`), for `U ⊆ W ⊆ E` and `D = (W ∖ U) ∪ {b}`: if `(U, W)` is a weak configuration at `a`
and at `a' ≥ a`, then
`r(ξ^{f'}(a')) − r(ξ^{f'}(a))`
`= [∑_{e∈U} m_e ξ^f_e]_a^{a'} + [∑_{e∈E∖W} m_e ξ^h_e]_a^{a'} + (a' − a) SS(D)`,
where the first bracket lies in `[0, r(ξ^f(a')) − r(ξ^f(a))]` and the second in
`[0, r(ξ^h(a')) − r(ξ^h(a))]`. Steps (in `windows_c_aux`): (1) subtract (`eq:windows`) at `a`
from (`eq:windows`) at `a'`; `X_{U,W}` and `m̄_D` do not depend on the share; (2) `U` is tight for
`ξ^f(a)` and `ξ^f(a')`, so by `lem:fullplane`(d) the sums over `U` and over `E ∖ U` both grow, and
their increments add up to `r(ξ^f(a')) − r(ξ^f(a))`; (3) likewise for `W` and `ξ^h`, with the
complement `E ∖ W`. The hypothesis `m > 0` is not used. -/
theorem windows_c (hf : Submodular f) (hf0 : f ∅ = 0) (_hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (hd : ∀ e, 0 ≤ d e) {U W : Finset E} (hUW : U ⊆ W) {a a' : ℝ}
    (haa : a ≤ a') (ha : IsWeakConfig f d K m' β' a U W)
    (ha' : IsWeakConfig f d K m' β' a' U W) :
    reward m' (xiPrime f d K m' β' a') - reward m' (xiPrime f d K m' β' a) =
        (∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e) +
        (∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e) +
        (a' - a) * SS m' β' (blockUW U W) ∧
      (0 ≤ ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e ∧
        ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e ≤
        reward (fun e => m' (some e)) (xi f (fun e => m' (some e)) (fun e => β' (some e)) a') -
          reward (fun e => m' (some e)) (xi f (fun e => m' (some e)) (fun e => β' (some e)) a)) ∧
      (0 ≤ ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e ∧
        ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
          ∑ e ∈ Wᶜ, m' (some e) *
            xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e ≤
        reward (fun e => m' (some e))
            (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a') -
          reward (fun e => m' (some e))
            (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a)) :=
  windows_c_aux ⟨hf, hf0, fun e => hβ (some e)⟩ hd (hβ none) hUW haa ha ha'

/-- **`lem:windows`** (Lemma B.13, `stoc-sections/appB-tools.tex:403-424`): in the setting
of `thm:splice` (`f` submodular with `f(∅) = 0`, `m, β > 0`, `d ≥ 0`, `K`, `b` with `m_b, β_b > 0`),
fix `α ∈ ℝ`, let `U ⊆ W ⊆ E` and `D := (W ∖ U) ∪ {b}` (`blockUW U W`), and let
`X_{U,W} := K + h(W) − f(U)` (`bigX`) and `θ_{U,W} := (α t(D) − X_{U,W})/β⁻¹(D)` (`thetaUW`). We
call `(U, W)` a weak configuration at `α` (`IsWeakConfig`) if, at `α`, `ρ^f_e ≥ θ_b` for `e ∈ U`,
`ρ^f_e ≤ θ_b ≤ ρ^h_e` for `e ∈ W ∖ U` and `ρ^h_e ≤ θ_b` for `e ∈ E ∖ W`, and if `U` is tight for
`ξ^f(α)` and `W` is tight for `ξ^h(α)`. The last two conditions hold if `U` is an upper level set of
`ρ^f(α)` and `W` one of `ρ^h(α)`, strict or not (`lem:fullplane`(a)). In particular, the
configuration at `α` is a weak configuration. At a weak configuration, `X_{U,W} = ξ'(D)` is the mass
of `D` and `θ_{U,W} = θ_b` is the common marginal of its elements, by (a), and for the
configuration, `D` is the block of `b`. (a) If `(U, W)` is a weak configuration at `α`, then
`θ_b(α) = θ_{U,W}`, `ξ'(α) = ξ^f(α)` on `U`, `ξ'(α) = ξ^h(α)` on `E ∖ W`, and (`eq:windows`)
`r(ξ^{f'}(α)) = ∑_{e∈U} m_e ξ^f_e(α) + ∑_{e∈E∖W} m_e ξ^h_e(α) + α SS(D) + X_{U,W} m̄_D`. (b)
Conversely, if `ρ^f_e(α) > θ_{U,W}` for `e ∈ U`, `ρ^f_e(α) ≤ θ_{U,W}` for `e ∈ E ∖ U`,
`ρ^h_e(α) ≥ θ_{U,W}` for `e ∈ W` and `ρ^h_e(α) < θ_{U,W}` for `e ∈ E ∖ W`, then `(U, W)` is the
configuration at `α`. (c) If `(U, W)` is a weak configuration at `a` and at `a' ≥ a`, then
`r(ξ^{f'}(a')) − r(ξ^{f'}(a))`
`= [∑_{e∈U} m_e ξ^f_e]_a^{a'} + [∑_{e∈E∖W} m_e ξ^h_e]_a^{a'} + (a' − a) SS(D)`, where the first
bracket lies in `[0, r(ξ^f(a')) − r(ξ^f(a))]` and the second in `[0, r(ξ^h(a')) − r(ξ^h(a))]`.

The share and the sets are quantified in each claim, as the parts take them: the first claim before
(a) does not need `U ⊆ W`, the second is about the configuration at `α`, and (c) has two shares
`a ≤ a'`. Its parts are `isWeakConfig_of_levelSets`, `isWeakConfig_config` and
`windows_mass_marginal` (the three claims before (a)) and `windows_a`, `windows_b` and `windows_c`;
their docstrings give the paper's steps. -/
theorem windows (hf : Submodular f) (hf0 : f ∅ = 0) (hm : ∀ o, 0 < m' o)
    (hβ : ∀ o, 0 < β' o) (hd : ∀ e, 0 ≤ d e) :
    -- before (a): the last two conditions hold for upper level sets
    (∀ (α : ℝ) {U W : Finset E},
      (∃ θ, U = levelSet (fun e => m' (some e)) (fun e => β' (some e)) α
          (xi f (fun e => m' (some e)) (fun e => β' (some e)) α) θ ∨
        U = univ.filter fun e => θ < rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) →
      (∃ θ, W = levelSet (fun e => m' (some e)) (fun e => β' (some e)) α
          (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α) θ ∨
        W = univ.filter fun e => θ < rho (subMod f d) (fun e => m' (some e))
          (fun e => β' (some e)) α e) →
      IsTight f (xi f (fun e => m' (some e)) (fun e => β' (some e)) α) U ∧
        IsTight (subMod f d) (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α)
          W) ∧
    -- before (a): the configuration is a weak configuration
    (∀ α : ℝ, IsWeakConfig f d K m' β' α (configU f d K m' β' α) (configW f d K m' β' α)) ∧
    -- before (a): the mass and the marginal of `D`, and the block of `b`
    (∀ {α : ℝ} {U W : Finset E}, U ⊆ W →
      (IsWeakConfig f d K m' β' α U W →
        bigX f d K U W = ∑ o ∈ blockUW U W, xiPrime f d K m' β' α o ∧
          thetaUW f d K m' β' α U W = thetaB f d K m' β' α ∧
          ∀ o ∈ blockUW U W, rhoPrime f d K m' β' α o = thetaB f d K m' β' α) ∧
      (U = configU f d K m' β' α → W = configW f d K m' β' α →
        univ.filter (fun o => rhoPrime f d K m' β' α o = thetaB f d K m' β' α) =
          blockUW U W)) ∧
    -- (a)
    (∀ {α : ℝ} {U W : Finset E}, U ⊆ W → IsWeakConfig f d K m' β' α U W →
      thetaB f d K m' β' α = thetaUW f d K m' β' α U W ∧
      (∀ e ∈ U, xiPrime f d K m' β' α (some e) =
        xi f (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      (∀ e ∉ W, xiPrime f d K m' β' α (some e) =
        xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) ∧
      reward m' (xiPrime f d K m' β' α) =
        ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) α e +
        ∑ e ∈ Wᶜ, m' (some e) * xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e +
        α * SS m' β' (blockUW U W) + bigX f d K U W * mbar m' β' (blockUW U W)) ∧
    -- (b)
    (∀ {α : ℝ} {U W : Finset E}, U ⊆ W →
      (∀ e ∈ U, thetaUW f d K m' β' α U W <
        rho f (fun e => m' (some e)) (fun e => β' (some e)) α e) →
      (∀ e ∉ U, rho f (fun e => m' (some e)) (fun e => β' (some e)) α e ≤
        thetaUW f d K m' β' α U W) →
      (∀ e ∈ W, thetaUW f d K m' β' α U W ≤
        rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e) →
      (∀ e ∉ W, rho (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) α e <
        thetaUW f d K m' β' α U W) →
      U = configU f d K m' β' α ∧ W = configW f d K m' β' α) ∧
    -- (c)
    ∀ {U W : Finset E}, U ⊆ W → ∀ {a a' : ℝ}, a ≤ a' → IsWeakConfig f d K m' β' a U W →
      IsWeakConfig f d K m' β' a' U W →
      reward m' (xiPrime f d K m' β' a') - reward m' (xiPrime f d K m' β' a) =
          (∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
            ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e) +
          (∑ e ∈ Wᶜ, m' (some e) *
              xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
            ∑ e ∈ Wᶜ, m' (some e) *
              xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e) +
          (a' - a) * SS m' β' (blockUW U W) ∧
        (0 ≤ ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
            ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e ∧
          ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a' e -
            ∑ e ∈ U, m' (some e) * xi f (fun e => m' (some e)) (fun e => β' (some e)) a e ≤
          reward (fun e => m' (some e)) (xi f (fun e => m' (some e)) (fun e => β' (some e)) a') -
            reward (fun e => m' (some e)) (xi f (fun e => m' (some e)) (fun e => β' (some e)) a)) ∧
        (0 ≤ ∑ e ∈ Wᶜ, m' (some e) *
              xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
            ∑ e ∈ Wᶜ, m' (some e) *
              xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e ∧
          ∑ e ∈ Wᶜ, m' (some e) *
              xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a' e -
            ∑ e ∈ Wᶜ, m' (some e) *
              xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a e ≤
          reward (fun e => m' (some e))
              (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a') -
            reward (fun e => m' (some e))
              (xi (subMod f d) (fun e => m' (some e)) (fun e => β' (some e)) a)) :=
  ⟨isWeakConfig_of_levelSets hf hf0 hm hβ hd, isWeakConfig_config hf hf0 hm hβ hd,
    windows_mass_marginal hf hf0 hm hβ hd, windows_a hf hf0 hm hβ hd,
    windows_b hf hf0 hm hβ hd, windows_c hf hf0 hm hβ hd⟩

end

end Hardness

end Stoc
