-- stamp r7 2026-11-02
import Stoc.Approximation.Scheme

/-!
# The lower bounds of Section 5

The lower bounds of Section 5, proved in Appendix D (`sec:E-lower`,
`stoc-sections/appE-halfrule.tex`:116-163): the bound for sets of shares that do not depend on the
instance (`prop:sharesets`) and the query lower bound for deterministic algorithms
(`prop:querylb`). Both use the `(1 − ε)`-optimal contracts of 08-approximation.tex:6
(`IsApproxOptimal`).

* One element (appE-halfrule.tex:118): "Both constructions have one element `e`, so an action is a
  number `z ∈ [0, f({e})]`." The polymatroid of one element with `f({e}) = T` is `oneF T`, the
  agent maximizes `U_A(z | α) = α z − c(z)` (`agentU`; `m_e = 1` in both constructions), and the
  best response breaks ties in favor of the principal (`IsPBR`); `isPBR_unit_iff` identifies this
  with the model's best response (`Convex.IsPBR`) on `P₊(oneF T)` for the cost `c(x) = c₁(x_e)`
  (`unitCost`).
* `eq:E-largest` (appE-halfrule.tex:118-121): for `c(z) = ∫_0^z c'` with a nondecreasing `c'`
  (`cost`), `α z − c(z)` is nondecreasing in `z` as long as `c' ≤ α` to the left of `z`, and
  decreasing afterwards (`agentU_le_of_le`, `agentU_lt_of_lt`), so the largest maximizer is
  `sup{z ∈ [0, f({e})] : c'(y) ≤ α for all y < z}` (`largest`, `largest_isMax`), the best response
  at every share `α < 1` (`isPBR_iff_eq_largest`); at `α = 1` the maximizer is unique in both
  constructions (`isPBR_one_iff`); `largest_eq` evaluates the supremum.
* `prop:sharesets` (`sharesets`): steps (1) `grossValue_oneF` (by `isPBR_iff_eq_largest` and
  `isPBR_one_iff`), (2) `optimal_oneF`, (3) `mem_Ico_of_optimal` (with `frac_monotoneOn`), (4) in
  `sharesets`; the remark after the proof is `sharesets_remark`. Section 5.1 cites it: "The `1/ε`
  dependence for fixed grids is optimal up to constants, already for one quadratic activity
  (`prop:sharesets`)" (08-approximation.tex:45).
* `prop:querylb` (`querylb`): deterministic algorithms (`Algorithm`, `Runs`), assumed correct only
  on the instances with one element, `m_e = 1`, `f({e}) = 1/(1 − ᾱ)` and convex costs for which `ᾱ`
  is a share bound; step (0) `zeroCost_isPBR_iff`, `isShareBound_zeroCost`; step (1) `gammaQ` (`γ`),
  `lsh`, `Kq`, `lsh_Kq_le`; step (2) `g0`, `gk` and their properties; step (3) `x0`, `xk`,
  `isPBR_x0`, `isPBR_xk`, `maximisers_window`, `x0_le_xk`; step (4) `profit_x0_low`,
  `profit_x0_mid`, `profit_x0_high`, `opt_x0`, `isShareBound_x0`, `profit_xk_window`, `opt_xk`,
  `isShareBound_xk`, `not_optimal_xk`, `probeAlpha_x0`, `probeAlpha_xk`; step (5) `window_disjoint`,
  `exists_free_window`, `Runs.congr`; step (6) `Kq_bound`. `OPT`, share bounds and
  `(1 − ε)`-optimality depend only on `U_P` on `[0, 1]` (`OPT_congr`, `isShareBound_congr`,
  `isApproxOptimal_congr`).
* Section 5 cites `prop:querylb`: "The dependence on the share bound is necessary. Even for
  one-dimensional convex costs, deterministic algorithms require `Ω(ε⁻¹ log(1/(1 − ᾱ)))` calls when
  this quantity is sufficiently large" (08-approximation.tex:23): the bound
  `ln(1/(1 − ᾱ))/(2ε) − 3` of `querylb`.
-/

namespace Stoc

namespace Lower

open Set MeasureTheory Stoc.Convex

noncomputable section

/-! ### One element -/

/-- The agent's utility `U_A(z | α) = α z − c(z)` for one element with `m_e = 1`. -/
def agentU (c : ℝ → ℝ) (α z : ℝ) : ℝ := α * z - c z

/-- `z` is the best response at the share `α` to the cost `c` on the actions `[0, T]` (one element
with `m_e = 1` and `f({e}) = T`), with ties broken in favor of the principal: `z` maximizes
`α z − c(z)`, and among the maximizers it maximizes `U_P = (1 − α) z`. -/
def IsPBR (c : ℝ → ℝ) (T α z : ℝ) : Prop :=
  z ∈ Icc 0 T ∧ (∀ y ∈ Icc 0 T, agentU c α y ≤ agentU c α z) ∧
    ∀ y ∈ Icc 0 T, agentU c α y = agentU c α z → (1 - α) * y ≤ (1 - α) * z

lemma util_unit (c₁ : ℝ → ℝ) (α : ℝ) (x : Unit → ℝ) :
    util 1 (fun v => c₁ (v ())) α x = agentU c₁ α (x ()) := by
  rw [util, reward_one_unit, agentU]

lemma isBR_unit_iff {T : ℝ} {c₁ : ℝ → ℝ} {α : ℝ} {x : Unit → ℝ} :
    IsBR (indepPoly (oneF T)) 1 (fun v => c₁ (v ())) α x ↔
      x () ∈ Icc 0 T ∧ ∀ y ∈ Icc 0 T, agentU c₁ α y ≤ agentU c₁ α (x ()) := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨mem_indepPoly_oneF.1 hx, fun y hy => ?_⟩
    have := hmax (fun _ => y) (mem_indepPoly_oneF.2 hy)
    rwa [util_unit, util_unit] at this
  · rintro ⟨hx, hmax⟩
    refine ⟨mem_indepPoly_oneF.2 hx, fun z hz => ?_⟩
    rw [util_unit, util_unit]
    exact hmax _ (mem_indepPoly_oneF.1 hz)

/-- appE-halfrule.tex:118, "Both constructions have one element `e`, so an action is a number
`z ∈ [0, f({e})]`": on `P₊(oneF T)` with `m_e = 1` and the cost `c(x) = c₁(x_e)`, the model's best
response is `IsPBR c₁ T`. -/
lemma isPBR_unit_iff {T : ℝ} {c₁ : ℝ → ℝ} {α : ℝ} {x : Unit → ℝ} :
    Convex.IsPBR (indepPoly (oneF T)) 1 (fun v => c₁ (v ())) α x ↔ IsPBR c₁ T α (x ()) := by
  constructor
  · rintro ⟨hbr, hfav⟩
    obtain ⟨hx, hmax⟩ := isBR_unit_iff.1 hbr
    refine ⟨hx, hmax, fun y hy heq => ?_⟩
    have hy' : IsBR (indepPoly (oneF T)) 1 (fun v => c₁ (v ())) α (fun _ => y) :=
      isBR_unit_iff.2 ⟨hy, fun z hz => (hmax z hz).trans heq.ge⟩
    have := hfav _ hy'
    rwa [reward_one_unit, reward_one_unit] at this
  · rintro ⟨hx, hmax, hfav⟩
    refine ⟨isBR_unit_iff.2 ⟨hx, hmax⟩, fun y hy => ?_⟩
    obtain ⟨hy, hymax⟩ := isBR_unit_iff.1 hy
    rw [reward_one_unit, reward_one_unit]
    exact hfav _ hy (le_antisymm (hmax _ hy) (hymax _ hx))

/-! ### Costs with a nondecreasing marginal cost (`eq:E-largest`) -/

/-- The cost `c(z) = ∫_0^z c'(y) dy` of the marginal cost `c' = g`. -/
def cost (g : ℝ → ℝ) (z : ℝ) : ℝ := ∫ y in (0 : ℝ)..z, g y

variable {g : ℝ → ℝ}

lemma cost_zero (g : ℝ → ℝ) : cost g 0 = 0 := by
  unfold cost
  exact intervalIntegral.integral_same

/-- A cost with a nonnegative marginal cost is nonnegative on `[0, ∞)`. -/
lemma cost_nonneg (hg0 : ∀ y, 0 ≤ y → 0 ≤ g y) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ cost g z := by
  unfold cost
  exact intervalIntegral.integral_nonneg hz fun u hu => hg0 u hu.1

lemma intervalIntegrable_of_monotoneOn (hg : MonotoneOn g (Ici 0)) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : IntervalIntegrable g volume a b :=
  MonotoneOn.intervalIntegrable (hg.mono fun u hu => by
    rcases Set.mem_uIcc.1 hu with h | h
    exacts [ha.trans h.1, hb.trans h.1])

/-- `U_A(b | α) − U_A(a | α) = (b − a) α − ∫_a^b c'`. -/
lemma agentU_sub (hg : MonotoneOn g (Ici 0)) (α : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    agentU (cost g) α b - agentU (cost g) α a = (b - a) * α - ∫ y in a..b, g y := by
  have := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_monotoneOn hg le_rfl hb)
    (intervalIntegrable_of_monotoneOn hg le_rfl ha)
  simp only [agentU, cost]
  linarith

/-- `eq:E-largest`, "`α z − c(z)` is nondecreasing in `z` as long as `c' ≤ α` to the left of `z`":
if `c' ≤ α` on `(a, b)`, then `U_A(a) ≤ U_A(b)`. -/
lemma agentU_le_of_le (hg : MonotoneOn g (Ici 0)) {α a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ y ∈ Ioo a b, g y ≤ α) : agentU (cost g) α a ≤ agentU (cost g) α b := by
  have h1 := agentU_sub hg α ha (ha.trans hab)
  have h2 : ∫ y in a..b, g y ≤ ∫ _ in a..b, α :=
    intervalIntegral.integral_mono_on_of_le_Ioo hab
      (intervalIntegrable_of_monotoneOn hg ha (ha.trans hab)) intervalIntegrable_const h
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  linarith

/-- If `c' ≥ α` on `(a, b)`, then `U_A(b) ≤ U_A(a)`. -/
lemma agentU_le_of_ge (hg : MonotoneOn g (Ici 0)) {α a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ y ∈ Ioo a b, α ≤ g y) : agentU (cost g) α b ≤ agentU (cost g) α a := by
  have h1 := agentU_sub hg α ha (ha.trans hab)
  have h2 : ∫ _ in a..b, α ≤ ∫ y in a..b, g y :=
    intervalIntegral.integral_mono_on_of_le_Ioo hab intervalIntegrable_const
      (intervalIntegrable_of_monotoneOn hg ha (ha.trans hab)) h
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  linarith

/-- The strict form: if `c' < α` on `(a, b)` and `a < b`, then `U_A(a) < U_A(b)`. -/
lemma agentU_lt_of_gt (hg : MonotoneOn g (Ici 0)) {α a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (h : ∀ y ∈ Ioo a b, g y < α) : agentU (cost g) α a < agentU (cost g) α b := by
  have hb : 0 ≤ b := ha.trans hab.le
  have h1 := agentU_sub hg α ha hb
  have h2 : 0 < ∫ y in a..b, (α - g y) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_const.sub (intervalIntegrable_of_monotoneOn hg ha hb))
      (fun y hy => sub_pos.2 (h y hy)) hab
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegrable_of_monotoneOn hg ha hb), intervalIntegral.integral_const,
    smul_eq_mul] at h2
  linarith

/-- `eq:E-largest`, "and decreasing afterwards": if `c' > α` on `(a, b)` and `a < b`, then
`U_A(b) < U_A(a)`. -/
lemma agentU_lt_of_lt (hg : MonotoneOn g (Ici 0)) {α a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (h : ∀ y ∈ Ioo a b, α < g y) : agentU (cost g) α b < agentU (cost g) α a := by
  have hb : 0 ≤ b := ha.trans hab.le
  have h1 := agentU_sub hg α ha hb
  have h2 : 0 < ∫ y in a..b, (g y - α) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((intervalIntegrable_of_monotoneOn hg ha hb).sub intervalIntegrable_const)
      (fun y hy => sub_pos.2 (h y hy)) hab
  rw [intervalIntegral.integral_sub (intervalIntegrable_of_monotoneOn hg ha hb)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at h2
  linarith

/-- A cost with a nondecreasing marginal cost is convex on `[0, ∞)` (not in the paper: it
asserts the convexity of `c₀` and `c_k`): the slope of `c` on `[x, y]` is at most `c'(y)`, and that
on `[y, z]` at least `c'(y)`. -/
lemma convexOn_cost (hg : MonotoneOn g (Ici 0)) : ConvexOn ℝ (Ici 0) (cost g) := by
  refine convexOn_of_slope_mono_adjacent (convex_Ici 0) ?_
  intro x y z hx hz hxy hyz
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hx0.trans hxy.le
  have hz0 : (0 : ℝ) ≤ z := hy0.trans hyz.le
  have e1 := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_monotoneOn hg le_rfl hy0)
    (intervalIntegrable_of_monotoneOn hg le_rfl hx0)
  have e2 := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_monotoneOn hg le_rfl hz0)
    (intervalIntegrable_of_monotoneOn hg le_rfl hy0)
  have i1 : ∫ u in x..y, g u ≤ ∫ _ in x..y, g y :=
    intervalIntegral.integral_mono_on_of_le_Ioo hxy.le
      (intervalIntegrable_of_monotoneOn hg hx0 hy0) intervalIntegrable_const
      fun u hu => hg (show (0 : ℝ) ≤ u from hx0.trans hu.1.le) hy0 hu.2.le
  have i2 : ∫ _ in y..z, g y ≤ ∫ u in y..z, g u :=
    intervalIntegral.integral_mono_on_of_le_Ioo hyz.le intervalIntegrable_const
      (intervalIntegrable_of_monotoneOn hg hy0 hz0)
      fun u hu => hg hy0 (show (0 : ℝ) ≤ u from hy0.trans hu.1.le) hu.1.le
  rw [intervalIntegral.integral_const, smul_eq_mul] at i1 i2
  rw [div_le_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 hyz)]
  simp only [cost]
  rw [e1, e2]
  have p1 := mul_le_mul_of_nonneg_right i1 (sub_pos.2 hyz).le
  have p2 := mul_le_mul_of_nonneg_right i2 (sub_pos.2 hxy).le
  linarith

/-- The set `{z ∈ [0, T] : c'(y) ≤ α for all y < z}` of `eq:E-largest`. -/
def largestSet (g : ℝ → ℝ) (T α : ℝ) : Set ℝ := {z | z ∈ Icc 0 T ∧ ∀ y ∈ Ico 0 z, g y ≤ α}

/-- `sup{z ∈ [0, T] : c'(y) ≤ α for all y < z}`, the right-hand side of `eq:E-largest`. -/
def largest (g : ℝ → ℝ) (T α : ℝ) : ℝ := sSup (largestSet g T α)

section Largest

variable {T α : ℝ}

lemma largestSet_nonempty (hT : 0 ≤ T) : (largestSet g T α).Nonempty :=
  ⟨0, ⟨le_rfl, hT⟩, fun _ hy => absurd hy.2 (not_lt.2 hy.1)⟩

lemma bddAbove_largestSet : BddAbove (largestSet g T α) := ⟨T, fun _ hz => hz.1.2⟩

/-- The supremum belongs to the set: `c' ≤ α` on `[0, z₁)` for `z₁ = sup{…}`. -/
lemma largest_mem (hT : 0 ≤ T) : largest g T α ∈ largestSet g T α := by
  have hne := largestSet_nonempty (g := g) (α := α) hT
  refine ⟨⟨(hne.some_mem.1.1).trans (le_csSup bddAbove_largestSet hne.some_mem),
    csSup_le hne fun z hz => hz.1.2⟩, fun y hy => ?_⟩
  obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne hy.2
  exact hz.2 y ⟨hy.1, hyz⟩

/-- `c' > α` on `(z₁, T]` for `z₁ = sup{…}`, as `c'` is nondecreasing. -/
lemma lt_of_largest_lt (hg : MonotoneOn g (Ici 0)) (hT : 0 ≤ T) {y : ℝ}
    (hy : y ∈ Ioc (largest g T α) T) : α < g y := by
  have h0 : 0 ≤ largest g T α := (largest_mem (g := g) (α := α) hT).1.1
  by_contra hle
  push Not at hle
  have hmem : y ∈ largestSet g T α :=
    ⟨⟨h0.trans hy.1.le, hy.2⟩, fun y' hy' => (hg hy'.1 (h0.trans hy.1.le) hy'.2.le).trans hle⟩
  exact absurd (le_csSup bddAbove_largestSet hmem) (not_le.2 hy.1)

/-- **`eq:E-largest`** (appE-halfrule.tex:118-121): with `z₁ = sup{z ∈ [0, T] : c'(y) ≤ α for all
y < z}`, "`α z − c(z)` is nondecreasing in `z` as long as `c' ≤ α` to the left of `z`, and
decreasing afterwards": `z₁` maximizes `U_A(· | α)` over `[0, T]`, and every maximizer is at most
`z₁`. -/
theorem largest_isMax (hg : MonotoneOn g (Ici 0)) (hT : 0 ≤ T) :
    (∀ y ∈ Icc 0 T, agentU (cost g) α y ≤ agentU (cost g) α (largest g T α)) ∧
      ∀ y ∈ Icc 0 T, agentU (cost g) α y = agentU (cost g) α (largest g T α) →
        y ≤ largest g T α := by
  obtain ⟨hz₁, hle⟩ := largest_mem (g := g) (α := α) hT
  have key : ∀ y ∈ Icc 0 T, largest g T α < y →
      agentU (cost g) α y < agentU (cost g) α (largest g T α) :=
    fun y hy h => agentU_lt_of_lt hg hz₁.1 h fun u hu =>
      lt_of_largest_lt hg hT ⟨hu.1, hu.2.le.trans hy.2⟩
  refine ⟨fun y hy => ?_, fun y hy heq => ?_⟩
  · rcases le_or_gt y (largest g T α) with h | h
    · exact agentU_le_of_le hg hy.1 h fun u hu => hle u ⟨hy.1.trans hu.1.le, hu.2⟩
    · exact (key y hy h).le
  · by_contra h
    exact (key y hy (not_le.1 h)).ne heq

/-- **`eq:E-largest`**: for `α < 1`, the best response, the largest maximizer as ties are broken in
favor of the principal, is `x*(α) = sup{z ∈ [0, T] : c'(y) ≤ α for all y < z}`. -/
theorem isPBR_iff_eq_largest (hg : MonotoneOn g (Ici 0)) (hT : 0 ≤ T) (hα : α < 1) {z : ℝ} :
    IsPBR (cost g) T α z ↔ z = largest g T α := by
  obtain ⟨hmax, hlarge⟩ := largest_isMax (α := α) hg hT
  have hz₁ := (largest_mem (g := g) (α := α) hT).1
  have hpos : 0 < 1 - α := by linarith
  constructor
  · rintro ⟨hz, hzmax, hfav⟩
    have heq : agentU (cost g) α z = agentU (cost g) α (largest g T α) :=
      le_antisymm (hmax z hz) (hzmax _ hz₁)
    exact le_antisymm (hlarge z hz heq)
      (le_of_mul_le_mul_left (hfav _ hz₁ heq.symm) hpos)
  · rintro rfl
    exact ⟨hz₁, hmax, fun y hy heq => mul_le_mul_of_nonneg_left (hlarge y hy heq) hpos.le⟩

/-- At the share `1`, if `c' < 1` on `[0, T)`, the maximizer is unique, namely `T` ("at `α = 1` the
maximizer is unique in both constructions", appE-halfrule.tex:118; not in the paper: it
asserts this without proof). -/
lemma isPBR_one_iff {g : ℝ → ℝ} (hg : MonotoneOn g (Ici 0)) {T : ℝ} (hT : 0 ≤ T)
    (hlt : ∀ y ∈ Ico 0 T, g y < 1) {z : ℝ} : IsPBR (cost g) T 1 z ↔ z = T := by
  have hmax : ∀ y ∈ Icc 0 T, agentU (cost g) 1 y ≤ agentU (cost g) 1 T := fun y hy =>
    agentU_le_of_le hg hy.1 hy.2 fun u hu => (hlt u ⟨hy.1.trans hu.1.le, hu.2⟩).le
  constructor
  · rintro ⟨hz, hzmax, -⟩
    by_contra hne
    have hzT : z < T := lt_of_le_of_ne hz.2 hne
    have := agentU_lt_of_gt hg hz.1 hzT fun u hu => hlt u ⟨hz.1.trans hu.1.le, hu.2⟩
    exact absurd (hzmax T ⟨hT, le_rfl⟩) (not_le.2 this)
  · rintro rfl
    exact ⟨⟨hT, le_rfl⟩, hmax, fun y _ _ => by simp⟩

/-- Evaluating the supremum of `eq:E-largest`: if `v ∈ [0, T]`, `c' ≤ α` on `[0, v)` and `c' > α` on
`(v, T]`, then `sup{z ∈ [0, T] : c'(y) ≤ α for all y < z} = v` (not in the paper: it
evaluates the supremum of `eq:E-largest` without proof, for `x*(α) = min{α, u}`, `x₀` and `x_k`). -/
lemma largest_eq (hT : 0 ≤ T) {v : ℝ} (hv : v ∈ Icc 0 T)
    (hle : ∀ y ∈ Ico 0 v, g y ≤ α) (hgt : ∀ y ∈ Ioc v T, α < g y) : largest g T α = v := by
  have hmem := largest_mem (g := g) (α := α) hT
  have h1 : v ≤ largest g T α := le_csSup bddAbove_largestSet ⟨hv, hle⟩
  by_contra hne
  have hlt : v < largest g T α := lt_of_le_of_ne h1 (Ne.symm hne)
  -- a point `y ∈ (v, z₁)` has `c'(y) ≤ α`, as `z₁` is in the set, and `c'(y) > α`
  obtain ⟨y, hvy, hyz⟩ := exists_between hlt
  have := hmem.2 y ⟨hv.1.trans hvy.le, hyz⟩
  exact absurd (hgt y ⟨hvy, hyz.le.trans hmem.1.2⟩) (not_lt.2 this)

end Largest

/-! ### `prop:sharesets` -/

/-- The quadratic cost `c(z) = z²/2` (`β_e = 1`) has the marginal cost `c'(y) = y`. -/
lemma cost_id : cost (fun y => y) = fun z => z ^ 2 / 2 := by
  funext z
  simp only [cost, integral_id]
  ring

lemma monotoneOn_id' : MonotoneOn (fun y : ℝ => y) (Ici 0) := fun _ _ _ _ h => h

/-- The quadratic cost of one element with `β_e = 1` is `c(z) = ∫_0^z y dy`. -/
lemma quadCost_one_unit : quadCost (1 : Unit → ℝ) = fun v => cost (fun y => y) (v ()) := by
  funext v
  rw [cost_id]
  simp [quadCost]
  ring

/-- `prop:sharesets`, step (1) (appE-halfrule.tex:128): "By `eq:E-largest`, its best response is
`x*(α) = min{α, u}`". The
best response `x*(α)` of the quadratic model is the model's best response for the cost
`c(z) = z²/2 = ∫_0^z y dy`, ties broken in favor of the principal (`isPBR_bestResponse`); for
`α < 1` it is `sup{z ∈ [0, u] : y ≤ α for all y < z} = min{α, u}` by `eq:E-largest`
(`isPBR_iff_eq_largest`, `largest_eq`), and at `α = 1` the maximizer is unique, `u = min{1, u}`
(`isPBR_one_iff`, appE-halfrule.tex:118). -/
lemma grossValue_oneF {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    grossValue (oneF u) 1 1 α = min α u := by
  -- `x*(α)` is the best response, with ties broken in favor of the principal, for the cost
  -- `c(z) = ∫_0^z y dy` on the actions `[0, u]`
  have hpbr : IsPBR (cost fun y => y) u α (bestResponse (oneF u) 1 1 α ()) := by
    have h := isPBR_bestResponse (isRankFunction_oneF hu.le) (m := 1) (β := 1)
      (fun _ => one_pos) α
    rw [quadCost_one_unit] at h
    exact isPBR_unit_iff.1 h
  rw [grossValue, reward_one_unit]
  rcases hα.2.lt_or_eq with hlt | rfl
  · -- "By `eq:E-largest`": `x*(α) = sup{z ∈ [0, u] : y ≤ α for all y < z} = min{α, u}`
    rw [(isPBR_iff_eq_largest monotoneOn_id' hu.le hlt).1 hpbr]
    exact largest_eq hu.le ⟨le_min hα.1 hu.le, min_le_right α u⟩
      (fun y hy => (lt_of_lt_of_le hy.2 (min_le_left α u)).le) fun y hy => by
        rcases le_total α u with h | h
        · rw [min_eq_left h] at hy
          exact hy.1
        · rw [min_eq_right h] at hy
          exact absurd hy.2 (not_le.2 hy.1)
  · -- at `α = 1` the maximizer is unique: `x*(1) = u = min{1, u}`
    rw [(isPBR_one_iff monotoneOn_id' hu.le fun y hy => hy.2.trans_le hu1).1 hpbr,
      min_eq_right hu1]

/-- `prop:sharesets`, step (2): "`α ↦ α(1 − α)` is increasing on `[0, 1/2]`" (not in the paper: the
proof states it without proof). -/
lemma mul_one_sub_monotoneOn : MonotoneOn (fun α : ℝ => α * (1 - α)) (Icc 0 (1 / 2)) := by
  intro a ha b hb hab
  simp only
  nlinarith [mul_nonneg (sub_nonneg.2 hab) (show (0 : ℝ) ≤ 1 - a - b by linarith [ha.2, hb.2])]

/-- `prop:sharesets`, steps (1)–(2): on `I_u`, `u ∈ (0, 1/2]`, `U_P(α) = (1 − α) min{α, u}`; "as
`α ↦ α(1 − α)` is increasing on `[0, 1/2]` and `u ≤ 1/2`, the optimal contract is `u`, and
`OPT = u(1 − u)`". -/
lemma optimal_oneF {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    IsMaxOn (profit (grossValue (oneF u) 1 1)) (Icc 0 1) u ∧
      OPT (profit (grossValue (oneF u) 1 1)) = u * (1 - u) := by
  have hU : ∀ α ∈ Icc (0 : ℝ) 1, profit (grossValue (oneF u) 1 1) α = (1 - α) * min α u :=
    fun α hα => by rw [profit, grossValue_oneF hu (by linarith) hα]
  have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.le, by linarith⟩
  have hUu : profit (grossValue (oneF u) 1 1) u = u * (1 - u) := by
    rw [hU u hu1, min_self]; ring
  have hle : ∀ α ∈ Icc (0 : ℝ) 1, profit (grossValue (oneF u) 1 1) α ≤ u * (1 - u) := by
    intro α hα
    rw [hU α hα]
    rcases le_total α u with h | h
    · rw [min_eq_left h]
      have := mul_one_sub_monotoneOn ⟨hα.1, h.trans hu2⟩ ⟨hu.le, hu2⟩ h
      simp only at this
      linarith
    · rw [min_eq_right h]
      nlinarith [mul_nonneg hu.le (sub_nonneg.2 h)]
  refine ⟨isMaxOn_iff.2 fun α hα => (hle α hα).trans hUu.ge, ?_⟩
  exact IsGreatest.csSup_eq ⟨⟨u, hu1, hUu⟩, by rintro _ ⟨α, hα, rfl⟩; exact hle α hα⟩

/-- `prop:sharesets`, step (3b): "`u ↦ u(1 − u)/(1 − 2u)` is increasing on `[0, 1/2)`" (not in the
paper: the proof states it without proof). -/
lemma frac_monotoneOn :
    MonotoneOn (fun u : ℝ => u * (1 - u) / (1 - 2 * u)) (Ico 0 (1 / 2)) := by
  intro u hu v hv huv
  simp only
  have h1 : 0 < 1 - 2 * u := by linarith [hu.2]
  have h2 : 0 < 1 - 2 * v := by linarith [hv.2]
  rw [div_le_div_iff₀ h1 h2]
  -- `v(1 − v)(1 − 2u) − u(1 − u)(1 − 2v) = (v − u)((1 − u)(1 − v) + uv)`
  have e : v * (1 - v) * (1 - 2 * u) - u * (1 - u) * (1 - 2 * v) =
      (v - u) * ((1 - u) * (1 - v) + u * v) := by ring
  have : 0 ≤ (v - u) * ((1 - u) * (1 - v) + u * v) :=
    mul_nonneg (by linarith) (by nlinarith [hu.1, hv.1, hu.2, hv.2])
  linarith

/-- **`prop:sharesets`**, step (3): the set `𝒢(u)` of `(1 − ε)`-optimal contracts of `I_u`,
`u ∈ (0, 1/3]`, lies in `[u − 2ε/3, u + ε)`.

(3a) "A share `α ≥ u` is `(1 − ε)`-optimal if and only if `(1 − α)u ≥ (1 − ε)(1 − u)u`, that is,
`α ≤ u + ε(1 − u)`, and `u + ε(1 − u) < u + ε`." (3b) "A share `α ≤ u` is `(1 − ε)`-optimal if and
only if `α(1 − α) ≥ (1 − ε)u(1 − u)`. The function `d ↦ (u − d)(1 − u + d)` decreases from
`u(1 − u)` to `0` on `[0, u]`, so there is a unique `d ∈ [0, u]` with
`(u − d)(1 − u + d) = (1 − ε)u(1 − u)`, and a share `α ≤ u` is `(1 − ε)`-optimal if and only if
`α ≥ u − d`. Expanding gives `d(1 − 2u + d) = εu(1 − u)`, so `d ≤ εu(1 − u)/(1 − 2u) ≤ 2ε/3`." -/
theorem mem_Ico_of_optimal {ε u : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hu : 0 < u) (hu3 : u ≤ 1 / 3)
    {α : ℝ} (hopt : IsApproxOptimal (profit (grossValue (oneF u) 1 1)) ε α) :
    α ∈ Ico (u - 2 / 3 * ε) (u + ε) := by
  obtain ⟨hα, hopt⟩ := hopt
  obtain ⟨-, hOPT⟩ := optimal_oneF hu (by linarith)
  rw [hOPT, profit, grossValue_oneF hu (by linarith) hα] at hopt
  obtain ⟨hε0, hε1⟩ := hε
  rcases le_total u α with huα | hαu
  · -- (3a) "A share `α ≥ u` is `(1 − ε)`-optimal if and only if `(1 − α)u ≥ (1 − ε)(1 − u)u`, that
    -- is, `α ≤ u + ε(1 − u)`, and `u + ε(1 − u) < u + ε`."
    rw [min_eq_right huα] at hopt
    have hiff : (1 - ε) * (u * (1 - u)) ≤ (1 - α) * u ↔ α ≤ u + ε * (1 - u) := by
      constructor
      · intro h
        have : u * (α - (u + ε * (1 - u))) ≤ 0 := by nlinarith
        nlinarith [(mul_nonpos_iff.1 this)]
      · intro h
        nlinarith
    have h1 := hiff.1 hopt
    have h2 : u + ε * (1 - u) < u + ε := by nlinarith
    exact ⟨by linarith, lt_of_le_of_lt h1 h2⟩
  · -- (3b) "A share `α ≤ u` is `(1 − ε)`-optimal if and only if `α(1 − α) ≥ (1 − ε)u(1 − u)`."
    rw [min_eq_left hαu] at hopt
    have hopt' : (1 - ε) * (u * (1 - u)) ≤ α * (1 - α) := by linarith
    -- "The function `d ↦ (u − d)(1 − u + d)` decreases from `u(1 − u)` to `0` on `[0, u]`"
    set φ : ℝ → ℝ := fun d => (u - d) * (1 - u + d) with hφ
    have hφanti : StrictAntiOn φ (Icc 0 u) := by
      intro d hd d' hd' hdd'
      simp only [hφ]
      nlinarith [mul_pos (sub_pos.2 hdd') (show (0 : ℝ) < 1 - 2 * u + d + d' by
        linarith [hd.1, hd'.1])]
    have hφ0 : φ 0 = u * (1 - u) := by simp [hφ]
    have hφu : φ u = 0 := by simp [hφ]
    -- "so there is a unique `d ∈ [0, u]` with `(u − d)(1 − u + d) = (1 − ε)u(1 − u)`"
    have hcont : ContinuousOn φ (Icc 0 u) := by
      simp only [hφ]; fun_prop
    have htarget : (1 - ε) * (u * (1 - u)) ∈ Icc (φ u) (φ 0) := by
      rw [hφu, hφ0]
      constructor
      · exact mul_nonneg (by linarith) (mul_nonneg hu.le (by linarith))
      · nlinarith [mul_pos hu (show (0 : ℝ) < 1 - u by linarith)]
    obtain ⟨d, hd, hdφ⟩ := intermediate_value_Icc' hu.le hcont htarget
    have _huniq : ∀ d' ∈ Icc 0 u, φ d' = (1 - ε) * (u * (1 - u)) → d' = d :=
      fun d' hd' h => hφanti.injOn hd' hd (h.trans hdφ.symm)
    -- "and a share `α ≤ u` is `(1 − ε)`-optimal if and only if `α ≥ u − d`"
    have hiff : ∀ a ∈ Icc 0 u, ((1 - ε) * (u * (1 - u)) ≤ a * (1 - a) ↔ u - d ≤ a) := by
      intro a ha
      have hφa : φ (u - a) = a * (1 - a) := by simp only [hφ]; ring
      have hua : u - a ∈ Icc 0 u := ⟨by linarith [ha.2], by linarith [ha.1]⟩
      rw [← hφa, ← hdφ, hφanti.le_iff_ge hd hua]
      constructor <;> intro h <;> linarith
    have hαd : u - d ≤ α := (hiff α ⟨hα.1, hαu⟩).1 hopt'
    -- "Expanding gives `d(1 − 2u + d) = εu(1 − u)`"
    have hexp : d * (1 - 2 * u + d) = ε * (u * (1 - u)) := by
      simp only [hφ] at hdφ
      linarith
    -- "so `d ≤ εu(1 − u)/(1 − 2u)`"
    have h12u : 0 < 1 - 2 * u := by linarith
    have hd1 : d ≤ ε * (u * (1 - u)) / (1 - 2 * u) := by
      rw [le_div_iff₀ h12u]
      nlinarith [mul_nonneg hd.1 hd.1]
    -- "`≤ 2ε/3`, as `u ↦ u(1 − u)/(1 − 2u)` is increasing on `[0, 1/2)` and equals `2/3` at
    -- `u = 1/3`"
    have hfrac : u * (1 - u) / (1 - 2 * u) ≤ 2 / 3 := by
      have := frac_monotoneOn ⟨hu.le, by linarith⟩ ⟨by norm_num, by norm_num⟩ hu3
      simp only at this
      norm_num at this
      exact this
    have hd2 : d ≤ 2 / 3 * ε := by
      calc d ≤ ε * (u * (1 - u)) / (1 - 2 * u) := hd1
        _ = ε * (u * (1 - u) / (1 - 2 * u)) := by ring
        _ ≤ ε * (2 / 3) := mul_le_mul_of_nonneg_left hfrac hε0.le
        _ = 2 / 3 * ε := by ring
    exact ⟨by linarith, by linarith⟩

/-- **`prop:sharesets`** (Proposition D.3, appE-halfrule.tex:123-125, proof 127-133): let
`ε ∈ (0, 1)`, and let `A ⊆ [0, 1]` contain a `(1 − ε)`-optimal contract (`IsApproxOptimal`) of every
instance with one element `e`, `m_e = β_e = 1` and quadratic costs (the instances are the rank
functions `f` of one element; their reward of success `r̄`, 02-preliminaries.tex:12, does not enter
`U_P`; the best response is that of the quadratic model, `grossValue f 1 1`). Then
`|A| ≥ ⌊1/(5ε)⌋`.

The proof: (1) the instances `I_u`, `u ∈ (0, 1/3]`, with `f({e}) = u` (`oneF u`) and
`x*(α) = min{α, u}` (`grossValue_oneF`, by `eq:E-largest`); (2) `OPT = u(1 − u)` (`optimal_oneF`);
(3) `𝒢(u) ⊆ [u − 2ε/3, u + ε)` (`mem_Ico_of_optimal`); (4) `N = ⌊1/(5ε)⌋`, `u_i = 5εi/3`, the sets
`𝒢(u_i)` are pairwise disjoint and `A` meets each. The hypothesis `A ⊆ [0, 1]` is not used, as a
`(1 − ε)`-optimal contract is a share in `[0, 1]` (`IsApproxOptimal`). -/
theorem sharesets {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (A : Set ℝ) (_hA01 : A ⊆ Icc 0 1)
    (hA : ∀ f : Finset Unit → ℝ, IsRankFunction f →
      ∃ α ∈ A, IsApproxOptimal (profit (grossValue f 1 1)) ε α) :
    (⌊1 / (5 * ε)⌋₊ : ℕ∞) ≤ A.encard := by
  have hε0 := hε.1
  -- (1) "For `u ∈ (0, 1/3]`, let `I_u` be the instance with `f({e}) = u`."
  -- "Let `𝒢(u)` be the set of `(1 − ε)`-optimal contracts of `I_u`."
  set 𝒢 : ℝ → Set ℝ := fun u => {α | IsApproxOptimal (profit (grossValue (oneF u) 1 1)) ε α}
    with h𝒢
  -- (4) "Let `N := ⌊1/(5ε)⌋` and `u_i := (5/3) ε i` for `i ∈ [N]`, so that `u_N ≤ 1/3`."
  set N := ⌊1 / (5 * ε)⌋₊ with hN
  set ui : ℕ → ℝ := fun i => 5 / 3 * ε * i with hui
  have hNle : ui N ≤ 1 / 3 := by
    have h1 : (N : ℝ) ≤ 1 / (5 * ε) := Nat.floor_le (by positivity)
    have h5 : (0 : ℝ) < 5 * ε := by positivity
    rw [le_div_iff₀ h5] at h1
    simp only [hui]
    linarith
  have hu_pos : ∀ i ∈ Finset.Icc 1 N, 0 < ui i := fun i hi => by
    have : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.1 hi).1
    simp only [hui]; positivity
  have hu_le : ∀ i ∈ Finset.Icc 1 N, ui i ≤ 1 / 3 := fun i hi => by
    have : (i : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hi).2
    refine le_trans ?_ hNle
    simp only [hui]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- "As `u_i + ε = u_{i+1} − 2ε/3`, the sets `𝒢(u_1), …, 𝒢(u_N)` are pairwise disjoint."
  have hstep : ∀ i : ℕ, ui i + ε = ui (i + 1) - 2 / 3 * ε := fun i => by
    simp only [hui]; push_cast; ring
  have hdisj : ∀ i ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N, i ≠ j →
      Disjoint (𝒢 (ui i)) (𝒢 (ui j)) := by
    -- by (3), `𝒢(u_i) ⊆ [u_i − 2ε/3, u_i + ε)`
    have hG : ∀ i ∈ Finset.Icc 1 N, 𝒢 (ui i) ⊆ Ico (ui i - 2 / 3 * ε) (ui i + ε) :=
      fun i hi α hα => mem_Ico_of_optimal hε (hu_pos i hi) (hu_le i hi) hα
    have hlt : ∀ i ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N, i < j →
        Disjoint (𝒢 (ui i)) (𝒢 (ui j)) := by
      intro i hi j hj hij
      rw [Set.disjoint_left]
      intro α hαi hαj
      have h1 := (hG i hi hαi).2
      have h2 := (hG j hj hαj).1
      have hmono : ui (i + 1) ≤ ui j := by
        simp only [hui]
        have : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hij
        exact mul_le_mul_of_nonneg_left this (by positivity)
      linarith [hstep i]
    intro i hi j hj hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt i hi j hj h
    · exact (hlt j hj i hi h).symm
  -- "The set `A` meets each of them, so `|A| ≥ N`."
  have hmeet : ∀ i ∈ Finset.Icc 1 N, ∃ a ∈ A, a ∈ 𝒢 (ui i) := by
    intro i hi
    obtain ⟨a, haA, hopt⟩ := hA (oneF (ui i)) (isRankFunction_oneF (hu_pos i hi).le)
    exact ⟨a, haA, hopt⟩
  choose! a haA haG using hmeet
  have hinj : Set.InjOn a (Finset.Icc 1 N : Set ℕ) := by
    intro i hi j hj hij
    by_contra hne
    exact Set.disjoint_left.1 (hdisj i hi j hj hne) (haG i hi) (hij ▸ haG j hj)
  have himage : ((Finset.Icc 1 N).image a : Set ℝ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact haA i hi
  calc (N : ℕ∞) = (((Finset.Icc 1 N).image a).card : ℕ∞) := by
        rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
        simp
    _ = ((Finset.Icc 1 N).image a : Set ℝ).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ A.encard := Set.encard_le_encard himage

/-- The remark after the proof of `prop:sharesets` (appE-halfrule.tex:135): "on these instances, one
best response suffices, as `x*(1) = u` is the optimal contract". -/
lemma sharesets_remark {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 1 / 2) :
    grossValue (oneF u) 1 1 1 = u ∧ IsMaxOn (profit (grossValue (oneF u) 1 1)) (Icc 0 1) u := by
  refine ⟨?_, (optimal_oneF hu hu2).1⟩
  rw [grossValue_oneF hu (by linarith) ⟨zero_le_one, le_rfl⟩, min_eq_right (by linarith)]

/-! ### `prop:querylb`: algorithms -/

/-- A deterministic algorithm that is given `ε` and `ᾱ` (fixed here) and learns about the costs only
from best responses at shares of its choice: on an instance with the ground set `E`, the rank
function `f` and the rewards `m`, from the best responses received so far it either asks for one
more, at a share of its choice (`Sum.inl α`), or returns a share (`Sum.inr α̂`). -/
def Algorithm : Type 1 :=
  ∀ (E : Type) [Fintype E] [DecidableEq E], (Finset E → ℝ) → (E → ℝ) → List (E → ℝ) → ℝ ⊕ ℝ

/-- `A`, run on the instance `(E, f, m)` with the best responses `x(α)`, computes the best responses
at the shares `as`, in this order, and returns `ret`; it makes `as.length` best-response
computations. -/
def Runs (A : Algorithm) {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (m : E → ℝ)
    (x : ℝ → E → ℝ) (as : List ℝ) (ret : ℝ) : Prop :=
  (∀ i (hi : i < as.length), A E f m ((as.take i).map x) = Sum.inl as[i]) ∧
    A E f m (as.map x) = Sum.inr ret

/-- "Being deterministic", `A` runs in the same way on two instances with the same `(E, f, m)` that
have the same best responses at the shares that `A` computes on the first. -/
lemma Runs.congr {A : Algorithm} {E : Type} [Fintype E] [DecidableEq E] {f : Finset E → ℝ}
    {m : E → ℝ} {x x' : ℝ → E → ℝ} {as : List ℝ} {ret : ℝ} (h : Runs A f m x as ret)
    (hx : ∀ a ∈ as, x' a = x a) : Runs A f m x' as ret := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have e : (as.take i).map x' = (as.take i).map x :=
      List.map_congr_left fun a ha => hx a (List.mem_of_mem_take ha)
    rw [e]
    exact h.1 i hi
  · have e : as.map x' = as.map x := List.map_congr_left hx
    rw [e]
    exact h.2

/-- `OPT` and share bounds only depend on `U_P` on `[0, 1]`. -/
lemma isShareBound_congr {U U' : ℝ → ℝ} (hU : ∀ α ∈ Icc (0 : ℝ) 1, U' α = U α) {ᾱ : ℝ}
    (h : IsShareBound U ᾱ) : IsShareBound U' ᾱ := by
  obtain ⟨h0, h1, hsup⟩ := h
  have himg : ∀ B ≤ 1, U' '' Icc 0 B = U '' Icc 0 B := fun B hB =>
    Set.image_congr fun α hα => hU α ⟨hα.1, hα.2.trans hB⟩
  refine ⟨h0, h1, ?_⟩
  unfold OPT at hsup ⊢
  rw [himg _ h1.le, himg _ le_rfl, hsup]

lemma OPT_congr {U U' : ℝ → ℝ} (hU : ∀ α ∈ Icc (0 : ℝ) 1, U' α = U α) : OPT U' = OPT U := by
  unfold OPT
  rw [Set.image_congr fun α hα => hU α hα]

/-- Whether a share is `(1 − ε)`-optimal only depends on `U_P` on `[0, 1]`. -/
lemma isApproxOptimal_congr {U U' : ℝ → ℝ} (hU : ∀ α ∈ Icc (0 : ℝ) 1, U' α = U α) {ε α : ℝ} :
    IsApproxOptimal U' ε α ↔ IsApproxOptimal U ε α := by
  unfold IsApproxOptimal
  rw [OPT_congr hU]
  exact ⟨fun ⟨h0, h⟩ => ⟨h0, by rwa [← hU α h0]⟩, fun ⟨h0, h⟩ => ⟨h0, by rwa [hU α h0]⟩⟩

/-! ### `prop:querylb`: the shares `l_j` and the number `K` -/

section Querylb

variable {ε ᾱ : ℝ}

/-- `γ = 1 + 2ε` (appE-halfrule.tex:141). -/
def gammaQ (ε : ℝ) : ℝ := 1 + 2 * ε

/-- `l_j = 1 − (1 − ε) γ^{−j}` (appE-halfrule.tex:141). -/
def lsh (ε : ℝ) (j : ℕ) : ℝ := 1 - (1 - ε) / gammaQ ε ^ j

/-- `K`, the largest integer with `(1 − ε) γ^{−K} ≥ 1 − ᾱ` (appE-halfrule.tex:141). -/
def Kq (ε ᾱ : ℝ) : ℕ := sSup {k : ℕ | 1 - ᾱ ≤ (1 - ε) / gammaQ ε ^ k}

lemma gammaQ_pos (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) : 0 < gammaQ ε := by
  unfold gammaQ
  linarith [hε.1]

lemma one_lt_gammaQ (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) : 1 < gammaQ ε := by
  unfold gammaQ
  linarith [hε.1]

lemma one_sub_lsh (j : ℕ) : 1 - lsh ε j = (1 - ε) / gammaQ ε ^ j := by
  unfold lsh
  ring

lemma lsh_zero : lsh ε 0 = ε := by
  unfold lsh
  rw [pow_zero, div_one]
  ring

lemma one_sub_lsh_pos (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (j : ℕ) : 0 < 1 - lsh ε j := by
  rw [one_sub_lsh]
  exact div_pos (by linarith [hε.2]) (pow_pos (gammaQ_pos hε) j)

/-- `1 − l_j = γ (1 − l_{j+1})`. -/
lemma one_sub_lsh_succ (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (j : ℕ) :
    1 - lsh ε j = gammaQ ε * (1 - lsh ε (j + 1)) := by
  rw [one_sub_lsh, one_sub_lsh, pow_succ, ← div_div, mul_div_cancel₀ _ (gammaQ_pos hε).ne']

lemma lsh_lt_succ (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (j : ℕ) : lsh ε j < lsh ε (j + 1) := by
  have h1 := one_sub_lsh_succ hε j
  have h2 := one_sub_lsh_pos hε (j + 1)
  have h3 := one_lt_gammaQ hε
  nlinarith [mul_pos (sub_pos.2 h3) h2]

lemma lsh_strictMono (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) : StrictMono (lsh ε) :=
  strictMono_nat_of_lt_succ (lsh_lt_succ hε)

/-- The window ratio: `1 − l_{k−1} = γ (1 − l_k)` for `k ≥ 1`. -/
lemma one_sub_lsh_pred (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) {k : ℕ} (hk : 1 ≤ k) :
    1 - lsh ε (k - 1) = gammaQ ε * (1 - lsh ε k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact one_sub_lsh_succ hε j

lemma one_div_one_sub_lsh (j : ℕ) : 1 - 1 / (1 / (1 - lsh ε j)) = lsh ε j := by
  rw [one_div_one_div]
  ring

/-- The regime of the proof of `prop:querylb` after its first sentence: `ε ∈ (0, 1/2)`,
`ᾱ ∈ (0, 1)` and `ᾱ ≥ ε` ("So let `ᾱ ≥ ε`"), so that `1/(1 − ε) ≤ 1/(1 − ᾱ)`. -/
structure Regime (ε ᾱ : ℝ) : Prop where
  ε_pos : 0 < ε
  ε_lt : ε < 1 / 2
  ᾱ_pos : 0 < ᾱ
  ᾱ_lt : ᾱ < 1
  ε_le : ε ≤ ᾱ

lemma Regime.one_sub_pos (R : Regime ε ᾱ) : 0 < 1 - ᾱ := sub_pos.2 R.ᾱ_lt

lemma Regime.one_sub_lt (R : Regime ε ᾱ) : 1 - ᾱ < 1 := by linarith [R.ᾱ_pos]

lemma Regime.one_sub_le (R : Regime ε ᾱ) : 1 - ᾱ ≤ 1 - ε := by linarith [R.ε_le]

lemma Regime.hε (R : Regime ε ᾱ) : ε ∈ Ioo (0 : ℝ) (1 / 2) := ⟨R.ε_pos, R.ε_lt⟩

/-- The shares `k` with `1 − ᾱ ≤ (1 − ε)/γ^k` are bounded, so the largest of them, `K`, exists
(not in the paper: the proof of `prop:querylb` takes the largest `K` without saying that it
exists). -/
lemma bddAbove_Kq (R : Regime ε ᾱ) : BddAbove {k : ℕ | 1 - ᾱ ≤ (1 - ε) / gammaQ ε ^ k} := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  have hγ := one_lt_gammaQ R.hε
  have hγ0 := gammaQ_pos R.hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos R.one_sub_pos h1ε) (inv_lt_one_of_one_lt₀ hγ)
  refine ⟨n, fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  have hk' : 1 - ᾱ ≤ (1 - ε) / gammaQ ε ^ k := hk
  have h1 : (1 - ε) / gammaQ ε ^ k ≤ (1 - ε) / gammaQ ε ^ n :=
    div_le_div_of_nonneg_left h1ε.le (pow_pos hγ0 n) (pow_le_pow_right₀ hγ.le hlt.le)
  have h2 : (1 - ε) / gammaQ ε ^ n < 1 - ᾱ := by
    rw [inv_pow, lt_div_iff₀ h1ε] at hn
    rw [div_lt_iff₀ (pow_pos hγ0 n)]
    have := (inv_mul_lt_iff₀ (pow_pos hγ0 n)).1
      (by linarith [hn] : (gammaQ ε ^ n)⁻¹ * (1 - ε) < 1 - ᾱ)
    linarith
  linarith

/-- `(1 − ε) γ^{−K} ≥ 1 − ᾱ`. -/
lemma Kq_mem (R : Regime ε ᾱ) : 1 - ᾱ ≤ (1 - ε) / gammaQ ε ^ Kq ε ᾱ :=
  Nat.sSup_mem ⟨0, show 1 - ᾱ ≤ (1 - ε) / gammaQ ε ^ 0 by
    rw [pow_zero, div_one]; exact R.one_sub_le⟩ (bddAbove_Kq R)

/-- The maximality of `K`: `(1 − ε) γ^{−K−1} < 1 − ᾱ`. -/
lemma Kq_succ (R : Regime ε ᾱ) : (1 - ε) / gammaQ ε ^ (Kq ε ᾱ + 1) < 1 - ᾱ := by
  by_contra hle
  push Not at hle
  have := le_csSup (bddAbove_Kq R) (show Kq ε ᾱ + 1 ∈ {k : ℕ | 1 - ᾱ ≤ (1 - ε) / gammaQ ε ^ k}
    from hle)
  exact absurd this (by unfold Kq; omega)

/-- `prop:querylb`, step (1): "Then `ε = l_0 < l_1 < ⋯ < l_K ≤ ᾱ`": `l_K ≤ ᾱ`. -/
lemma lsh_Kq_le (R : Regime ε ᾱ) : lsh ε (Kq ε ᾱ) ≤ ᾱ := by
  have := Kq_mem R
  rw [lsh]
  linarith

/-- `prop:querylb`, step (6): "By the choice of `K`, `(1 − ε)γ^{−K−1} < 1 − ᾱ`, so
`K + 1 > ln((1 − ε)/(1 − ᾱ))/ln(1 + 2ε)`. Here `ln((1 − ε)/(1 − ᾱ)) ≥ 0`, `ln(1 + 2ε) ≤ 2ε`, and
`ln(1/(1 − ε)) ≤ ε/(1 − ε) ≤ 2ε`, as `ε < 1/2`. So
`q ≥ K − 1 > (ln(1/(1 − ᾱ)) − 2ε)/(2ε) − 2 = ln(1/(1 − ᾱ))/(2ε) − 3`" (the part
`K − 1 > …`; `q ≥ K − 1` is step (5)).
-/
lemma Kq_bound (R : Regime ε ᾱ) : Real.log (1 / (1 - ᾱ)) / (2 * ε) - 3 < (Kq ε ᾱ : ℝ) - 1 := by
  have hε0 := R.ε_pos
  have h1ᾱ := R.one_sub_pos
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  have hγ0 : 0 < gammaQ ε := gammaQ_pos R.hε
  have hγ : 0 < Real.log (gammaQ ε) := Real.log_pos (one_lt_gammaQ R.hε)
  -- "`(1 − ε)γ^{−K−1} < 1 − ᾱ`, so `K + 1 > ln((1 − ε)/(1 − ᾱ))/ln(1 + 2ε)`"
  have hK1 : Real.log ((1 - ε) / (1 - ᾱ)) / Real.log (gammaQ ε) < (Kq ε ᾱ : ℝ) + 1 := by
    have h := Kq_succ R
    rw [div_lt_iff₀ (pow_pos hγ0 _), ← div_lt_iff₀' h1ᾱ] at h
    have hl := Real.log_lt_log (div_pos h1ε h1ᾱ) h
    rw [Real.log_pow] at hl
    rw [div_lt_iff₀ hγ]
    push_cast at hl
    linarith
  -- "Here `ln((1 − ε)/(1 − ᾱ)) ≥ 0`"
  have hL0 : 0 ≤ Real.log ((1 - ε) / (1 - ᾱ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ h1ᾱ]; linarith [R.one_sub_le])
  -- "`ln(1 + 2ε) ≤ 2ε`"
  have hγle : Real.log (gammaQ ε) ≤ 2 * ε := by
    have := Real.log_le_sub_one_of_pos hγ0
    unfold gammaQ at this ⊢
    linarith
  -- "and `ln(1/(1 − ε)) ≤ ε/(1 − ε) ≤ 2ε`, as `ε < 1/2`"
  have hlog1 : Real.log (1 / (1 - ε)) ≤ 2 * ε := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 - ε) by positivity)
    have h2 : 1 / (1 - ε) - 1 = ε / (1 - ε) := by field_simp; ring
    have h3 : ε / (1 - ε) ≤ 2 * ε := by
      rw [div_le_iff₀ h1ε]
      nlinarith [R.ε_lt]
    linarith
  -- `K + 1 > ln((1 − ε)/(1 − ᾱ))/(2ε) = (ln(1/(1 − ᾱ)) − ln(1/(1 − ε)))/(2ε)`
  -- `≥ (ln(1/(1 − ᾱ)) − 2ε)/(2ε)`
  have h2ε : (0 : ℝ) < 2 * ε := by positivity
  have hstep : Real.log ((1 - ε) / (1 - ᾱ)) / (2 * ε) ≤
      Real.log ((1 - ε) / (1 - ᾱ)) / Real.log (gammaQ ε) :=
    div_le_div_of_nonneg_left hL0 hγ hγle
  have hsplit :
      Real.log ((1 - ε) / (1 - ᾱ)) = Real.log (1 / (1 - ᾱ)) - Real.log (1 / (1 - ε)) := by
    rw [Real.log_div h1ε.ne' h1ᾱ.ne', Real.log_div one_ne_zero h1ᾱ.ne',
      Real.log_div one_ne_zero h1ε.ne', Real.log_one]
    ring
  have h3 :
      (Real.log (1 / (1 - ᾱ)) - 2 * ε) / (2 * ε) ≤ Real.log ((1 - ε) / (1 - ᾱ)) / (2 * ε) := by
    rw [hsplit]
    exact div_le_div_of_nonneg_right (by linarith) h2ε.le
  have e :
      (Real.log (1 / (1 - ᾱ)) - 2 * ε) / (2 * ε) - 2 = Real.log (1 / (1 - ᾱ)) / (2 * ε) - 3 := by
    field_simp
    ring
  linarith

/-- `prop:querylb`, step (5): "The windows `[l_{k−1}, l_k)`, `k ∈ [K]`, are pairwise disjoint". -/
lemma window_disjoint (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hij : i ≠ j) :
    Disjoint (Ico (lsh ε (i - 1)) (lsh ε i)) (Ico (lsh ε (j - 1)) (lsh ε j)) := by
  have hmono := (lsh_strictMono hε).monotone
  rcases lt_or_gt_of_ne hij with h | h
  · rw [Set.disjoint_left]
    intro a ha ha'
    have : lsh ε i ≤ lsh ε (j - 1) := hmono (by omega)
    linarith [ha.2, ha'.1]
  · rw [Set.disjoint_left]
    intro a ha ha'
    have : lsh ε j ≤ lsh ε (i - 1) := hmono (by omega)
    linarith [ha.1, ha'.2]

/-- `prop:querylb`, step (5): "The windows … are pairwise disjoint, so at most `q + 1` of them
contain one of the shares `α_1, …, α_q, α̂`. Suppose that `q + 1 < K`. Then some window
`[l_{k−1}, l_k)` contains none of them." -/
lemma exists_free_window (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (P : List ℝ) {K : ℕ}
    (hK : P.length < K) :
    ∃ k, 1 ≤ k ∧ k ≤ K ∧ ∀ a ∈ P, a ∉ Ico (lsh ε (k - 1)) (lsh ε k) := by
  classical
  -- the windows that contain one of the points
  set W := (Finset.Icc 1 K).filter fun k => ∃ a ∈ P, a ∈ Ico (lsh ε (k - 1)) (lsh ε k)
  -- each point lies in at most one window, as the windows are pairwise disjoint
  have hone : ∀ a ∈ P.toFinset,
      ((Finset.Icc 1 K).filter fun k => a ∈ Ico (lsh ε (k - 1)) (lsh ε k)).card ≤ 1 := by
    intro a _
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hne
    have hi' := Finset.mem_filter.1 hi
    have hj' := Finset.mem_filter.1 hj
    exact Set.disjoint_left.1 (window_disjoint hε (Finset.mem_Icc.1 hi'.1).1
      (Finset.mem_Icc.1 hj'.1).1 hne) hi'.2 hj'.2
  have hW : W ⊆ P.toFinset.biUnion fun a =>
      (Finset.Icc 1 K).filter fun k => a ∈ Ico (lsh ε (k - 1)) (lsh ε k) := by
    intro k hk
    obtain ⟨hkK, a, haP, ha⟩ := Finset.mem_filter.1 hk
    exact Finset.mem_biUnion.2 ⟨a, List.mem_toFinset.2 haP, Finset.mem_filter.2 ⟨hkK, ha⟩⟩
  -- so at most `q + 1 = |P|` windows contain a point
  have hcard : W.card < (Finset.Icc 1 K).card := by
    calc W.card ≤ (P.toFinset.biUnion fun a =>
            (Finset.Icc 1 K).filter fun k => a ∈ Ico (lsh ε (k - 1)) (lsh ε k)).card :=
          Finset.card_le_card hW
      _ ≤ ∑ a ∈ P.toFinset,
            ((Finset.Icc 1 K).filter fun k => a ∈ Ico (lsh ε (k - 1)) (lsh ε k)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ P.toFinset, 1 := Finset.sum_le_sum hone
      _ = P.toFinset.card := by simp
      _ ≤ P.length := P.toFinset_card_le
      _ < K := hK
      _ = (Finset.Icc 1 K).card := by simp
  obtain ⟨k, hk, hkW⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.1 hk
  refine ⟨k, hk1, hkK, fun a ha haw => hkW (Finset.mem_filter.2 ⟨hk, a, ha, haw⟩)⟩

/-! ### `prop:querylb`: the base instance `I₀` -/

/-- The marginal cost `c₀'` of the base instance `I₀` (appE-halfrule.tex:145): `ε(1 − ε) y` for
`0 ≤ y ≤ 1/(1 − ε)`, `1 − 1/y` for `1/(1 − ε) ≤ y ≤ 1/(1 − ᾱ)`, and `ᾱ` for `y ≥ 1/(1 − ᾱ)`. -/
def g0 (ε ᾱ : ℝ) (y : ℝ) : ℝ :=
  if y ≤ 1 / (1 - ε) then ε * (1 - ε) * y else if y ≤ 1 / (1 - ᾱ) then 1 - 1 / y else ᾱ

/-- The best response `x₀` of `I₀` (appE-halfrule.tex:151): `α/(ε(1 − ε))` for `0 ≤ α ≤ ε`,
`1/(1 − α)` for `ε ≤ α ≤ ᾱ`, and `1/(1 − ᾱ)` for `ᾱ ≤ α ≤ 1`. -/
def x0 (ε ᾱ : ℝ) (α : ℝ) : ℝ :=
  if α ≤ ε then α / (ε * (1 - ε)) else if α ≤ ᾱ then 1 / (1 - α) else 1 / (1 - ᾱ)

/-- The cost `c(x) = c₁(x_e)` of one element as a function on `ℝ^{e}`. -/
def unitCost (c₁ : ℝ → ℝ) (v : Unit → ℝ) : ℝ := c₁ (v ())

/-- A cost `∫_0^z c'` with `c' ≥ 0` nondecreasing is a cost of the model, convex on `ℝ^{e}_{≥0}`. -/
lemma unitCost_cost {g : ℝ → ℝ} (hg : MonotoneOn g (Ici 0)) (hg0 : ∀ y, 0 ≤ y → 0 ≤ g y) :
    IsCost (unitCost (cost g)) ∧ ConvexOn ℝ (Ici 0) (unitCost (cost g)) := by
  refine ⟨⟨fun v hv => cost_nonneg hg0 (hv ()), by simp [unitCost, cost_zero]⟩,
    ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩⟩
  have h := (convexOn_cost hg).2 (mem_Ici.2 ((mem_Ici.1 hx) ())) (mem_Ici.2 ((mem_Ici.1 hy) ()))
    ha hb hab
  simpa [unitCost] using h

section Instances

variable {ε ᾱ : ℝ}

lemma inv_le_inv_regime (R : Regime ε ᾱ) : 1 / (1 - ε) ≤ 1 / (1 - ᾱ) :=
  one_div_le_one_div_of_le R.one_sub_pos R.one_sub_le

lemma g0_low {y : ℝ} (hy : y ≤ 1 / (1 - ε)) : g0 ε ᾱ y = ε * (1 - ε) * y := by
  unfold g0
  rw [ite_eq_left hy]

/-- "The pieces agree where they meet": the middle piece. -/
lemma g0_mid (R : Regime ε ᾱ) {y : ℝ} (h1 : 1 / (1 - ε) ≤ y) (h2 : y ≤ 1 / (1 - ᾱ)) :
    g0 ε ᾱ y = 1 - 1 / y := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  unfold g0
  split_ifs with h
  · have hy : y = 1 / (1 - ε) := le_antisymm h h1
    rw [hy, one_div_one_div]
    field_simp
    ring
  · rfl

/-- "The pieces agree where they meet": the last piece. -/
lemma g0_high (R : Regime ε ᾱ) {y : ℝ} (hy : 1 / (1 - ᾱ) ≤ y) : g0 ε ᾱ y = ᾱ := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  have hab := inv_le_inv_regime R
  unfold g0
  split_ifs with h h'
  · -- `y = 1/(1 − ε) = 1/(1 − ᾱ)`, so `ᾱ = ε`
    have hy1 : y = 1 / (1 - ε) := le_antisymm h (hab.trans hy)
    have hᾱ : ᾱ = ε := by
      have : 1 / (1 - ᾱ) = 1 / (1 - ε) := le_antisymm (hy.trans h) hab
      rw [one_div, one_div, inv_inj] at this
      linarith
    rw [hy1, hᾱ]
    field_simp
  · rw [le_antisymm h' hy, one_div_one_div]
    ring
  · rfl

/-- `c₀' ≤ ᾱ` on `[0, ∞)`. -/
lemma g0_le (R : Regime ε ᾱ) (y : ℝ) : g0 ε ᾱ y ≤ ᾱ := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  rcases le_or_gt y (1 / (1 - ε)) with h1 | h1
  · rw [g0_low h1]
    have : y * (1 - ε) ≤ 1 := by rwa [le_div_iff₀ h1ε] at h1
    nlinarith [R.one_sub_le, R.ε_pos]
  · rcases le_or_gt y (1 / (1 - ᾱ)) with h2 | h2
    · rw [g0_mid R h1.le h2]
      have hy0 : 0 < y := lt_of_lt_of_le (by positivity) h1.le
      have := (le_one_div R.one_sub_pos hy0).2 h2
      linarith
    · rw [g0_high R h2.le]

/-- `c₀' ≥ ε` from `1/(1 − ε)` on. -/
lemma ε_le_g0 (R : Regime ε ᾱ) {y : ℝ} (hy : 1 / (1 - ε) ≤ y) : ε ≤ g0 ε ᾱ y := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  rcases le_or_gt y (1 / (1 - ᾱ)) with h2 | h2
  · rw [g0_mid R hy h2]
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
    have := (one_div_le hy0 h1ε).2 hy
    linarith
  · rw [g0_high R h2.le]
    linarith [R.one_sub_le]

/-- `prop:querylb`, step (2): "The pieces agree where they meet, so `c₀'` is continuous, …". -/
lemma continuousOn_g0 (R : Regime ε ᾱ) : ContinuousOn (g0 ε ᾱ) (Ici 0) := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  have hab := inv_le_inv_regime R
  have hpos : 0 < 1 / (1 - ε) := by positivity
  have hset : Ici (0 : ℝ) =
      (Icc 0 (1 / (1 - ε)) ∪ Icc (1 / (1 - ε)) (1 / (1 - ᾱ))) ∪ Ici (1 / (1 - ᾱ)) := by
    ext y
    simp only [mem_Ici, mem_union, mem_Icc]
    constructor
    · intro hy
      rcases le_or_gt y (1 / (1 - ε)) with h | h
      · exact Or.inl (Or.inl ⟨hy, h⟩)
      · rcases le_or_gt y (1 / (1 - ᾱ)) with h' | h'
        · exact Or.inl (Or.inr ⟨h.le, h'⟩)
        · exact Or.inr h'.le
    · rintro ((⟨h, -⟩ | ⟨h, -⟩) | h)
      · exact h
      · exact hpos.le.trans h
      · exact (hpos.le.trans hab).trans h
  rw [hset]
  refine ContinuousOn.union_of_isClosed (ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc
    isClosed_Icc) ?_ (isClosed_Icc.union isClosed_Icc) isClosed_Ici
  · exact (continuousOn_const.mul continuousOn_id).congr fun y hy => g0_low hy.2
  · refine (continuousOn_const.sub (continuousOn_const.div continuousOn_id fun y hy => ?_)).congr
      fun y hy => g0_mid R hy.1 hy.2
    exact (lt_of_lt_of_le hpos hy.1).ne'
  · exact continuousOn_const.congr fun y hy => g0_high R hy

/-- `prop:querylb`, step (2): "… `c₀'` is … nonnegative …". -/
lemma g0_nonneg (R : Regime ε ᾱ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ g0 ε ᾱ y := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  rcases le_or_gt y (1 / (1 - ε)) with h1 | h1
  · rw [g0_low h1]
    exact mul_nonneg (mul_nonneg R.ε_pos.le h1ε.le) hy
  · linarith [ε_le_g0 R h1.le, R.ε_pos]

/-- `prop:querylb`, step (2): "… and nondecreasing". -/
lemma monotoneOn_g0 (R : Regime ε ᾱ) : MonotoneOn (g0 ε ᾱ) (Ici 0) := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  intro y hy y' hy' hyy'
  have hy0 : (0 : ℝ) ≤ y := hy
  rcases le_or_gt y' (1 / (1 - ε)) with h' | h'
  · -- both in the first piece
    rw [g0_low (hyy'.trans h'), g0_low h']
    exact mul_le_mul_of_nonneg_left hyy' (mul_nonneg R.ε_pos.le h1ε.le)
  · rcases le_or_gt y (1 / (1 - ε)) with h | h
    · -- `y` in the first piece: `c₀'(y) ≤ ε ≤ c₀'(y')`
      rw [g0_low h]
      have : y * (1 - ε) ≤ 1 := by rwa [le_div_iff₀ h1ε] at h
      nlinarith [ε_le_g0 R h'.le, R.ε_pos]
    · rcases le_or_gt y' (1 / (1 - ᾱ)) with h2' | h2'
      · -- both in the middle piece
        rw [g0_mid R h.le (hyy'.trans h2'), g0_mid R h'.le h2']
        have hy0' : 0 < y := lt_of_lt_of_le (by positivity) h.le
        linarith [one_div_le_one_div_of_le hy0' hyy']
      · rw [g0_high R h2'.le]
        exact g0_le R y

lemma x0_low {α : ℝ} (h : α ≤ ε) : x0 ε ᾱ α = α / (ε * (1 - ε)) := by
  unfold x0
  rw [ite_eq_left h]

lemma x0_mid (R : Regime ε ᾱ) {α : ℝ} (h1 : ε ≤ α) (h2 : α ≤ ᾱ) :
    x0 ε ᾱ α = 1 / (1 - α) := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  unfold x0
  split_ifs with h
  · rw [le_antisymm h h1]
    field_simp [R.ε_pos.ne']
  · rfl

lemma x0_high (R : Regime ε ᾱ) {α : ℝ} (h : ᾱ ≤ α) : x0 ε ᾱ α = 1 / (1 - ᾱ) := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  unfold x0
  split_ifs with h1 h2
  · -- `α = ε = ᾱ`
    have hα : α = ε := le_antisymm h1 (R.ε_le.trans h)
    have hᾱ : ᾱ = ε := le_antisymm (h.trans h1) R.ε_le
    rw [hα, hᾱ]
    field_simp [R.ε_pos.ne']
  · rw [le_antisymm h2 h]
  · rfl

lemma x0_mem (R : Regime ε ᾱ) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    x0 ε ᾱ α ∈ Icc 0 (1 / (1 - ᾱ)) := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  have hab := inv_le_inv_regime R
  rcases le_or_gt α ε with h1 | h1
  · rw [x0_low h1]
    have hpos : 0 < ε * (1 - ε) := mul_pos R.ε_pos h1ε
    refine ⟨div_nonneg hα.1 hpos.le, le_trans ?_ hab⟩
    rw [div_le_div_iff₀ hpos h1ε]
    nlinarith [mul_le_mul_of_nonneg_right h1 h1ε.le]
  · rcases le_or_gt α ᾱ with h2 | h2
    · rw [x0_mid R h1.le h2]
      have h1α : 0 < 1 - α := by linarith [R.one_sub_pos]
      exact ⟨(one_div_pos.2 h1α).le, one_div_le_one_div_of_le R.one_sub_pos (by linarith)⟩
    · rw [x0_high R h2.le]
      exact ⟨(one_div_pos.2 R.one_sub_pos).le, le_rfl⟩

/-- `eq:E-largest` for `I₀`, the left part: `c₀' ≤ α` on `[0, x₀(α))` (not in the paper: it
leaves the evaluation of `eq:E-largest` for `I₀` implicit). -/
lemma g0_le_of_lt_x0 (R : Regime ε ᾱ) {α : ℝ} {y : ℝ} (hy : y ∈ Ico 0 (x0 ε ᾱ α)) :
    g0 ε ᾱ y ≤ α := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  obtain ⟨hy0, hyx⟩ := hy
  rcases le_or_gt α ε with h1 | h1
  · -- `x₀(α) = α/(ε(1 − ε)) ≤ 1/(1 − ε)`, `c₀'(y) = ε(1 − ε) y < α`
    rw [x0_low h1] at hyx
    have hpos : 0 < ε * (1 - ε) := mul_pos R.ε_pos h1ε
    have hya : y ≤ 1 / (1 - ε) := by
      refine le_trans hyx.le ?_
      rw [div_le_div_iff₀ hpos h1ε]
      nlinarith [mul_le_mul_of_nonneg_right h1 h1ε.le]
    rw [g0_low hya]
    have := mul_lt_mul_of_pos_left hyx hpos
    rw [mul_div_cancel₀ _ hpos.ne'] at this
    linarith
  · rcases le_or_gt α ᾱ with h2 | h2
    · -- `x₀(α) = 1/(1 − α)`
      rw [x0_mid R h1.le h2] at hyx
      have h1α : 0 < 1 - α := by linarith [R.one_sub_pos]
      rcases le_or_gt y (1 / (1 - ε)) with hya | hya
      · rw [g0_low hya]
        have : y * (1 - ε) ≤ 1 := by rwa [le_div_iff₀ h1ε] at hya
        nlinarith [R.ε_pos]
      · have hy0' : 0 < y := lt_of_lt_of_le (by positivity) hya.le
        have hyb : y ≤ 1 / (1 - ᾱ) :=
          le_trans hyx.le (one_div_le_one_div_of_le R.one_sub_pos (by linarith))
        rw [g0_mid R hya.le hyb]
        have := (lt_one_div hy0' h1α).1 hyx
        linarith
    · -- `α > ᾱ`: `c₀' ≤ ᾱ < α`
      linarith [g0_le R y]

/-- `eq:E-largest` for `I₀`, the right part: `c₀' > α` on `(x₀(α), 1/(1 − ᾱ)]`, for `α ∈ [0, 1)`
(not in the paper: it leaves the evaluation of `eq:E-largest` for `I₀` implicit). -/
lemma lt_g0_of_x0_lt (R : Regime ε ᾱ) {α : ℝ} (hα : α ∈ Ico (0 : ℝ) 1) {y : ℝ}
    (hy : y ∈ Ioc (x0 ε ᾱ α) (1 / (1 - ᾱ))) : α < g0 ε ᾱ y := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  obtain ⟨hxy, hyb⟩ := hy
  have hx0 := (x0_mem R ⟨hα.1, hα.2.le⟩).1
  have hy0 : 0 < y := lt_of_le_of_lt hx0 hxy
  rcases le_or_gt α ε with h1 | h1
  · rw [x0_low h1] at hxy
    rcases le_or_gt y (1 / (1 - ε)) with hya | hya
    · rw [g0_low hya]
      have hpos : 0 < ε * (1 - ε) := mul_pos R.ε_pos h1ε
      have := mul_lt_mul_of_pos_left hxy hpos
      rwa [mul_div_cancel₀ _ hpos.ne'] at this
    · -- `c₀'(y) = 1 − 1/y > ε ≥ α`
      rw [g0_mid R hya.le hyb]
      have := (one_div_lt hy0 h1ε).2 hya
      linarith
  · rcases le_or_gt α ᾱ with h2 | h2
    · rw [x0_mid R h1.le h2] at hxy
      have h1α : 0 < 1 - α := by linarith [R.one_sub_pos]
      have hay : 1 / (1 - ε) ≤ y :=
        le_trans (one_div_le_one_div_of_le h1α (by linarith)) hxy.le
      rw [g0_mid R hay hyb]
      have := (one_div_lt hy0 h1α).2 hxy
      linarith
    · rw [x0_high R h2.le] at hxy
      exact absurd hyb (not_le.2 hxy)

/-- `prop:querylb`, step (3): "By `eq:E-largest`, the best response of `I₀` is `x₀`", at every
share `α ∈ [0, 1]` (for `α < 1` by `eq:E-largest`, at `α = 1` the maximizer is unique). -/
lemma isPBR_x0 (R : Regime ε ᾱ) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) {z : ℝ} :
    IsPBR (cost (g0 ε ᾱ)) (1 / (1 - ᾱ)) α z ↔ z = x0 ε ᾱ α := by
  have hT : (0 : ℝ) ≤ 1 / (1 - ᾱ) := by have := R.one_sub_pos; positivity
  rcases hα.2.lt_or_eq with hlt | rfl
  · rw [isPBR_iff_eq_largest (monotoneOn_g0 R) hT hlt,
      largest_eq hT (x0_mem R hα) (fun y hy => g0_le_of_lt_x0 R hy)
        fun y hy => lt_g0_of_x0_lt R ⟨hα.1, hlt⟩ hy]
  · rw [isPBR_one_iff (monotoneOn_g0 R) hT fun y hy => (g0_le R y).trans_lt
      (by linarith [R.one_sub_pos]), x0_high R (by linarith [R.one_sub_pos])]

/-! ### `prop:querylb`: the variants `I_k` of `I₀` -/

/-- The marginal cost `c_k'` of `I_k` (appE-halfrule.tex:147): `c₀'`, except
`c_k' = l_{k−1}` on `[1/(1 − l_{k−1}), 1/(1 − l_k))`. -/
def gk (ε ᾱ : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  if 1 / (1 - lsh ε (k - 1)) ≤ y ∧ y < 1 / (1 - lsh ε k) then lsh ε (k - 1) else g0 ε ᾱ y

/-- The best response `x_k` of `I_k` (appE-halfrule.tex:153): `x₀` outside the window
`[l_{k−1}, l_k)`, and `1/(1 − l_k)` on it. -/
def xk (ε ᾱ : ℝ) (k : ℕ) (α : ℝ) : ℝ :=
  if α ∈ Ico (lsh ε (k - 1)) (lsh ε k) then 1 / (1 - lsh ε k) else x0 ε ᾱ α

variable {k : ℕ}

/-- `x_k = x₀` outside the window. -/
lemma xk_eq_x0 {α : ℝ} (hα : α ∉ Ico (lsh ε (k - 1)) (lsh ε k)) : xk ε ᾱ k α = x0 ε ᾱ α := by
  unfold xk
  rw [ite_eq_right hα]

/-- `prop:querylb`, step (1): the window `[l_{k−1}, l_k)`, `k ∈ [K]`, lies in `[ε, ᾱ]`. -/
lemma window_sub (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) :
    ε ≤ lsh ε (k - 1) ∧ lsh ε (k - 1) < lsh ε k ∧ lsh ε k ≤ ᾱ := by
  have hmono := (lsh_strictMono R.hε).monotone
  refine ⟨?_, lsh_strictMono R.hε (by omega), (hmono hkK).trans (lsh_Kq_le R)⟩
  have := hmono (Nat.zero_le (k - 1))
  rwa [lsh_zero] at this

/-- `prop:querylb`, step (2): "`[1/(1 − l_{k−1}), 1/(1 − l_k)) ⊆ [1/(1 − ε), 1/(1 − ᾱ)]`". -/
lemma window_actions (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) :
    1 / (1 - ε) ≤ 1 / (1 - lsh ε (k - 1)) ∧ 1 / (1 - lsh ε (k - 1)) < 1 / (1 - lsh ε k) ∧
      1 / (1 - lsh ε k) ≤ 1 / (1 - ᾱ) := by
  obtain ⟨hw1, hw2, hw3⟩ := window_sub R hk1 hkK
  have hp := one_sub_lsh_pos R.hε k
  exact ⟨one_div_le_one_div_of_le (one_sub_lsh_pos R.hε (k - 1)) (by linarith),
    one_div_lt_one_div_of_lt hp (by linarith), one_div_le_one_div_of_le R.one_sub_pos (by linarith)⟩

/-- `prop:querylb`, step (2): "There `c₀'` increases from `l_{k−1}`":
`c₀'(1/(1 − l_{k−1})) = l_{k−1}`. -/
lemma g0_p (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) :
    g0 ε ᾱ (1 / (1 - lsh ε (k - 1))) = lsh ε (k - 1) := by
  obtain ⟨h1, h2, h3⟩ := window_actions R hk1 hkK
  rw [g0_mid R h1 (h2.le.trans h3), one_div_one_sub_lsh]

/-- `prop:querylb`, step (2): "… to `l_k`": `c₀'(1/(1 − l_k)) = l_k`. -/
lemma g0_q (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) :
    g0 ε ᾱ (1 / (1 - lsh ε k)) = lsh ε k := by
  obtain ⟨h1, h2, h3⟩ := window_actions R hk1 hkK
  rw [g0_mid R (h1.trans h2.le) h3, one_div_one_sub_lsh]

lemma one_div_one_sub_lsh_pos (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (j : ℕ) :
    0 < 1 / (1 - lsh ε j) :=
  one_div_pos.2 (one_sub_lsh_pos hε j)

/-- `c₀' < l_{k−1}` before `1/(1 − l_{k−1})`. -/
lemma g0_lt_p (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {y : ℝ}
    (hy : y ∈ Ico 0 (1 / (1 - lsh ε (k - 1)))) : g0 ε ᾱ y < lsh ε (k - 1) := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  obtain ⟨hw1, -, -⟩ := window_sub R hk1 hkK
  obtain ⟨ha, -, -⟩ := window_actions R hk1 hkK
  rcases lt_or_ge y (1 / (1 - ε)) with h | h
  · rw [g0_low h.le]
    have : y * (1 - ε) < 1 := by rwa [lt_div_iff₀ h1ε] at h
    nlinarith [R.ε_pos]
  · have hy0 : 0 < y := lt_of_lt_of_le (by positivity) h
    rw [g0_mid R h (hy.2.le.trans ((window_actions R hk1 hkK).2.1.le.trans
      (window_actions R hk1 hkK).2.2))]
    have := (one_div_lt_one_div_of_lt hy0 hy.2)
    rw [one_div_one_div] at this
    linarith

/-- `c₀' > l_k` after `1/(1 − l_k)`. -/
lemma lsh_lt_g0 (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {y : ℝ}
    (hy : y ∈ Ioc (1 / (1 - lsh ε k)) (1 / (1 - ᾱ))) : lsh ε k < g0 ε ᾱ y := by
  obtain ⟨h1, h2, -⟩ := window_actions R hk1 hkK
  have hp := one_sub_lsh_pos R.hε k
  have hy0 : 0 < y := lt_of_lt_of_le (one_div_one_sub_lsh_pos R.hε k) hy.1.le
  rw [g0_mid R ((h1.trans h2.le).trans hy.1.le) hy.2]
  have := (one_div_lt hy0 hp).2 hy.1
  linarith

/-- `c_k' ≤ c₀'` on `[0, ∞)`. -/
lemma gk_le_g0 (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {y : ℝ} (hy : 0 ≤ y) :
    gk ε ᾱ k y ≤ g0 ε ᾱ y := by
  unfold gk
  split_ifs with hw
  · rw [← g0_p R hk1 hkK]
    exact monotoneOn_g0 R (one_div_one_sub_lsh_pos R.hε (k - 1)).le hy hw.1
  · exact le_rfl

/-- `prop:querylb`, step (2): "There `c₀'` increases from `l_{k−1}` to `l_k`, so `c_k'` is still
nondecreasing". -/
lemma monotoneOn_gk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) :
    MonotoneOn (gk ε ᾱ k) (Ici 0) := by
  have hg := monotoneOn_g0 R
  have hp0 := (one_div_one_sub_lsh_pos R.hε (k - 1)).le
  -- "There `c₀'` increases from `l_{k−1}` to `l_k`"
  have hgp := g0_p R hk1 hkK
  have _hgq := g0_q R hk1 hkK
  intro y hy y' hy' hyy'
  unfold gk
  by_cases h1 : 1 / (1 - lsh ε (k - 1)) ≤ y ∧ y < 1 / (1 - lsh ε k)
  · by_cases h2 : 1 / (1 - lsh ε (k - 1)) ≤ y' ∧ y' < 1 / (1 - lsh ε k)
    · simp only [ite_eq_left h1, ite_eq_left h2, le_refl]
    · -- `y` in the action window, `y'` after it
      rw [ite_eq_left h1, ite_eq_right h2, ← hgp]
      exact hg hp0 hy' (h1.1.trans hyy')
  · by_cases h2 : 1 / (1 - lsh ε (k - 1)) ≤ y' ∧ y' < 1 / (1 - lsh ε k)
    · -- `y` before the action window, `y'` in it
      have hyp : y < 1 / (1 - lsh ε (k - 1)) := by
        by_contra hc
        exact h1 ⟨not_lt.1 hc, lt_of_le_of_lt hyy' h2.2⟩
      rw [ite_eq_right h1, ite_eq_left h2, ← hgp]
      exact hg hy hp0 hyp.le
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact hg hy hy' hyy'

/-- `prop:querylb`, step (2): `c_k' ≥ 0`. -/
lemma gk_nonneg (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ gk ε ᾱ k y := by
  unfold gk
  split_ifs
  · linarith [(window_sub R hk1 hkK).1, R.ε_pos]
  · exact g0_nonneg R hy

/-- `x₀(α) ≥ 1/(1 − l_k)` for `α ≥ l_k`. -/
lemma x0_ge_q (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {α : ℝ}
    (hα : α ∈ Icc (lsh ε k) 1) : 1 / (1 - lsh ε k) ≤ x0 ε ᾱ α := by
  obtain ⟨hw1, hw2, hw3⟩ := window_sub R hk1 hkK
  rcases le_or_gt α ᾱ with h | h
  · rw [x0_mid R (by linarith [hα.1]) h]
    exact one_div_le_one_div_of_le (by linarith [R.one_sub_pos]) (by linarith [hα.1])
  · rw [x0_high R h.le]
    exact (window_actions R hk1 hkK).2.2

lemma xk_mem (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) : xk ε ᾱ k α ∈ Icc 0 (1 / (1 - ᾱ)) := by
  unfold xk
  split_ifs
  · exact ⟨(one_div_one_sub_lsh_pos R.hε k).le, (window_actions R hk1 hkK).2.2⟩
  · exact x0_mem R hα

/-- `prop:querylb`, step (3): "that of `I_k` is the function `x_k`", for `α ∈ [0, 1)`:
`eq:E-largest` with `c_k'` (not in the paper: it leaves the evaluation of the supremum of
`eq:E-largest` for `I_k` implicit). -/
lemma largest_gk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {α : ℝ}
    (hα : α ∈ Ico (0 : ℝ) 1) : largest (gk ε ᾱ k) (1 / (1 - ᾱ)) α = xk ε ᾱ k α := by
  have hT : (0 : ℝ) ≤ 1 / (1 - ᾱ) := by have := R.one_sub_pos; positivity
  obtain ⟨hw1, hw2, hw3⟩ := window_sub R hk1 hkK
  obtain ⟨ha1, ha2, ha3⟩ := window_actions R hk1 hkK
  refine largest_eq hT (xk_mem R hk1 hkK ⟨hα.1, hα.2.le⟩) (fun y hy => ?_) (fun y hy => ?_)
  · -- `c_k' ≤ α` on `[0, x_k(α))`
    unfold xk at hy
    split_ifs at hy with hw
    · unfold gk
      split_ifs with hyw
      · exact hw.1
      · have hyp : y < 1 / (1 - lsh ε (k - 1)) := by
          by_contra hc
          exact hyw ⟨not_lt.1 hc, hy.2⟩
        exact (g0_lt_p R hk1 hkK ⟨hy.1, hyp⟩).le.trans hw.1
    · exact (gk_le_g0 R hk1 hkK hy.1).trans (g0_le_of_lt_x0 R hy)
  · -- `c_k' > α` on `(x_k(α), 1/(1 − ᾱ)]`
    unfold xk at hy
    split_ifs at hy with hw
    · have hyw : ¬ (1 / (1 - lsh ε (k - 1)) ≤ y ∧ y < 1 / (1 - lsh ε k)) :=
        fun h => absurd h.2 (not_lt.2 hy.1.le)
      unfold gk
      rw [ite_eq_right hyw]
      exact hw.2.trans (lsh_lt_g0 R hk1 hkK hy)
    · unfold gk
      split_ifs with hyw
      · -- `y` in the action window: then `α < l_{k−1}`
        rcases lt_or_ge α (lsh ε (k - 1)) with hlt | hge
        · exact hlt
        · have hαk : lsh ε k ≤ α := by
            by_contra hc
            exact hw ⟨hge, not_le.1 hc⟩
          have := x0_ge_q R hk1 hkK ⟨hαk, hα.2.le⟩
          exact absurd hyw.2 (not_lt.2 (this.trans hy.1.le))
      · exact lt_g0_of_x0_lt R hα hy

/-- `c_k' < 1`, so the maximizer of `I_k` at the share `1` is unique. -/
lemma gk_lt_one (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {y : ℝ} (hy : 0 ≤ y) :
    gk ε ᾱ k y < 1 :=
  ((gk_le_g0 R hk1 hkK hy).trans (g0_le R y)).trans_lt (by linarith [R.one_sub_pos])

/-- `prop:querylb`, step (3): the best response of `I_k` is `x_k` at every share `α ∈ [0, 1]` (for
`α < 1` by `eq:E-largest`, at `α = 1` the maximizer is unique). -/
lemma isPBR_xk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {α : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) {z : ℝ} :
    IsPBR (cost (gk ε ᾱ k)) (1 / (1 - ᾱ)) α z ↔ z = xk ε ᾱ k α := by
  have hT : (0 : ℝ) ≤ 1 / (1 - ᾱ) := by have := R.one_sub_pos; positivity
  rcases hα.2.lt_or_eq with hlt | rfl
  · rw [isPBR_iff_eq_largest (monotoneOn_gk R hk1 hkK) hT hlt, largest_gk R hk1 hkK ⟨hα.1, hlt⟩]
  · have h1 : (1 : ℝ) ∉ Ico (lsh ε (k - 1)) (lsh ε k) := fun h => by
      linarith [h.2, (window_sub R hk1 hkK).2.2, R.one_sub_pos]
    rw [isPBR_one_iff (monotoneOn_gk R hk1 hkK) hT fun y hy => gk_lt_one R hk1 hkK hy.1,
      xk_eq_x0 h1, x0_high R (by linarith [R.one_sub_pos])]

/-- `prop:querylb`, step (3): "At `α = l_{k−1}`, the maximizers of `I_k` form the interval
`[1/(1 − l_{k−1}), 1/(1 − l_k)]`" (and the tie is broken in favor of the principal, `isPBR_xk`). -/
lemma maximisers_window (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {z : ℝ}
    (hz : z ∈ Icc 0 (1 / (1 - ᾱ))) :
    (∀ y ∈ Icc 0 (1 / (1 - ᾱ)), agentU (cost (gk ε ᾱ k)) (lsh ε (k - 1)) y ≤
      agentU (cost (gk ε ᾱ k)) (lsh ε (k - 1)) z) ↔
      z ∈ Icc (1 / (1 - lsh ε (k - 1))) (1 / (1 - lsh ε k)) := by
  have hT : (0 : ℝ) ≤ 1 / (1 - ᾱ) := by have := R.one_sub_pos; positivity
  have hg := monotoneOn_gk R hk1 hkK
  obtain ⟨ha1, ha2, ha3⟩ := window_actions R hk1 hkK
  obtain ⟨hw1, hw2, hw3⟩ := window_sub R hk1 hkK
  have hp0 := one_div_one_sub_lsh_pos R.hε (k - 1)
  set p := 1 / (1 - lsh ε (k - 1))
  set v := 1 / (1 - lsh ε k)
  set α := lsh ε (k - 1)
  -- `v` is the largest maximizer (`eq:E-largest`)
  have hl : largest (gk ε ᾱ k) (1 / (1 - ᾱ)) α = v := by
    rw [largest_gk R hk1 hkK ⟨by linarith [R.ε_pos], by linarith [R.one_sub_pos]⟩]
    unfold xk
    rw [ite_eq_left ⟨le_rfl, hw2⟩]
  obtain ⟨hmax, hlarge⟩ := largest_isMax (α := α) hg hT
  rw [hl] at hmax hlarge
  -- `U_A` is constant on `[p, v]`, where `c_k' = α`, and increases strictly before `p`
  have hconst : ∀ y ∈ Icc p v, agentU (cost (gk ε ᾱ k)) α y = agentU (cost (gk ε ᾱ k)) α v := by
    intro y hy
    refine le_antisymm (hmax y ⟨hp0.le.trans hy.1, hy.2.trans ha3⟩)
      (agentU_le_of_ge hg (hp0.le.trans hy.1) hy.2 fun u hu => ?_)
    unfold gk
    rw [ite_eq_left ⟨hy.1.trans hu.1.le, hu.2⟩]
  have hbefore : ∀ y ∈ Ico 0 p, agentU (cost (gk ε ᾱ k)) α y < agentU (cost (gk ε ᾱ k)) α p := by
    intro y hy
    refine agentU_lt_of_gt hg hy.1 hy.2 fun u hu => ?_
    unfold gk
    have hu' : ¬ (p ≤ u ∧ u < v) := fun h => absurd h.1 (not_le.2 hu.2)
    rw [ite_eq_right hu']
    exact g0_lt_p R hk1 hkK ⟨hy.1.trans hu.1.le, hu.2⟩
  constructor
  · intro hzmax
    have hzv : agentU (cost (gk ε ᾱ k)) α z = agentU (cost (gk ε ᾱ k)) α v :=
      le_antisymm (hmax z hz) (hzmax v ⟨hp0.le.trans ha2.le, ha3⟩)
    refine ⟨?_, hlarge z hz hzv⟩
    by_contra hzp
    push Not at hzp
    have := hbefore z ⟨hz.1, hzp⟩
    rw [hconst p ⟨le_rfl, ha2.le⟩] at this
    exact absurd hzv this.ne
  · intro hzw y hy
    rw [hconst z hzw]
    exact hmax y hy

/-- `prop:querylb`, step (3): "In particular, `x_k ≥ x₀` and `x_k(1) = x₀(1) = 1/(1 − ᾱ)`." -/
lemma x0_le_xk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) (α : ℝ) :
    x0 ε ᾱ α ≤ xk ε ᾱ k α ∧ xk ε ᾱ k 1 = 1 / (1 - ᾱ) ∧ x0 ε ᾱ 1 = 1 / (1 - ᾱ) := by
  obtain ⟨hw1, hw2, hw3⟩ := window_sub R hk1 hkK
  have hx01 : x0 ε ᾱ 1 = 1 / (1 - ᾱ) := x0_high R (by linarith [R.one_sub_pos])
  have h1 : (1 : ℝ) ∉ Ico (lsh ε (k - 1)) (lsh ε k) := fun h => by
    linarith [h.2, R.one_sub_pos]
  refine ⟨?_, by rw [xk_eq_x0 h1, hx01], hx01⟩
  unfold xk
  split_ifs with hw
  · rw [x0_mid R (by linarith [hw.1]) (by linarith [hw.2])]
    exact one_div_le_one_div_of_le (one_sub_lsh_pos R.hε k) (by linarith [hw.2])
  · exact le_rfl

/-! ### `prop:querylb`: `ᾱ` is a share bound, and the `(1 − ε)`-optimal contracts of `I_k` -/

/-- `prop:querylb`, step (4): `U_P^{(0)}(α) = (1 − α) x₀(α)` "equals `α(1 − α)/(ε(1 − ε)) ≤ 1` on
`[0, ε]`, as `ε < 1/2`". -/
lemma profit_x0_low (R : Regime ε ᾱ) {α : ℝ} (hα : α ∈ Icc 0 ε) :
    profit (x0 ε ᾱ) α = α * (1 - α) / (ε * (1 - ε)) ∧ profit (x0 ε ᾱ) α ≤ 1 := by
  have h1ε : 0 < 1 - ε := by linarith [R.ε_lt]
  have hpos : 0 < ε * (1 - ε) := mul_pos R.ε_pos h1ε
  have e : profit (x0 ε ᾱ) α = α * (1 - α) / (ε * (1 - ε)) := by
    rw [profit, x0_low hα.2]
    ring
  refine ⟨e, ?_⟩
  rw [e, div_le_one hpos]
  have := mul_one_sub_monotoneOn ⟨hα.1, hα.2.trans R.ε_lt.le⟩ ⟨R.ε_pos.le, R.ε_lt.le⟩ hα.2
  simpa using this

/-- `prop:querylb`, step (4): `U_P^{(0)}` "equals `1` on `[ε, ᾱ]`". -/
lemma profit_x0_mid (R : Regime ε ᾱ) {α : ℝ} (hα : α ∈ Icc ε ᾱ) :
    profit (x0 ε ᾱ) α = 1 := by
  have h1α : 0 < 1 - α := by linarith [hα.2, R.one_sub_pos]
  rw [profit, x0_mid R hα.1 hα.2, mul_one_div_cancel h1α.ne']

/-- `prop:querylb`, step (4): `U_P^{(0)}` "equals `(1 − α)/(1 − ᾱ) ≤ 1` on `[ᾱ, 1]`". -/
lemma profit_x0_high (R : Regime ε ᾱ) {α : ℝ} (hα : α ∈ Icc ᾱ 1) :
    profit (x0 ε ᾱ) α = (1 - α) / (1 - ᾱ) ∧ profit (x0 ε ᾱ) α ≤ 1 := by
  have e : profit (x0 ε ᾱ) α = (1 - α) / (1 - ᾱ) := by
    rw [profit, x0_high R hα.1, mul_one_div]
  refine ⟨e, ?_⟩
  rw [e, div_le_one R.one_sub_pos]
  linarith [hα.1]

lemma profit_x0_le (R : Regime ε ᾱ) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) : profit (x0 ε ᾱ) α ≤ 1 := by
  rcases le_or_gt α ε with h1 | h1
  · exact (profit_x0_low R ⟨hα.1, h1⟩).2
  · rcases le_or_gt α ᾱ with h2 | h2
    · exact (profit_x0_mid R ⟨h1.le, h2⟩).le
    · exact (profit_x0_high R ⟨h2.le, hα.2⟩).2

/-- `prop:querylb`, step (4): "So `OPT₀ = 1` is attained on `[ε, ᾱ]`, and `I₀` is a continuous
counterpart of the equal-revenue instances of [DFGR26, Def. 5], as every share in `[ε, ᾱ]` is
optimal, each with a different best response." -/
lemma opt_x0 (R : Regime ε ᾱ) :
    OPT (profit (x0 ε ᾱ)) = 1 ∧ (∀ α ∈ Icc ε ᾱ, IsMaxOn (profit (x0 ε ᾱ)) (Icc 0 1) α) ∧
      InjOn (x0 ε ᾱ) (Icc ε ᾱ) := by
  have hεmem : ε ∈ Icc ε ᾱ := ⟨le_rfl, by linarith [R.one_sub_le]⟩
  refine ⟨IsGreatest.csSup_eq ⟨⟨ε, ⟨R.ε_pos.le, by linarith [R.ε_lt]⟩, profit_x0_mid R hεmem⟩,
    by rintro _ ⟨α, hα, rfl⟩; exact profit_x0_le R hα⟩,
    fun α hα => isMaxOn_iff.2 fun β hβ => by rw [profit_x0_mid R hα]; exact profit_x0_le R hβ,
    fun α hα β hβ h => ?_⟩
  rw [x0_mid R hα.1 hα.2, x0_mid R hβ.1 hβ.2] at h
  have h1 : 0 < 1 - α := by linarith [hα.2, R.one_sub_pos]
  have h2 : 0 < 1 - β := by linarith [hβ.2, R.one_sub_pos]
  rw [div_eq_div_iff h1.ne' h2.ne'] at h
  linarith

/-- `prop:querylb`, step (4): "Hence `ᾱ` is a share bound for all these instances", for `I₀`. -/
lemma isShareBound_x0 (R : Regime ε ᾱ) : IsShareBound (profit (x0 ε ᾱ)) ᾱ := by
  have hεmem : ε ∈ Icc (0 : ℝ) ᾱ := ⟨R.ε_pos.le, R.ε_le⟩
  refine ⟨R.ᾱ_pos.le, R.ᾱ_lt, ?_⟩
  rw [(opt_x0 R).1]
  exact IsGreatest.csSup_eq ⟨⟨ε, hεmem, profit_x0_mid R ⟨le_rfl, hεmem.2⟩⟩,
    by rintro _ ⟨α, hα, rfl⟩; exact profit_x0_le R ⟨hα.1, hα.2.trans R.ᾱ_lt.le⟩⟩

variable {k : ℕ}

/-- `prop:querylb`, step (4): "In `I_k`, the utility `U_P^{(k)}` equals `U_P^{(0)}` outside the
window". -/
lemma profit_xk_out {α : ℝ} (hα : α ∉ Ico (lsh ε (k - 1)) (lsh ε k)) :
    profit (xk ε ᾱ k) α = profit (x0 ε ᾱ) α := by
  rw [profit, profit, xk_eq_x0 hα]

/-- `prop:querylb`, step (4): "on the window `U_P^{(k)}(α) = (1 − α)/(1 − l_k)` decreases from
`U_P^{(k)}(l_{k−1}) = (1 − l_{k−1})/(1 − l_k) = γ = 1 + 2ε`". -/
lemma profit_xk_window (R : Regime ε ᾱ) (hk1 : 1 ≤ k) :
    (∀ α ∈ Ico (lsh ε (k - 1)) (lsh ε k), profit (xk ε ᾱ k) α = (1 - α) / (1 - lsh ε k)) ∧
      StrictAntiOn (profit (xk ε ᾱ k)) (Ico (lsh ε (k - 1)) (lsh ε k)) ∧
      profit (xk ε ᾱ k) (lsh ε (k - 1)) = gammaQ ε := by
  have hp := one_sub_lsh_pos R.hε k
  have hw : ∀ α ∈ Ico (lsh ε (k - 1)) (lsh ε k), profit (xk ε ᾱ k) α = (1 - α) / (1 - lsh ε k) :=
    fun α hα => by
      unfold profit xk
      rw [ite_eq_left hα, mul_one_div]
  refine ⟨hw, fun α hα β hβ hlt => ?_, ?_⟩
  · rw [hw α hα, hw β hβ]
    exact div_lt_div_of_pos_right (by linarith) hp
  · have hlo : lsh ε (k - 1) ∈ Ico (lsh ε (k - 1)) (lsh ε k) :=
      ⟨le_rfl, lsh_strictMono R.hε (by omega)⟩
    rw [hw _ hlo, one_sub_lsh_pred R.hε hk1, mul_div_assoc, div_self hp.ne', mul_one]

lemma profit_xk_le (R : Regime ε ᾱ) (hk1 : 1 ≤ k) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    profit (xk ε ᾱ k) α ≤ gammaQ ε := by
  by_cases hw : α ∈ Ico (lsh ε (k - 1)) (lsh ε k)
  · have hp := one_sub_lsh_pos R.hε k
    rw [(profit_xk_window R hk1).1 α hw, ← (profit_xk_window R hk1).2.2,
      (profit_xk_window R hk1).1 _ ⟨le_rfl, lt_of_le_of_lt hw.1 hw.2⟩]
    exact div_le_div_of_nonneg_right (by linarith [hw.1]) hp.le
  · rw [profit_xk_out hw]
    linarith [profit_x0_le R hα, one_lt_gammaQ R.hε]

/-- `prop:querylb`, step (4): "So `OPT_k = 1 + 2ε` is attained at `l_{k−1} ≤ ᾱ`": for
`B ∈ [ᾱ, 1]`, the supremum of `U_P^{(k)}` over `[0, B]` is `γ = 1 + 2ε`, attained at
`l_{k−1} ≤ ᾱ ≤ B`; for `B = 1` it is `OPT_k`. -/
lemma opt_xk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {B : ℝ}
    (hB : B ∈ Icc ᾱ 1) :
    sSup (profit (xk ε ᾱ k) '' Icc 0 B) = gammaQ ε := by
  obtain ⟨hw1, hw2, hw3⟩ := window_sub R hk1 hkK
  refine IsGreatest.csSup_eq ⟨⟨lsh ε (k - 1), ⟨by linarith [R.ε_pos], by linarith [hB.1]⟩,
    (profit_xk_window R hk1).2.2⟩, ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  exact profit_xk_le R hk1 ⟨hα.1, hα.2.trans hB.2⟩

/-- `prop:querylb`, step (4): "Hence `ᾱ` is a share bound for all these instances", for `I_k`. -/
lemma isShareBound_xk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) :
    IsShareBound (profit (xk ε ᾱ k)) ᾱ := by
  refine ⟨R.ᾱ_pos.le, R.ᾱ_lt, ?_⟩
  unfold OPT
  rw [opt_xk R hk1 hkK ⟨le_rfl, R.ᾱ_lt.le⟩, opt_xk R hk1 hkK ⟨R.ᾱ_lt.le, le_rfl⟩]

/-- `prop:querylb`, step (4): "as `(1 − ε)(1 + 2ε) = 1 + ε(1 − 2ε) > 1`, no share outside the window
is `(1 − ε)`-optimal for `I_k`", that is, "every `(1 − ε)`-optimal contract of `I_k` lies in its
window". -/
lemma not_optimal_xk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {α : ℝ}
    (hw : α ∉ Ico (lsh ε (k - 1)) (lsh ε k)) : ¬ IsApproxOptimal (profit (xk ε ᾱ k)) ε α := by
  rintro ⟨hα, hopt⟩
  unfold OPT at hopt
  rw [opt_xk R hk1 hkK ⟨by linarith [R.one_sub_pos], le_rfl⟩, profit_xk_out hw] at hopt
  have e : (1 - ε) * gammaQ ε = 1 + ε * (1 - 2 * ε) := by unfold gammaQ; ring
  have : 0 < ε * (1 - 2 * ε) := mul_pos R.ε_pos (by linarith [R.ε_lt])
  linarith [profit_x0_le R hα]

/-- `prop:querylb`, step (4): "Moreover, for `a ∈ [ε, ᾱ]` and `k ∈ {0, …, K}`, the share bound
of `cor:probe` satisfies `ᾱ_a = 1 − (1 − a) x_k(a)/x_k(1) ≤ 1 − (1 − a) x₀(a)(1 − ᾱ) = ᾱ`" (here
`k ≥ 1`; for `k = 0`, `probeAlpha_x0`). -/
lemma probeAlpha_xk (R : Regime ε ᾱ) (hk1 : 1 ≤ k) (hkK : k ≤ Kq ε ᾱ) {a : ℝ}
    (ha : a ∈ Icc ε ᾱ) : 1 - (1 - a) * xk ε ᾱ k a / xk ε ᾱ k 1 ≤ ᾱ := by
  obtain ⟨hle, h1, h01⟩ := x0_le_xk R hk1 hkK a
  have h1a : 0 < 1 - a := by linarith [ha.2, R.ᾱ_lt]
  rw [h1, div_div_eq_mul_div, div_one]
  have key : 1 - ᾱ = (1 - a) * x0 ε ᾱ a * (1 - ᾱ) := by
    rw [x0_mid R ha.1 ha.2, mul_one_div_cancel h1a.ne', one_mul]
  have : (1 - a) * x0 ε ᾱ a * (1 - ᾱ) ≤ (1 - a) * xk ε ᾱ k a * (1 - ᾱ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle h1a.le) R.one_sub_pos.le
  linarith

/-- `prop:querylb`, step (4), the case `k = 0`: `ᾱ_a = 1 − (1 − a) x₀(a)/x₀(1) = ᾱ`. -/
lemma probeAlpha_x0 (R : Regime ε ᾱ) {a : ℝ} (ha : a ∈ Icc ε ᾱ) :
    1 - (1 - a) * x0 ε ᾱ a / x0 ε ᾱ 1 = ᾱ := by
  have h1a : 0 < 1 - a := by linarith [ha.2, R.ᾱ_lt]
  rw [x0_mid R ha.1 ha.2, x0_high R R.ᾱ_lt.le, mul_one_div_cancel h1a.ne', one_div_one_div]
  ring

end Instances

/-! ### `prop:querylb` -/

/-- The instance with the cost `0` (not in the paper: if `ᾱ < ε`, it says "there is
nothing to show"; the Lean still exhibits an instance of the class of the statement, with one
element and convex costs, see also `isShareBound_zeroCost`): at every share `α ∈ [0, 1]`, its best
response is `f({e}) = T`. -/
lemma zeroCost_isPBR_iff {T : ℝ} (hT : 0 ≤ T) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) {v : Unit → ℝ} :
    Convex.IsPBR (indepPoly (oneF T)) 1 (unitCost (cost fun _ => 0)) α v ↔ v () = T := by
  refine isPBR_unit_iff.trans ?_
  rcases hα.2.lt_or_eq with hlt | rfl
  · rw [isPBR_iff_eq_largest monotoneOn_const hT hlt,
      largest_eq hT ⟨hT, le_rfl⟩ (fun _ _ => hα.1) fun y hy => absurd hy.2 (not_le.2 hy.1)]
  · exact isPBR_one_iff monotoneOn_const hT fun _ _ => zero_lt_one

/-- The instance with the cost `0` and `f({e}) = 1/(1 − ᾱ)` (not in the paper, see
`zeroCost_isPBR_iff`): `ᾱ` is a share bound, as `U_P(α) = (1 − α)/(1 − ᾱ)` is largest at `α = 0`. -/
lemma isShareBound_zeroCost {ᾱ : ℝ} (hᾱ : ᾱ ∈ Ioo (0 : ℝ) 1) :
    IsShareBound (fun α => (1 - α) * (1 / (1 - ᾱ))) ᾱ := by
  have hT : 0 < 1 / (1 - ᾱ) := one_div_pos.2 (sub_pos.2 hᾱ.2)
  have hmax : ∀ B : ℝ, 0 ≤ B →
      sSup ((fun α => (1 - α) * (1 / (1 - ᾱ))) '' Icc 0 B) = 1 / (1 - ᾱ) := by
    intro B hB0
    refine IsGreatest.csSup_eq ⟨⟨0, ⟨le_rfl, hB0⟩, by ring⟩, ?_⟩
    rintro _ ⟨α, hα, rfl⟩
    show (1 - α) * (1 / (1 - ᾱ)) ≤ 1 / (1 - ᾱ)
    nlinarith [mul_nonneg hα.1 hT.le]
  refine ⟨hᾱ.1.le, hᾱ.2, ?_⟩
  unfold OPT
  rw [hmax _ hᾱ.1.le, hmax 1 zero_le_one]

/-- **`prop:querylb`** (Proposition D.4, appE-halfrule.tex:137-139, proof 140-163): let
`ε ∈ (0, 1/2)` and `ᾱ ∈ (0, 1)`, and let `A` be a deterministic algorithm that is given `ε` and `ᾱ`,
learns about the costs only from best responses at shares of its choice, with ties broken in favor
of the principal as in `sec:model` (`Algorithm`, `Runs`, `Convex.IsPBR`), and returns a
`(1 − ε)`-optimal contract (`IsApproxOptimal`) for every instance with one element, `m_e = 1`,
`f({e}) = 1/(1 − ᾱ)` and convex costs for which `ᾱ` is a share bound. Then `A` needs more than
`ln(1/(1 − ᾱ))/(2ε) − 3` best-response computations on one of these instances, on which the share
bound `ᾱ_a` of `cor:probe` satisfies `ᾱ_a ≤ ᾱ` for every `a ∈ [ε, ᾱ]` (`probeAlpha`). (An
instance of this class is the polymatroid `oneF (1/(1 − ᾱ))` of one element with `m = 1`, a cost
`c` of the model that is convex on `ℝ^{e}_{≥0}`, and its best responses `x(α)` at the shares
`α ∈ [0, 1]`; the reward of success `r̄ ≥ 1/(1 − ᾱ)` of the model plays no role. The algorithm `A`
is defined on all instances, but it is assumed correct only on these. The instance of the
conclusion has best responses, and the claims hold for all of them.)

The proof: (0) "If `ᾱ < ε`, … the bound is negative and there is nothing to show" (here the
Lean exhibits the instance with the cost `0`, `zeroCost_isPBR_iff`, `isShareBound_zeroCost`);
(1) `γ := 1 + 2ε` (`gammaQ`), `l_j` (`lsh`) and `K` (`Kq`), and `ε = l_0 < l_1 < ⋯ < l_K ≤ ᾱ`;
(2) "We now define a base instance `I₀` and `K` variants `I_1, …, I_K` of it" (`g0`, `gk`), with
convex costs; (3) "Next we compute the best responses of these instances": `x₀` (`isPBR_x0`) and
`x_k` (`isPBR_xk`), by `eq:E-largest`, the maximizers at `l_{k−1}` (`maximisers_window`), and
`x_k ≥ x₀`, `x_k(1) = x₀(1) = 1/(1 − ᾱ)` (`x0_le_xk`); (4) "Then we show that `ᾱ` is a share
bound for all these instances and that every `(1 − ε)`-optimal contract of `I_k` lies in its window"
(`opt_x0`,
`profit_xk_window`, `opt_xk`, `isShareBound_x0`, `isShareBound_xk`, `not_optimal_xk`,
`probeAlpha_x0`, `probeAlpha_xk`); (5) "Now we show that `A` needs at least `K − 1` best-response
computations on `I₀`" (`exists_free_window`, `Runs.congr`); (6) "Finally, we bound `K` from below"
(`Kq_bound`). The claims of steps (3) and (4) that the conclusion does not use (`maximisers_window`,
`x0_le_xk`, `probeAlpha_xk`) are recorded in `have`s. -/
theorem querylb {ε ᾱ : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (hᾱ : ᾱ ∈ Ioo (0 : ℝ) 1)
    (A : Algorithm)
    (hA : ∀ (c : (Unit → ℝ) → ℝ) (x : ℝ → Unit → ℝ), IsCost c → ConvexOn ℝ (Ici 0) c →
      (∀ α ∈ Icc (0 : ℝ) 1, Convex.IsPBR (indepPoly (oneF (1 / (1 - ᾱ)))) 1 c α (x α)) →
      IsShareBound (profit fun α => reward 1 (x α)) ᾱ →
      ∀ as ret, Runs A (oneF (1 / (1 - ᾱ))) 1 x as ret →
        IsApproxOptimal (profit fun α => reward 1 (x α)) ε ret) :
    ∃ c : (Unit → ℝ) → ℝ, IsCost c ∧ ConvexOn ℝ (Ici 0) c ∧
      (∃ x : ℝ → Unit → ℝ,
        ∀ α ∈ Icc (0 : ℝ) 1, Convex.IsPBR (indepPoly (oneF (1 / (1 - ᾱ)))) 1 c α (x α)) ∧
      ∀ x : ℝ → Unit → ℝ,
        (∀ α ∈ Icc (0 : ℝ) 1, Convex.IsPBR (indepPoly (oneF (1 / (1 - ᾱ)))) 1 c α (x α)) →
        IsShareBound (profit fun α => reward 1 (x α)) ᾱ ∧
        (∀ a ∈ Icc ε ᾱ, probeAlpha 1 x a ≤ ᾱ) ∧
        ∀ as ret, Runs A (oneF (1 / (1 - ᾱ))) 1 x as ret →
          Real.log (1 / (1 - ᾱ)) / (2 * ε) - 3 < as.length := by
  have hε0 := hε.1
  have h1ᾱ : 0 < 1 - ᾱ := sub_pos.2 hᾱ.2
  have hT : (0 : ℝ) ≤ 1 / (1 - ᾱ) := (one_div_pos.2 h1ᾱ).le
  -- (0) "If `ᾱ < ε`, then `ln(1/(1 − ᾱ)) < ln(1/(1 − ε)) ≤ ε/(1 − ε) < 2ε`, so the bound is
  -- negative and there is nothing to show. So let `ᾱ ≥ ε`."
  by_cases hεᾱ : ε ≤ ᾱ
  swap
  · -- the instance with the cost `0` (`zeroCost_isPBR_iff`), for which `ᾱ` is a share bound and
    -- on which every bound below holds
    have h1ε1ᾱ : 1 - ε < 1 - ᾱ := by linarith [not_le.1 hεᾱ]
    have h1ε : 0 < 1 - ε := by linarith [hε.2]
    have hzero := unitCost_cost (g := fun _ => 0) monotoneOn_const fun _ _ => le_rfl
    refine ⟨unitCost (cost fun _ => 0), hzero.1, hzero.2,
      ⟨fun _ _ => 1 / (1 - ᾱ), fun α hα => (zeroCost_isPBR_iff hT hα).2 rfl⟩, fun x hx => ⟨?_,
        fun a ha => absurd (ha.1.trans ha.2) (by linarith), fun as ret _ => ?_⟩⟩
    · refine isShareBound_congr (fun α hα => ?_) (isShareBound_zeroCost hᾱ)
      rw [profit, reward_one_unit, (zeroCost_isPBR_iff hT hα).1 (hx α hα)]
    · have hlog : Real.log (1 / (1 - ᾱ)) < 2 * ε := by
        have h1 : Real.log (1 / (1 - ᾱ)) < Real.log (1 / (1 - ε)) :=
          Real.log_lt_log (one_div_pos.2 h1ᾱ) (one_div_lt_one_div_of_lt h1ε h1ε1ᾱ)
        have h2 : Real.log (1 / (1 - ε)) ≤ ε / (1 - ε) := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 - ε) by positivity)
          have e : 1 / (1 - ε) - 1 = ε / (1 - ε) := by field_simp; ring
          linarith
        have h3 : ε / (1 - ε) < 2 * ε := by
          rw [div_lt_iff₀ h1ε]
          nlinarith [hε.2]
        linarith
      have h2ε : (0 : ℝ) < 2 * ε := by positivity
      have : Real.log (1 / (1 - ᾱ)) / (2 * ε) < 1 := by rw [div_lt_one h2ε]; exact hlog
      have : (0 : ℝ) ≤ as.length := Nat.cast_nonneg _
      linarith
  have R : Regime ε ᾱ := ⟨hε0, hε.2, hᾱ.1, hᾱ.2, hεᾱ⟩
  -- (1) "Let `γ := 1 + 2ε`, let `l_j := 1 − (1 − ε)γ^{−j}` for `j ≥ 0`, and let `K ≥ 0` be the
  -- largest integer with `(1 − ε)γ^{−K} ≥ 1 − ᾱ`" (`gammaQ`, `lsh`, `Kq`). "Then
  -- `ε = l_0 < l_1 < ⋯ < l_K ≤ ᾱ`."
  have _h1 : lsh ε 0 = ε ∧ StrictMono (lsh ε) ∧ lsh ε (Kq ε ᾱ) ≤ ᾱ :=
    ⟨lsh_zero, lsh_strictMono R.hε, lsh_Kq_le R⟩
  -- (2) "We now define a base instance `I₀` and `K` variants `I_1, …, I_K` of it. All instances
  -- have one element `e` with `m_e = 1` and `f({e}) = 1/(1 − ᾱ)`, so `r(z) = z`, and they differ
  -- only in the costs." `c₀` "is convex with `c₀(0) = 0` and `c₀ ≥ 0`", and so is `c_k`.
  -- "The pieces agree where they meet, so `c₀'` is continuous, nonnegative and nondecreasing"
  have _hcont0 : ContinuousOn (g0 ε ᾱ) (Ici 0) := continuousOn_g0 R
  have hc0 := unitCost_cost (monotoneOn_g0 R) fun y hy => g0_nonneg R hy
  have hck : ∀ k, 1 ≤ k → k ≤ Kq ε ᾱ →
      IsCost (unitCost (cost (gk ε ᾱ k))) ∧ ConvexOn ℝ (Ici 0) (unitCost (cost (gk ε ᾱ k))) :=
    fun k hk1 hkK => unitCost_cost (monotoneOn_gk R hk1 hkK) fun y hy => gk_nonneg R hk1 hkK hy
  -- (3) "Next we compute the best responses of these instances. By `eq:E-largest`, the best
  -- response of `I₀` is `x₀`, and that of `I_k` is the function `x_k`".
  have hBR0 : ∀ α ∈ Icc (0 : ℝ) 1, ∀ v : Unit → ℝ,
      Convex.IsPBR (indepPoly (oneF (1 / (1 - ᾱ)))) 1 (unitCost (cost (g0 ε ᾱ))) α v ↔
        v () = x0 ε ᾱ α :=
    fun α hα _ => isPBR_unit_iff.trans (isPBR_x0 R hα)
  have hBRk : ∀ k, 1 ≤ k → k ≤ Kq ε ᾱ → ∀ α ∈ Icc (0 : ℝ) 1, ∀ v : Unit → ℝ,
      Convex.IsPBR (indepPoly (oneF (1 / (1 - ᾱ)))) 1 (unitCost (cost (gk ε ᾱ k))) α v ↔
        v () = xk ε ᾱ k α :=
    fun k hk1 hkK α hα _ => isPBR_unit_iff.trans (isPBR_xk R hk1 hkK hα)
  -- "At `α = l_{k−1}`, the maximizers of `I_k` form the interval `[1/(1 − l_{k−1}), 1/(1 − l_k)]`,
  -- and the tie is broken in favor of the principal. In particular, `x_k ≥ x₀` and
  -- `x_k(1) = x₀(1) = 1/(1 − ᾱ)`."
  have _hwin : ∀ k, 1 ≤ k → k ≤ Kq ε ᾱ → ∀ z ∈ Icc 0 (1 / (1 - ᾱ)),
      (∀ y ∈ Icc 0 (1 / (1 - ᾱ)), agentU (cost (gk ε ᾱ k)) (lsh ε (k - 1)) y ≤
        agentU (cost (gk ε ᾱ k)) (lsh ε (k - 1)) z) ↔
        z ∈ Icc (1 / (1 - lsh ε (k - 1))) (1 / (1 - lsh ε k)) :=
    fun k hk1 hkK z hz => maximisers_window R hk1 hkK hz
  have _hx0xk : ∀ k, 1 ≤ k → k ≤ Kq ε ᾱ → ∀ α,
      x0 ε ᾱ α ≤ xk ε ᾱ k α ∧ xk ε ᾱ k 1 = 1 / (1 - ᾱ) ∧ x0 ε ᾱ 1 = 1 / (1 - ᾱ) :=
    fun k hk1 hkK α => x0_le_xk R hk1 hkK α
  refine ⟨unitCost (cost (g0 ε ᾱ)), hc0.1, hc0.2,
    ⟨fun α _ => x0 ε ᾱ α, fun α hα => (hBR0 α hα _).2 rfl⟩, fun x hx => ?_⟩
  have hxe : ∀ α ∈ Icc (0 : ℝ) 1, x α () = x0 ε ᾱ α := fun α hα => (hBR0 α hα (x α)).1 (hx α hα)
  have hU0 : ∀ α ∈ Icc (0 : ℝ) 1,
      profit (fun α => reward 1 (x α)) α = profit (x0 ε ᾱ) α := fun α hα => by
    rw [profit, profit, reward_one_unit, hxe α hα]
  -- (4) "Then we show that `ᾱ` is a share bound for all these instances and that every
  -- `(1 − ε)`-optimal contract of `I_k` lies in its window." … "Hence `ᾱ` is a share bound for all
  -- these instances" (here for `I₀`)
  have hsb0 : IsShareBound (profit fun α => reward 1 (x α)) ᾱ :=
    isShareBound_congr hU0 (isShareBound_x0 R)
  -- (4) "Moreover, for `a ∈ [ε, ᾱ]` and `k ∈ {0, …, K}`, the share bound of `cor:probe` satisfies
  -- `ᾱ_a = 1 − (1 − a) x_k(a)/x_k(1) ≤ 1 − (1 − a) x₀(a)(1 − ᾱ) = ᾱ`" (the case `k ≥ 1`; the case
  -- `k = 0`, the instance `I₀` of the statement, is below)
  have _hᾱk : ∀ k, 1 ≤ k → k ≤ Kq ε ᾱ → ∀ a ∈ Icc ε ᾱ,
      1 - (1 - a) * xk ε ᾱ k a / xk ε ᾱ k 1 ≤ ᾱ :=
    fun k hk1 hkK a ha => probeAlpha_xk R hk1 hkK ha
  refine ⟨hsb0, fun a ha => ?_, fun as ret hrun => ?_⟩
  · -- (4) "Moreover, for `a ∈ [ε, ᾱ]` and `k ∈ {0, …, K}`" (here `k = 0`), "the share bound of
    -- `cor:probe` satisfies `ᾱ_a = 1 − (1 − a) x_k(a)/x_k(1) ≤ 1 − (1 − a) x₀(a)(1 − ᾱ) = ᾱ`".
    have ha01 : a ∈ Icc (0 : ℝ) 1 := ⟨hε0.le.trans ha.1, by linarith [ha.2]⟩
    rw [probeAlpha, reward_one_unit, reward_one_unit, hxe a ha01, hxe 1 ⟨zero_le_one, le_rfl⟩,
      probeAlpha_x0 R ha]
  -- (5) "Now we show that `A` needs at least `K − 1` best-response computations on `I₀`. Let
  -- `α_1, …, α_q` be the shares at which `A` computes best responses on `I₀`, and let `α̂` be the
  -- share it returns." … "So `q ≥ K − 1`."
  have hqK : Kq ε ᾱ ≤ as.length + 1 := by
    -- "The windows `[l_{k−1}, l_k)`, `k ∈ [K]`, are pairwise disjoint, so at most `q + 1` of them
    -- contain one of the shares `α_1, …, α_q, α̂`. Suppose that `q + 1 < K`. Then some window
    -- `[l_{k−1}, l_k)` contains none of them."
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk1, hkK, hfree⟩ := exists_free_window R.hε (ret :: as) (by simpa using hlt)
    -- "As `x_k = x₀` outside this window, `A` receives on `I_k` the same best responses as on `I₀`"
    set y : ℝ → Unit → ℝ := fun α =>
      if α ∈ Ico (lsh ε (k - 1)) (lsh ε k) then fun _ => 1 / (1 - lsh ε k) else x α with hydef
    have hy : ∀ α ∈ Icc (0 : ℝ) 1,
        Convex.IsPBR (indepPoly (oneF (1 / (1 - ᾱ)))) 1 (unitCost (cost (gk ε ᾱ k))) α (y α) := by
      intro α hα
      rw [hBRk k hk1 hkK α hα]
      by_cases hw : α ∈ Ico (lsh ε (k - 1)) (lsh ε k)
      · simp only [hydef, ite_eq_left hw]
        unfold xk
        rw [ite_eq_left hw]
      · simp only [hydef, ite_eq_right hw]
        rw [xk_eq_x0 hw, hxe α hα]
    -- "so, being deterministic, it computes them at the same shares and returns `α̂` on `I_k` too."
    have hrunk : Runs A (oneF (1 / (1 - ᾱ))) 1 y as ret := hrun.congr fun a ha => by
      simp only [hydef, ite_eq_right (hfree a (List.mem_cons_of_mem _ ha))]
    -- "But `ᾱ` is a share bound for `I_k`, and `α̂` is not `(1 − ε)`-optimal for `I_k`, a
    -- contradiction."
    have hUk : ∀ α ∈ Icc (0 : ℝ) 1,
        profit (fun α => reward 1 (y α)) α = profit (xk ε ᾱ k) α := fun α hα => by
      rw [profit, profit, reward_one_unit, ((hBRk k hk1 hkK α hα (y α)).1 (hy α hα))]
    have hopt := hA _ y (hck k hk1 hkK).1 (hck k hk1 hkK).2 hy
      (isShareBound_congr hUk (isShareBound_xk R hk1 hkK)) as ret hrunk
    rw [isApproxOptimal_congr hUk] at hopt
    exact not_optimal_xk R hk1 hkK (hfree ret List.mem_cons_self) hopt
  -- (6) "Finally, we bound `K` from below." … "So
  -- `q ≥ K − 1 > (ln(1/(1 − ᾱ)) − 2ε)/(2ε) − 2 = ln(1/(1 − ᾱ))/(2ε) − 3`."
  have hK := Kq_bound R
  have : ((Kq ε ᾱ : ℕ) : ℝ) ≤ as.length + 1 := by exact_mod_cast hqK
  linarith

end Querylb

end

end Lower

end Stoc
