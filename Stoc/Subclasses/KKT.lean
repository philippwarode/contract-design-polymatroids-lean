-- stamp r7 2026-11-02
import Stoc.BestResponse.Quadratic

/-!
# The KKT conditions on the polyhedra of Appendix B.8

The STOC version uses the Karush–Kuhn–Tucker conditions without proof, in the proof of
`lem:E-laminarformula` (`stoc-sections/appB-quadratic.tex:790-800`: "Since all constraints are
linear, `x*` satisfies the KKT conditions, … This problem has a strictly concave objective and
linear constraints, so its KKT conditions are sufficient and its optimum is unique."). This file
proves the forms used there; all of it is "not in the paper" (D3):

*  `farkas`: Farkas' lemma for finitely many vectors of `ℝ^E`, by induction on their number.
*  `exists_kkt`: at the maximizer `x` of `U_A(· | α)` over `{x ≥ 0 | x(L) ≤ f(L), L ∈ 𝓛}` there
  are multipliers `λ_L ≥ 0` of the constraints `x(L) ≤ f(L)` and `μ_e ≥ 0` of the constraints
  `x_e ≥ 0` with stationarity `α m_e − β_e x_e = ∑_{L ∋ e} λ_L − μ_e` and complementary
  slackness: the first-order condition holds along every direction that keeps the active
  constraints, and Farkas' lemma turns this into the multipliers.
*  `isBestResponse_of_kkt`: for the problem without sign constraints on the vectors that vanish off
  a set `W` (`signFreeSet`), the KKT conditions (`IsKKTPoint`) are sufficient; with
  `IsBestResponse.unique` on the convex `signFreeSet` the optimum is unique.
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### Farkas' lemma -/

omit [DecidableEq E] in
/-- (Not in the paper: used for the KKT conditions, which the paper uses without proof.)
**Farkas' lemma**: if
`c · d ≤ 0` for every `d` with `a_i · d ≤ 0` for all `i ∈ s`, then `c = ∑_{i ∈ s} λ_i a_i` with
`λ ≥ 0`. By induction on `s`: if `c · d' > 0` for some `d'` with `a_i · d' ≤ 0` (`i ∈ s`), then
`a_k · d' > 0`, and the vectors `b_i = (a_k · d') a_i − (a_i · d') a_k` and
`c'' = (a_k · d') c − (c · d') a_k` satisfy the hypothesis for `s`. -/
theorem farkas {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ (a : ι → E → ℝ) (c : E → ℝ),
      (∀ d : E → ℝ, (∀ i ∈ s, ∑ e, a i e * d e ≤ 0) → ∑ e, c e * d e ≤ 0) →
      ∃ lam : ι → ℝ, (∀ i ∈ s, 0 ≤ lam i) ∧ ∀ e, c e = ∑ i ∈ s, lam i * a i e := by
  induction s using Finset.induction_on with
  | empty =>
    intro a c h
    -- `c · c ≤ 0`, so `c = 0`.
    have hcc := h c (by simp)
    have hc : ∀ e, c e = 0 := by
      intro e
      have hsq : ∀ g ∈ univ, 0 ≤ c g * c g := fun g _ => mul_self_nonneg (c g)
      have h0 := (sum_eq_zero_iff_of_nonneg hsq).1 (le_antisymm hcc (sum_nonneg hsq)) e (mem_univ e)
      exact mul_self_eq_zero.1 h0
    exact ⟨0, by simp, fun e => by simp [hc e]⟩
  | insert k s hk ih =>
    intro a c h
    by_cases hs : ∀ d : E → ℝ, (∀ i ∈ s, ∑ e, a i e * d e ≤ 0) → ∑ e, c e * d e ≤ 0
    · -- `c` lies in the cone of the `a_i`, `i ∈ s`.
      obtain ⟨lam, hlam, hc⟩ := ih a c hs
      refine ⟨Function.update lam k 0, fun i hi => ?_, fun e => ?_⟩
      · rcases mem_insert.1 hi with rfl | hi
        · simp
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hk)]
          exact hlam i hi
      · rw [sum_insert hk, Function.update_self, zero_mul, zero_add, hc e]
        refine sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hk)]
    · push Not at hs
      obtain ⟨d', hd's, hcd'⟩ := hs
      set p := ∑ e, a k e * d' e
      -- `a_k · d' > 0`, as `c · d' > 0`.
      have hp : 0 < p := by
        by_contra hle
        rw [not_lt] at hle
        have := h d' fun i hi => by
          rcases mem_insert.1 hi with rfl | hi
          · exact hle
          · exact hd's i hi
        linarith
      set q : ι → ℝ := fun i => ∑ e, a i e * d' e
      set r := ∑ e, c e * d' e
      set b : ι → E → ℝ := fun i e => p * a i e - q i * a k e
      set c'' : E → ℝ := fun e => p * c e - r * a k e
      have hb : ∀ d : E → ℝ, (∀ i ∈ s, ∑ e, b i e * d e ≤ 0) → ∑ e, c'' e * d e ≤ 0 := by
        intro d hd
        -- `d̃ = d − (a_k · d / p) d'` has `a_k · d̃ = 0` and `a_i · d̃ = (b_i · d)/p`.
        set t := (∑ e, a k e * d e) / p
        set dt : E → ℝ := fun e => d e - t * d' e
        have hdot : ∀ v : E → ℝ, ∑ e, v e * dt e = ∑ e, v e * d e - t * ∑ e, v e * d' e := by
          intro v
          simp only [dt, mul_sub, sum_sub_distrib, mul_sum]
          congr 1
          exact sum_congr rfl fun e _ => by ring
        have ht : p * t = ∑ e, a k e * d e := by
          simp only [t]
          field_simp
        have hbd : ∀ i, ∑ e, b i e * d e = p * ∑ e, a i e * dt e := by
          intro i
          rw [hdot]
          simp only [b, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
          linear_combination (q i) * ht
        have hcd : ∑ e, c'' e * d e = p * ∑ e, c e * dt e := by
          rw [hdot]
          simp only [c'', sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
          linear_combination r * ht
        have hkdt : ∑ e, a k e * dt e = 0 := by
          rw [hdot]
          linear_combination (-1 : ℝ) * ht
        have := h dt fun i hi => by
          rcases mem_insert.1 hi with rfl | hi
          · exact hkdt.le
          · have := hd i hi
            rw [hbd] at this
            exact (mul_nonpos_iff_pos_imp_nonpos.1 this).1 hp
        rw [hcd]
        exact mul_nonpos_of_nonneg_of_nonpos hp.le this
      obtain ⟨ν, hν, hc''⟩ := ih b c'' hb
      -- `c = ∑_{i ∈ s} ν_i a_i + ((c · d' − ∑ ν_i (a_i · d'))/p) a_k`.
      set κ := (r - ∑ i ∈ s, ν i * q i) / p
      have hκ : 0 ≤ κ := by
        have : ∑ i ∈ s, ν i * q i ≤ 0 :=
          sum_nonpos fun i hi => mul_nonpos_of_nonneg_of_nonpos (hν i hi) (hd's i hi)
        exact div_nonneg (by linarith) hp.le
      refine ⟨Function.update ν k κ, fun i hi => ?_, fun e => ?_⟩
      · rcases mem_insert.1 hi with rfl | hi
        · rw [Function.update_self]
          exact hκ
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hk)]
          exact hν i hi
      · rw [sum_insert hk, Function.update_self]
        have hs' : ∑ i ∈ s, Function.update ν k κ i * a i e = ∑ i ∈ s, ν i * a i e :=
          sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hk)]
        rw [hs']
        have he := hc'' e
        simp only [c'', b, mul_sub, sum_sub_distrib] at he
        have hsum1 : ∑ i ∈ s, ν i * (p * a i e) = p * ∑ i ∈ s, ν i * a i e := by
          rw [mul_sum]
          exact sum_congr rfl fun i _ => by ring
        have hsum2 : ∑ i ∈ s, ν i * (q i * a k e) = (∑ i ∈ s, ν i * q i) * a k e := by
          rw [sum_mul]
          exact sum_congr rfl fun i _ => by ring
        rw [hsum1, hsum2] at he
        simp only [κ]
        field_simp
        linarith

/-! ### The KKT conditions on `{x ≥ 0 | x(L) ≤ f(L), L ∈ 𝓛}` -/

omit [Fintype E] [DecidableEq E] in
/-- The polyhedron `{x ≥ 0 | x(L) ≤ f(L), L ∈ 𝓛}` is convex. -/
theorem convex_familyPoly (𝓛 : Finset (Finset E)) (f : Finset E → ℝ) :
    Convex ℝ {x : E → ℝ | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L} := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => ?_, fun L hL => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 L hL) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 L hL) hb
    have h3 : a * f L + b * f L = f L := by rw [← add_mul, hab, one_mul]
    linarith

/-- (Not in the paper: the paper uses the KKT conditions without proof.) At the maximizer `x` of
`U_A(· | α)` over `{x ≥ 0 | x(L) ≤ f(L), L ∈ 𝓛}`, there are KKT multipliers `λ_L ≥ 0` (`L ∈ 𝓛`)
and `μ_e ≥ 0` with stationarity `α m_e − β_e x_e = ∑_{L ∈ 𝓛, e ∈ L} λ_L − μ_e` and complementary
slackness `λ_L (x(L) − f(L)) = 0`, `μ_e x_e = 0`. -/
theorem exists_kkt {𝓛 : Finset (Finset E)} {f : Finset E → ℝ} {m β : E → ℝ} {α : ℝ}
    {x : E → ℝ}
    (hx : IsBestResponse {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L} m β α x) :
    ∃ (lam : Finset E → ℝ) (μ : E → ℝ), (∀ L ∈ 𝓛, 0 ≤ lam L) ∧ (∀ e, 0 ≤ μ e) ∧
      (∀ L ∈ 𝓛, lam L * (∑ e ∈ L, x e - f L) = 0) ∧ (∀ e, μ e * x e = 0) ∧
      ∀ e, marg m β α x e = ∑ L ∈ 𝓛.filter (fun L => e ∈ L), lam L - μ e := by
  classical
  -- The active constraints: `x_e ≥ 0` with `x_e = 0` (`Sum.inl e`, vector `−1_e`) and
  -- `x(L) ≤ f(L)` with `x(L) = f(L)` (`Sum.inr L`, vector `1_L`).
  set Z := univ.filter fun e => x e = 0
  set T := 𝓛.filter fun L => ∑ e ∈ L, x e = f L
  set s : Finset (E ⊕ Finset E) := Z.disjSum T
  set a : E ⊕ Finset E → E → ℝ := fun i g => match i with
    | Sum.inl e => if g = e then -1 else 0
    | Sum.inr L => if g ∈ L then 1 else 0
  have hdot_inl : ∀ e (d : E → ℝ), ∑ g, a (Sum.inl e) g * d g = -d e := by
    intro e d
    simp [a]
  have hdot_inr : ∀ L (d : E → ℝ), ∑ g, a (Sum.inr L) g * d g = ∑ g ∈ L, d g := by
    intro L d
    simp only [a, ite_mul, one_mul, zero_mul]
    rw [sum_ite, sum_const_zero, add_zero]
    congr 1
    ext g
    simp
  -- The first-order condition along every direction `d` that keeps the active constraints.
  have hfarkas : ∀ d : E → ℝ, (∀ i ∈ s, ∑ g, a i g * d g ≤ 0) →
      ∑ g, marg m β α x g * d g ≤ 0 := by
    intro d hd
    have hdZ : ∀ e, x e = 0 → 0 ≤ d e := by
      intro e he
      have := hd (Sum.inl e) (mem_disjSum.2 (Or.inl ⟨e, mem_filter.2 ⟨mem_univ e, he⟩, rfl⟩))
      rw [hdot_inl] at this
      linarith
    have hdT : ∀ L ∈ 𝓛, ∑ e ∈ L, x e = f L → ∑ e ∈ L, d e ≤ 0 := by
      intro L hL hLt
      have := hd (Sum.inr L) (mem_disjSum.2 (Or.inr ⟨L, mem_filter.2 ⟨hL, hLt⟩, rfl⟩))
      rwa [hdot_inr] at this
    -- For small `t > 0`, `x + t d` is feasible.
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (fun e => x e + t * d e) ∈ {x : E → ℝ | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L} := by
      have h1 : ∀ e, ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ x e + t * d e := by
        intro e
        rcases (hx.1.1 e).lt_or_eq with hpos | hzero
        · have hc : Continuous fun t : ℝ => x e + t * d e := by fun_prop
          have := (hc.tendsto 0).eventually (lt_mem_nhds (show 0 < x e + 0 * d e by
            rw [zero_mul, add_zero]; exact hpos))
          exact (this.filter_mono nhdsWithin_le_nhds).mono fun t ht => ht.le
        · filter_upwards [self_mem_nhdsWithin] with t ht
          rw [← hzero, zero_add]
          exact mul_nonneg (le_of_lt ht) (hdZ e hzero.symm)
      have h2 : ∀ L ∈ 𝓛, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ e ∈ L, (x e + t * d e) ≤ f L := by
        intro L hL
        have hsum : ∀ t : ℝ, ∑ e ∈ L, (x e + t * d e) = ∑ e ∈ L, x e + t * ∑ e ∈ L, d e := by
          intro t
          rw [sum_add_distrib, mul_sum]
        rcases (hx.1.2 L hL).lt_or_eq with hlt | heq
        · have hc : Continuous fun t : ℝ => ∑ e ∈ L, x e + t * ∑ e ∈ L, d e := by fun_prop
          have := (hc.tendsto 0).eventually (gt_mem_nhds (show
            ∑ e ∈ L, x e + 0 * ∑ e ∈ L, d e < f L by rw [zero_mul, add_zero]; exact hlt))
          exact (this.filter_mono nhdsWithin_le_nhds).mono fun t ht => by rw [hsum]; exact ht.le
        · filter_upwards [self_mem_nhdsWithin] with t ht
          rw [hsum, heq]
          have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (hdT L hL heq)
          linarith
      filter_upwards [eventually_all.2 h1, (eventually_all_finset 𝓛).2 h2] with t ht1 ht2
      exact ⟨ht1, ht2⟩
    obtain ⟨t, htP, ht⟩ := (hev.and self_mem_nhdsWithin).exists
    have hfoc := hx.foc (convex_familyPoly 𝓛 f) htP
    have hfoc' : t * ∑ g, marg m β α x g * d g ≤ 0 := by
      rw [mul_sum]
      convert hfoc using 2 with g
      ring
    exact nonpos_of_mul_nonpos_right hfoc' ht
  obtain ⟨lam', hlam', hρ⟩ := farkas s a (marg m β α x) hfarkas
  -- The multipliers of the active constraints, and `0` for the others.
  refine ⟨fun L => if L ∈ T then lam' (Sum.inr L) else 0,
    fun e => if e ∈ Z then lam' (Sum.inl e) else 0, fun L _ => ?_, fun e => ?_,
    fun L hL => ?_, fun e => ?_, fun g => ?_⟩
  · dsimp only
    split_ifs with h
    · exact hlam' _ (mem_disjSum.2 (Or.inr ⟨L, h, rfl⟩))
    · exact le_rfl
  · dsimp only
    split_ifs with h
    · exact hlam' _ (mem_disjSum.2 (Or.inl ⟨e, h, rfl⟩))
    · exact le_rfl
  · dsimp only
    split_ifs with h
    · rw [(mem_filter.1 h).2, sub_self, mul_zero]
    · rw [zero_mul]
  · dsimp only
    split_ifs with h
    · rw [(mem_filter.1 h).2, mul_zero]
    · rw [zero_mul]
  · rw [hρ g, sum_disjSum]
    simp only [a]
    -- The terms of the active constraints `x_e ≥ 0` give `−μ_g`, those of the active
    -- `x(L) ≤ f(L)` give `∑_{L ∋ g} λ_L`.
    have h1 : ∑ e ∈ Z, lam' (Sum.inl e) * (if g = e then -1 else 0) =
        -(if g ∈ Z then lam' (Sum.inl g) else 0) := by
      have : ∀ e ∈ Z, lam' (Sum.inl e) * (if g = e then -1 else 0) =
          if g = e then -lam' (Sum.inl e) else 0 := fun e _ => by split_ifs <;> ring
      rw [sum_congr rfl this, sum_ite_eq]
      split_ifs <;> ring
    have h2 : ∑ L ∈ T, lam' (Sum.inr L) * (if g ∈ L then 1 else 0) =
        ∑ L ∈ 𝓛.filter (fun L => g ∈ L), if L ∈ T then lam' (Sum.inr L) else 0 := by
      have hT : T.filter (fun L => g ∈ L) = (𝓛.filter fun L => g ∈ L).filter (fun L => L ∈ T) := by
        ext L
        simp only [T, mem_filter]
        tauto
      simp only [mul_ite, mul_one, mul_zero]
      rw [← sum_filter, ← sum_filter, hT]
    rw [h1, h2]
    ring

/-! ### The problem without sign constraints on a support `W` -/

omit [Fintype E] [DecidableEq E] in
/-- The feasible set of the problem of `lem:E-laminarformula` on `ℝ^W` without sign constraints,
as vectors of `ℝ^E` that vanish off `W`: `x(L ∩ W) ≤ f(L)` for `L ∈ 𝓚`. -/
def signFreeSet (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) : Set (E → ℝ) :=
  {z | (∀ e ∉ W, z e = 0) ∧ ∀ L ∈ 𝓚, ∑ e ∈ L ∩ W, z e ≤ f L}

omit [Fintype E] [DecidableEq E] in
/-- The KKT conditions of this problem at `y` with multipliers `λ`: feasibility, `λ ≥ 0`,
complementary slackness and stationarity `α m_e − β_e y_e = ∑_{L ∈ 𝓚, e ∈ L} λ_L` on `W`. -/
structure IsKKTPoint (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (α : ℝ) (y : E → ℝ) (lam : Finset E → ℝ) : Prop where
  mem : y ∈ signFreeSet 𝓚 W f
  nonneg : ∀ L ∈ 𝓚, 0 ≤ lam L
  slack : ∀ L ∈ 𝓚, lam L * (∑ e ∈ L ∩ W, y e - f L) = 0
  stat : ∀ e ∈ W, marg m β α y e = ∑ L ∈ 𝓚.filter (fun L => e ∈ L), lam L

omit [Fintype E] in
theorem convex_signFreeSet (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) :
    Convex ℝ (signFreeSet 𝓚 W f) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e he => ?_, fun L hL => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx.1 e he, hy.1 e he, mul_zero,
      add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 L hL) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 L hL) hb
    have h3 : a * f L + b * f L = f L := by rw [← add_mul, hab, one_mul]
    linarith

/-- (Not in the paper: the paper uses the KKT conditions without proof.) The KKT conditions of the
problem without sign constraints are sufficient, as its objective is concave and its constraints
linear: `∑_e ρ_e (z_e − y_e) = ∑_L λ_L (z(L ∩ W) − f(L)) ≤ 0` for every feasible `z`. -/
theorem isBestResponse_of_kkt {𝓚 : Finset (Finset E)} {W : Finset E} {f : Finset E → ℝ}
    {m β : E → ℝ} (hβ : ∀ e, 0 ≤ β e) {α : ℝ} {y : E → ℝ} {lam : Finset E → ℝ}
    (h : IsKKTPoint 𝓚 W f m β α y lam) : IsBestResponse (signFreeSet 𝓚 W f) m β α y := by
  refine isBestResponse_of_foc hβ h.mem fun z hz => ?_
  -- Off `W` both vanish; on `W`, `ρ_e = ∑_{L ∋ e} λ_L`.
  have hterm : ∀ e, marg m β α y e * (z e - y e) =
      if e ∈ W then (∑ L ∈ 𝓚.filter (fun L => e ∈ L), lam L) * (z e - y e) else 0 := by
    intro e
    split_ifs with he
    · rw [h.stat e he]
    · rw [hz.1 e he, h.mem.1 e he, sub_self, mul_zero]
  rw [sum_congr rfl fun e _ => hterm e, ← sum_filter]
  simp only [sum_mul]
  -- exchange the sums: `∑_L λ_L ∑_{e ∈ L ∩ W} (z_e − y_e)`
  rw [sum_comm' (t' := 𝓚) (s' := fun L => L ∩ W)]
  · refine sum_nonpos fun L hL => ?_
    rw [← mul_sum, sum_sub_distrib]
    have hs := h.slack L hL
    have hzL := hz.2 L hL
    have hl := h.nonneg L hL
    nlinarith
  · intro e L
    simp only [mem_filter, mem_inter, mem_univ, true_and]
    tauto

end

end Stoc
