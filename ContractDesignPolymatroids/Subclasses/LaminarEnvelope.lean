-- stamp r9 2026-11-03
import ContractDesignPolymatroids.Subclasses.Laminar
import ContractDesignPolymatroids.Subclasses.KKT

/-!
# The formula on a pinning interval

The STOC version, Appendix B.8 (`sec:A-subclasses`), Lemma `lem:E-laminarformula`
(`stoc-sections/appB-quadratic.tex:770-833`): let `I` be a pinning interval with support `W`; for
every `α ∈ I` and `e ∈ W`, `x*_e(α) = (α m_e − Π_{ℓ(e)}(α)) / β_e`; moreover every `π_L ≢ −∞` is
concave, piecewise linear, and strictly increasing (`laminarformula`).

The proof follows the STOC version. It first shows the second claim:

1. as `D_L` is the minimum of finitely many affine functions `α t(U) − θ β⁻¹(U) + c` with
   `U ⊆ L ∩ W` (`Stoc.isMinAffine_Dfun`), the set `{(α, θ) | D_L(α, θ) ≥ f(L)}` is the
   intersection of the half-planes on which these functions are at least `f(L)`;
2. for `U = ∅` such a half-plane is the whole plane or empty, and in the latter case `π_L ≡ −∞`;
3. otherwise, `π_L(α)` is the minimum of `(α t(U) + c − f(L))/β⁻¹(U)` over the functions with
   `U ≠ ∅` (steps (1)-(3): `pressure_eq_inf'`),
4. a minimum of finitely many affine functions of `α` whose slopes `t(U)/β⁻¹(U)` are positive, as
   `m_e > 0` for every `e ∈ W`; so `π_L` is concave, piecewise linear, and strictly increasing
   (`pressure_properties`).

Then it fixes `α ∈ I`:

5. since all constraints are linear, `x*` satisfies the KKT conditions, and the multipliers of the
   constraints `x_e ≥ 0`, `e ∈ W`, vanish by complementary slackness; the removed constraint sets
   contain no element of `W`, so their multipliers do not enter the stationarity conditions of the
   elements of `W`; so the restriction of `x*` to `W` satisfies the KKT conditions of the problem
   of maximizing `∑_{e ∈ W} (α m_e x_e − β_e/2 x_e²)` subject to `x(L ∩ W) ≤ f(L)` for
   `L ∈ 𝓛_W`, without sign constraints; this problem has a strictly concave objective and linear
   constraints, so its KKT conditions are sufficient and its optimum is unique; hence it suffices
   to show that `x_e = (α m_e − Π_{ℓ(e)})/β_e` (`candidate`) with the multipliers
   `λ_V = Π_V − Π_{par(V)} ≥ 0` (`lamV`) satisfies these conditions (`bestResponse_eq_candidate`);
6. stationarity holds by construction, as `α m_e − β_e x_e = Π_{ℓ(e)} = ∑_{L ∋ e} λ_L`, where the
   sum telescopes along the constraint sets in `𝓛_W` that contain `ℓ(e)` (`sum_lamV_eq`);
7. the claim `Y_V(θ) = min {f(V), D_V(θ)}` for all `θ`, by induction over the forest (`Yfun_eq`);
8. for `e ∈ V ∩ W`, `Π_{ℓ(e)} = max {Π_{par(V)}, max_{V ⊇ L ⊇ ℓ(e)} π_L}`
   (`Stoc.PiUp_ell_eq`), hence `x(V ∩ W) = Y_V(Π_{par(V)})` and, by the claim,
   `x(V ∩ W) = min {f(V), D_V(Π_{par(V)})} ≤ f(V)`: feasibility;
9. if `λ_V > 0`, then `π_V > Π_{par(V)}`, hence `D_V(Π_{par(V)}) ≥ f(V)` and `x(V ∩ W) = f(V)`:
   complementary slackness (steps (6), (8) and (9): `candidate_isKKTPoint`).

The setup's (s2), "if `m_e = 0`, then `x*_e(α) = 0` for all `α`", which gives `m_e > 0` on `W` in
step (4), is `bestResponse_eq_zero_of_reward_eq_zero`; the other facts of the setup on `D_L`, `π_L`
and `Π_V` are in `ContractDesignPolymatroids/Subclasses/Laminar.lean`. Not in the paper (D3): the KKT conditions
(`ContractDesignPolymatroids/Subclasses/KKT.lean`), and that a minimum of finitely many affine functions is concave,
piecewise linear and, with positive slopes, strictly increasing (`Stoc.concaveOn_inf'`,
`Stoc.kinks_inf'_finite`, `Stoc.strictMono_inf'`, `ContractDesignPolymatroids/Subclasses/LinearPieces.lean`).

The family `𝓛_W` is `meeting 𝓛 W`, written `𝓚` in the auxiliary lemmas; `Y_V(θ)` is
`Yfun 𝓚 W f m β α V θ`. The paper's `π_L(α) = −∞` is `PiBot L α`, and `π_L ≢ −∞` is
`¬ ∀ α, PiBot L α`; its maxima of values in `ℝ ∪ {−∞}`, in `Π_V` and in `Y_V(θ)`, are the maxima
over the `L` with `¬ PiBot L α` (`Stoc.maxPi`, `ContractDesignPolymatroids/Subclasses/Laminar.lean`).

Taken over on 2026-10-21 from `Paper/Subclasses/LaminarEnvelope.lean` (the long paper's
`lem:envelope`, whose proof the STOC version takes over) for the STOC version (`stoc.tex`); from
then on this copy follows the STOC version. Adapted on 2026-10-28 to the STOC version after PR #88
(`D_L` instead of the pools, and the new proof of the second claim).
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
variable {𝓚 : Finset (Finset E)} {W : Finset E} {f : Finset E → ℝ} {m β : E → ℝ}

/-! ### Steps (1)-(4): the second claim -/

/-- **Steps (1)-(3)** of the proof of `lem:E-laminarformula` (`appB-quadratic.tex:779-787`): "As
`D_L` is the minimum of finitely many affine functions `α t(U) − θ β⁻¹(U) + c` with `U ⊆ L ∩ W`, the
set `{(α, θ) : D_L(α, θ) ≥ f(L)}` is the intersection of the half-planes on which these functions
are at least `f(L)`. For `U = ∅` such a half-plane is the whole plane or empty, and in the latter
case `π_L ≡ −∞`. Otherwise, `π_L(α)` is the minimum of `(α t(U) + c − f(L))/β⁻¹(U)` over the
functions with `U ≠ ∅`, …" In particular `π_L(α) > −∞` for every `α` in the second case. -/
theorem pressure_eq_inf' (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) :
    (∀ α, PiBot 𝓚 W f m β L α) ∨
      ((∀ α, ¬ PiBot 𝓚 W f m β L α) ∧ ∃ P : Finset (Finset E × ℝ), ∃ hP : P.Nonempty,
        (∀ p ∈ P, p.1.Nonempty ∧ p.1 ⊆ W) ∧
        pressure 𝓚 W f m β L =
          fun α => P.inf' hP fun p => (α * tA m β p.1 + p.2 - f L) / binv β p.1) := by
  classical
  obtain ⟨P, hP, hPS, ⟨p₀, hp₀, hp₀S⟩, hD⟩ :=
    isMinAffine_Dfun (W := W) (f := f) (m := m) (β := β) h𝓚 L hL
  -- (1) "As `D_L` is the minimum of finitely many affine functions `α t(U) − θ β⁻¹(U) + c` with
  -- `U ⊆ L ∩ W`, the set `{(α, θ) : D_L(α, θ) ≥ f(L)}` is the intersection of the half-planes on
  -- which these functions are at least `f(L)`."
  have hT : ∀ α θ, f L ≤ Dfun 𝓚 W f m β L α θ ↔ ∀ p ∈ P, f L ≤ affU m β p α θ := fun α θ => by
    rw [hD, le_inf'_iff]
  -- (2) "For `U = ∅` such a half-plane is the whole plane or empty, …"
  by_cases hbad : ∃ p ∈ P, p.1 = ∅ ∧ p.2 < f L
  · -- (2) "… and in the latter case `π_L ≡ −∞`."
    left
    obtain ⟨p, hp, hpe, hpc⟩ := hbad
    intro α θ
    by_contra hle
    have := (hT α θ).1 (not_lt.1 hle) p hp
    rw [show p = (∅, p.2) from Prod.ext hpe rfl, affU_empty] at this
    linarith
  · -- (3) "Otherwise, `π_L(α)` is the minimum of `(α t(U) + c − f(L))/β⁻¹(U)` over the
    -- functions with `U ≠ ∅`, …"
    right
    push Not at hbad
    set P' := P.filter fun p => p.1.Nonempty
    have hP' : P'.Nonempty := ⟨p₀, mem_filter.2 ⟨hp₀, hp₀S ▸ hLW⟩⟩
    -- the section of `{D_L ≥ f(L)}` at `α` is `(−∞, min_{U ≠ ∅} (α t(U) + c − f(L))/β⁻¹(U)]`
    have hsec : ∀ α θ, f L ≤ Dfun 𝓚 W f m β L α θ ↔
        θ ≤ P'.inf' hP' fun p => (α * tA m β p.1 + p.2 - f L) / binv β p.1 := by
      intro α θ
      rw [hT, le_inf'_iff]
      constructor
      · intro h p hp
        obtain ⟨hpP, hpne⟩ := mem_filter.1 hp
        have := h p hpP
        rw [le_div_iff₀ (binv_pos hβ hpne)]
        unfold affU at this
        linarith
      · intro h p hp
        rcases p.1.eq_empty_or_nonempty with he | hne
        · rw [show p = (∅, p.2) from Prod.ext he rfl, affU_empty]
          exact hbad p hp he
        · have := h p (mem_filter.2 ⟨hp, hne⟩)
          rw [le_div_iff₀ (binv_pos hβ hne)] at this
          unfold affU
          linarith
    have hnot : ∀ α, ¬ PiBot 𝓚 W f m β L α := fun α hbot =>
      absurd ((hsec α _).2 le_rfl) (not_le.2 (hbot _))
    refine ⟨hnot, P', hP', fun p hp => ⟨(mem_filter.1 hp).2,
      (hPS p (mem_filter.1 hp).1).trans inter_subset_right⟩, funext fun α => ?_⟩
    -- `π_L(α) = max {θ | D_L(α, θ) ≥ f(L)}` is this minimum
    have hset : {θ | f L ≤ Dfun 𝓚 W f m β L α θ} =
        Set.Iic (P'.inf' hP' fun p => (α * tA m β p.1 + p.2 - f L) / binv β p.1) :=
      Set.ext fun θ => hsec α θ
    rw [pressure, hset, csSup_Iic]

/-- The paper's dichotomy: for `L ∈ 𝓛_W`, if `π_L ≢ −∞`, then `π_L(α) > −∞` for every `α` (step
(3), `pressure_eq_inf'`). -/
theorem not_piBot_of_not_forall (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E}
    (hL : L ∈ 𝓚) (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) (α : ℝ) :
    ¬ PiBot 𝓚 W f m β L α := by
  rcases pressure_eq_inf' (f := f) (m := m) h𝓚 hβ hL hLW with hbot | ⟨hnot, -⟩
  · exact absurd hbot hgood
  · exact hnot α

/-- For `π_L ≢ −∞`, `π_L` is the minimum of the finitely many affine functions
`α ↦ (c − f(L))/β⁻¹(U) + (t(U)/β⁻¹(U)) α` of step (3), with `∅ ≠ U ⊆ W`. -/
theorem exists_pressure_eq_inf' (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E}
    (hL : L ∈ 𝓚) (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) :
    ∃ P : Finset (Finset E × ℝ), ∃ hP : P.Nonempty, (∀ p ∈ P, p.1.Nonempty ∧ p.1 ⊆ W) ∧
      pressure 𝓚 W f m β L = fun α => P.inf' hP fun p =>
        (p.2 - f L) / binv β p.1 + tA m β p.1 / binv β p.1 * α := by
  rcases pressure_eq_inf' (f := f) (m := m) h𝓚 hβ hL hLW with hbot | ⟨-, P, hP, hPW, heq⟩
  · exact absurd hbot hgood
  refine ⟨P, hP, hPW, ?_⟩
  rw [heq]
  funext α
  congr 1
  funext p
  ring

/-- `π_L ≢ −∞` is continuous, as a minimum of finitely many affine functions (step (3)). -/
theorem continuous_pressure (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) :
    Continuous (pressure 𝓚 W f m β L) := by
  obtain ⟨P, hP, -, heq⟩ := exists_pressure_eq_inf' h𝓚 hβ hL hLW hgood
  rw [heq]
  exact Continuous.finset_inf'_apply hP fun p _ => by fun_prop

/-- **Step (4)**, "So `π_L` is concave, …": `π_L ≢ −∞` is a minimum of affine functions
(`Stoc.concaveOn_inf'`). -/
theorem concaveOn_pressure (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) :
    ConcaveOn ℝ Set.univ (pressure 𝓚 W f m β L) := by
  obtain ⟨P, hP, -, heq⟩ := exists_pressure_eq_inf' h𝓚 hβ hL hLW hgood
  rw [heq]
  exact concaveOn_inf' hP _ _

/-- **Step (4)**, "So `π_L` is … piecewise linear …": `π_L ≢ −∞` is a minimum of finitely many
affine functions, so it has finitely many kinks (`Stoc.kinks_inf'_finite`). -/
theorem kinks_pressure_finite (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L : Finset E} (hL : L ∈ 𝓚)
    (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) :
    (kinks (pressure 𝓚 W f m β L)).Finite := by
  obtain ⟨P, hP, -, heq⟩ := exists_pressure_eq_inf' h𝓚 hβ hL hLW hgood
  rw [heq]
  exact kinks_inf'_finite hP _ _

/-- **Step (4)** of the proof of `lem:E-laminarformula` (`appB-quadratic.tex:785-788`): "… a
minimum of finitely many affine functions of `α` whose slopes `t(U)/β⁻¹(U)` are positive, as
`m_e > 0` for every `e ∈ W`. So `π_L` is concave, piecewise linear, and strictly increasing." Here
for `π_L ≢ −∞`; and `π_L(α) > −∞` for every `α` (step (3)). -/
theorem pressure_properties (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hm : ∀ e ∈ W, 0 < m e)
    {L : Finset E} (hL : L ∈ 𝓚) (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) :
    (∀ α, ¬ PiBot 𝓚 W f m β L α) ∧ ConcaveOn ℝ Set.univ (pressure 𝓚 W f m β L) ∧
      (kinks (pressure 𝓚 W f m β L)).Finite ∧ StrictMono (pressure 𝓚 W f m β L) := by
  refine ⟨not_piBot_of_not_forall h𝓚 hβ hL hLW hgood, concaveOn_pressure h𝓚 hβ hL hLW hgood,
    kinks_pressure_finite h𝓚 hβ hL hLW hgood, ?_⟩
  obtain ⟨P, hP, hPW, heq⟩ := exists_pressure_eq_inf' h𝓚 hβ hL hLW hgood
  rw [heq]
  refine strictMono_inf' hP _ _ fun p hp => ?_
  -- (4) "… whose slopes `t(U)/β⁻¹(U)` are positive, as `m_e > 0` for every `e ∈ W`."
  obtain ⟨hne, hsub⟩ := hPW p hp
  exact div_pos (sum_pos (fun e he => div_pos (hm e (hsub he)) (hβ e)) hne) (binv_pos hβ hne)

/-! ### Definitions for the formula -/

/-- `Y_V(θ) = ∑_{e ∈ V ∩ W} (α m_e − max {θ, max_{V ⊇ L ⊇ ℓ(e)} π_L})/β_e`
(`appB-quadratic.tex:808-813`); the inner maximum, of values in `ℝ ∪ {−∞}`, is the maximum over the
constraint sets `L` with `V ⊇ L ⊇ ℓ(e)` and `¬ PiBot L α` (`maxPi`). -/
def Yfun (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ)
    (V : Finset E) (θ : ℝ) : ℝ :=
  ∑ e ∈ V ∩ W, (α * m e - maxPi 𝓚 W f m β (𝓚.filter fun L => L ⊆ V ∧ ell 𝓚 e ⊆ L) θ α) / β e

/-- The candidate `x_e = (α m_e − Π_{ℓ(e)}) / β_e` for `e ∈ W`, and `0` off `W`
(`appB-quadratic.tex:800-803`). -/
def candidate (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ)
    (e : E) : ℝ :=
  if e ∈ W then (α * m e - PiUp 𝓚 W f m β (ell 𝓚 e) α) / β e else 0

/-- The multipliers `λ_V = Π_V − Π_{par(V)}` (`appB-quadratic.tex:801-803`). -/
def lamV (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ) (α : ℝ)
    (V : Finset E) : ℝ :=
  PiUp 𝓚 W f m β V α - PiPar 𝓚 W f m β V α

/-! ### Step (7): the claim -/

/-- **Step (7)**, the claim of the proof of `lem:E-laminarformula` (`appB-quadratic.tex:814-822`):
`Y_V(θ) = min {f(V), D_V(θ)}` for all `θ`. By induction over the forest, with
`θ' = max {θ, π_V}`: the elements `e` with `ℓ(e) = V` contribute `α t(E_V) − θ' β⁻¹(E_V)` to
`Y_V(θ)`, and the elements inside a child `K` contribute `Y_K(θ') = min {f(K), D_K(θ')}`; by
(eq:E-D), this gives `Y_V(θ) = D_V(θ')`. If `θ ≥ π_V` (in particular if `π_V = −∞`), then
`θ' = θ` and `D_V(θ) ≤ f(V)`; otherwise, `D_V(θ') = D_V(π_V) = f(V) ≤ D_V(θ)`. In both cases, the
claim follows. -/
theorem Yfun_eq (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e)
    (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty) (α : ℝ) :
    ∀ V ∈ 𝓚, ∀ θ, Yfun 𝓚 W f m β α V θ = min (f V) (Dfun 𝓚 W f m β V α θ) := by
  intro V
  induction V using Finset.strongInduction with
  | H V ih =>
  intro hV θ
  -- (7) "We proceed by induction over the forest, so let the claim hold for the children `K` of
  -- `V`, and put `θ' := max {θ, π_V}`."
  set θ' := maxPi 𝓚 W f m β {V} θ α with hθ'
  -- (7) "The elements `e` with `ℓ(e) = V` contribute `α t(E_V) − θ' β⁻¹(E_V)` to `Y_V(θ)`, …"
  have hown : ∑ e ∈ own 𝓚 W V,
      (α * m e - maxPi 𝓚 W f m β (𝓚.filter fun L => L ⊆ V ∧ ell 𝓚 e ⊆ L) θ α) / β e =
        α * tA m β (own 𝓚 W V) - θ' * binv β (own 𝓚 W V) := by
    have hterm : ∀ e ∈ own 𝓚 W V,
        (α * m e - maxPi 𝓚 W f m β (𝓚.filter fun L => L ⊆ V ∧ ell 𝓚 e ⊆ L) θ α) / β e =
          α * (m e / β e) - θ' * (1 / β e) := by
      intro e he
      have hfil : (𝓚.filter fun L => L ⊆ V ∧ ell 𝓚 e ⊆ L) = {V} := by
        rw [(mem_own.1 he).2]
        ext L
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨-, h1, h2⟩
          exact Subset.antisymm h1 h2
        · rintro rfl
          exact ⟨hV, Subset.refl _, Subset.refl _⟩
      rw [hfil]
      ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, ← mul_sum]
    rfl
  -- (7) "… and the elements inside a child `K` contribute `Y_K(θ') = min {f(K), D_K(θ')}`."
  -- Here the contribution `Y_K(θ')`; its value is the induction hypothesis below.
  have hchild : ∀ K ∈ children 𝓚 V, ∑ e ∈ K ∩ W,
      (α * m e - maxPi 𝓚 W f m β (𝓚.filter fun L => L ⊆ V ∧ ell 𝓚 e ⊆ L) θ α) / β e =
        Yfun 𝓚 W f m β α K θ' := by
    intro K hK
    obtain ⟨hK𝓚, hKpar⟩ := mem_children.1 hK
    unfold Yfun
    refine sum_congr rfl fun e he => ?_
    have heK := (mem_inter.1 he).1
    have hℓ := isEll_ell h𝓚 ⟨K, hK𝓚, heK⟩
    -- the constraint sets `L` with `V ⊇ L ⊇ ℓ(e)` are `V` and those with `K ⊇ L ⊇ ℓ(e)`
    have hsplit : (𝓚.filter fun L => L ⊆ V ∧ ell 𝓚 e ⊆ L) =
        (𝓚.filter fun L => L ⊆ K ∧ ell 𝓚 e ⊆ L) ∪ {V} := by
      ext L
      simp only [mem_filter, mem_union, mem_singleton]
      constructor
      · rintro ⟨hL, hLV, hℓL⟩
        rcases h𝓚.subset_or_subset hL hK𝓚 (hℓL hℓ.2.1) heK with h | h
        · exact Or.inl ⟨hL, h, hℓL⟩
        · by_cases hKL : K = L
          · subst hKL
            exact Or.inl ⟨hL, Subset.refl _, hℓL⟩
          · exact Or.inr (Subset.antisymm hLV (hKpar.2.2 L hL (ssubset_of_subset_of_ne h hKL)))
      · rintro (⟨hL, hLK, hℓL⟩ | rfl)
        · exact ⟨hL, hLK.trans hKpar.2.1.subset, hℓL⟩
        · exact ⟨hV, Subset.refl _, hℓ.2.2 _ hV (hKpar.2.1.subset heK)⟩
    rw [hsplit, maxPi_union]
  -- The induction hypothesis: `Y_K(θ') = min {f(K), D_K(θ')}`.
  have hK : ∀ K ∈ children 𝓚 V, Yfun 𝓚 W f m β α K θ' = min (f K) (Dfun 𝓚 W f m β K α θ') :=
    fun K hK => ih K (ssubset_of_mem_children hK) (mem_children.1 hK).1 θ'
  -- (7) "By (`eq:E-D`), this gives `Y_V(θ) = D_V(θ')`."
  have hYD : Yfun 𝓚 W f m β α V θ = Dfun 𝓚 W f m β V α θ' := by
    rw [Dfun_eq, Yfun, sum_inter_eq_own_add h𝓚 hV W, hown, sum_congr rfl hchild,
      sum_congr rfl hK]
    congr 1
    simp only [tA, binv, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  rw [hYD]
  by_cases hcase : PiBot 𝓚 W f m β V α ∨ pressure 𝓚 W f m β V α ≤ θ
  · -- (7) "If `θ ≥ π_V`, then `θ' = θ` and `D_V(θ) ≤ f(V)`."
    -- This case includes `π_V = −∞`.
    have hθθ : θ' = θ := maxPi_eq_left fun L hL hgood => by
      rw [mem_singleton.1 hL] at hgood ⊢
      exact hcase.resolve_left hgood
    have hle : Dfun 𝓚 W f m β V α θ ≤ f V := by
      by_cases hbot : PiBot 𝓚 W f m β V α
      · exact (hbot θ).le
      · rcases (hcase.resolve_left hbot).lt_or_eq with hlt | heq
        · exact (Dfun_lt_of_pressure_lt h𝓚 hβ hV (hmeet V hV) hbot hlt).le
        · rw [← heq, Dfun_pressure h𝓚 hβ hV (hmeet V hV) hbot]
    -- (7) In both cases, the claim follows.
    rw [hθθ]
    exact (min_eq_right hle).symm
  · -- (7) "Otherwise, `D_V(θ') = D_V(π_V) = f(V) ≤ D_V(θ)`."
    push Not at hcase
    obtain ⟨hgood, hlt⟩ := hcase
    have hθθ : θ' = pressure 𝓚 W f m β V α := by
      rw [hθ', maxPi_singleton hgood, max_eq_right hlt.le]
    have h1 : Dfun 𝓚 W f m β V α θ' = f V := by
      rw [hθθ, Dfun_pressure h𝓚 hβ hV (hmeet V hV) hgood]
    have h2 : f V ≤ Dfun 𝓚 W f m β V α θ := by
      have hmem : θ ∈ Set.Iic (pressure 𝓚 W f m β V α) := hlt.le
      rw [← setOf_le_Dfun_eq h𝓚 hβ hV (hmeet V hV) hgood] at hmem
      exact hmem
    -- (7) In both cases, the claim follows.
    rw [h1]
    exact (min_eq_left h2).symm

/-! ### Steps (6), (8) and (9): the KKT conditions of the candidate -/

/-- **Step (6)**, the telescoping sum (`appB-quadratic.tex:803-806`): the multipliers
`λ_L = Π_L − Π_{par(L)}` of the constraint sets `L` containing `L₀` sum to `Π_{L₀}`, as the sum
telescopes along these constraint sets. -/
theorem sum_lamV_eq (h𝓚 : IsLaminar 𝓚) (α : ℝ) :
    ∀ L₀ ∈ 𝓚, ∑ L ∈ 𝓚.filter (fun L => L₀ ⊆ L), lamV 𝓚 W f m β α L = PiUp 𝓚 W f m β L₀ α := by
  intro L₀
  induction' hn : (𝓚.filter fun L => L₀ ⊆ L).card using Nat.strong_induction_on with n ih
    generalizing L₀
  intro hL₀
  by_cases hP : ∃ P, IsParent 𝓚 L₀ P
  · obtain ⟨P, hP⟩ := hP
    have hnot : L₀ ∉ 𝓚.filter fun L => P ⊆ L := fun h =>
      not_subset_of_ssubset hP.2.1 (mem_filter.1 h).2
    have hcard : (𝓚.filter fun L => P ⊆ L).card < n := by
      rw [← hn, filter_supset_eq_insert hL₀ hP, card_insert_of_notMem hnot]
      omega
    rw [filter_supset_eq_insert hL₀ hP, sum_insert hnot, ih _ hcard P rfl hP.1, lamV,
      PiPar_eq hP]
    ring
  · rw [filter_supset_eq_singleton h𝓚 hL₀ hP, sum_singleton, lamV, PiPar_eq_zero hP, sub_zero]

/-- The constraint sets containing `e` are the constraint sets containing `ℓ(e)`. -/
theorem filter_mem_eq_filter_ell (h𝓚 : IsLaminar 𝓚) {e : E} (he : ∃ L ∈ 𝓚, e ∈ L) :
    𝓚.filter (fun L => e ∈ L) = 𝓚.filter (fun L => ell 𝓚 e ⊆ L) := by
  have hℓ := isEll_ell h𝓚 he
  exact filter_congr fun L hL => ⟨fun heL => hℓ.2.2 L hL heL, fun h => h hℓ.2.1⟩

/-- **Steps (6), (8) and (9)** of the proof of `lem:E-laminarformula`
(`appB-quadratic.tex:800-832`): the candidate `x_e = (α m_e − Π_{ℓ(e)}) / β_e` with the multipliers
`λ_V = Π_V − Π_{par(V)} ≥ 0` satisfies the KKT conditions of the problem without sign constraints.
-/
theorem candidate_isKKTPoint (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e)
    (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty) (hcov : ∀ e ∈ W, ∃ L ∈ 𝓚, e ∈ L) (α : ℝ) :
    IsKKTPoint 𝓚 W f m β α (candidate 𝓚 W f m β α) (lamV 𝓚 W f m β α) := by
  -- (5) "… the multipliers `λ_V := Π_V − Π_{par(V)} ≥ 0`, `V ∈ 𝓛_W`, …"
  -- Nonnegative as `Π_V = max {Π_{par(V)}, π_V}` (`PiUp_eq_maxPi`).
  have hlam : ∀ V ∈ 𝓚, 0 ≤ lamV 𝓚 W f m β α V := fun V hV => by
    rw [lamV, PiUp_eq_maxPi h𝓚 hV, sub_nonneg]
    exact le_maxPi _ _ _
  -- (6) "Stationarity holds by construction, as `α m_e − β_e x_e = Π_{ℓ(e)} = ∑_{L ∋ e} λ_L`,
  -- where the sum telescopes along the constraint sets in `𝓛_W` that contain `ℓ(e)`."
  have hstat : ∀ e ∈ W, marg m β α (candidate 𝓚 W f m β α) e =
      ∑ L ∈ 𝓚.filter (fun L => e ∈ L), lamV 𝓚 W f m β α L := by
    intro e he
    rw [filter_mem_eq_filter_ell h𝓚 (hcov e he),
      sum_lamV_eq h𝓚 α _ (isEll_ell h𝓚 (hcov e he)).1]
    simp only [marg, candidate, ite_eq_left he]
    field_simp [(hβ e).ne']
    ring
  -- (7) "We claim that `Y_V(θ) = min {f(V), D_V(θ)}` for all `θ ∈ ℝ`." (`Yfun_eq`)
  have hY := Yfun_eq (f := f) (m := m) h𝓚 hβ hmeet α
  -- (8) "For `e ∈ V ∩ W`, we have `Π_{ℓ(e)} = max {Π_{par(V)}, max_{V ⊇ L ⊇ ℓ(e)} π_L}`, hence
  -- `x(V ∩ W) = Y_V(Π_{par(V)})` …"
  have hxY : ∀ V ∈ 𝓚, ∑ e ∈ V ∩ W, candidate 𝓚 W f m β α e =
      Yfun 𝓚 W f m β α V (PiPar 𝓚 W f m β V α) := by
    intro V hV
    unfold Yfun
    refine sum_congr rfl fun e he => ?_
    rw [candidate, ite_eq_left (mem_inter.1 he).2, PiUp_ell_eq h𝓚 hV (mem_inter.1 he).1]
  -- (8) "… and, by the claim, `x(V ∩ W) = min {f(V), D_V(Π_{par(V)})} ≤ f(V)`. This is
  -- feasibility."
  have hfeas : ∀ V ∈ 𝓚, ∑ e ∈ V ∩ W, candidate 𝓚 W f m β α e =
      min (f V) (Dfun 𝓚 W f m β V α (PiPar 𝓚 W f m β V α)) := fun V hV => by
    rw [hxY V hV]
    exact hY V hV _
  have hfeas' : ∀ V ∈ 𝓚, ∑ e ∈ V ∩ W, candidate 𝓚 W f m β α e ≤ f V := fun V hV =>
    (hfeas V hV).trans_le (min_le_left _ _)
  -- (9) "If `λ_V > 0`, then `π_V > Π_{par(V)}`, hence `D_V(Π_{par(V)}) ≥ f(V)` and
  -- `x(V ∩ W) = f(V)`, which is complementary slackness."
  have hcs : ∀ V ∈ 𝓚, lamV 𝓚 W f m β α V * (∑ e ∈ V ∩ W, candidate 𝓚 W f m β α e - f V) = 0 := by
    intro V hV
    rcases (hlam V hV).lt_or_eq with hpos | hzero
    · have hgood : ¬ PiBot 𝓚 W f m β V α := fun hbot => by
        rw [lamV, PiUp_eq_maxPi h𝓚 hV, maxPi_eq_left fun L hL hg =>
          (hg (by rw [mem_singleton.1 hL]; exact hbot)).elim, sub_self] at hpos
        exact lt_irrefl 0 hpos
      have hlt : PiPar 𝓚 W f m β V α < pressure 𝓚 W f m β V α := by
        rw [lamV, PiUp_eq_maxPi h𝓚 hV, maxPi_singleton hgood] at hpos
        by_contra hle
        push Not at hle
        rw [max_eq_left hle, sub_self] at hpos
        exact lt_irrefl 0 hpos
      have hD : f V ≤ Dfun 𝓚 W f m β V α (PiPar 𝓚 W f m β V α) := by
        have hmem : PiPar 𝓚 W f m β V α ∈ Set.Iic (pressure 𝓚 W f m β V α) := hlt.le
        rw [← setOf_le_Dfun_eq h𝓚 hβ hV (hmeet V hV) hgood] at hmem
        exact hmem
      rw [hfeas V hV, min_eq_left hD, sub_self, mul_zero]
    · rw [← hzero, zero_mul]
  exact ⟨⟨fun e he => by simp [candidate, he], hfeas'⟩, hlam, hcs, hstat⟩

/-! ### The lemma -/

variable [Fintype E]

/-- **(s2)** of the setup of `thm:laminar` (`appB-quadratic.tex:723-725`): "If `m_e = 0`, then
`x*_e(α) = 0` for all `α`, since lowering `x_e` to `0` keeps a point in `P₊(f)` and does not
decrease `U_A(· | α)`." So the lowered point is the unique best response. -/
theorem bestResponse_eq_zero_of_reward_eq_zero (hf : IsRankFunction f) (hβ : ∀ e, 0 < β e)
    {e : E} (he : m e = 0) (α : ℝ) : bestResponse f m β α e = 0 := by
  set x := bestResponse f m β α
  have hx := isBestResponse_bestResponse hf m β α
  -- "… since lowering `x_e` to `0` keeps a point in `P₊(f)` …"
  set y := Function.update x e 0
  have hy : y ∈ indepPoly f := by
    refine mem_indepPoly_of_le hx.1 (fun e' => ?_) (fun e' => ?_)
    · by_cases h : e' = e
      · simp [y, h]
      · simp only [y, Function.update_of_ne h]
        exact hx.1.1 e'
    · by_cases h : e' = e
      · simp [y, h, hx.1.1 e]
      · simp only [y, Function.update_of_ne h]
        exact le_rfl
  -- "… and does not decrease `U_A(· | α)`.": the utility grows by `β_e/2 x_e² ≥ 0`
  have hdiff : utility m β α y - utility m β α x = β e / 2 * x e ^ 2 := by
    simp only [utility_eq_sum]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
    · simp only [y, Function.update_self, he]
      ring
    · intro e' _ he'
      simp [y, he']
    · simp
  have hyx : IsBestResponse (indepPoly f) m β α y := by
    refine ⟨hy, fun z hz => (hx.2 z hz).trans ?_⟩
    have : 0 ≤ β e / 2 * x e ^ 2 := by
      have := (hβ e).le
      positivity
    linarith
  have hyeq : y = x := hyx.eq_bestResponse hβ hf
  rw [← hyeq]
  simp [y]

/-- **`lem:E-laminarformula`**, the formula at one share (step (5), `appB-quadratic.tex:790-806`):
if the support of `x*(α)` is `W`, then `x*(α)` is the candidate:
`x*_e(α) = (α m_e − Π_{ℓ(e)}(α))/β_e` for `e ∈ W` and `x*_e(α) = 0` otherwise, for the family `𝓛_W`
of the constraint sets of `𝓛` that contain an element of `W`. -/
theorem bestResponse_eq_candidate (hf : IsRankFunction f) {𝓛 : Finset (Finset E)}
    (h𝓛 : IsLaminar 𝓛) (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) {α : ℝ} (hW : brSupport f m β α = W) :
    bestResponse f m β α = candidate (meeting 𝓛 W) W f m β α := by
  set 𝓚 := meeting 𝓛 W
  set x := bestResponse f m β α
  have h𝓚 : IsLaminar 𝓚 := h𝓛.subset (filter_subset _ _)
  have hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty := fun L hL => (mem_filter.1 hL).2
  have hxW : ∀ e, 0 < x e ↔ e ∈ W := fun e => by rw [← hW, mem_brSupport]
  have hx0 : ∀ e ∉ W, x e = 0 := fun e he =>
    le_antisymm (not_lt.1 fun h => he ((hxW e).1 h)) ((isBestResponse_bestResponse hf m β α).1.1 e)
  -- (s1) "Every element `e` lies in some constraint set, …"
  have hcov : ∀ e ∈ W, ∃ L ∈ 𝓚, e ∈ L := fun e he => by
    obtain ⟨L, hL, heL⟩ := exists_mem_of_indepPoly_eq hf hP e
    exact ⟨L, mem_filter.2 ⟨hL, e, mem_inter.2 ⟨heL, he⟩⟩, heL⟩
  -- (5) "Since all constraints are linear, `x*` satisfies the KKT conditions, …"
  obtain ⟨lam, μ, hlam, -, hslack, hμx, hstat⟩ := exists_kkt (𝓛 := 𝓛) (f := f)
    (by rw [← hP]; exact isBestResponse_bestResponse hf m β α)
  -- (5) "… and the multipliers of the constraints `x_e ≥ 0`, `e ∈ W`, vanish by complementary
  -- slackness."
  have hμ : ∀ e ∈ W, μ e = 0 := fun e he =>
    (mul_eq_zero.1 (hμx e)).resolve_right ((hxW e).2 he).ne'
  -- (5) "The removed constraint sets contain no element of `W`, so their multipliers do not enter
  -- the stationarity conditions of the elements of `W`. So the restriction of `x*` to `W`
  -- satisfies the KKT conditions of the problem of maximizing
  -- `∑_{e∈W} (α m_e x_e − β_e/2 x_e²)` over `x ∈ ℝ^W` subject to `x(L ∩ W) ≤ f(L)` for
  -- `L ∈ 𝓛_W`, without sign constraints."
  -- The first sentence is shown in the stationarity part of `hKKTx` below.
  have hsumW : ∀ L : Finset E, ∑ e ∈ L ∩ W, x e = ∑ e ∈ L, x e := fun L => by
    rw [← sum_filter_add_sum_filter_not L (· ∈ W),
      sum_eq_zero (s := L.filter fun e => e ∉ W) fun e he => hx0 e (mem_filter.1 he).2,
      add_zero, filter_mem_eq_inter]
  have hKKTx : IsKKTPoint 𝓚 W f m β α x lam := by
    refine ⟨⟨hx0, fun L _ => ?_⟩, fun L hL => hlam L (mem_filter.1 hL).1, fun L hL => ?_,
      fun e he => ?_⟩
    · rw [hsumW]
      exact (isBestResponse_bestResponse hf m β α).1.2 L
    · rw [hsumW]
      exact hslack L (mem_filter.1 hL).1
    · rw [hstat e, hμ e he, sub_zero]
      -- (5) The removed constraint sets, as quoted above: the constraint sets of `𝓛` containing
      -- `e ∈ W` are the constraint sets of `𝓛_W` containing `e`.
      congr 1
      ext L
      simp only [𝓚, meeting, mem_filter]
      exact ⟨fun ⟨hL, heL⟩ => ⟨⟨hL, e, mem_inter.2 ⟨heL, he⟩⟩, heL⟩,
        fun ⟨⟨hL, _⟩, heL⟩ => ⟨hL, heL⟩⟩
  -- (5) "This problem has a strictly concave objective and linear constraints, so its KKT
  -- conditions are sufficient and its optimum is unique."
  have h1 := isBestResponse_of_kkt (fun e => (hβ e).le) hKKTx
  -- (5) "Hence it suffices to show that `x_e := (α m_e − Π_{ℓ(e)})/β_e`, `e ∈ W`, together with
  -- the multipliers `λ_V := Π_V − Π_{par(V)} ≥ 0`, `V ∈ 𝓛_W`, satisfies these conditions."
  -- Steps (6)-(9): `candidate_isKKTPoint`.
  have h2 := isBestResponse_of_kkt (fun e => (hβ e).le)
    (candidate_isKKTPoint (f := f) (m := m) h𝓚 hβ hmeet hcov α)
  exact h1.unique (convex_signFreeSet 𝓚 W f) hβ h2

/-- **`lem:E-laminarformula`** (Lemma B.20, `stoc-sections/appB-quadratic.tex:770-833`): let `I` be
a pinning interval with support `W`. For every `α ∈ I` and every `e ∈ W`,
`x*_e(α) = (α m_e − Π_{ℓ(e)}(α)) / β_e`. Moreover, every `π_L ≢ −∞` is concave, piecewise linear
(finitely many kinks), and strictly increasing (and `π_L(α) > −∞` for every `α`). Here `𝓛_W` is
`meeting 𝓛 W`, `π_L` is `pressure`, `Π_V` is `PiUp` and `ℓ(e)` is `ell`; `π_L ≢ −∞` is
`¬ ∀ α, PiBot L α`.

The STOC version's steps: (1)-(3) the half-planes of the affine functions of `D_L`
(`pressure_eq_inf'`); (4) `pressure_properties`, with `m_e > 0` on `W` from (s2)
(`bestResponse_eq_zero_of_reward_eq_zero`); (5)-(9) the KKT conditions (`bestResponse_eq_candidate`,
`candidate_isKKTPoint`, `sum_lamV_eq`, `Yfun_eq`). -/
theorem laminarformula (hf : IsRankFunction f) {𝓛 : Finset (Finset E)} (h𝓛 : IsLaminar 𝓛)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {I : Set ℝ} (hI : IsPinningInterval f m β I)
    (hW : ∀ α ∈ I, brSupport f m β α = W) :
    (∀ α ∈ I, ∀ e ∈ W, bestResponse f m β α e =
      (α * m e - PiUp (meeting 𝓛 W) W f m β (ell (meeting 𝓛 W) e) α) / β e) ∧
    ∀ L ∈ meeting 𝓛 W, ¬ (∀ α, PiBot (meeting 𝓛 W) W f m β L α) →
      (∀ α, ¬ PiBot (meeting 𝓛 W) W f m β L α) ∧
        ConcaveOn ℝ Set.univ (pressure (meeting 𝓛 W) W f m β L) ∧
        (kinks (pressure (meeting 𝓛 W) W f m β L)).Finite ∧
        StrictMono (pressure (meeting 𝓛 W) W f m β L) := by
  have h𝓚 : IsLaminar (meeting 𝓛 W) := h𝓛.subset (filter_subset _ _)
  -- (1)-(4) "We first show the second claim."
  -- With `m_e > 0` for every `e ∈ W` by (s2), as `x*_e > 0` on `I`.
  have hm' : ∀ e ∈ W, 0 < m e := by
    obtain ⟨α₁, hα₁, hIeq⟩ := hI
    have hα₁I : α₁ ∈ I := hIeq ▸ mem_connectedComponentIn hα₁
    intro e he
    rw [← hW α₁ hα₁I, mem_brSupport] at he
    refine lt_of_le_of_ne (hm e) fun h => ?_
    rw [bestResponse_eq_zero_of_reward_eq_zero hf hβ h.symm α₁] at he
    exact lt_irrefl 0 he
  have h2 : ∀ L ∈ meeting 𝓛 W, ¬ (∀ α, PiBot (meeting 𝓛 W) W f m β L α) →
      (∀ α, ¬ PiBot (meeting 𝓛 W) W f m β L α) ∧
        ConcaveOn ℝ Set.univ (pressure (meeting 𝓛 W) W f m β L) ∧
        (kinks (pressure (meeting 𝓛 W) W f m β L)).Finite ∧
        StrictMono (pressure (meeting 𝓛 W) W f m β L) := fun L hL hgood =>
    pressure_properties h𝓚 hβ hm' hL (mem_filter.1 hL).2 hgood
  -- (5)-(9) "Now fix `α ∈ I` and drop `α` from the notation."
  -- Then `x*(α)` is the candidate (`bestResponse_eq_candidate`).
  refine ⟨fun α hα e he => ?_, h2⟩
  rw [bestResponse_eq_candidate hf h𝓛 hP hβ (hW α hα), candidate, ite_eq_left he]

end

end Stoc
