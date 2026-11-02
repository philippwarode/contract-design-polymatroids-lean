-- stamp r8 2026-11-02
import ContractDesignPolymatroids.BestResponse.LevelSets
import ContractDesignPolymatroids.BestResponse.LayerCake
import ContractDesignPolymatroids.Preliminaries.Greedy
import ContractDesignPolymatroids.OptimalShare.PiecewiseAffine

/-!
# The full plane

The STOC version's Appendix B.6.1 (`sec:B-fullplane`, "The full plane",
`stoc-sections/appB-tools.tex:8-222`): the full-plane best response `ξ^g` and its marginals `ρ^g`
of a submodular function `g` with `g(∅) = 0` that need not be monotone, the weighted means, and
`lem:fullplane`.

The paper's objects:
* `fpBase g`: the full plane `B_{(±)}(g) = {y ∈ ℝ^E : y(S) ≤ g(S) for all S, y(E) = g(E)}`;
* `xi g m β α` and `rho g m β α`: the full-plane best response `ξ^g(α)` and the full-plane marginals
  `ρ^g(α) = α m − β ξ^g(α)`; the reward `r(ξ^g(α))` is `Stoc.reward m (xi g m β α)`, which is
  `curve g m β α` by definition; the upper level set `A^g_θ(α) = A_θ(ξ^g(α))` is
  `Stoc.levelSet m β α (xi g m β α) θ`, and `F^g_{α,θ}` is `Stoc.levelFun g m β α θ`;
* `GrowsAtLeast`, `GrowsAtMost`: a function grows at least (at most) at a rate;
* `mbar`, `SS`: the weighted mean reward `m̄_D = t(D)/β⁻¹(D)` and the weighted sum of squares
  `SS(D) = ∑_{e∈D} (m_e − m̄_D)²/β_e`;
* `modSingleton F`: the modular singleton `π_F`.

The paper's claims, with the declarations of their exact statements:
* the setting (`appB-tools.tex:30-40`): `fpBase_nonempty` (the greedy vector),
  `fpBase_subset_Icc` and `isCompact_fpBase` (compactness, with `isClosed_fpBase`),
  `existsUnique_isBestResponse_fpBase` (the unique maximizer), `xi_isProjection` (the projection of
  `α t`, by step (1) of the proof of `lem:pwaffine`, `Stoc.isBestResponse_iff_isProjβ`), and
  `xi_eq_bestResponse` (line 40, `lem:fullplane`(g) with `Λ = Θ = 0`); the claim that `ξ^g` is
  piecewise affine with finitely many breakpoints (line 36, "that proof applies verbatim") is not
  formalised, and no later proof uses it;
* the weighted means (`appB-tools.tex:55-78`): `SS_le` (the minimum form, as the convex quadratic
  `v ↦ ∑_{e∈D} (m_e − v)²/β_e`, `convexOn_sum_sq`, has the derivative `−2(t(D) − v β⁻¹(D))`,
  `hasDerivAt_sum_sq`, which vanishes at `v = m̄_D`), `SS_mono`, `SS_pair` (`eq:B-pair`, as the mean
  divides the gap in the ratio of the curvatures), `SS_union` (`eq:B-twogroups`, by expanding about
  the two group means and `eq:B-pair` for the two groups);
* `lem:fullplane` (`appB-tools.tex:80-105`, proof `appB-tools.tex:111-222`): its parts
  `fullplane_a`, `fullplane_b`, `fullplane_c`, `fullplane_d`, `fullplane_e`, `fullplane_f` and
  `fullplane_f_singleton`, `fullplane_g`; the exact statement of the lemma, the conjunction of
  (a)–(g), is `fullplane`, after part (g).

Each exact statement carries all hypotheses of the paper. Its proof is carried by auxiliary lemmas
under the standing hypotheses `FPHyp g β` (`g` submodular with `g(∅) = 0`, and `β > 0`; mostly
without `m > 0`): `exists_tight_exchange`, `levelSet_tight`, `isBestResponse_of_levelSets` and
`xi_strictLevelSet_tight` for (a); `levelSet_isMaxMinimiser` for (b); `rho_add_ge_of` and
`rho_add_le` for steps (1) and (2) of (c), whose steps (3) and (4) are in `fullplane_c` itself;
`sum_mul_xi_mono` and `curve_mono` for (d); `sum_mul_xi_of_rho_eq` for (e); `xi_dirSum` and
`xi_modSingleton` (with `fpBase_modSingleton`: `B_{(±)}(π_F) = {F}`) for (f); `bestResponse_eq_add`
for (g). The later files apply (a) in the forms `xi_levelSet_tight`, `eq_xi_of_levelSets` and
`xi_strictLevelSet_tight`. The direct sum `g ⊕ π_F` with a modular singleton on a new element
`b = none` of `Option E` is `addSingleton g F`, with `xi_addSingleton` derived from (f).

Taken over on 2026-10-20 from `Paper/Hardness/FullPlane.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset Filter Topology

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The full plane (`appB-tools.tex:19-36`) -/

/-- `{y ∈ ℝ^E : y(S) ≤ g(S) for all S ⊆ E}`, without a sign constraint. -/
def fpPoly (g : Finset E → ℝ) : Set (E → ℝ) :=
  {y | ∀ T : Finset E, ∑ e ∈ T, y e ≤ g T}

/-- The full plane `B_{(±)}(g) = {y ∈ ℝ^E : y(S) ≤ g(S) for all S ⊆ E, y(E) = g(E)}`, the base
polyhedron of `g` without a sign constraint (`appB-tools.tex:22-26`). -/
def fpBase (g : Finset E → ℝ) : Set (E → ℝ) :=
  {y | y ∈ fpPoly g ∧ ∑ e, y e = g univ}

variable {g : Finset E → ℝ}

omit [DecidableEq E] in
/-- `B_{(±)}(g)` is convex (not in the paper: the paper leaves implicit that the full plane is
convex, which the uniqueness of the maximizer of the strictly concave `U_A(· | α)`,
`appB-tools.tex:34`, uses). -/
lemma convex_fpBase (g : Finset E → ℝ) : Convex ℝ (fpBase g) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun T => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    calc a * ∑ e ∈ T, x e + b * ∑ e ∈ T, y e ≤ a * g T + b * g T :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.1 T) ha)
            (mul_le_mul_of_nonneg_left (hy.1 T) hb)
      _ = g T := by rw [← add_mul, hab, one_mul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hx.2, hy.2]
    rw [← add_mul, hab, one_mul]

omit [DecidableEq E] in
/-- `B_{(±)}(g)` is closed (not in the paper: the paper uses without proof that the full plane is
closed, in "it is closed and its points satisfy ...", `appB-tools.tex:33`). -/
lemma isClosed_fpBase (g : Finset E → ℝ) : IsClosed (fpBase g) := by
  have h1 : IsClosed (fpPoly g) := by
    simp only [fpPoly, Set.ofPred_forall]
    exact isClosed_iInter fun T =>
      isClosed_le (continuous_finsetSum _ fun e _ => continuous_apply e) continuous_const
  have h2 : IsClosed {y : E → ℝ | ∑ e, y e = g univ} :=
    isClosed_eq (continuous_finsetSum _ fun e _ => continuous_apply e) continuous_const
  exact h1.inter h2

/-- The setting (`appB-tools.tex:33`): every point `y` of `B_{(±)}(g)` satisfies
`g(E) − g(E ∖ {e}) ≤ y_e ≤ g({e})` for every `e ∈ E`, where the lower bound follows from
`y_e = y(E) − y(E ∖ {e})`. -/
lemma fpBase_subset_Icc (g : Finset E → ℝ) :
    fpBase g ⊆ Set.Icc (fun e => g univ - g (univ.erase e)) (fun e => g {e}) := by
  intro y hy
  refine ⟨fun e => ?_, fun e => ?_⟩
  · -- the lower bound follows from `y_e = y(E) − y(E ∖ {e})`, with `y(E) = g(E)` and
    -- `y(E ∖ {e}) ≤ g(E ∖ {e})`
    have hye : y e = ∑ e', y e' - ∑ e' ∈ univ.erase e, y e' := by
      rw [← add_sum_erase univ y (mem_univ e)]
      ring
    show g univ - g (univ.erase e) ≤ y e
    rw [hye, hy.2]
    linarith [hy.1 (univ.erase e)]
  · -- the upper bound: `y_e = y({e}) ≤ g({e})`
    simpa using hy.1 {e}

/-- The setting (`appB-tools.tex:33`): the full plane `B_{(±)}(g)` is also compact, as it is closed
(`isClosed_fpBase`) and its points satisfy `g(E) − g(E ∖ {e}) ≤ y_e ≤ g({e})`
(`fpBase_subset_Icc`). -/
lemma isCompact_fpBase (g : Finset E → ℝ) : IsCompact (fpBase g) :=
  isCompact_Icc.of_isClosed_subset (isClosed_fpBase g) (fpBase_subset_Icc g)

/-- The setting (`appB-tools.tex:30-32`): the full-plane best response is the maximizer of a
strictly concave function on `B_{(±)}(g)`, so the paper first shows that `B_{(±)}(g)` is nonempty
(here) and compact (`isCompact_fpBase`); `g` is submodular with `g(∅) = 0`. For an order
`e_1, …, e_n` of `E` (here `e_{i+1} = σ i`, indices from 0) and `S_i = {e_1, …, e_i}`
(`Stoc.prefixSet σ i`), the greedy vector `y_{e_i} = g(S_i) − g(S_{i−1})` lies in it (compare
[Sch03, Thm. 44.3]). Steps: (1) `y(E) = g(E)`; (2) let `S ⊆ E`; for `e_i ∈ S`,
`S ∩ S_i = (S ∩ S_{i−1}) ∪ {e_i}` with `S ∩ S_{i−1} ⊆ S_{i−1}` and `e_i ∉ S_{i−1}`, so submodularity
gives `y_{e_i} ≤ g(S ∩ S_i) − g(S ∩ S_{i−1})`; (3) for `e_i ∉ S`, this right-hand side is `0`;
(4) so summing over `e_i ∈ S` gives
`y(S) ≤ ∑_{i=1}^n (g(S ∩ S_i) − g(S ∩ S_{i−1})) = g(S)`, and `y ∈ B_{(±)}(g)`. -/
theorem fpBase_nonempty (hg : Submodular g) (h0 : g ∅ = 0) : (fpBase g).Nonempty := by
  -- An order `e_1, …, e_n` of `E` and the sets `S_i = {e_1, …, e_i}`.
  set n := Fintype.card E
  set σ : Fin n ≃ E := (Fintype.equivFin E).symm
  have hS0 : prefixSet σ 0 = ∅ := by
    ext e
    simp [prefixSet]
  have hSn : prefixSet σ n = univ := by
    ext e
    simp [prefixSet]
  have hSsucc : ∀ e, prefixSet σ (σ.symm e + 1) = insert e (prefixSet σ (σ.symm e)) := fun e => by
    rw [prefixSet_succ_eq_insert_before, prefixSet_eq_before]
  have hnot : ∀ e, e ∉ prefixSet σ (σ.symm e) := fun e => by
    rw [prefixSet_eq_before]
    exact not_mem_before e
  -- Sums over `E` are sums over the positions `i < n`.
  have hre : ∀ F : ℕ → ℝ, ∑ e, F (σ.symm e) = ∑ i ∈ range n, F i := fun F => by
    rw [Equiv.sum_comp σ.symm (fun i : Fin n => F i), Fin.sum_univ_eq_sum_range]
  -- The greedy vector `y_{e_i} = g(S_i) − g(S_{i−1})`.
  set y : E → ℝ := fun e => g (prefixSet σ (σ.symm e + 1)) - g (prefixSet σ (σ.symm e))
  -- (1) `y(E) = g(E)`.
  have h1 : ∑ e, y e = g univ := by
    rw [hre fun i => g (prefixSet σ (i + 1)) - g (prefixSet σ i),
      sum_range_sub (fun i => g (prefixSet σ i)), hSn, hS0, h0, sub_zero]
  -- (2) Let `S ⊆ E`.
  refine ⟨y, fun S => ?_, h1⟩
  -- For `e_i ∈ S`, we have `S ∩ S_i = (S ∩ S_{i−1}) ∪ {e_i}` with `S ∩ S_{i−1} ⊆ S_{i−1}` and
  -- `e_i ∉ S_{i−1}`, so submodularity gives `y_{e_i} ≤ g(S ∩ S_i) − g(S ∩ S_{i−1})`.
  have h2 : ∀ e ∈ S, y e ≤
      g (S ∩ prefixSet σ (σ.symm e + 1)) - g (S ∩ prefixSet σ (σ.symm e)) := by
    intro e he
    have hSi : S ∩ prefixSet σ (σ.symm e + 1) = insert e (S ∩ prefixSet σ (σ.symm e)) := by
      rw [hSsucc, inter_insert_of_mem he]
    show g (prefixSet σ (σ.symm e + 1)) - g (prefixSet σ (σ.symm e)) ≤ _
    rw [hSi, hSsucc]
    exact hg.diminishingReturns inter_subset_right (hnot e)
  -- (3) For `e_i ∉ S`, this right-hand side is `0`.
  have h3 : ∀ e ∉ S,
      g (S ∩ prefixSet σ (σ.symm e + 1)) - g (S ∩ prefixSet σ (σ.symm e)) = 0 := by
    intro e he
    rw [hSsucc, inter_insert_of_notMem he, sub_self]
  -- (4) So summing over `e_i ∈ S` gives
  -- `y(S) ≤ ∑_{i=1}^n (g(S ∩ S_i) − g(S ∩ S_{i−1})) = g(S)`, and `y ∈ B_{(±)}(g)`.
  calc ∑ e ∈ S, y e
      ≤ ∑ e ∈ S, (g (S ∩ prefixSet σ (σ.symm e + 1)) - g (S ∩ prefixSet σ (σ.symm e))) :=
        sum_le_sum h2
    _ = ∑ e, (g (S ∩ prefixSet σ (σ.symm e + 1)) - g (S ∩ prefixSet σ (σ.symm e))) :=
        sum_subset (subset_univ S) fun e _ he => h3 e he
    _ = ∑ i ∈ range n, (g (S ∩ prefixSet σ (i + 1)) - g (S ∩ prefixSet σ i)) :=
        hre fun i => g (S ∩ prefixSet σ (i + 1)) - g (S ∩ prefixSet σ i)
    _ = g S := by
        rw [sum_range_sub (fun i => g (S ∩ prefixSet σ i)), hSn, hS0, inter_univ, inter_empty, h0,
          sub_zero]

/-! ### The full-plane best response and the full-plane marginals -/

/-- The standing hypotheses of the auxiliary lemmas: `g` is submodular with `g(∅) = 0`, and
`β > 0`. -/
structure FPHyp (g : Finset E → ℝ) (β : E → ℝ) : Prop where
  submod : Submodular g
  empty : g ∅ = 0
  pos : ∀ e, 0 < β e

/-- A maximizer of `U_A(· | α)` over `B_{(±)}(g)` exists, as `B_{(±)}(g)` is nonempty and
compact. -/
theorem exists_isBestResponse_fpBase (hg : Submodular g) (h0 : g ∅ = 0) (m β : E → ℝ)
    (α : ℝ) : ∃ x, IsBestResponse (fpBase g) m β α x := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_fpBase g).exists_isMaxOn (fpBase_nonempty hg h0)
    (continuous_utility m β α).continuousOn
  exact ⟨x, hx, isMaxOn_iff.1 hmax⟩

/-- The setting (`appB-tools.tex:34`): for every `α ∈ ℝ`, the strictly concave function
`U_A(· | α)` has a unique maximizer on `B_{(±)}(g)` (for `g` submodular with `g(∅) = 0` and
`m, β > 0`; the hypothesis `m > 0` is not used). -/
theorem existsUnique_isBestResponse_fpBase (hg : Submodular g) (h0 : g ∅ = 0) {m β : E → ℝ}
    (_hm : ∀ e, 0 < m e) (hβ : ∀ e, 0 < β e) (α : ℝ) :
    ∃! x, IsBestResponse (fpBase g) m β α x := by
  obtain ⟨x, hx⟩ := exists_isBestResponse_fpBase hg h0 m β α
  exact ⟨x, hx, fun y hy => hy.unique (convex_fpBase g) hβ hx⟩

/-- The full-plane best response `ξ^g(α)`: the maximizer of `U_A(· | α)` over `B_{(±)}(g)`. -/
def xi (g : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : E → ℝ :=
  Classical.epsilon fun x => IsBestResponse (fpBase g) m β α x

/-- The full-plane marginals `ρ^g(α) = α m − β ξ^g(α)`. -/
def rho (g : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) (e : E) : ℝ :=
  marg m β α (xi g m β α) e

/-- The reward `r(ξ^g(α)) = m^⊤ξ^g(α)` of the full-plane best response. -/
def curve (g : Finset E → ℝ) (m β : E → ℝ) (α : ℝ) : ℝ :=
  ∑ e, m e * xi g m β α e

variable {m β : E → ℝ} {α : ℝ} {x y : E → ℝ}

/-- `ξ^g(α)` maximizes `U_A(· | α)` over `B_{(±)}(g)` (the setting, `appB-tools.tex:34`; a
maximizer exists by `exists_isBestResponse_fpBase`). -/
theorem FPHyp.isBestResponse (H : FPHyp g β) (m : E → ℝ) (α : ℝ) :
    IsBestResponse (fpBase g) m β α (xi g m β α) :=
  Classical.epsilon_spec (exists_isBestResponse_fpBase H.submod H.empty m β α)

/-- Every maximizer of `U_A(· | α)` over `B_{(±)}(g)` is `ξ^g(α)`: the maximizer is unique
(`appB-tools.tex:34`), as `U_A(· | α)` is strictly concave and `B_{(±)}(g)` is convex. -/
theorem FPHyp.eq_xi (H : FPHyp g β) (hx : IsBestResponse (fpBase g) m β α x) :
    x = xi g m β α :=
  hx.unique (convex_fpBase g) H.pos (H.isBestResponse m α)

/-- `ξ^g(α) ∈ B_{(±)}(g)`. -/
theorem xi_mem_fpBase (H : FPHyp g β) (m : E → ℝ) (α : ℝ) : xi g m β α ∈ fpBase g :=
  (H.isBestResponse m α).1

omit [DecidableEq E] in
/-- `ξ^g_e(α) = (α m_e − ρ^g_e(α))/β_e`, that is, `ξ_e = α t_e − ρ_e/β_e`. -/
lemma xi_eq_of_pos (hβ : ∀ e, 0 < β e) (e : E) :
    xi g m β α e = (α * m e - rho g m β α e) / β e := by
  have := (hβ e).ne'
  simp only [rho, marg]
  field_simp
  ring

/-- `ξ^g_e(α) = (α m_e − ρ^g_e(α))/β_e`, that is, `ξ_e = α t_e − ρ_e/β_e` (`xi_eq_of_pos`). -/
lemma xi_eq (H : FPHyp g β) (e : E) : xi g m β α e = (α * m e - rho g m β α e) / β e :=
  xi_eq_of_pos H.pos e

/-- The setting (`appB-tools.tex:35-36`): for `g` submodular with `g(∅) = 0` and `m, β > 0`,
`ξ^g(α)` is the projection `IsProjβ` of `α t` onto `B_{(±)}(g)` with respect to `‖·‖_β`.
Completing the square as in the proof of `lem:pwaffine`: its step (1),
`U_A(x | α) = α²/2 ‖t‖_β² − 1/2 ‖x − αt‖_β²`, so that the maximizers of `U_A(· | α)` on an action
set are the projections of `αt` onto it (`Stoc.isBestResponse_iff_isProjβ`), applies verbatim with
`B_{(±)}(g)` in place of `P₊(f)` and with `α ∈ ℝ`. The hypothesis `m > 0` is not used. -/
theorem xi_isProjection (hg : Submodular g) (h0 : g ∅ = 0) (_hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) (α : ℝ) :
    IsProjβ β (fpBase g) (α • fun e => m e / β e) (xi g m β α) :=
  (isBestResponse_iff_isProjβ hβ).1 (FPHyp.isBestResponse ⟨hg, h0, hβ⟩ m α)

/-! ### Rates (`appB-tools.tex:52-53`) -/

/-- `φ` grows at least at the rate `c`: `φ(α + Δ) ≥ φ(α) + c Δ` for all `α ∈ ℝ` and `Δ ≥ 0`. -/
def GrowsAtLeast (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ α Δ : ℝ, 0 ≤ Δ → φ α + c * Δ ≤ φ (α + Δ)

/-- `φ` grows at most at the rate `c`: `φ(α + Δ) ≤ φ(α) + c Δ` for all `α ∈ ℝ` and `Δ ≥ 0`. -/
def GrowsAtMost (φ : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ α Δ : ℝ, 0 ≤ Δ → φ (α + Δ) ≤ φ α + c * Δ

/-! ### Weighted means (`appB-tools.tex:55-78`) -/

section WeightedMeans

variable {ι : Type*} {m β : ι → ℝ}

/-- The weighted mean reward `m̄_D = t(D)/β⁻¹(D) = (∑_{e∈D} m_e/β_e)/(∑_{e∈D} 1/β_e)` of a nonempty
`D`, weighted by `1/β` (`appB-tools.tex:56-60`). -/
def mbar (m β : ι → ℝ) (D : Finset ι) : ℝ :=
  (∑ e ∈ D, m e / β e) / ∑ e ∈ D, 1 / β e

/-- The weighted sum of squares `SS(D) = ∑_{e∈D} (m_e − m̄_D)²/β_e` (`appB-tools.tex:62-65`). -/
def SS (m β : ι → ℝ) (D : Finset ι) : ℝ :=
  ∑ e ∈ D, (m e - mbar m β D) ^ 2 / β e

/-- The function `v ↦ ∑_{e∈D} (m_e − v)²/β_e` is convex (not in the paper: the paper uses without
proof that this quadratic is convex, `appB-tools.tex:66`): for `a, b ≥ 0` with `a + b = 1`,
`a (m_e − x)² + b (m_e − y)² − (m_e − (a x + b y))² = a b (x − y)² ≥ 0` for every `e`. -/
lemma convexOn_sum_sq (hβ : ∀ e, 0 < β e) (D : Finset ι) :
    ConvexOn ℝ Set.univ fun v => ∑ e ∈ D, (m e - v) ^ 2 / β e := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun e _ => ?_
  have hkey : (m e - (a * x + b * y)) ^ 2 ≤ a * (m e - x) ^ 2 + b * (m e - y) ^ 2 := by
    have hid : a * (m e - x) ^ 2 + b * (m e - y) ^ 2 - (m e - (a * x + b * y)) ^ 2 =
        a * b * (x - y) ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      ring
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
  calc (m e - (a * x + b * y)) ^ 2 / β e ≤ (a * (m e - x) ^ 2 + b * (m e - y) ^ 2) / β e :=
        div_le_div_of_nonneg_right hkey (hβ e).le
    _ = a * ((m e - x) ^ 2 / β e) + b * ((m e - y) ^ 2 / β e) := by ring

/-- The function `v ↦ ∑_{e∈D} (m_e − v)²/β_e` has the derivative `−2(t(D) − v β⁻¹(D))` (not in the
paper: the paper states the derivative without computing it, `appB-tools.tex:66`). -/
lemma hasDerivAt_sum_sq (D : Finset ι) (v : ℝ) :
    HasDerivAt (fun v => ∑ e ∈ D, (m e - v) ^ 2 / β e)
      (-2 * (∑ e ∈ D, m e / β e - v * ∑ e ∈ D, 1 / β e)) v := by
  have h : ∀ e ∈ D, HasDerivAt (fun v => (m e - v) ^ 2 / β e) (-2 * (m e - v) / β e) v := by
    intro e _
    have h1 : HasDerivAt (fun v => m e - v) (-1) v := by
      simpa using (hasDerivAt_id v).const_sub (m e)
    have h2 := (h1.fun_pow 2).div_const (β e)
    convert h2 using 1
    norm_num
  convert HasDerivAt.fun_sum (u := D) (A := fun e v => (m e - v) ^ 2 / β e)
    (A' := fun e => -2 * (m e - v) / β e) h using 1
  rw [mul_sum, ← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun e _ => by ring

/-- The weighted means (`appB-tools.tex:66-68`): `SS(D) = min_{v∈ℝ} ∑_{e∈D} (m_e − v)²/β_e`, that
is, `SS(D) ≤ ∑_{e∈D} (m_e − v)²/β_e` for every `v`, with equality at `v = m̄_D` by the definition of
`SS`. Steps (for nonempty `D`; for `D = ∅` both sides vanish): (1) the function
`v ↦ ∑_{e∈D} (m_e − v)²/β_e` is a convex quadratic (`convexOn_sum_sq`) (2) with derivative
`−2(t(D) − v β⁻¹(D))` (`hasDerivAt_sum_sq`), which vanishes at `v = m̄_D = t(D)/β⁻¹(D)`; (3) so it
is minimized at `v = m̄_D` (a convex function is minimized where its derivative vanishes,
`ConvexOn.isMinOn_of_rightDeriv_eq_zero`), and its minimum is `SS(D)`. -/
lemma SS_le (hβ : ∀ e, 0 < β e) (D : Finset ι) (v : ℝ) :
    SS m β D ≤ ∑ e ∈ D, (m e - v) ^ 2 / β e := by
  rcases D.eq_empty_or_nonempty with rfl | hD
  · simp [SS]
  have hpos : 0 < ∑ e ∈ D, 1 / β e := sum_pos (fun e _ => one_div_pos.2 (hβ e)) hD
  -- (1) The function `v ↦ ∑_{e∈D} (m_e − v)²/β_e` is a convex quadratic
  have hconv := convexOn_sum_sq (m := m) hβ D
  -- (2) with derivative `−2(t(D) − v β⁻¹(D))`, which vanishes at `v = m̄_D`,
  have hderiv := hasDerivAt_sum_sq (m := m) (β := β) D (mbar m β D)
  have hzero : -2 * (∑ e ∈ D, m e / β e - mbar m β D * ∑ e ∈ D, 1 / β e) = 0 := by
    rw [mbar, div_mul_cancel₀ _ hpos.ne', sub_self, mul_zero]
  rw [hzero] at hderiv
  -- (3) so it is minimized at `v = m̄_D`, and `SS(D) = min_{v∈ℝ} ∑_{e∈D} (m_e − v)²/β_e`.
  have hmin : IsMinOn (fun v => ∑ e ∈ D, (m e - v) ^ 2 / β e) Set.univ (mbar m β D) :=
    hconv.isMinOn_of_rightDeriv_eq_zero (by simp)
      (hderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi _))
  exact isMinOn_iff.1 hmin v (Set.mem_univ v)

/-- The weighted means (`appB-tools.tex:70`): hence `SS` is monotone under inclusion, as for
`D ⊆ D'` the choice `v = m̄_{D'}` gives `SS(D) ≤ SS(D')`:
`SS(D) ≤ ∑_{e∈D} (m_e − m̄_{D'})²/β_e ≤ ∑_{e∈D'} (m_e − m̄_{D'})²/β_e = SS(D')`. -/
lemma SS_mono (hβ : ∀ e, 0 < β e) {D D' : Finset ι} (h : D ⊆ D') : SS m β D ≤ SS m β D' :=
  calc SS m β D ≤ ∑ e ∈ D, (m e - mbar m β D') ^ 2 / β e := SS_le hβ D _
    _ ≤ ∑ e ∈ D', (m e - mbar m β D') ^ 2 / β e :=
        sum_le_sum_of_subset_of_nonneg h fun e _ _ => div_nonneg (sq_nonneg _) (hβ e).le

/-- `SS(D) = ∑_{e∈D} m_e²/β_e − t(D)²/β⁻¹(D)` for nonempty `D`: the expansion of the square in
`SS(D)` (the last step of the proof of `lem:fullplane`(e)). -/
lemma SS_eq (hβ : ∀ e, 0 < β e) {D : Finset ι} (hD : D.Nonempty) :
    SS m β D = ∑ e ∈ D, m e ^ 2 / β e - (∑ e ∈ D, m e / β e) ^ 2 / ∑ e ∈ D, 1 / β e := by
  have hpos : 0 < ∑ e ∈ D, 1 / β e := sum_pos (fun e _ => one_div_pos.2 (hβ e)) hD
  have hexp : ∑ e ∈ D, (m e - mbar m β D) ^ 2 / β e = ∑ e ∈ D, m e ^ 2 / β e -
      2 * mbar m β D * ∑ e ∈ D, m e / β e + mbar m β D ^ 2 * ∑ e ∈ D, 1 / β e := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => by ring
  rw [SS, hexp, mbar]
  field_simp
  ring

/-- `eq:B-pair` (`appB-tools.tex:71-74`): `SS({e, e'}) = (m_e − m_{e'})²/(β_e + β_{e'})` for
distinct `e, e'`. Steps: (1) the mean `m̄ = m̄_{{e,e'}}` divides the gap between `m_e` and `m_{e'}`
in the ratio of the curvatures, `m_e − m̄ = β_e (m_e − m_{e'})/(β_e + β_{e'})` and
`m_{e'} − m̄ = −β_{e'} (m_e − m_{e'})/(β_e + β_{e'})`; (2) so
`SS({e, e'}) = (m_e − m̄)²/β_e + (m_{e'} − m̄)²/β_{e'} = (m_e − m_{e'})²/(β_e + β_{e'})`. -/
lemma SS_pair [DecidableEq ι] (hβ : ∀ e, 0 < β e) {a c : ι} (hac : a ≠ c) :
    SS m β {a, c} = (m a - m c) ^ 2 / (β a + β c) := by
  have ha := (hβ a).ne'
  have hc := (hβ c).ne'
  have hac' : β a + β c ≠ 0 := by linarith [hβ a, hβ c]
  have hca' : β c + β a ≠ 0 := by linarith [hβ a, hβ c]
  -- (1) The mean `m̄ = m̄_{{e,e'}}` divides the gap between `m_e` and `m_{e'}` in the ratio of the
  -- curvatures, `m_e − m̄ = β_e (m_e − m_{e'})/(β_e + β_{e'})`
  have h1 : m a - mbar m β {a, c} = β a * (m a - m c) / (β a + β c) := by
    rw [mbar, sum_pair hac, sum_pair hac]
    field_simp
    ring
  -- and `m_{e'} − m̄ = −β_{e'} (m_e − m_{e'})/(β_e + β_{e'})`,
  have h2 : m c - mbar m β {a, c} = -(β c * (m a - m c)) / (β a + β c) := by
    rw [mbar, sum_pair hac, sum_pair hac]
    field_simp
    ring
  -- (2) so `SS({e, e'}) = (m_e − m_{e'})²/(β_e + β_{e'})`.
  rw [SS, sum_pair hac, h1, h2]
  field_simp

/-- `eq:B-twogroups` (`appB-tools.tex:75-78`): for disjoint nonempty `D₁, D₂`,
`SS(D₁ ∪ D₂) = SS(D₁) + SS(D₂) + (m̄_{D₁} − m̄_{D₂})²/(1/β⁻¹(D₁) + 1/β⁻¹(D₂))`. Steps, with
`m̄ = m̄_{D₁ ∪ D₂}`: (1) expanding about the two group means, for `e ∈ D_i`,
`(m_e − m̄)² = (m_e − m̄_{D_i})² + 2 (m_e − m̄_{D_i})(m̄_{D_i} − m̄) + (m̄_{D_i} − m̄)²`,
the cross terms vanish, as `∑_{e∈D_i} (m_e − m̄_{D_i})/β_e = t(D_i) − m̄_{D_i} β⁻¹(D_i) = 0`, so
`SS(D₁ ∪ D₂) = SS(D₁) + SS(D₂) + ∑_i (m̄_{D_i} − m̄)²/(1/β⁻¹(D_i))`; (2) the term between the
groups is `eq:B-pair` (`SS_pair`) for two elements with rewards `m̄_{D_i}` and curvatures
`1/β⁻¹(D_i)` (the elements `true` and `false` of `Bool`), whose mean is `m̄`. -/
lemma SS_union [DecidableEq ι] (hβ : ∀ e, 0 < β e) {D₁ D₂ : Finset ι} (hdisj : Disjoint D₁ D₂)
    (h₁ : D₁.Nonempty) (h₂ : D₂.Nonempty) :
    SS m β (D₁ ∪ D₂) = SS m β D₁ + SS m β D₂ +
      (mbar m β D₁ - mbar m β D₂) ^ 2 / (1 / ∑ e ∈ D₁, 1 / β e + 1 / ∑ e ∈ D₂, 1 / β e) := by
  have hb₁ : 0 < ∑ e ∈ D₁, 1 / β e := sum_pos (fun e _ => one_div_pos.2 (hβ e)) h₁
  have hb₂ : 0 < ∑ e ∈ D₂, 1 / β e := sum_pos (fun e _ => one_div_pos.2 (hβ e)) h₂
  -- (1) Expanding about the two group means, with `m̄ = m̄_{D₁ ∪ D₂}`, the cross terms vanish:
  have hexp : ∀ D : Finset ι, D.Nonempty → ∑ e ∈ D, (m e - mbar m β (D₁ ∪ D₂)) ^ 2 / β e =
      SS m β D + (mbar m β D - mbar m β (D₁ ∪ D₂)) ^ 2 / (1 / ∑ e ∈ D, 1 / β e) := by
    intro D hD
    have hb : 0 < ∑ e ∈ D, 1 / β e := sum_pos (fun e _ => one_div_pos.2 (hβ e)) hD
    -- `(m_e − m̄)² = (m_e − m̄_D)² + 2 (m_e − m̄_D)(m̄_D − m̄) + (m̄_D − m̄)²` for `e ∈ D`,
    have hsq : ∑ e ∈ D, (m e - mbar m β (D₁ ∪ D₂)) ^ 2 / β e = SS m β D +
        2 * (mbar m β D - mbar m β (D₁ ∪ D₂)) * ∑ e ∈ D, (m e - mbar m β D) / β e +
        (mbar m β D - mbar m β (D₁ ∪ D₂)) ^ 2 * ∑ e ∈ D, 1 / β e := by
      rw [SS, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun e _ => by ring
    -- and the cross term vanishes, as `∑_{e∈D} (m_e − m̄_D)/β_e = t(D) − m̄_D β⁻¹(D) = 0`
    have hcross : ∑ e ∈ D, (m e - mbar m β D) / β e = 0 := by
      have hlin : ∑ e ∈ D, (m e - mbar m β D) / β e =
          ∑ e ∈ D, m e / β e - mbar m β D * ∑ e ∈ D, 1 / β e := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun e _ => by ring
      rw [hlin, mbar, div_mul_cancel₀ _ hb.ne', sub_self]
    rw [hsq, hcross, mul_zero, add_zero, div_div_eq_mul_div, div_one]
  -- so `SS(D₁ ∪ D₂) = SS(D₁) + SS(D₂) + ∑_i (m̄_{D_i} − m̄)²/(1/β⁻¹(D_i))`.
  have hsplit : SS m β (D₁ ∪ D₂) = SS m β D₁ + SS m β D₂ +
      ((mbar m β D₁ - mbar m β (D₁ ∪ D₂)) ^ 2 / (1 / ∑ e ∈ D₁, 1 / β e) +
        (mbar m β D₂ - mbar m β (D₁ ∪ D₂)) ^ 2 / (1 / ∑ e ∈ D₂, 1 / β e)) := by
    rw [SS, sum_union hdisj, hexp D₁ h₁, hexp D₂ h₂]
    ring
  -- (2) The term between the groups is `eq:B-pair` for two elements with rewards `m̄_{D_i}` and
  -- curvatures `1/β⁻¹(D_i)`,
  set m₂ : Bool → ℝ := fun i => if i then mbar m β D₁ else mbar m β D₂
  set β₂ : Bool → ℝ := fun i => if i then 1 / ∑ e ∈ D₁, 1 / β e else 1 / ∑ e ∈ D₂, 1 / β e
  have hm₂t : m₂ true = mbar m β D₁ := rfl
  have hm₂f : m₂ false = mbar m β D₂ := rfl
  have hβ₂t : β₂ true = 1 / ∑ e ∈ D₁, 1 / β e := rfl
  have hβ₂f : β₂ false = 1 / ∑ e ∈ D₂, 1 / β e := rfl
  have hβ₂pos : ∀ i, 0 < β₂ i := fun i => by
    cases i
    · rw [hβ₂f]
      exact one_div_pos.2 hb₂
    · rw [hβ₂t]
      exact one_div_pos.2 hb₁
  have htf : (true : Bool) ≠ false := by decide
  -- whose mean is `m̄`.
  have hmean : mbar m₂ β₂ {true, false} = mbar m β (D₁ ∪ D₂) := by
    rw [mbar, sum_pair htf, sum_pair htf, hm₂t, hm₂f, hβ₂t, hβ₂f, mbar, mbar, mbar,
      sum_union hdisj, sum_union hdisj]
    field_simp
  have hSS₂ : SS m₂ β₂ {true, false} =
      (mbar m β D₁ - mbar m β (D₁ ∪ D₂)) ^ 2 / (1 / ∑ e ∈ D₁, 1 / β e) +
        (mbar m β D₂ - mbar m β (D₁ ∪ D₂)) ^ 2 / (1 / ∑ e ∈ D₂, 1 / β e) := by
    rw [SS, hmean, sum_pair htf, hm₂t, hm₂f, hβ₂t, hβ₂f]
  rw [hsplit, ← hSS₂, SS_pair hβ₂pos htf, hm₂t, hm₂f, hβ₂t, hβ₂f]

end WeightedMeans

/-! ### Tight sets -/

omit [Fintype E] in
/-- The tight sets of a vector `y` with `y(S) ≤ g(S)` for all `S` are closed under union and
intersection (`appB-tools.tex:125-131`), by the argument of `prop:tight` [Sch03, Thm. 44.2], which
needs only the submodularity of `g` and `y(S) ≤ g(S)` for all `S`: for tight `S, S'`,
`g(S ∪ S') + g(S ∩ S') ≥ y(S ∪ S') + y(S ∩ S') = y(S) + y(S') = g(S) + g(S')`
`≥ g(S ∪ S') + g(S ∩ S')`,
so equality holds throughout, and as `y(S ∪ S') ≤ g(S ∪ S')` and `y(S ∩ S') ≤ g(S ∩ S')`, both
sets are tight. -/
theorem IsTight.union_inter' (hg : Submodular g) (hy : y ∈ fpPoly g) {S T : Finset E}
    (hS : IsTight g y S) (hT : IsTight g y T) : IsTight g y (S ∪ T) ∧ IsTight g y (S ∩ T) := by
  have h1 := hy (S ∪ T)
  have h2 := hy (S ∩ T)
  -- (1) "Indeed, for tight sets `S, S'`,
  -- `g(S ∪ S') + g(S ∩ S') ≥ y(S ∪ S') + y(S ∩ S') = y(S) + y(S') = g(S) + g(S')`
  -- `≥ g(S ∪ S') + g(S ∩ S')`, so equality holds throughout, …"
  -- The Lean writes `T` for `S'`.
  have hchain : ∑ e ∈ S ∪ T, y e + ∑ e ∈ S ∩ T, y e = g (S ∪ T) + g (S ∩ T) := by
    refine le_antisymm (add_le_add h1 h2) ?_
    calc g (S ∪ T) + g (S ∩ T) ≤ g S + g T := hg S T
      _ = ∑ e ∈ S, y e + ∑ e ∈ T, y e := by rw [hS, hT]
      _ = ∑ e ∈ S ∪ T, y e + ∑ e ∈ S ∩ T, y e := sum_union_inter.symm
  -- (2) "… and as `y(S ∪ S') ≤ g(S ∪ S')` and `y(S ∩ S') ≤ g(S ∩ S')`, both sets are tight."
  unfold IsTight
  constructor <;> linarith

omit [Fintype E] in
/-- A finite union of tight sets is tight; the empty union `∅` is tight as `g(∅) = 0` (not in the
paper: the paper leaves implicit the induction from two sets to finitely many and that the empty
union `∅` is tight). -/
theorem isTight_biUnion' (hg : Submodular g) (h0 : g ∅ = 0) (hy : y ∈ fpPoly g) {ι : Type*}
    [DecidableEq ι] (A : Finset ι) (N : ι → Finset E) (h : ∀ i ∈ A, IsTight g y (N i)) :
    IsTight g y (A.biUnion N) := by
  induction A using Finset.induction_on with
  | empty => simp [IsTight, h0]
  | insert i A _ ih =>
    rw [biUnion_insert]
    exact (IsTight.union_inter' hg hy (h i (mem_insert_self i A))
      (ih fun j hj => h j (mem_insert_of_mem hj))).1

/-- A finite intersection of tight sets is tight; the empty intersection `E` is tight for
`y ∈ B_{(±)}(g)` (not in the paper: the paper leaves implicit the induction from two sets to
finitely many and that the empty intersection `E` is tight). -/
theorem isTight_inf' (hg : Submodular g) (hy : y ∈ fpBase g) {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (N : ι → Finset E) (h : ∀ i ∈ D, IsTight g y (N i)) :
    IsTight g y (D.inf N) := by
  induction D using Finset.induction_on with
  | empty => exact hy.2
  | insert i D _ ih =>
    rw [inf_insert, inf_eq_inter]
    exact (IsTight.union_inter' hg hy.1 (h i (mem_insert_self i D))
      (ih fun j hj => h j (mem_insert_of_mem hj))).2

/-! ### `lem:fullplane`(a): the level criterion -/

/-- `lem:fullplane`(a), the exchange (`appB-tools.tex:114-118`): at a maximizer `x` of
`U_A(· | α)` over `B_{(±)}(g)`, if `ρ_e(x) > ρ_{e'}(x)`, some set that is tight for `x` contains `e`
but not `e'`. Steps: (1) the gradient of `U_A(· | α)` at `x` is `ρ(x)`; for the direction
`v = 1_e − 1_{e'}`, `U_A(x + εv | α) = U_A(x | α) + ε (ρ_e(x) − ρ_{e'}(x)) − ε² (β_e + β_{e'})/2`;
(2) suppose that no set that is tight for `x` contains `e` but not `e'`; (3) moving a little mass
from `e'` to `e`, that is, increasing `x_e` and decreasing `x_{e'}` by the same small amount `ε`,
changes `x(S)` only for the sets `S` that contain exactly one of `e` and `e'`; it increases `x(S)`
only for the sets that contain `e` but not `e'`, which are finitely many and not tight, so for a
small enough amount the new vector stays in `B_{(±)}(g)`; (4) as `ρ_e(x) > ρ_{e'}(x)`, it increases
`U_A(· | α)`, which contradicts the maximality of `x`. ("For a small enough amount" is
`∀ᶠ ε in 𝓝[>] 0`.) -/
theorem exists_tight_exchange (hx : IsBestResponse (fpBase g) m β α x) {e e' : E}
    (hlt : marg m β α x e' < marg m β α x e) : ∃ S, e ∈ S ∧ e' ∉ S ∧ IsTight g x S := by
  have hne : e ≠ e' := by
    rintro rfl
    exact lt_irrefl _ hlt
  -- (1) "The gradient of `U_A(· | α)` at `y` is `ρ(y)`."
  -- The Lean writes `x` for `y` and uses the gradient through the expansion
  -- `U_A(x + εv | α) = U_A(x | α) + ε (ρ_e(x) − ρ_{e'}(x)) − ε² (β_e + β_{e'})/2` in the direction
  -- `v = 1_e − 1_{e'}`.
  set v : E → ℝ := fun e'' => (if e'' = e then 1 else 0) - (if e'' = e' then 1 else 0) with hv
  have hU : ∀ ε : ℝ, utility m β α (x + ε • v) = utility m β α x +
      ε * (marg m β α x e - marg m β α x e') - ε ^ 2 / 2 * (β e + β e') := by
    intro ε
    have h := utility_add_smul m β α ε x (x + v)
    simp only [add_sub_cancel_left, Pi.add_apply] at h
    have h1 : ∑ e'', marg m β α x e'' * v e'' = marg m β α x e - marg m β α x e' := by
      simp only [hv, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq',
        mem_univ, ite_true]
    have h2 : ∑ e'', β e'' * v e'' ^ 2 = β e + β e' := by
      rw [Fintype.sum_eq_add e e' hne fun c hc => by simp [hv, hc.1, hc.2]]
      simp [hv, hne, hne.symm]
    rw [h, h1, h2]
  -- (2) "Let `e, e' ∈ E` with `ρ_e(y) > ρ_{e'}(y)`, and suppose that no set that is tight for `y`
  -- contains `e` but not `e'`."
  -- Here `e`, `e'` and `ρ_e(x) > ρ_{e'}(x)` are hypotheses of the lemma.
  by_contra hcon
  have hslack : ∀ S : Finset E, e ∈ S → e' ∉ S → ∑ e'' ∈ S, x e'' < g S := fun S heS he'S =>
    (hx.1.1 S).lt_of_ne fun h => hcon ⟨S, heS, he'S, h⟩
  -- (3) "Moving a little mass from `e'` to `e`, that is, increasing `y_e` and decreasing `y_{e'}`
  -- by the same small amount, changes `y(S)` only for the sets `S` that contain exactly one of `e`
  -- and `e'`."
  -- The new vector is `x + εv`, for the amount `ε`.
  have hsum : ∀ (ε : ℝ) (S : Finset E), ∑ e'' ∈ S, (x + ε • v) e'' =
      ∑ e'' ∈ S, x e'' + ε * ((if e ∈ S then 1 else 0) - (if e' ∈ S then 1 else 0)) := by
    intro ε S
    simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      sum_sub_distrib, sum_ite_eq']
  -- "It increases `y(S)` only for the sets that contain `e` but not `e'`, which are finitely many
  -- and not tight, so for a small enough amount the new vector stays in `B_{(±)}(g)`."
  have hfeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x + ε • v ∈ fpBase g := by
    have hS : ∀ S : Finset E, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∑ e'' ∈ S, (x + ε • v) e'' ≤ g S := by
      intro S
      by_cases h : e ∈ S ∧ e' ∉ S
      · have hpos : 0 < g S - ∑ e'' ∈ S, x e'' := sub_pos.2 (hslack S h.1 h.2)
        filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hpos)] with ε hε
        rw [hsum, ite_eq_left h.1, ite_eq_right h.2]
        linarith
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε0 : 0 < ε := hε
        have hxS := hx.1.1 S
        rw [hsum]
        by_cases he : e ∈ S
        · have he' : e' ∈ S := by
            by_contra h'
            exact h ⟨he, h'⟩
          rw [ite_eq_left he, ite_eq_left he', sub_self, mul_zero, add_zero]
          exact hxS
        · rw [ite_eq_right he, zero_sub]
          split_ifs <;> nlinarith
    filter_upwards [eventually_all.2 hS] with ε hε
    refine ⟨hε, ?_⟩
    rw [hsum, ite_eq_left (mem_univ e), ite_eq_left (mem_univ e'), sub_self, mul_zero, add_zero]
    exact hx.1.2
  -- (4) "As `ρ_e(y) > ρ_{e'}(y)`, it increases `U_A(· | α)`, …"
  -- The increase is shown by the expansion of (1), for a small enough amount.
  have hinc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), utility m β α x < utility m β α (x + ε • v) := by
    set Δ := marg m β α x e - marg m β α x e'
    have hΔ : 0 < Δ := sub_pos.2 hlt
    have hden : 0 < |β e + β e'| / 2 + 1 := by positivity
    have hpos : 0 < Δ / (|β e + β e'| / 2 + 1) := div_pos hΔ hden
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hpos)]
      with ε hε0 hε
    have hε0' : 0 < ε := hε0
    have h1 : ε * (|β e + β e'| / 2 + 1) < Δ := (lt_div_iff₀ hden).1 hε
    have h2 : ε ^ 2 * (β e + β e') ≤ ε ^ 2 * |β e + β e'| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg ε)
    have h3 := mul_lt_mul_of_pos_left h1 hε0'
    rw [hU]
    nlinarith
  -- "… which contradicts the maximality of `y`."
  obtain ⟨ε, hεB, hεU⟩ := (hfeas.and hinc).exists
  exact absurd (hx.2 _ hεB) (not_le.2 hεU)

/-- `lem:fullplane`(a), the first direction (`appB-tools.tex:119-132`): at the maximizer `x`, every
upper level set `U = A_θ(x)` is tight. Steps: (1) by the exchange (`exists_tight_exchange`), every
`e ∈ U` and every `e' ∈ E ∖ U`, which satisfy `ρ_e(x) ≥ θ > ρ_{e'}(x)`, have a tight set `S_{ee'}`
with `e ∈ S_{ee'}` and `e' ∉ S_{ee'}`; (2) `U = ⋃_{e∈U} ⋂_{e'∈E∖U} S_{ee'}`, an empty intersection
being `E` and an empty union `∅`, because each intersection contains `e` and no element of
`E ∖ U`; (3) the tight sets are closed under union and intersection (`IsTight.union_inter'`, with
`isTight_biUnion'` and `isTight_inf'` for finitely many sets), hence `U` is tight. -/
theorem levelSet_tight (H : FPHyp g β) (hx : IsBestResponse (fpBase g) m β α x) (θ : ℝ) :
    IsTight g x (levelSet m β α x θ) := by
  -- (1) "So for an upper level set `U := A_{θ'}(y)`, every `e ∈ U` and every `e' ∈ E ∖ U`, which
  -- satisfy `ρ_e(y) ≥ θ' > ρ_{e'}(y)`, have a tight set `S_{ee'}` with `e ∈ S_{ee'}` and
  -- `e' ∉ S_{ee'}`."
  -- The Lean writes `x` for `y`, `θ` for `θ'` and `D` for `E ∖ U`; the tight sets come from
  -- `exists_tight_exchange`.
  set U := levelSet m β α x θ
  set D := univ.filter fun e' => marg m β α x e' < θ
  have h2 : ∀ e e', ∃ S, e ∈ U → e' ∈ D → e ∈ S ∧ e' ∉ S ∧ IsTight g x S := by
    intro e e'
    by_cases h : e ∈ U ∧ e' ∈ D
    · have he : θ ≤ marg m β α x e := by simpa [U, levelSet] using h.1
      have he' : marg m β α x e' < θ := by simpa [D] using h.2
      obtain ⟨S, hS⟩ := exists_tight_exchange hx (lt_of_lt_of_le he' he)
      exact ⟨S, fun _ _ => hS⟩
    · exact ⟨∅, fun ha hd => absurd ⟨ha, hd⟩ h⟩
  choose S₂ hS₂ using h2
  -- (2) "Then `U = ⋃_{e∈U} ⋂_{e'∈E∖U} S_{ee'}`, an empty intersection being `E` and an empty union
  -- being `∅`, because each intersection contains `e` and no element of `E ∖ U`."
  set N : E → Finset E := fun e => D.inf (S₂ e)
  have hNe : ∀ e ∈ U, e ∈ N e := fun e he => mem_inf.2 fun e' he' => (hS₂ e e' he he').1
  have hND : ∀ e ∈ U, ∀ e' ∈ D, e' ∉ N e := fun e he e' he' hmem =>
    (hS₂ e e' he he').2.1 (mem_inf.1 hmem e' he')
  have hTU : U.biUnion N = U := by
    refine Subset.antisymm (fun e he => ?_) fun e he => mem_biUnion.2 ⟨e, he, hNe e he⟩
    obtain ⟨e₀, he₀, heN⟩ := mem_biUnion.1 he
    by_contra heU
    have hlt : marg m β α x e < θ := by simpa [U, levelSet] using heU
    exact hND e₀ he₀ e (by simp [D, hlt]) heN
  -- (3) "The tight sets of a vector `y` with `y(S) ≤ g(S)` for all `S` are closed under union and
  -- intersection, by the argument of `prop:tight` [Sch03, Thm. 44.2], which needs only the
  -- submodularity of `g` and `y(S) ≤ g(S)` for all `S`. … Hence `U` is tight."
  -- The omitted sentence is `IsTight.union_inter'`; `isTight_inf'` and `isTight_biUnion'` take it
  -- to finitely many sets, the empty intersection and the empty union included.
  have hNt : ∀ e ∈ U, IsTight g x (N e) := fun e he =>
    isTight_inf' H.submod hx.1 D (S₂ e) fun e' he' => (hS₂ e e' he he').2.2
  have hT : IsTight g x (U.biUnion N) := isTight_biUnion' H.submod H.empty hx.1.1 U N hNt
  rwa [hTU] at hT

omit [DecidableEq E] in
/-- `lem:fullplane`(a), the converse (`appB-tools.tex:134-146`): a vector `y` with `y(S) ≤ g(S)`
for all `S` whose upper level sets `A_θ(y)` are all tight maximizes `U_A(· | α)` over
`B_{(±)}(g)`. Steps: (1) `E = A_θ(y)` for every `θ` below all marginals, so `E` is tight and
`y ∈ B_{(±)}(g)`; (2) by concavity, `U_A(x | α) − U_A(y | α) ≤ ρ(y)^⊤(x − y)`; (3) for
`x ∈ B_{(±)}(g)`, the distinct values `ϱ_1 > ⋯ > ϱ_k` of `ρ(y)` (`Stoc.theta ρ c i`, indices from
0), a level `ϱ_{k+1} < ϱ_k` (here `c = −∑_e |ρ_e(y)| − 1`) and `A_i = A_{ϱ_i}(y)`, as
`x(E) = y(E)`,
`ρ(y)^⊤(x − y) = ∑_e (ρ_e(y) − ϱ_{k+1})(x_e − y_e) = ∑_i (ϱ_i − ϱ_{i+1})(x(A_i) − y(A_i)) ≤ 0`
(the layer-cake identity `Stoc.layerCake` of the proof of `prop:optchar`); (4) so `y` maximizes
`U_A(· | α)` on `B_{(±)}(g)`. -/
theorem isBestResponse_of_levelSets (hβ : ∀ e, 0 < β e) (hy : y ∈ fpPoly g)
    (ht : ∀ θ, IsTight g y (levelSet m β α y θ)) : IsBestResponse (fpBase g) m β α y := by
  set ρ := marg m β α y
  -- A level `c` below all marginals: a `θ'` of step (1) and the arbitrary `ϱ_{k+1} < ϱ_k` of
  -- step (3).
  set c : ℝ := -∑ e, |ρ e| - 1
  have hc : ∀ e, c < ρ e := fun e => by
    have h1 : |ρ e| ≤ ∑ e, |ρ e| :=
      single_le_sum (f := fun e => |ρ e|) (fun e _ => abs_nonneg _) (mem_univ e)
    have h2 := neg_abs_le (ρ e)
    linarith
  -- (1) "As `E = A_{θ'}(y)` for every `θ' ≤ min_{e∈E} ρ_e(y)`, the set `E` is tight, so
  -- `y ∈ B_{(±)}(g)`."
  -- The Lean takes `θ' = c`.
  have hE : levelSet m β α y c = univ := by
    ext e
    simp only [levelSet, mem_filter, mem_univ, true_and, iff_true]
    exact (hc e).le
  have hyB : y ∈ fpBase g := ⟨hy, by have := ht c; rwa [hE] at this⟩
  refine ⟨hyB, fun x hx => ?_⟩
  -- (2) "By concavity, `U_A(x | α) − U_A(y | α) ≤ ρ(y)^⊤(x − y)` for every `x ∈ ℝ^E`."
  -- This is `Stoc.utility_sub_le`, the concavity step of the proof of `prop:optchar`; the Lean
  -- applies it to the `x ∈ B_{(±)}(g)` of step (3), which it introduces before.
  have hconc := utility_sub_le (m := m) (fun e => (hβ e).le) α y x
  -- (3) "Let `x ∈ B_{(±)}(g)`, let `ϱ_1 > ⋯ > ϱ_k` be the distinct values of `ρ(y)`, let
  -- `ϱ_{k+1} < ϱ_k` be arbitrary, and let `A_i := A_{ϱ_i}(y)` for `i = 1, …, k`, so that `A_k = E`.
  -- Since `x(E) = y(E)`, `ρ(y)^⊤(x − y) = ∑_{e∈E} (ρ_e(y) − ϱ_{k+1})(x_e − y_e)` …"
  -- Here `ϱ_{k+1}` is `c`, and the `ϱ_i` are `Stoc.theta ρ c i` (indices from 0).
  have h1 : ∑ e, ρ e * (x e - y e) = ∑ e, (ρ e - c) * (x e - y e) := by
    have hxy : ∑ e, (x e - y e) = 0 := by rw [sum_sub_distrib, hx.2, hyB.2, sub_self]
    have : ∑ e, (ρ e - c) * (x e - y e) = ∑ e, ρ e * (x e - y e) - c * ∑ e, (x e - y e) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun e _ => by ring
    rw [this, hxy, mul_zero, sub_zero]
  -- "… `= ∑_{i=1}^k (ϱ_i − ϱ_{i+1})(x(A_i) − y(A_i))` …"
  -- This equality is the layer-cake identity `Stoc.layerCake`.
  have h2 := layerCake (fun e => (hc e).le) (fun e => x e - y e)
  -- "… `≤ 0`, as every `A_i` is tight for `y` and `x(A_i) ≤ g(A_i)`."
  have h3 : ∑ i ∈ range (numVals ρ c), (theta ρ c i - theta ρ c (i + 1)) *
      ∑ e ∈ univ.filter (fun e => theta ρ c i ≤ ρ e), (x e - y e) ≤ 0 := by
    refine sum_nonpos fun i hi => mul_nonpos_of_nonneg_of_nonpos ?_ ?_
    · exact sub_nonneg.2 (theta_lt_theta (Nat.lt_succ_self i) (mem_range.1 hi)).le
    · have hti : ∑ e ∈ levelSet m β α y (theta ρ c i), y e = g (levelSet m β α y (theta ρ c i)) :=
        ht (theta ρ c i)
      have hxi := hx.1 (levelSet m β α y (theta ρ c i))
      rw [sum_sub_distrib]
      show ∑ e ∈ levelSet m β α y (theta ρ c i), x e -
        ∑ e ∈ levelSet m β α y (theta ρ c i), y e ≤ 0
      linarith
  -- (4) "So `y` maximizes `U_A(· | α)` on `B_{(±)}(g)`, …"
  linarith

/-- The level criterion (a) in the form used below: such a `y` is `ξ^g(α)`. -/
theorem eq_xi_of_levelSets (H : FPHyp g β) (hy : y ∈ fpPoly g)
    (ht : ∀ θ, IsTight g y (levelSet m β α y θ)) : y = xi g m β α :=
  H.eq_xi (isBestResponse_of_levelSets H.pos hy ht)

/-- (a) for `ξ^g`: every upper level set `A^g_θ(α) = {e : ρ^g_e(α) ≥ θ}` is tight. -/
theorem xi_levelSet_tight (H : FPHyp g β) (m : E → ℝ) (α θ : ℝ) :
    IsTight g (xi g m β α) (levelSet m β α (xi g m β α) θ) :=
  levelSet_tight H (H.isBestResponse m α) θ

/-- (a), the last step (`appB-tools.tex:148-149`): the set `{e : ρ^g_e(α) > θ}` is empty or equals
`A^g_{θ''}(α)` for the smallest marginal `θ''` of its elements, so it is an upper level set of
`ρ(ξ^g(α))` at the share `α` (if it is empty, every `ρ^g_e(α) ≤ θ`, and it is `A^g_{θ+1}(α)`), and
it is tight for `ξ^g(α)` by (a) (`xi_levelSet_tight`). -/
theorem xi_strictLevelSet_tight (H : FPHyp g β) (m : E → ℝ) (α θ : ℝ) :
    IsTight g (xi g m β α) (univ.filter fun e => θ < rho g m β α e) := by
  set U := univ.filter fun e => θ < rho g m β α e
  -- (1) "Finally, the set `{e ∈ E : ρ^g_e(α) > θ}` is empty or equals `A^g_{θ''}(α)`, where `θ''`
  -- is the smallest marginal of its elements."
  have hlev : ∃ θ', U = levelSet m β α (xi g m β α) θ' := by
    by_cases hU : U.Nonempty
    · obtain ⟨e₀, he₀, hmin⟩ := U.exists_min_image (rho g m β α) hU
      refine ⟨rho g m β α e₀, ?_⟩
      ext e
      simp only [U, levelSet, mem_filter, mem_univ, true_and]
      constructor
      · intro h
        exact hmin e (by simpa [U] using h)
      · intro h
        have : θ < rho g m β α e₀ := by simpa [U] using he₀
        exact lt_of_lt_of_le this h
    · -- (if it is empty, every `ρ^g_e(α) ≤ θ < θ + 1`, and it is `A^g_{θ+1}(α)`)
      refine ⟨θ + 1, ?_⟩
      ext e
      have he : rho g m β α e ≤ θ := not_lt.1 fun h => hU ⟨e, by simp [U, h]⟩
      have : marg m β α (xi g m β α) e = rho g m β α e := rfl
      simp only [U, levelSet, mem_filter, mem_univ, true_and]
      constructor
      · intro h
        linarith
      · intro h
        linarith
  -- (2) "So both sets of the last claim are upper level sets of `ρ(ξ^g(α))` at the share `α`, and
  -- they are tight for `ξ^g(α)`."
  -- The Lean shows it for the set `{e ∈ E : ρ^g_e(α) > θ}`, by (a) (`xi_levelSet_tight`).
  obtain ⟨θ', hθ'⟩ := hlev
  rw [hθ']
  exact xi_levelSet_tight H m α θ'

/-- **`lem:fullplane`(a)** (Lemma B.10, `appB-tools.tex:83-84`, proof
`appB-tools.tex:112-149`): for `g` submodular with `g(∅) = 0`, `m, β > 0` and `α, θ ∈ ℝ`, a vector
`y ∈ ℝ^E` is `ξ^g(α)` if and only if `y(S) ≤ g(S)` for all `S ⊆ E` and every upper level set
`A_{θ'}(y)`, `θ' ∈ ℝ`, of the marginals at the share `α` is tight for `y`; in particular, the sets
`A^g_θ(α)` and `{e : ρ^g_e(α) > θ}` are tight for `ξ^g(α)`. Steps: (1) `y := ξ^g(α)` satisfies
`y(S) ≤ g(S)` for all `S`, as `y ∈ B_{(±)}(g)`; (2) the exchange: if `ρ_e(y) > ρ_{e'}(y)`, some
tight set contains `e` but not `e'` (`exists_tight_exchange`); (3) every upper level set `U` is
`⋃_{e∈U} ⋂_{e'∈E∖U} S_{ee'}`, and the tight sets are closed under union and intersection, so `U` is
tight (`levelSet_tight`); (4) conversely, a `y` with the two properties has `E` tight, so
`y ∈ B_{(±)}(g)`, and by concavity and the telescoping sum over the distinct values of `ρ(y)` it
maximizes `U_A(· | α)` on `B_{(±)}(g)`, that is, `y = ξ^g(α)` (`isBestResponse_of_levelSets`);
(5) the set `{e : ρ^g_e(α) > θ}` is empty or an upper level set, so both sets of the last claim are
tight (`xi_strictLevelSet_tight`). The hypothesis `m > 0` is not used. (The text after the lemma,
`appB-tools.tex:107`, notes that (a) is in substance Fujishige's criterion [Fuj05, Thm. 9.1], and
its exchange step Groenevelt's [Fuj05, Thm. 8.1]; the proof here is the paper's own.) -/
theorem fullplane_a (hg : Submodular g) (hg0 : g ∅ = 0) (_hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) (α θ : ℝ) :
    (∀ y : E → ℝ, y = xi g m β α ↔
        (∀ S : Finset E, ∑ e ∈ S, y e ≤ g S) ∧ ∀ θ' : ℝ, IsTight g y (levelSet m β α y θ')) ∧
      IsTight g (xi g m β α) (levelSet m β α (xi g m β α) θ) ∧
      IsTight g (xi g m β α) (univ.filter fun e => θ < rho g m β α e) := by
  have H : FPHyp g β := ⟨hg, hg0, hβ⟩
  refine ⟨fun y => ⟨?_, ?_⟩, ?_, ?_⟩
  · -- (1) "We first show that `y := ξ^g(α)` has the two properties. It satisfies `y(S) ≤ g(S)` for
    -- all `S`, as `y ∈ B_{(±)}(g)`."
    -- (2), (3) "The gradient of `U_A(· | α)` at `y` is `ρ(y)`. … Hence `U` is tight."
    -- These sentences (`appB-tools.tex:114-132`) are `exists_tight_exchange` and `levelSet_tight`.
    rintro rfl
    exact ⟨(xi_mem_fpBase H m α).1, levelSet_tight H (H.isBestResponse m α)⟩
  · -- (4) "Conversely, let `y` satisfy the two conditions. … So `y` maximizes `U_A(· | α)` on
    -- `B_{(±)}(g)`, that is, `y = ξ^g(α)`."
    -- The omitted sentences (`appB-tools.tex:135-143`) are `isBestResponse_of_levelSets`.
    rintro ⟨hy, ht⟩
    exact H.eq_xi (isBestResponse_of_levelSets hβ hy ht)
  · -- (5) "Finally, the set `{e ∈ E : ρ^g_e(α) > θ}` is empty or equals `A^g_{θ''}(α)`, where `θ''`
    -- is the smallest marginal of its elements. So both sets of the last claim are upper level
    -- sets of `ρ(ξ^g(α))` at the share `α`, and they are tight for `ξ^g(α)`."
    -- For `A^g_θ(α)`, this is `xi_levelSet_tight`.
    exact xi_levelSet_tight H m α θ
  · -- For `{e ∈ E : ρ^g_e(α) > θ}`, it is `xi_strictLevelSet_tight`.
    exact xi_strictLevelSet_tight H m α θ

/-! ### `lem:fullplane`(b): the level sets -/

/-- `lem:fullplane`(b), auxiliary form (`appB-tools.tex:151-159`): the level set
`A = A^g_θ(α)` minimizes `F^g_{α,θ}` and contains every set `S` with `F^g_{α,θ}(S) ≤ F^g_{α,θ}(A)`.
Steps: (1) `ξ_e = α t_e − ρ^g_e(α)/β_e`, so
`F^g_{α,θ}(S) = (g(S) − ξ(S)) + ∑_{e∈S} (θ − ρ^g_e(α))/β_e`; (2) the first term is nonnegative, and
it vanishes at `S = A` by (a); (3) the sum is smallest exactly for the sets that contain every `e`
with `ρ^g_e(α) > θ` and no `e` with `ρ^g_e(α) < θ`, among them `A`; (4) so `A` minimizes
`F^g_{α,θ}`, and every minimizer makes the sum smallest, hence is contained in `A`. -/
theorem levelSet_isMaxMinimiser (H : FPHyp g β) (m : E → ℝ) (α θ : ℝ) :
    (∀ S, levelFun g m β α θ (levelSet m β α (xi g m β α) θ) ≤ levelFun g m β α θ S) ∧
      ∀ S, levelFun g m β α θ S ≤ levelFun g m β α θ (levelSet m β α (xi g m β α) θ) →
        S ⊆ levelSet m β α (xi g m β α) θ := by
  set ξ := xi g m β α
  set ρ := rho g m β α
  set A := levelSet m β α ξ θ
  set w : E → ℝ := fun e => (θ - ρ e) / β e
  -- (1) "In short, `ξ := ξ^g(α)` has `ξ_e = α t_e − ρ^g_e(α)/β_e`, so
  -- `F^g_{α,θ}(S) = (g(S) − ξ(S)) + ∑_{e∈S} (θ − ρ^g_e(α))/β_e` (`S ⊆ E`)."
  -- The Lean writes `A` for `A^g_θ(α)` and `w_e` for `(θ − ρ^g_e(α))/β_e`.
  have hF : ∀ S, levelFun g m β α θ S = (g S - ∑ e ∈ S, ξ e) + ∑ e ∈ S, w e := by
    intro S
    have key : ∀ e, -(α * (m e / β e)) + θ * (1 / β e) = -ξ e + w e := by
      intro e
      simp only [w, ρ, rho, marg]
      have := (H.pos e).ne'
      field_simp
      ring
    unfold levelFun
    rw [mul_sum, mul_sum]
    have : g S - ∑ e ∈ S, α * (m e / β e) + ∑ e ∈ S, θ * (1 / β e) =
        g S + ∑ e ∈ S, (-(α * (m e / β e)) + θ * (1 / β e)) := by
      rw [sum_add_distrib, sum_neg_distrib]
      ring
    rw [this, sum_congr rfl fun e _ => key e, sum_add_distrib, sum_neg_distrib]
    ring
  -- (2) "The first term is nonnegative, and it vanishes at `S = A^g_θ(α)` by (a)."
  have hfirst : ∀ S, 0 ≤ g S - ∑ e ∈ S, ξ e := fun S =>
    sub_nonneg.2 ((xi_mem_fpBase H m α).1 S)
  have hfirstA : g A - ∑ e ∈ A, ξ e = 0 := by
    have := xi_levelSet_tight H m α θ
    unfold IsTight at this
    rw [this, sub_self]
  -- (3) "The sum is smallest exactly for the sets that contain every `e` with `ρ^g_e(α) > θ` and no
  -- `e` with `ρ^g_e(α) < θ`, among them `A^g_θ(α)`."
  -- The Lean shows it with `P = {e : ρ^g_e(α) > θ}`: `∑_{e∈S} w_e − ∑_{e∈P} w_e` is a sum of
  -- nonnegative terms, which all vanish exactly if `P ⊆ S ⊆ A`.
  set P := univ.filter fun e => θ < ρ e
  have hwP : ∀ e, e ∈ P ↔ w e < 0 := by
    intro e
    simp only [P, w, mem_filter, mem_univ, true_and]
    rw [div_neg_iff]
    constructor
    · intro h
      exact Or.inr ⟨by linarith, H.pos e⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_lt.2 (H.pos e).le)
      · linarith
  have hwA : ∀ e, e ∈ A ↔ w e ≤ 0 := by
    intro e
    simp only [A, levelSet, mem_filter, mem_univ, true_and, w]
    rw [div_nonpos_iff]
    constructor
    · intro h
      exact Or.inr ⟨by simp only [ρ, rho]; linarith, (H.pos e).le⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_le.2 (H.pos e))
      · simp only [ρ, rho] at h
        linarith
  set φ : Finset E → E → ℝ := fun S e => (if e ∈ S then w e else 0) - (if e ∈ P then w e else 0)
  have hdiff : ∀ S, ∑ e ∈ S, w e - ∑ e ∈ P, w e = ∑ e, φ S e := by
    intro S
    simp only [φ, sum_sub_distrib, sum_ite_mem, univ_inter]
  have hφ : ∀ S e, 0 ≤ φ S e := by
    intro S e
    simp only [φ]
    by_cases heP : e ∈ P
    · have := (hwP e).1 heP
      split_ifs <;> linarith
    · have : 0 ≤ w e := not_lt.1 fun h => heP ((hwP e).2 h)
      split_ifs <;> linarith
  have hlow : ∀ S, ∑ e ∈ P, w e ≤ ∑ e ∈ S, w e := fun S => by
    have := hdiff S
    have := sum_nonneg fun e (_ : e ∈ univ) => hφ S e
    linarith
  have hexact : ∀ S, ∑ e ∈ S, w e = ∑ e ∈ P, w e ↔ P ⊆ S ∧ S ⊆ A := by
    intro S
    rw [← sub_eq_zero, hdiff, sum_eq_zero_iff_of_nonneg fun e _ => hφ S e]
    constructor
    · intro h
      refine ⟨fun e heP => ?_, fun e heS => ?_⟩
      · have h0 := h e (mem_univ e)
        have hw := (hwP e).1 heP
        by_contra heS
        simp only [φ, ite_eq_right heS, ite_eq_left heP] at h0
        linarith
      · have h0 := h e (mem_univ e)
        by_cases heP : e ∈ P
        · exact (hwA e).2 ((hwP e).1 heP).le
        · simp only [φ, ite_eq_left heS, ite_eq_right heP, sub_zero] at h0
          exact (hwA e).2 h0.le
    · rintro ⟨hPS, hSA⟩ e _
      simp only [φ]
      by_cases heP : e ∈ P
      · rw [ite_eq_left (hPS heP), ite_eq_left heP, sub_self]
      · rw [ite_eq_right heP, sub_zero]
        split_ifs with heS
        · have h1 := (hwA e).1 (hSA heS)
          have h2 : 0 ≤ w e := not_lt.1 fun h => heP ((hwP e).2 h)
          linarith
        · rfl
  have hPA : P ⊆ A := fun e he => (hwA e).2 ((hwP e).1 he).le
  have hA : ∑ e ∈ A, w e = ∑ e ∈ P, w e := (hexact A).2 ⟨hPA, Subset.refl A⟩
  -- (4) "So `A^g_θ(α)` minimizes `F^g_{α,θ}`, and every minimizer makes the sum smallest, hence is
  -- contained in `A^g_θ(α)`."
  refine ⟨fun S => ?_, fun S hS => ?_⟩
  · rw [hF, hF, hfirstA, hA]
    linarith [hfirst S, hlow S]
  · rw [hF, hF, hfirstA, hA] at hS
    have h1 := hfirst S
    have h2 := hlow S
    exact ((hexact S).1 (by linarith)).2

/-- **`lem:fullplane`(b)** (`appB-tools.tex:85`, proof `appB-tools.tex:151-159`):
for `g` submodular with `g(∅) = 0`, `m, β > 0` and `α, θ ∈ ℝ`, the set `A^g_θ(α)` minimizes
`F^g_{α,θ}` and contains every minimizer. The proof of `thm:levelsets` with (a) for the tightness
of `A^g_θ(α)`, in the steps of `levelSet_isMaxMinimiser`: (1) `ξ_e = α t_e − ρ^g_e(α)/β_e`, so
`F^g_{α,θ}(S) = (g(S) − ξ(S)) + ∑_{e∈S} (θ − ρ^g_e(α))/β_e`; (2) the first term is nonnegative and
vanishes at `A^g_θ(α)` by (a); (3) the sum is smallest exactly for the sets that contain every `e`
with `ρ^g_e(α) > θ` and no `e` with `ρ^g_e(α) < θ`; (4) so `A^g_θ(α)` minimizes `F^g_{α,θ}`, and
every minimizer is contained in it. The hypothesis `m > 0` is not used. -/
theorem fullplane_b (hg : Submodular g) (hg0 : g ∅ = 0) (_hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) (α θ : ℝ) :
    (∀ S, levelFun g m β α θ (levelSet m β α (xi g m β α) θ) ≤ levelFun g m β α θ S) ∧
      ∀ S, (∀ S', levelFun g m β α θ S ≤ levelFun g m β α θ S') →
        S ⊆ levelSet m β α (xi g m β α) θ := by
  have H : FPHyp g β := ⟨hg, hg0, hβ⟩
  exact ⟨(levelSet_isMaxMinimiser H m α θ).1,
    fun S hS => (levelSet_isMaxMinimiser H m α θ).2 S (hS _)⟩

/-! ### `lem:fullplane`(c): rates -/

/-- `lem:fullplane`(c), the lower rate of one element (`appB-tools.tex:161-170`), auxiliary form:
if `c β⁻¹(S) ≤ t(S)` for every `S ∋ b`, then `ρ^g_b(α) + c Δ ≤ ρ^g_b(α + Δ)` for `Δ ≥ 0`. Steps:
(1) `ρ_0 = ρ^g_b(α)`, `A = A^g_{ρ_0}(α)`, `A' = A^g_{ρ_0 + cΔ}(α + Δ)`, so that `b ∈ A`; suppose
`b ∉ A'`; (2) `G = F^g_{α,ρ_0}` and `G' = F^g_{α+Δ,ρ_0+cΔ}` satisfy `G' = G − Δ(t − c β⁻¹)`;
(3) by submodularity of `G'` and the minimality of `A` for `G` (by (b)),
`G'(A ∪ A') − G'(A') ≤ G'(A) − G'(A ∩ A') = G(A) − G(A ∩ A') − Δ (t − cβ⁻¹)(A ∖ A') ≤ 0`, as
`b ∈ A ∖ A'`; (4) so `A ∪ A'` minimizes `G'`, and `A ⊆ A ∪ A' ⊆ A'` by (b), a contradiction. -/
theorem rho_add_ge_of (H : FPHyp g β) {b : E} {c : ℝ}
    (hc : ∀ S : Finset E, b ∈ S → c * ∑ e ∈ S, 1 / β e ≤ ∑ e ∈ S, m e / β e)
    (α : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : rho g m β α b + δ * c ≤ rho g m β (α + δ) b := by
  -- (1) "Let `Δ ≥ 0`, `ρ_0 := ρ^g_b(α)`, `A := A^g_{ρ_0}(α)` and `A' := A^g_{ρ_0+cΔ}(α + Δ)`, so
  -- that `b ∈ A`, and suppose that `b ∉ A'`."
  -- The Lean writes `δ` for `Δ` and supposes the negation of the claim, which gives `b ∉ A'`.
  set ρ₀ := rho g m β α b
  set A := levelSet m β α (xi g m β α) ρ₀
  set A' := levelSet m β (α + δ) (xi g m β (α + δ)) (ρ₀ + c * δ)
  have hbA : b ∈ A := by simp [A, levelSet, ρ₀, rho]
  by_contra hcon
  have hbA' : b ∉ A' := by
    simp only [A', levelSet, mem_filter, mem_univ, true_and, not_le]
    show rho g m β (α + δ) b < ρ₀ + c * δ
    linarith
  -- (2) "Write `G := F^g_{α,ρ_0}` and `G' := F^g_{α+Δ,ρ_0+cΔ}`. Then `G' = G − Δ(t − c β⁻¹)`, …"
  set G := levelFun g m β α ρ₀
  set G' := levelFun g m β (α + δ) (ρ₀ + c * δ)
  have hGG' : ∀ S, G' S = G S - δ * (∑ e ∈ S, m e / β e - c * ∑ e ∈ S, 1 / β e) := fun S => by
    simp only [G, G', levelFun]
    ring
  -- (3) "… and by submodularity of `G'` and the minimality of `A` for `G` (by (b)),
  -- `G'(A ∪ A') − G'(A') ≤ G'(A) − G'(A ∩ A')`
  -- `= G(A) − G(A ∩ A') − Δ (t − c β⁻¹)(A ∖ A') ≤ 0`,
  -- as `b ∈ A ∖ A'` gives `c β⁻¹(A ∖ A') ≤ t(A ∖ A')`."
  have hsub := levelFun_submodular H.submod m β (α + δ) (ρ₀ + c * δ) A A'
  have hmin := (levelSet_isMaxMinimiser H m α ρ₀).1 (A ∩ A')
  have hsplit : ∀ f : E → ℝ, ∑ e ∈ A, f e = ∑ e ∈ A ∩ A', f e + ∑ e ∈ A \ A', f e :=
    fun f => (sum_inter_add_sum_sdiff A A' f).symm
  have hbd : 0 ≤ ∑ e ∈ A \ A', m e / β e - c * ∑ e ∈ A \ A', 1 / β e :=
    sub_nonneg.2 (hc (A \ A') (mem_sdiff.2 ⟨hbA, hbA'⟩))
  have hcalc : G' (A ∪ A') - G' A' ≤ 0 :=
    calc G' (A ∪ A') - G' A' ≤ G' A - G' (A ∩ A') := by linarith
      _ = G A - G (A ∩ A') -
            δ * (∑ e ∈ A \ A', m e / β e - c * ∑ e ∈ A \ A', 1 / β e) := by
          rw [hGG', hGG', hsplit fun e => m e / β e, hsplit fun e => 1 / β e]
          ring
      _ ≤ 0 := by nlinarith [mul_nonneg hδ hbd]
  -- (4) "So `A ∪ A'` minimizes `G'`, and `A ⊆ A ∪ A' ⊆ A'` by (b), a contradiction. Hence
  -- `ρ^g_b(α + Δ) ≥ ρ_0 + cΔ`."
  have hAA' : A ∪ A' ⊆ A' := (levelSet_isMaxMinimiser H m (α + δ) (ρ₀ + c * δ)).2 _ (by linarith)
  exact hbA' (hAA' (mem_union_left _ hbA))

/-- `lem:fullplane`(c), the upper rate (`appB-tools.tex:172-180`), auxiliary form for a bound
`C ≥ m` (the paper's `m_max`): `ρ^g_e(α + Δ) ≤ ρ^g_e(α) + C Δ` for `Δ ≥ 0`. Steps: (1)
`ρ_1 = ρ^g_e(α + Δ)`, `A' = A^g_{ρ_1}(α + Δ)`, `A = A^g_{ρ_1 − CΔ}(α)`, so that `e ∈ A'`; suppose
`e ∉ A`; (2) `G = F^g_{α+Δ,ρ_1}` and `G' = F^g_{α,ρ_1−CΔ}` satisfy `G' = G − Δ(Cβ⁻¹ − t)` with
`Cβ⁻¹ − t ≥ 0`, and by (b) `A'` minimizes `G` and `A` minimizes `G'`; (3) the same computation with
`A` and `A'` exchanged,
`G'(A ∪ A') − G'(A) ≤ G'(A') − G'(A ∩ A') = G(A') − G(A ∩ A') − Δ(Cβ⁻¹ − t)(A' ∖ A) ≤ 0`;
(4) so `A ∪ A'` minimizes `G'`, and `e ∈ A' ⊆ A ∪ A' ⊆ A` by (b), a contradiction. -/
theorem rho_add_le (H : FPHyp g β) {C : ℝ} (hC : ∀ e, m e ≤ C) (α : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (e : E) : rho g m β (α + δ) e ≤ rho g m β α e + δ * C := by
  -- (1) "For the upper rate, let `e ∈ E`, `m_max := max_{e'∈E} m_{e'}`, `ρ_1 := ρ^g_e(α + Δ)`,
  -- `A' := A^g_{ρ_1}(α + Δ)` and `A := A^g_{ρ_1−m_max Δ}(α)`, so that `e ∈ A'`, and suppose that
  -- `e ∉ A`."
  -- The Lean writes `C` for `m_max`, for any `C` with `m_{e'} ≤ C` for all `e'`, and `δ` for `Δ`;
  -- it supposes the negation of the claim, which gives `e ∉ A`.
  set ρ₁ := rho g m β (α + δ) e
  set A' := levelSet m β (α + δ) (xi g m β (α + δ)) ρ₁
  set A := levelSet m β α (xi g m β α) (ρ₁ - C * δ)
  have heA' : e ∈ A' := by simp [A', levelSet, ρ₁, rho]
  by_contra hcon
  have heA : e ∉ A := by
    simp only [A, levelSet, mem_filter, mem_univ, true_and, not_le]
    show rho g m β α e < ρ₁ - C * δ
    linarith
  -- (2) "Now `G := F^g_{α+Δ,ρ_1}` and `G' := F^g_{α,ρ_1−m_max Δ}` satisfy
  -- `G' = G − Δ(m_max β⁻¹ − t)` with `m_max β⁻¹ − t ≥ 0`, and by (b), `A'` minimizes `G` and `A`
  -- minimizes `G'`."
  set G := levelFun g m β (α + δ) ρ₁
  set G' := levelFun g m β α (ρ₁ - C * δ)
  have hGG' : ∀ S, G' S = G S - δ * (C * ∑ e ∈ S, 1 / β e - ∑ e ∈ S, m e / β e) := fun S => by
    simp only [G, G', levelFun]
    ring
  have hnn : ∀ S : Finset E, 0 ≤ C * ∑ e ∈ S, 1 / β e - ∑ e ∈ S, m e / β e := fun S => by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_nonneg fun e _ => by
      rw [mul_one_div, ← sub_div]
      exact div_nonneg (sub_nonneg.2 (hC e)) (H.pos e).le
  -- (3) "The same computation with the roles of `A` and `A'` exchanged,
  -- `G'(A ∪ A') − G'(A) ≤ G'(A') − G'(A ∩ A')`
  -- `= G(A') − G(A ∩ A') − Δ (m_max β⁻¹ − t)(A' ∖ A) ≤ 0`, …"
  have hsub := levelFun_submodular H.submod m β α (ρ₁ - C * δ) A A'
  have hmin := (levelSet_isMaxMinimiser H m (α + δ) ρ₁).1 (A ∩ A')
  have hsplit : ∀ f : E → ℝ, ∑ e ∈ A', f e = ∑ e ∈ A ∩ A', f e + ∑ e ∈ A' \ A, f e := by
    intro f
    rw [inter_comm]
    exact (sum_inter_add_sum_sdiff A' A f).symm
  have hcalc : G' (A ∪ A') - G' A ≤ 0 :=
    calc G' (A ∪ A') - G' A ≤ G' A' - G' (A ∩ A') := by linarith
      _ = G A' - G (A ∩ A') -
            δ * (C * ∑ e ∈ A' \ A, 1 / β e - ∑ e ∈ A' \ A, m e / β e) := by
          rw [hGG', hGG', hsplit fun e => m e / β e, hsplit fun e => 1 / β e]
          ring
      _ ≤ 0 := by nlinarith [mul_nonneg hδ (hnn (A' \ A))]
  -- (4) "… shows that `A ∪ A'` minimizes `G'`, so `e ∈ A' ⊆ A ∪ A' ⊆ A` by (b), a contradiction.
  -- Hence `ρ^g_e(α) ≥ ρ_1 − m_max Δ`, that is, `ρ^g_e(α + Δ) ≤ ρ^g_e(α) + m_max Δ`."
  have hAA : A ∪ A' ⊆ A := (levelSet_isMaxMinimiser H m α (ρ₁ - C * δ)).2 _ (by linarith)
  exact heA (hAA (mem_union_right _ heA'))

/-- **`lem:fullplane`(c)** (`appB-tools.tex:86-89`, proof `appB-tools.tex:161-185`): let `g`
be submodular with `g(∅) = 0`, `m, β > 0`, and let `b ∈ E` and `c ∈ ℝ` with `c β⁻¹(S) ≤ t(S)` for
every `S ∋ b`. Then `ρ^g_b` grows at least at the rate `c`, and every `ρ^g_e` grows at most at the
rate `max_{e'} m_{e'}`. In particular, every `ρ^g_e` grows at least at the rate
`min_{e'} m_{e'} > 0` and at most at the rate `max_{e'} m_{e'}`, so it is nondecreasing, and `ρ^g`,
`ξ^g` and `α ↦ r(ξ^g(α))` are continuous. Moreover, `ρ^g_b` grows at least at the rate
`t_b/β⁻¹(E)`. (`max` and `min` are `univ.sup' _ m` and `univ.inf' _ m`, for `E ∋ e` nonempty.)
Steps: (1) the lower rate `rho_add_ge_of`; (2) the upper rate `rho_add_le` with `C = m_max`;
(3) `c = min m` satisfies `c β⁻¹(S) ≤ t(S)` for every `S`, and `c = t_b/β⁻¹(E)` satisfies
`c β⁻¹(S) ≤ t_b ≤ t(S)` for every `S ∋ b`; (4) the rates give
`|ρ^g_e(α') − ρ^g_e(α)| ≤ m_max |α' − α|`, so `ρ^g` is continuous, and so are
`ξ^g_e(α) = α t_e − ρ^g_e(α)/β_e` and `r(ξ^g(α)) = m^⊤ξ^g(α)`. -/
theorem fullplane_c (hg : Submodular g) (hg0 : g ∅ = 0) (hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) (b : E) (c : ℝ)
    (hc : ∀ S : Finset E, b ∈ S → c * ∑ e ∈ S, 1 / β e ≤ ∑ e ∈ S, m e / β e) :
    GrowsAtLeast (fun α => rho g m β α b) c ∧
      (∀ e : E, GrowsAtMost (fun α => rho g m β α e) (univ.sup' ⟨e, mem_univ e⟩ m)) ∧
      (∀ e : E, GrowsAtLeast (fun α => rho g m β α e) (univ.inf' ⟨e, mem_univ e⟩ m) ∧
        0 < univ.inf' ⟨e, mem_univ e⟩ m ∧
        GrowsAtMost (fun α => rho g m β α e) (univ.sup' ⟨e, mem_univ e⟩ m) ∧
        Monotone fun α => rho g m β α e) ∧
      Continuous (fun α => rho g m β α) ∧ Continuous (fun α => xi g m β α) ∧
      Continuous (fun α => reward m (xi g m β α)) ∧
      GrowsAtLeast (fun α => rho g m β α b) ((m b / β b) / ∑ e, 1 / β e) := by
  have H : FPHyp g β := ⟨hg, hg0, hβ⟩
  -- (1) "Let `Δ ≥ 0`, `ρ_0 := ρ^g_b(α)`, … Hence `ρ^g_b(α + Δ) ≥ ρ_0 + cΔ`."
  -- These sentences (`appB-tools.tex:161-170`) are `rho_add_ge_of`.
  have hlow : ∀ (b' : E) (c' : ℝ), (∀ S : Finset E, b' ∈ S →
      c' * ∑ e ∈ S, 1 / β e ≤ ∑ e ∈ S, m e / β e) →
      GrowsAtLeast (fun α => rho g m β α b') c' := fun b' c' hc' α Δ hΔ => by
    have := rho_add_ge_of H hc' α hΔ
    simp only
    linarith
  -- (2) "For the upper rate, let `e ∈ E`, `m_max := max_{e'∈E} m_{e'}`, … Hence
  -- `ρ^g_e(α) ≥ ρ_1 − m_max Δ`, that is, `ρ^g_e(α + Δ) ≤ ρ^g_e(α) + m_max Δ`."
  -- These sentences (`appB-tools.tex:172-180`) are `rho_add_le`, here with `C = m_max`.
  have hup : ∀ e : E, GrowsAtMost (fun α => rho g m β α e) (univ.sup' ⟨e, mem_univ e⟩ m) :=
    fun e α Δ hΔ => by
      have := rho_add_le H (C := univ.sup' ⟨e, mem_univ e⟩ m)
        (fun e' => le_sup' m (mem_univ e')) α hΔ e
      simp only
      linarith
  -- (3) "The two lower rates hold because `c = min_{e'∈E} m_{e'}` satisfies `c β⁻¹(S) ≤ t(S)` for
  -- every `S ⊆ E`, …"
  have hmin : ∀ e : E, GrowsAtLeast (fun α => rho g m β α e) (univ.inf' ⟨e, mem_univ e⟩ m) :=
    fun e => hlow e _ fun S _ => by
      rw [mul_sum]
      exact sum_le_sum fun e' _ => by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (inf'_le m (mem_univ e')) (hβ e').le
  have hminpos : ∀ e : E, 0 < univ.inf' ⟨e, mem_univ e⟩ m := fun e =>
    (lt_inf'_iff _).2 fun e' _ => hm e'
  -- As `min_{e'∈E} m_{e'} > 0`, every `ρ^g_e` is nondecreasing (the statement,
  -- `appB-tools.tex:88`).
  have hmono : ∀ e : E, Monotone fun α => rho g m β α e := fun e α α' h => by
    have := hmin e α (α' - α) (sub_nonneg.2 h)
    simp only [add_sub_cancel] at this
    nlinarith [hminpos e, sub_nonneg.2 h]
  -- "… and `c = t_b/β⁻¹(E)` satisfies `c β⁻¹(S) ≤ t_b ≤ t(S)` for every `S ∋ b`."
  have hmore : GrowsAtLeast (fun α => rho g m β α b) ((m b / β b) / ∑ e, 1 / β e) := by
    refine hlow b _ fun S hb => ?_
    have hE : 0 < ∑ e, 1 / β e := sum_pos (fun e _ => one_div_pos.2 (hβ e)) ⟨b, mem_univ b⟩
    have htb : 0 ≤ m b / β b := (div_pos (hm b) (hβ b)).le
    have h1 : ∑ e ∈ S, 1 / β e ≤ ∑ e, 1 / β e :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) fun e _ _ => (one_div_pos.2 (hβ e)).le
    have h2 : m b / β b ≤ ∑ e ∈ S, m e / β e :=
      single_le_sum (f := fun e => m e / β e) (fun e _ => (div_pos (hm e) (hβ e)).le) hb
    calc (m b / β b / ∑ e, 1 / β e) * ∑ e ∈ S, 1 / β e
        ≤ (m b / β b / ∑ e, 1 / β e) * ∑ e, 1 / β e :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg htb hE.le)
      _ = m b / β b := div_mul_cancel₀ _ hE.ne'
      _ ≤ ∑ e ∈ S, m e / β e := h2
  -- (4) "These rates give `|ρ^g_e(α') − ρ^g_e(α)| ≤ m_max |α' − α|` for all `α, α' ∈ ℝ`, so
  -- `ρ^g` is continuous, …"
  have hlip : ∀ (e : E) (α α' : ℝ),
      |rho g m β α' e - rho g m β α e| ≤ univ.sup' ⟨e, mem_univ e⟩ m * |α' - α| := by
    intro e α α'
    rcases le_total α α' with h | h
    · have h1 := hmono e h
      have h2 := hup e α (α' - α) (sub_nonneg.2 h)
      simp only [add_sub_cancel] at h2
      rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 h)]
      linarith
    · have h1 := hmono e h
      have h2 := hup e α' (α - α') (sub_nonneg.2 h)
      simp only [add_sub_cancel] at h2
      rw [abs_of_nonpos (sub_nonpos.2 h1), abs_of_nonpos (sub_nonpos.2 h)]
      linarith
  have hcontρ : Continuous (fun α => rho g m β α) := by
    refine continuous_pi fun e => ?_
    have hK : 0 ≤ univ.sup' ⟨e, mem_univ e⟩ m := (hm e).le.trans (le_sup' m (mem_univ e))
    refine (LipschitzWith.of_dist_le_mul (K := ⟨_, hK⟩) fun α α' => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq]
    exact hlip e α' α
  -- "… and so are `ξ^g_e(α) = α t_e − ρ^g_e(α)/β_e` and `r(ξ^g(α)) = m^⊤ξ^g(α)`."
  have hcontξ : Continuous (fun α => xi g m β α) := by
    refine continuous_pi fun e => ?_
    have : (fun α => xi g m β α e) = fun α => α * (m e / β e) - rho g m β α e / β e := by
      funext α
      rw [xi_eq_of_pos hβ e]
      have := (hβ e).ne'
      field_simp
    rw [this]
    exact (continuous_id.mul continuous_const).sub
      (((continuous_apply e).comp hcontρ).div_const _)
  have hcontr : Continuous (fun α => reward m (xi g m β α)) :=
    continuous_finsetSum _ fun e _ => continuous_const.mul ((continuous_apply e).comp hcontξ)
  exact ⟨hlow b c hc, hup, fun e => ⟨hmin e, hminpos e, hup e, hmono e⟩, hcontρ, hcontξ, hcontr,
    hmore⟩

/-! ### `lem:fullplane`(d): the parts of the reward -/

/-- `lem:fullplane`(d), the first step (`appB-tools.tex:188-193`): the vector equal to `u` on `U`
and to `v` off `U` lies in `B_{(±)}(g)` if `U` is tight for `u, v ∈ B_{(±)}(g)`: its sum is
`g(U) + g(E) − g(U) = g(E)`, and by submodularity
`y(S) = u(S ∩ U) + v(S ∪ U) − v(U) ≤ g(S ∩ U) + g(S ∪ U) − g(U) ≤ g(S)`. -/
lemma mix_mem_fpBase (hg : Submodular g) {u v : E → ℝ} (hu : u ∈ fpBase g) (hv : v ∈ fpBase g)
    {U : Finset E} (hUu : IsTight g u U) (hUv : IsTight g v U) :
    (fun e => if e ∈ U then u e else v e) ∈ fpBase g := by
  have hsplit : ∀ T : Finset E, ∑ e ∈ T, (if e ∈ U then u e else v e) =
      ∑ e ∈ T ∩ U, u e + ∑ e ∈ T \ U, v e := by
    intro T
    rw [sum_ite, filter_mem_eq_inter]
    congr 1
    exact sum_congr (by ext e; simp) fun _ _ => rfl
  refine ⟨fun T => ?_, ?_⟩
  · rw [hsplit]
    have h1 := hu.1 (T ∩ U)
    have h2 := hv.1 (T ∪ U)
    have h3 : ∑ e ∈ T ∪ U, v e = ∑ e ∈ T \ U, v e + ∑ e ∈ U, v e := by
      rw [← sum_union sdiff_disjoint, sdiff_union_self_eq_union]
    have h4 := hg T U
    unfold IsTight at hUv
    linarith
  · rw [hsplit univ, univ_inter]
    have h3 : ∑ e, v e = ∑ e ∈ univ \ U, v e + ∑ e ∈ U, v e := (sum_sdiff (subset_univ U)).symm
    unfold IsTight at hUu hUv
    linarith [hv.2]

/-- `U_A(z | α)` is the sum of its parts on `U` and on `E ∖ U` (the bookkeeping behind "the
vectors differ only on `U`, the quadratic terms cancel" in the proof of `lem:fullplane`(d)). -/
lemma utility_split (m β : E → ℝ) (α : ℝ) (U : Finset E) (z : E → ℝ) :
    utility m β α z = (α * ∑ e ∈ U, m e * z e - ∑ e ∈ U, β e / 2 * z e ^ 2) +
      (α * ∑ e ∈ Uᶜ, m e * z e - ∑ e ∈ Uᶜ, β e / 2 * z e ^ 2) := by
  rw [utility_eq_sum, ← sum_add_sum_compl U, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  congr 1 <;> exact sum_congr rfl fun e _ => by ring

/-- The parts of `U_A(· | α)` at the vector equal to `u` on `U` and to `v` on `E ∖ U`. -/
lemma utility_mix (m β : E → ℝ) (α : ℝ) (U : Finset E) (u v : E → ℝ) :
    utility m β α (fun e => if e ∈ U then u e else v e) =
      (α * ∑ e ∈ U, m e * u e - ∑ e ∈ U, β e / 2 * u e ^ 2) +
      (α * ∑ e ∈ Uᶜ, m e * v e - ∑ e ∈ Uᶜ, β e / 2 * v e ^ 2) := by
  rw [utility_split m β α U]
  have h1 : ∀ (k : E → ℝ → ℝ), ∑ e ∈ U, k e (if e ∈ U then u e else v e) = ∑ e ∈ U, k e (u e) :=
    fun k => sum_congr rfl fun e he => by simp [he]
  have h2 : ∀ (k : E → ℝ → ℝ), ∑ e ∈ Uᶜ, k e (if e ∈ U then u e else v e) =
      ∑ e ∈ Uᶜ, k e (v e) :=
    fun k => sum_congr rfl fun e he => by simp [mem_compl.1 he]
  rw [h1 fun e w => m e * w, h1 fun e w => β e / 2 * w ^ 2, h2 fun e w => m e * w,
    h2 fun e w => β e / 2 * w ^ 2]

/-- `lem:fullplane`(d), auxiliary form (`appB-tools.tex:187-196`): if `U` is tight for `ξ^g(a)` and
`ξ^g(a')`, `a ≤ a'`, then `∑_{e∈U} m_e ξ^g_e` and `∑_{e∈E∖U} m_e ξ^g_e` are both at least as large
at `a'` as at `a`. Steps: (1) `x = ξ^g(a)`, `x' = ξ^g(a')`, and the vectors `y` (equal to `x'` on
`U`, to `x` off `U`) and `y'` (equal to `x` on `U`, to `x'` off `U`) lie in `B_{(±)}(g)`
(`mix_mem_fpBase`); (2) adding `U_A(x | a) ≥ U_A(y | a)` and `U_A(x' | a') ≥ U_A(y' | a')`, whose
vectors differ only on `U`, the quadratic terms cancel, and `(a' − a) ∑_{e∈U} m_e(x'_e − x_e) ≥ 0`;
(3) the comparisons of `x` with `y'` at `a` and of `x'` with `y` at `a'` give the same for
`E ∖ U`. -/
theorem sum_mul_xi_mono (H : FPHyp g β) {a a' : ℝ} (haa : a ≤ a') {U : Finset E}
    (hU : IsTight g (xi g m β a) U) (hU' : IsTight g (xi g m β a') U) :
    ∑ e ∈ U, m e * xi g m β a e ≤ ∑ e ∈ U, m e * xi g m β a' e ∧
      ∑ e ∈ Uᶜ, m e * xi g m β a e ≤ ∑ e ∈ Uᶜ, m e * xi g m β a' e := by
  -- (1) "Let `x := ξ^g(a)` and `x' := ξ^g(a')`. The vector `y` equal to `x'` on `U` and to `x` on
  -- `E ∖ U` lies in `B_{(±)}(g)`. … In the same way, the vector `y'` equal to `x` on `U` and to
  -- `x'` on `E ∖ U` lies in `B_{(±)}(g)`."
  -- The omitted sentence (`appB-tools.tex:189-192`) is `mix_mem_fpBase`.
  set x := xi g m β a
  set x' := xi g m β a'
  have hx := H.isBestResponse m a
  have hx' := H.isBestResponse m a'
  have hy := mix_mem_fpBase H.submod hx'.1 hx.1 hU' hU
  have hy' := mix_mem_fpBase H.submod hx.1 hx'.1 hU hU'
  -- (2) "As in the proof of `lem:monreward`, we add two optimality inequalities, here
  -- `U_A(x | a) ≥ U_A(y | a)` and `U_A(x' | a') ≥ U_A(y' | a')`. The vectors in each of them differ
  -- only on `U`, the quadratic terms cancel, and we obtain `(a' − a) ∑_{e∈U} m_e(x'_e − x_e) ≥ 0`."
  have i1 := hx.2 _ hy
  have i2 := hx'.2 _ hy'
  rw [utility_mix, utility_split m β a U x] at i1
  rw [utility_mix, utility_split m β a' U x'] at i2
  have hU0 : 0 ≤ (a' - a) * (∑ e ∈ U, m e * x' e - ∑ e ∈ U, m e * x e) := by nlinarith
  -- (3) "The comparisons of `x` with `y'` at `a` and of `x'` with `y` at `a'` give the same for
  -- `E ∖ U`."
  have i3 := hx.2 _ hy'
  have i4 := hx'.2 _ hy
  rw [utility_mix, utility_split m β a U x] at i3
  rw [utility_mix, utility_split m β a' U x'] at i4
  have hUc0 : 0 ≤ (a' - a) * (∑ e ∈ Uᶜ, m e * x' e - ∑ e ∈ Uᶜ, m e * x e) := by nlinarith
  -- The Lean divides both inequalities by `a' − a` if `a < a'`; if `a = a'`, both sides agree.
  rcases haa.lt_or_eq with hlt | heq
  · have hpos : 0 < a' - a := sub_pos.2 hlt
    exact ⟨by linarith [(mul_nonneg_iff_of_pos_left hpos).1 hU0],
      by linarith [(mul_nonneg_iff_of_pos_left hpos).1 hUc0]⟩
  · simp only [x', ← heq, x]
    exact ⟨le_rfl, le_rfl⟩

/-- The full-plane reward is nondecreasing: (d) with `U = ∅`, which is tight for every vector of
the full plane (`appB-tools.tex:197`). -/
theorem curve_mono (H : FPHyp g β) {a a' : ℝ} (haa : a ≤ a') :
    curve g m β a ≤ curve g m β a' := by
  have h0 : ∀ α', IsTight g (xi g m β α') ∅ := fun _ => by simp [IsTight, H.empty]
  have h := (sum_mul_xi_mono (m := m) H haa (h0 a) (h0 a')).2
  simpa [curve] using h

/-- **`lem:fullplane`(d)** (`appB-tools.tex:90-91`, proof
`appB-tools.tex:187-197`): for `g` submodular with `g(∅) = 0` and `m, β > 0`, if `U ⊆ E` is tight
for `ξ^g(a)` and for `ξ^g(a')`, where `a ≤ a'`, then `∑_{e∈U} m_e ξ^g_e` and `∑_{e∈E∖U} m_e ξ^g_e`
are both at least as large at `a'` as at `a`; in particular, `α ↦ r(ξ^g(α))` is nondecreasing.
Steps: (1)–(3) of `sum_mul_xi_mono`: the vectors `y` (`ξ^g(a')` on `U`, `ξ^g(a)` off `U`) and `y'`
(the other way round) lie in `B_{(±)}(g)` by submodularity; adding the optimality inequalities
`U_A(x | a) ≥ U_A(y | a)` and `U_A(x' | a') ≥ U_A(y' | a')`, the quadratic terms cancel, which
gives the claim for `U`, and the comparisons of `x` with `y'` and of `x'` with `y` give it for
`E ∖ U`; (4) `U = ∅` is tight for every vector of the full plane, and for it this shows that
`α ↦ r(ξ^g(α))` is nondecreasing (`curve_mono`). The hypothesis `m > 0` is not used. -/
theorem fullplane_d (hg : Submodular g) (hg0 : g ∅ = 0) (_hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) {U : Finset E} {a a' : ℝ} (haa : a ≤ a')
    (hU : IsTight g (xi g m β a) U) (hU' : IsTight g (xi g m β a') U) :
    (∑ e ∈ U, m e * xi g m β a e ≤ ∑ e ∈ U, m e * xi g m β a' e ∧
      ∑ e ∈ Uᶜ, m e * xi g m β a e ≤ ∑ e ∈ Uᶜ, m e * xi g m β a' e) ∧
    Monotone fun α => reward m (xi g m β α) := by
  have H : FPHyp g β := ⟨hg, hg0, hβ⟩
  -- (1)–(3) "Let `x := ξ^g(a)` and `x' := ξ^g(a')`. … The comparisons of `x` with `y'` at `a` and
  -- of `x'` with `y` at `a'` give the same for `E ∖ U`."
  -- These sentences (`appB-tools.tex:187-196`) are `sum_mul_xi_mono`.
  refine ⟨sum_mul_xi_mono H haa hU hU', ?_⟩
  -- (4) "The set `U = ∅` is tight for every vector of the full plane, and for it this is the proof
  -- of `lem:monreward` in the full plane, which shows that `α ↦ r(ξ^g(α))` is nondecreasing."
  -- This is `curve_mono`.
  exact fun α α' h => curve_mono H h

/-! ### `lem:fullplane`(e): equal marginals -/

omit [DecidableEq E] in
/-- `lem:fullplane`(e), auxiliary form (`appB-tools.tex:199-205`, for `β > 0` only): if the
elements of a nonempty `D ⊆ E` have equal marginals at `α`, then `ξ = ξ^g(α)` satisfies
`∑_{e∈D} m_e ξ_e = α SS(D) + ξ(D) m̄_D`. Steps: (1) with the common marginal `ρ_D`,
`ξ_e = α t_e − ρ_D/β_e` for `e ∈ D`; (2) summing over `D` gives
`ρ_D = (α t(D) − ξ(D))/β⁻¹(D)`; (3)
`∑_{e∈D} m_e ξ_e = α ∑_{e∈D} m_e²/β_e − ρ_D t(D) = α (∑_{e∈D} m_e²/β_e − t(D)²/β⁻¹(D)) + ξ(D) m̄_D`;
(4) `= α SS(D) + ξ(D) m̄_D`, by expanding the square in `SS(D)`. -/
theorem sum_mul_xi_of_rho_eq (hβ : ∀ e, 0 < β e) (α : ℝ) {D : Finset E} (hD : D.Nonempty)
    (heq : ∀ e ∈ D, ∀ e' ∈ D, rho g m β α e = rho g m β α e') :
    ∑ e ∈ D, m e * xi g m β α e = α * SS m β D + (∑ e ∈ D, xi g m β α e) * mbar m β D := by
  set ξ := xi g m β α
  obtain ⟨e₀, he₀⟩ := hD
  have hpos : 0 < ∑ e ∈ D, 1 / β e := sum_pos (fun e _ => one_div_pos.2 (hβ e)) ⟨e₀, he₀⟩
  -- (1) "Let `ρ_D` be the common marginal, so `ξ_e = α t_e − ρ_D/β_e` for `e ∈ D`."
  set ρD := rho g m β α e₀ with hρD
  have h1 : ∀ e ∈ D, ξ e = α * (m e / β e) - ρD / β e := by
    intro e he
    show xi g m β α e = α * (m e / β e) - ρD / β e
    rw [xi_eq_of_pos hβ e, heq e he e₀ he₀, ← hρD]
    have := (hβ e).ne'
    field_simp
  -- (2) "Summing over `D` gives `ρ_D = (α t(D) − ξ(D))/β⁻¹(D)`, …"
  have h2 : ρD = (α * ∑ e ∈ D, m e / β e - ∑ e ∈ D, ξ e) / ∑ e ∈ D, 1 / β e := by
    have hs : ∑ e ∈ D, ξ e = α * ∑ e ∈ D, m e / β e - ρD * ∑ e ∈ D, 1 / β e := by
      rw [sum_congr rfl h1, mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun e _ => by ring
    rw [hs]
    field_simp
    ring
  -- (3) "… and therefore `∑_{e∈D} m_e ξ_e = α ∑_{e∈D} m_e²/β_e − ρ_D t(D)`
  -- `= α (∑_{e∈D} m_e²/β_e − t(D)²/β⁻¹(D)) + ξ(D) m̄_D` …"
  have h3 : ∑ e ∈ D, m e * ξ e = α * ∑ e ∈ D, m e ^ 2 / β e - ρD * ∑ e ∈ D, m e / β e := by
    rw [sum_congr rfl fun e he => by rw [h1 e he], mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  have h3' : ∑ e ∈ D, m e * ξ e = α * (∑ e ∈ D, m e ^ 2 / β e -
      (∑ e ∈ D, m e / β e) ^ 2 / ∑ e ∈ D, 1 / β e) + (∑ e ∈ D, ξ e) * mbar m β D := by
    rw [h3, h2, mbar]
    field_simp
    ring
  -- (4) "… `= α SS(D) + ξ(D) m̄_D`, the last step by expanding the square in `SS(D)`."
  rw [h3', SS_eq hβ ⟨e₀, he₀⟩]

/-- **`lem:fullplane`(e)** (`appB-tools.tex:92-95`, proof
`appB-tools.tex:199-205`): for `g` submodular with `g(∅) = 0` and `m, β > 0`, if the elements of a
nonempty `D ⊆ E` have equal marginals at `α`, then `ξ = ξ^g(α)` satisfies
`∑_{e∈D} m_e ξ_e = α SS(D) + ξ(D) m̄_D`. Steps (in `sum_mul_xi_of_rho_eq`): (1) with the common
marginal `ρ_D`, `ξ_e = α t_e − ρ_D/β_e` for `e ∈ D`; (2) summing over `D` gives
`ρ_D = (α t(D) − ξ(D))/β⁻¹(D)`; (3) so
`∑_{e∈D} m_e ξ_e = α ∑_{e∈D} m_e²/β_e − ρ_D t(D) = α (∑_{e∈D} m_e²/β_e − t(D)²/β⁻¹(D)) + ξ(D) m̄_D`;
(4) `= α SS(D) + ξ(D) m̄_D` by expanding the square in `SS(D)`. The hypotheses on `g` and `m > 0`
are not used. -/
theorem fullplane_e (_hg : Submodular g) (_hg0 : g ∅ = 0) (_hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) (α : ℝ) {D : Finset E} (hD : D.Nonempty)
    (heq : ∀ e ∈ D, ∀ e' ∈ D, rho g m β α e = rho g m β α e') :
    ∑ e ∈ D, m e * xi g m β α e = α * SS m β D + (∑ e ∈ D, xi g m β α e) * mbar m β D :=
  sum_mul_xi_of_rho_eq hβ α hD heq

/-! ### `lem:fullplane`(f): direct sums -/

section DirectSum

variable {E₁ E₂ : Type*} [Fintype E₁] [DecidableEq E₁] [Fintype E₂] [DecidableEq E₂]

omit [Fintype E] [DecidableEq E₁] [DecidableEq E₂] in
/-- For disjoint `E₁, E₂` with `E = E₁ ∪ E₂` (given by `σ : E₁ ⊕ E₂ ≃ E`),
`y(S) = y(S ∩ E₁) + y(S ∩ E₂)`, where `S ∩ E₁ = {a : σ(a) ∈ S}`. -/
lemma sum_eq_sum_add_sum (σ : E₁ ⊕ E₂ ≃ E) (S : Finset E) (y : E → ℝ) :
    ∑ e ∈ S, y e = ∑ a ∈ univ.filter (fun a => σ (Sum.inl a) ∈ S), y (σ (Sum.inl a)) +
      ∑ b ∈ univ.filter (fun b => σ (Sum.inr b) ∈ S), y (σ (Sum.inr b)) := by
  have hS : S.map σ.symm.toEmbedding = (univ.filter fun a => σ (Sum.inl a) ∈ S).disjSum
      (univ.filter fun b => σ (Sum.inr b) ∈ S) := by
    rw [← toLeft_disjSum_toRight (u := S.map σ.symm.toEmbedding)]
    congr 1
    · ext a
      simp [mem_toLeft]
    · ext b
      simp [mem_toRight]
  have h1 : ∑ e ∈ S, y e = ∑ u ∈ S.map σ.symm.toEmbedding, y (σ u) := by
    rw [sum_map]
    simp
  rw [h1, hS, sum_disjSum]

/-- `lem:fullplane`(f), auxiliary form (`appB-tools.tex:207-210`): for `g = g₁ ⊕ g₂`, that is,
`g(S) = g₁(S ∩ E₁) + g₂(S ∩ E₂)` for disjoint `E₁, E₂` with `E = E₁ ∪ E₂` (here given by
`σ : E₁ ⊕ E₂ ≃ E`, so that `S ∩ E₁` is `{a : σ(a) ∈ S}` and `m|_{E₁} = m ∘ σ ∘ inl`),
`ξ^g = (ξ^{g₁}, ξ^{g₂})` and `ρ^g = (ρ^{g₁}, ρ^{g₂})`. Steps: (1) the vector
`y = (ξ^{g₁}(α), ξ^{g₂}(α))` satisfies `y(S) = y(S ∩ E₁) + y(S ∩ E₂) ≤ g(S)`; (2) its marginals at
`α` are those of the two summands, so its upper level sets are the unions of the upper level sets
of the two summands at the same level, which are tight for the summands, hence for `y`; (3) so
`y = ξ^g(α)` by (a), and `ρ^g(α) = ρ(y) = (ρ^{g₁}(α), ρ^{g₂}(α))`. -/
theorem xi_dirSum (σ : E₁ ⊕ E₂ ≃ E) {g₁ : Finset E₁ → ℝ} {g₂ : Finset E₂ → ℝ}
    (H₁ : FPHyp g₁ fun a => β (σ (Sum.inl a))) (H₂ : FPHyp g₂ fun b => β (σ (Sum.inr b)))
    (hgsum : ∀ S : Finset E, g S = g₁ (univ.filter fun a => σ (Sum.inl a) ∈ S) +
      g₂ (univ.filter fun b => σ (Sum.inr b) ∈ S))
    (H : FPHyp g β) (m : E → ℝ) (α : ℝ) :
    ((∀ a, xi g m β α (σ (Sum.inl a)) =
        xi g₁ (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α a) ∧
      ∀ b, xi g m β α (σ (Sum.inr b)) =
        xi g₂ (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α b) ∧
    ((∀ a, rho g m β α (σ (Sum.inl a)) =
        rho g₁ (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α a) ∧
      ∀ b, rho g m β α (σ (Sum.inr b)) =
        rho g₂ (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α b) := by
  set ξ₁ := xi g₁ (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α
  set ξ₂ := xi g₂ (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α
  -- (1) "The claimed vectors satisfy the conditions of (a). The vector
  -- `y := (ξ^{g_1}(α), ξ^{g_2}(α))` satisfies `y(S) = y(S ∩ E_1) + y(S ∩ E_2) ≤ g(S)` for every
  -- `S ⊆ E`."
  -- In the Lean, `E` is `E₁ ⊕ E₂` through `σ`, and `S ∩ E₁` is `{a : σ(a) ∈ S}`.
  set y : E → ℝ := fun e => Sum.elim ξ₁ ξ₂ (σ.symm e) with hy
  have hy1 : ∀ a, y (σ (Sum.inl a)) = ξ₁ a := fun a => by simp [hy]
  have hy2 : ∀ b, y (σ (Sum.inr b)) = ξ₂ b := fun b => by simp [hy]
  have hsum : ∀ S : Finset E, ∑ e ∈ S, y e =
      ∑ a ∈ univ.filter (fun a => σ (Sum.inl a) ∈ S), ξ₁ a +
        ∑ b ∈ univ.filter (fun b => σ (Sum.inr b) ∈ S), ξ₂ b := by
    intro S
    rw [sum_eq_sum_add_sum σ S y]
    simp only [hy1, hy2]
  have hP : y ∈ fpPoly g := fun S => by
    rw [hsum, hgsum]
    exact add_le_add ((xi_mem_fpBase H₁ _ α).1 _) ((xi_mem_fpBase H₂ _ α).1 _)
  -- (2) "Its marginals at the share `α` are those of the two summands, so its upper level sets are
  -- the unions of the upper level sets of the two summands at the same level, which are tight for
  -- the summands, hence for `y`."
  have hlev1 : ∀ θ, (univ.filter fun a => σ (Sum.inl a) ∈ levelSet m β α y θ) =
      levelSet (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α ξ₁ θ := fun θ => by
    ext a
    unfold levelSet
    rw [mem_filter, mem_filter, mem_filter]
    simp only [marg, mem_univ, true_and, hy1]
  have hlev2 : ∀ θ, (univ.filter fun b => σ (Sum.inr b) ∈ levelSet m β α y θ) =
      levelSet (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α ξ₂ θ := fun θ => by
    ext b
    unfold levelSet
    rw [mem_filter, mem_filter, mem_filter]
    simp only [marg, mem_univ, true_and, hy2]
  have ht : ∀ θ, IsTight g y (levelSet m β α y θ) := fun θ => by
    unfold IsTight
    rw [hsum, hgsum, hlev1, hlev2, xi_levelSet_tight H₁ _ α θ, xi_levelSet_tight H₂ _ α θ]
  -- (3) "So `y = ξ^g(α)` by (a), and `ρ^g(α) = ρ(y) = (ρ^{g_1}(α), ρ^{g_2}(α))`."
  have hξ : y = xi g m β α := eq_xi_of_levelSets H hP ht
  refine ⟨⟨fun a => by rw [← hξ, hy1], fun b => by rw [← hξ, hy2]⟩,
    ⟨fun a => ?_, fun b => ?_⟩⟩
  · simp only [rho, marg, ← hξ, hy1]
    rfl
  · simp only [rho, marg, ← hξ, hy2]
    rfl

/-- **`lem:fullplane`(f)** (`appB-tools.tex:96-97`, proof `appB-tools.tex:207-210`):
let `g = g₁ ⊕ g₂`, that is, `g(S) = g₁(S ∩ E₁) + g₂(S ∩ E₂)` for `S ⊆ E`, for submodular
`g_i : 2^{E_i} → ℝ` with `g_i(∅) = 0` on disjoint sets `E₁, E₂` with `E = E₁ ∪ E₂` (given by
`σ : E₁ ⊕ E₂ ≃ E`), and let `ξ^{g_i}`, `ρ^{g_i}` be taken with respect to `m|_{E_i}` and
`β|_{E_i}`. Then `ξ^g = (ξ^{g₁}, ξ^{g₂})` and `ρ^g = (ρ^{g₁}, ρ^{g₂})`, for `g` submodular with
`g(∅) = 0`, `m, β > 0` and every `α`. Steps (in `xi_dirSum`): the claimed vectors satisfy the
conditions of (a): (1) `y = (ξ^{g₁}(α), ξ^{g₂}(α))` satisfies `y(S) = y(S ∩ E₁) + y(S ∩ E₂) ≤ g(S)`;
(2) its marginals are those of the summands, so its upper level sets are the unions of those of
the summands at the same level, which are tight; (3) so `y = ξ^g(α)` by (a), and
`ρ^g(α) = ρ(y) = (ρ^{g₁}(α), ρ^{g₂}(α))`. The hypothesis `m > 0` is not used. -/
theorem fullplane_f (σ : E₁ ⊕ E₂ ≃ E) {g₁ : Finset E₁ → ℝ} {g₂ : Finset E₂ → ℝ}
    (hg₁ : Submodular g₁) (hg₁0 : g₁ ∅ = 0) (hg₂ : Submodular g₂) (hg₂0 : g₂ ∅ = 0)
    (hgsum : ∀ S : Finset E, g S = g₁ (univ.filter fun a => σ (Sum.inl a) ∈ S) +
      g₂ (univ.filter fun b => σ (Sum.inr b) ∈ S))
    (hg : Submodular g) (hg0 : g ∅ = 0) (_hm : ∀ e, 0 < m e) (hβ : ∀ e, 0 < β e) (α : ℝ) :
    ((∀ a, xi g m β α (σ (Sum.inl a)) =
        xi g₁ (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α a) ∧
      ∀ b, xi g m β α (σ (Sum.inr b)) =
        xi g₂ (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α b) ∧
    ((∀ a, rho g m β α (σ (Sum.inl a)) =
        rho g₁ (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α a) ∧
      ∀ b, rho g m β α (σ (Sum.inr b)) =
        rho g₂ (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α b) :=
  xi_dirSum σ ⟨hg₁, hg₁0, fun _ => hβ _⟩ ⟨hg₂, hg₂0, fun _ => hβ _⟩ hgsum ⟨hg, hg0, hβ⟩ m α

end DirectSum

/-! ### `lem:fullplane`(f): the modular singleton -/

section Singleton

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Unique Z]

/-- The modular singleton `π_F` on a one-element set `{τ_1}` (`τ_1 = default`): `π_F(∅) = 0` and
`π_F({τ_1}) = F` (`lem:cutforms`(c)(ii), here with `F ∈ ℝ`). -/
def modSingleton (F : ℝ) (T : Finset Z) : ℝ :=
  if (default : Z) ∈ T then F else 0

omit [Fintype Z] in
/-- The modular singleton `π_F` is submodular with `π_F(∅) = 0` (not in the paper: the paper uses
this without proof in `lem:fullplane`(f), `appB-tools.tex:98`). -/
theorem FPHyp.modSingleton {β : Z → ℝ} (hβ : ∀ z, 0 < β z) (F : ℝ) :
    FPHyp (modSingleton F) β where
  submod X Y := by
    simp only [Hardness.modSingleton, mem_union, mem_inter]
    by_cases hX : (default : Z) ∈ X <;> by_cases hY : (default : Z) ∈ Y <;> simp [hX, hY]
  empty := by simp [Hardness.modSingleton]
  pos := hβ

omit [DecidableEq Z] in
/-- `B_{(±)}(π_F) = {F}` (`appB-tools.tex:211`). -/
theorem fpBase_modSingleton [DecidableEq Z] (F : ℝ) :
    fpBase (modSingleton (Z := Z) F) = {fun _ => F} := by
  have huniv : (univ : Finset Z) = {default} := by
    ext z
    simp [Unique.eq_default z]
  have hval : modSingleton (Z := Z) F {default} = F := by
    rw [Hardness.modSingleton, ite_eq_left (mem_singleton_self _)]
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, hy⟩
    funext z
    rw [huniv, sum_singleton, hval] at hy
    rw [Unique.eq_default z, hy]
  · rintro rfl
    refine ⟨fun T => ?_, ?_⟩
    · rcases T.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
      · simp [Hardness.modSingleton]
      · have hT : T = {default} := by
          ext z'
          simp only [mem_singleton]
          constructor
          · intro _
            exact Unique.eq_default z'
          · rintro rfl
            rwa [← Unique.eq_default z]
        rw [hT, sum_singleton, hval]
    · show ∑ _z, F = modSingleton F univ
      rw [huniv, sum_singleton, hval]

omit [DecidableEq Z] in
/-- `lem:fullplane`(f), the modular singleton, auxiliary form: `ξ^{π_F}_{τ_1}(α) = F` and
`ρ^{π_F}_{τ_1}(α) = α m_{τ_1} − β_{τ_1} F`, as `B_{(±)}(π_F) = {F}`. -/
theorem xi_modSingleton [DecidableEq Z] {m β : Z → ℝ} (hβ : ∀ z, 0 < β z) (F : ℝ) (α : ℝ)
    (τ₁ : Z) :
    xi (modSingleton F) m β α τ₁ = F ∧ rho (modSingleton F) m β α τ₁ = α * m τ₁ - β τ₁ * F := by
  have h := xi_mem_fpBase (FPHyp.modSingleton hβ F) m α
  rw [fpBase_modSingleton, Set.mem_singleton_iff] at h
  refine ⟨by rw [h], ?_⟩
  simp only [rho, marg, h]

omit [DecidableEq Z] in
/-- **`lem:fullplane`(f)**, the modular singleton (`appB-tools.tex:98`, proof
`appB-tools.tex:211`): a modular singleton `π_F` on `{τ_1}` with `π_F({τ_1}) = F`, for
`m, β > 0`, has `ξ^{π_F}_{τ_1}(α) = F` and `ρ^{π_F}_{τ_1}(α) = α m_{τ_1} − β_{τ_1} F` for every
`α ∈ ℝ`, as `B_{(±)}(π_F) = {F}`. The hypothesis `m > 0` is not used. -/
theorem fullplane_f_singleton [DecidableEq Z] {m β : Z → ℝ} (_hm : ∀ z, 0 < m z)
    (hβ : ∀ z, 0 < β z) (F : ℝ) (α : ℝ) (τ₁ : Z) :
    xi (modSingleton F) m β α τ₁ = F ∧ rho (modSingleton F) m β α τ₁ = α * m τ₁ - β τ₁ * F :=
  xi_modSingleton hβ F α τ₁

end Singleton

/-! ### Direct sums with a modular singleton, on `Option E` -/

omit [Fintype E] in
/-- A sum over a finite set of `Option E` splits into the term of `none` and the rest. -/
lemma sum_option_finset {M : Type*} [AddCommMonoid M] (T : Finset (Option E))
    (y : Option E → M) :
    ∑ o ∈ T, y o = (if none ∈ T then y none else 0) + ∑ e ∈ eraseNone T, y (some e) := by
  by_cases h : none ∈ T
  · have hT : T = insertNone (eraseNone T) := by rw [insertNone_eraseNone, insert_eq_of_mem h]
    simp only [h, ↓reduceIte]
    conv_lhs => rw [hT]
    rw [sum_insertNone]
  · have hT : T = (eraseNone T).image some := by rw [image_some_eraseNone, erase_eq_of_notMem h]
    simp only [h, ↓reduceIte, zero_add]
    conv_lhs => rw [hT]
    rw [sum_image fun a _ b _ hab => Option.some_injective _ hab]

/-- The direct sum `g ⊕ π_F` of `g` with the modular singleton `π_F` on the new element
`b = none`, on `Option E` (`E ∪ {b}`): `(g ⊕ π_F)(S) = g(S ∩ E) + π_F(S ∩ {b})`. -/
def addSingleton (g : Finset E → ℝ) (F : ℝ) (T : Finset (Option E)) : ℝ :=
  g (eraseNone T) + if none ∈ T then F else 0

variable {m' β' : Option E → ℝ}

omit [Fintype E] in
/-- The direct sum `g ⊕ π_F` is submodular with `(g ⊕ π_F)(∅) = 0` (not in the paper: the paper
uses without proof that a direct sum of submodular functions that vanish at `∅` is submodular and
vanishes at `∅`, `lem:fullplane`(f), `appB-tools.tex:96-98`). -/
theorem FPHyp.addSingleton (H : FPHyp g fun e => β' (some e)) (hb : 0 < β' none) (F : ℝ) :
    FPHyp (addSingleton g F) β' where
  submod X Y := by
    have h := H.submod (eraseNone X) (eraseNone Y)
    simp only [Hardness.addSingleton, eraseNone_union, eraseNone_inter, mem_union, mem_inter]
    by_cases hX : none ∈ X <;> by_cases hY : none ∈ Y <;> simp [hX, hY] <;> linarith
  empty := by simp [Hardness.addSingleton, H.empty]
  pos o := by
    cases o with
    | none => exact hb
    | some e => exact H.pos e

/-- `g ⊕ π_F` on `Option E` is the direct sum of `lem:fullplane`(f) for
`σ : E ⊕ Unit ≃ Option E` (`some` on `E`, `none` on the new element). -/
lemma addSingleton_eq_sum (g : Finset E → ℝ) (F : ℝ) (T : Finset (Option E)) :
    addSingleton g F T =
      g (univ.filter fun a => (Equiv.optionEquivSumPUnit E).symm (Sum.inl a) ∈ T) +
        modSingleton (Z := Unit) F
          (univ.filter fun b : Unit => (Equiv.optionEquivSumPUnit E).symm (Sum.inr b) ∈ T) := by
  have h1 : (univ.filter fun a => (Equiv.optionEquivSumPUnit E).symm (Sum.inl a) ∈ T) =
      eraseNone T := by
    ext a
    rw [mem_filter, mem_eraseNone, Equiv.optionEquivSumPUnit_symm_inl]
    simp
  have h2 : (default : Unit) ∈
      (univ.filter fun b : Unit => (Equiv.optionEquivSumPUnit E).symm (Sum.inr b) ∈ T) ↔
        none ∈ T := by
    rw [mem_filter, Equiv.optionEquivSumPUnit_symm_inr]
    simp
  rw [h1, addSingleton, modSingleton]
  by_cases hT : none ∈ T
  · rw [ite_eq_left hT, ite_eq_left (h2.2 hT)]
  · rw [ite_eq_right hT, ite_eq_right (mt h2.1 hT)]

/-- `lem:fullplane`(f) for `g ⊕ π_F` on `Option E`: the old coordinates of `ξ` are those of `g`,
and the new one is `F` (`xi_dirSum` and `xi_modSingleton`). -/
theorem xi_addSingleton (H : FPHyp g fun e => β' (some e)) (hb : 0 < β' none) (F : ℝ)
    (α : ℝ) : xi (addSingleton g F) m' β' α =
      fun o => Option.elim o F (xi g (fun e => m' (some e)) (fun e => β' (some e)) α) := by
  set σ : E ⊕ Unit ≃ Option E := (Equiv.optionEquivSumPUnit E).symm
  have h := xi_dirSum σ (g₁ := g) (g₂ := modSingleton (Z := Unit) F) H
    (FPHyp.modSingleton (fun _ => hb) F) (addSingleton_eq_sum g F) (H.addSingleton hb F) m' α
  funext o
  cases o with
  | none =>
    have := h.1.2 PUnit.unit
    simp only [σ, Equiv.optionEquivSumPUnit_symm_inr] at this
    rw [this]
    exact (xi_modSingleton (fun _ => hb) F α _).1
  | some e =>
    have := h.1.1 e
    simp only [σ, Equiv.optionEquivSumPUnit_symm_inl] at this
    exact this

/-- `lem:fullplane`(f) for `g ⊕ π_F` on `Option E`: the old marginals are those of `g`. -/
theorem rho_addSingleton_some (H : FPHyp g fun e => β' (some e)) (hb : 0 < β' none) (F : ℝ)
    (α : ℝ) (e : E) : rho (addSingleton g F) m' β' α (some e) =
      rho g (fun e => m' (some e)) (fun e => β' (some e)) α e := by
  simp only [rho, marg, xi_addSingleton H hb F α, Option.elim]

/-- `lem:fullplane`(f) for `g ⊕ π_F` on `Option E`: the new element `b` has the marginal
`α m_b − β_b F`. -/
theorem rho_addSingleton_none (H : FPHyp g fun e => β' (some e)) (hb : 0 < β' none) (F : ℝ)
    (α : ℝ) : rho (addSingleton g F) m' β' α none = α * m' none - β' none * F := by
  simp only [rho, marg, xi_addSingleton H hb F α, Option.elim]

/-! ### `lem:fullplane`(g): the embedding -/

/-- `lem:fullplane`(g), auxiliary form (`appB-tools.tex:213-221`), for `f = g + Λ t − Θ β⁻¹` a
polymatroid rank function: `x*(α + Λ) = ξ^g(α) + Λ t − Θ β⁻¹` at every `α` with
`(α + Λ) m ≥ 0` and `ρ^g(α) + Θ ≥ 0`. Steps: (1) `y = ξ^g(α) + Λ t − Θ β⁻¹` satisfies
`y(S) ≤ f(S)` for every `S`, with equality exactly for the sets that are tight for `ξ^g(α)`, and its
marginals at `α + Λ` are `ρ^g(α) + Θ`; (2) so its upper level sets are those of `ρ^g(α)`, tight by
(a); (3) by (a) for `f`, `y = ξ^f(α + Λ)`; (4) as `f` is monotone, every `ỹ ∈ B_{(±)}(f)` is
nonnegative, so `B_{(±)}(f) = B(f)` and `y ∈ P₊(f)`; (5) at `α + Λ` the marginals `ρ(y)` are
nonnegative and every `A_{θ'}(y)`, `θ' > 0`, is tight by (a), so `y = x*(α + Λ)` by
`prop:optchar`. -/
theorem bestResponse_eq_add (H : FPHyp g β) {Λ Θ : ℝ}
    (hf : IsRankFunction fun S => g S + Λ * ∑ e ∈ S, m e / β e - Θ * ∑ e ∈ S, 1 / β e)
    {α : ℝ} (hm : ∀ e, 0 ≤ (α + Λ) * m e) (hρ : ∀ e, 0 ≤ rho g m β α e + Θ) :
    bestResponse (fun S => g S + Λ * ∑ e ∈ S, m e / β e - Θ * ∑ e ∈ S, 1 / β e) m β (α + Λ) =
      fun e => xi g m β α e + Λ * (m e / β e) - Θ * (1 / β e) := by
  set f : Finset E → ℝ := fun S => g S + Λ * ∑ e ∈ S, m e / β e - Θ * ∑ e ∈ S, 1 / β e
  have Hf : FPHyp f β := ⟨hf.submod, hf.empty, H.pos⟩
  -- (1) "The vector `y := ξ^g(α) + Λ t − Θ β⁻¹` satisfies `y(S) ≤ g(S) + Λ t(S) − Θ β⁻¹(S) = f(S)`
  -- for every `S ⊆ E`, with equality exactly for the sets that are tight for `ξ^g(α)` with respect
  -- to `g`, and its marginals at the share `α + Λ` are
  -- `ρ_e(y) = (α + Λ)m_e − β_e ξ^g_e(α) − Λ m_e + Θ = ρ^g_e(α) + Θ`."
  set ξ := xi g m β α
  set y : E → ℝ := fun e => ξ e + Λ * (m e / β e) - Θ * (1 / β e) with hy
  have hysum : ∀ S, ∑ e ∈ S, y e = ∑ e ∈ S, ξ e + Λ * ∑ e ∈ S, m e / β e -
      Θ * ∑ e ∈ S, 1 / β e := fun S => by
    simp only [hy, sum_sub_distrib, sum_add_distrib, mul_sum]
  have hyle : ∀ S, ∑ e ∈ S, y e ≤ f S := fun S => by
    rw [hysum]
    simp only [f]
    linarith [(xi_mem_fpBase H m α).1 S]
  have htight : ∀ S, IsTight f y S ↔ IsTight g ξ S := fun S => by
    unfold IsTight
    rw [hysum]
    simp only [f]
    constructor <;> intro h <;> linarith
  have hmarg : ∀ e, marg m β (α + Λ) y e = rho g m β α e + Θ := fun e => by
    have := (H.pos e).ne'
    simp only [marg, hy, rho, ξ]
    field_simp
    ring
  -- (2) "So the upper level sets of `ρ(y)` are those of `ρ^g(α)`, which are tight for `ξ^g(α)` by
  -- (a), hence for `y` with respect to `f`."
  have hlev : ∀ θ', levelSet m β (α + Λ) y θ' = levelSet m β α ξ (θ' - Θ) := fun θ' => by
    ext e
    simp only [levelSet, mem_filter, mem_univ, true_and, hmarg]
    show θ' ≤ rho g m β α e + Θ ↔ θ' - Θ ≤ rho g m β α e
    constructor <;> intro h <;> linarith
  have hyt : ∀ θ', IsTight f y (levelSet m β (α + Λ) y θ') := fun θ' => by
    rw [htight, hlev]
    exact xi_levelSet_tight H m α _
  -- (3) "By (a), applied to `f`, `y = ξ^f(α + Λ)`, and its marginals `ρ^g(α) + Θ` are
  -- nonnegative by assumption."
  have hyξ : y = xi f m β (α + Λ) := eq_xi_of_levelSets Hf hyle hyt
  have hyρ : ∀ e, 0 ≤ marg m β (α + Λ) y e := fun e => by rw [hmarg]; exact hρ e
  -- (4) "As `f` is monotone, every `ỹ ∈ B_{(±)}(f)` is nonnegative, since
  -- `ỹ_e ≥ f(E) − f(E ∖ {e}) ≥ 0`, so `B_{(±)}(f) = B(f)` and `y ∈ P₊(f)`."
  have hnonneg : ∀ z ∈ fpBase f, ∀ e, 0 ≤ z e := fun z hz e => by
    have h1 := (fpBase_subset_Icc f hz).1 e
    have h2 := hf.mono (erase_subset e (univ : Finset E))
    simp only at h1
    linarith
  have hB : fpBase f = basePoly f := by
    ext z
    exact ⟨fun hz => ⟨⟨hnonneg z hz, hz.1⟩, hz.2⟩, fun hz => ⟨hz.1.2, hz.2⟩⟩
  have hyP : y ∈ indepPoly f := by
    have hyB : y ∈ fpBase f := hyξ ▸ xi_mem_fpBase Hf m (α + Λ)
    rw [hB] at hyB
    exact hyB.1
  -- (5) "At the share `α + Λ ≥ 0`, the marginals `ρ(y)` are nonnegative and every level set
  -- `A_{θ'}(y)` with `θ' > 0` is tight by (a). By `prop:optchar`, `y = x*(α + Λ)`."
  -- The Lean assumes `(α + Λ)m_e ≥ 0` for every `e` in place of `α + Λ ≥ 0`.
  have hopt : IsBestResponse (indepPoly f) m β (α + Λ) y :=
    (isBestResponse_iff_levelSets hf H.pos hm).2 ⟨hyP, hyρ, fun θ' _ => by
      rw [hyξ]
      exact xi_levelSet_tight Hf m (α + Λ) θ'⟩
  exact (hopt.eq_bestResponse H.pos hf).symm

/-- **`lem:fullplane`(g)** (`appB-tools.tex:99-103`, proof `appB-tools.tex:213-221`):
for `g` submodular with `g(∅) = 0` and `m, β > 0`, if `f = g + Λ t − Θ β⁻¹` is a polymatroid rank
function for some `Λ, Θ ∈ ℝ`, then the instance `(f, m, β)` has
`x*(α + Λ) = ξ^g(α) + Λ t − Θ β⁻¹` at every `α ≥ −Λ` with `ρ^g_e(α) + Θ ≥ 0` for all `e ∈ E`.
Steps (in `bestResponse_eq_add`): (1) `y = ξ^g(α) + Λ t − Θ β⁻¹` satisfies `y ≤ f` with the tight
sets of `ξ^g(α)`, and its marginals at `α + Λ` are `ρ^g(α) + Θ`; (2) its upper level sets are those
of `ρ^g(α)`, tight by (a); (3) so `y = ξ^f(α + Λ)` by (a); (4) as `f` is monotone,
`B_{(±)}(f) = B(f)` and `y ∈ P₊(f)`; (5) `y = x*(α + Λ)` by `prop:optchar`. -/
theorem fullplane_g (hg : Submodular g) (hg0 : g ∅ = 0) (hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) {Λ Θ : ℝ}
    (hf : IsRankFunction fun S => g S + Λ * ∑ e ∈ S, m e / β e - Θ * ∑ e ∈ S, 1 / β e)
    {α : ℝ} (hα : -Λ ≤ α) (hρ : ∀ e, 0 ≤ rho g m β α e + Θ) :
    bestResponse (fun S => g S + Λ * ∑ e ∈ S, m e / β e - Θ * ∑ e ∈ S, 1 / β e) m β (α + Λ) =
      fun e => xi g m β α e + Λ * (m e / β e) - Θ * (1 / β e) :=
  bestResponse_eq_add ⟨hg, hg0, hβ⟩ hf (fun e => mul_nonneg (by linarith) (hm e).le) hρ

/-- **`lem:fullplane`** (Lemma B.10, `stoc-sections/appB-tools.tex:80-105`): let `g : 2^E → ℝ` be
submodular with `g(∅) = 0`, let `m, β ∈ ℝ^E_{>0}`, and let `α, θ ∈ ℝ`. (a) A vector `y ∈ ℝ^E` is
`ξ^g(α)` if and only if `y(S) ≤ g(S)` for all `S ⊆ E` and every upper level set `A_{θ'}(y)`,
`θ' ∈ ℝ`, of the marginals at the share `α` is tight for `y`. In particular, the sets `A^g_θ(α)` and
`{e ∈ E : ρ^g_e(α) > θ}` are tight for `ξ^g(α)`. (b) The set `A^g_θ(α)` minimizes `F^g_{α,θ}` and
contains every minimizer. (c) Let `b ∈ E` and `c ∈ ℝ` with `c β⁻¹(S) ≤ t(S)` for every `S ⊆ E`
with `b ∈ S`. Then `ρ^g_b` grows at least at the rate `c`, and every `ρ^g_e` grows at most at the
rate `max_{e'∈E} m_{e'}`. In particular, every `ρ^g_e` grows at least at the rate
`min_{e'∈E} m_{e'} > 0` and at most at the rate `max_{e'∈E} m_{e'}`, so it is nondecreasing, and
`ρ^g`, `ξ^g` and `α ↦ r(ξ^g(α))` are continuous. Moreover, `ρ^g_b` grows at least at the rate
`t_b/β⁻¹(E)`. (d) If `U ⊆ E` is tight for `ξ^g(a)` and for `ξ^g(a')`, where `a ≤ a'`, then
`∑_{e∈U} m_e ξ^g_e` and `∑_{e∈E∖U} m_e ξ^g_e` are both at least as large at `a'` as at `a`. In
particular, `α ↦ r(ξ^g(α))` is nondecreasing. (e) If the elements of a nonempty `D ⊆ E` have equal
marginals at `α`, then `ξ := ξ^g(α)` satisfies `∑_{e∈D} m_e ξ_e = α SS(D) + ξ(D) m̄_D`. (f) Let
`g = g_1 ⊕ g_2`, that is, `g(S) = g_1(S ∩ E_1) + g_2(S ∩ E_2)` for `S ⊆ E`, for submodular
`g_i : 2^{E_i} → ℝ` with `g_i(∅) = 0` on disjoint sets `E_1, E_2` with `E = E_1 ∪ E_2` (given by
`σ : E₁ ⊕ E₂ ≃ E`), and let `ξ^{g_i}` and `ρ^{g_i}` be taken with respect to `m|_{E_i}` and
`β|_{E_i}`. Then `ξ^g = (ξ^{g_1}, ξ^{g_2})` and `ρ^g = (ρ^{g_1}, ρ^{g_2})`. A modular singleton
`π_F` on `{τ_1}` with `π_F({τ_1}) = F` (`modSingleton F`) has `ξ^{π_F}_{τ_1}(α) = F` and
`ρ^{π_F}_{τ_1}(α) = α m_{τ_1} − β_{τ_1} F` for every `α ∈ ℝ`. (g) If `f := g + Λ t − Θ β⁻¹` is a
polymatroid rank function for some `Λ, Θ ∈ ℝ`, then the instance `(f, m, β)` has
`x*(α + Λ) = ξ^g(α) + Λ t − Θ β⁻¹` at every `α ≥ −Λ` with `ρ^g_e(α) + Θ ≥ 0` for all `e ∈ E`.

The shares `α, θ` are quantified in each part that uses them; the modular singleton of (f) lies on
its own one-element ground set, with its own `m, β > 0`. Its parts are `fullplane_a`,
`fullplane_b`, `fullplane_c`, `fullplane_d`, `fullplane_e`, `fullplane_f` and
`fullplane_f_singleton` (the two sentences of (f)), and `fullplane_g`; their docstrings give the
paper's steps. -/
theorem fullplane (hg : Submodular g) (hg0 : g ∅ = 0) (hm : ∀ e, 0 < m e)
    (hβ : ∀ e, 0 < β e) :
    -- (a) the level criterion
    (∀ α θ : ℝ, (∀ y : E → ℝ, y = xi g m β α ↔
        (∀ S : Finset E, ∑ e ∈ S, y e ≤ g S) ∧ ∀ θ' : ℝ, IsTight g y (levelSet m β α y θ')) ∧
      IsTight g (xi g m β α) (levelSet m β α (xi g m β α) θ) ∧
      IsTight g (xi g m β α) (univ.filter fun e => θ < rho g m β α e)) ∧
    -- (b) the level sets
    (∀ α θ : ℝ,
      (∀ S, levelFun g m β α θ (levelSet m β α (xi g m β α) θ) ≤ levelFun g m β α θ S) ∧
      ∀ S, (∀ S', levelFun g m β α θ S ≤ levelFun g m β α θ S') →
        S ⊆ levelSet m β α (xi g m β α) θ) ∧
    -- (c) rates
    (∀ (b : E) (c : ℝ),
      (∀ S : Finset E, b ∈ S → c * ∑ e ∈ S, 1 / β e ≤ ∑ e ∈ S, m e / β e) →
      GrowsAtLeast (fun α => rho g m β α b) c ∧
      (∀ e : E, GrowsAtMost (fun α => rho g m β α e) (univ.sup' ⟨e, mem_univ e⟩ m)) ∧
      (∀ e : E, GrowsAtLeast (fun α => rho g m β α e) (univ.inf' ⟨e, mem_univ e⟩ m) ∧
        0 < univ.inf' ⟨e, mem_univ e⟩ m ∧
        GrowsAtMost (fun α => rho g m β α e) (univ.sup' ⟨e, mem_univ e⟩ m) ∧
        Monotone fun α => rho g m β α e) ∧
      Continuous (fun α => rho g m β α) ∧ Continuous (fun α => xi g m β α) ∧
      Continuous (fun α => reward m (xi g m β α)) ∧
      GrowsAtLeast (fun α => rho g m β α b) ((m b / β b) / ∑ e, 1 / β e)) ∧
    -- (d) parts of the reward
    (∀ {U : Finset E} {a a' : ℝ}, a ≤ a' → IsTight g (xi g m β a) U →
      IsTight g (xi g m β a') U →
      (∑ e ∈ U, m e * xi g m β a e ≤ ∑ e ∈ U, m e * xi g m β a' e ∧
        ∑ e ∈ Uᶜ, m e * xi g m β a e ≤ ∑ e ∈ Uᶜ, m e * xi g m β a' e) ∧
      Monotone fun α => reward m (xi g m β α)) ∧
    -- (e) equal marginals
    (∀ (α : ℝ) {D : Finset E}, D.Nonempty →
      (∀ e ∈ D, ∀ e' ∈ D, rho g m β α e = rho g m β α e') →
      ∑ e ∈ D, m e * xi g m β α e = α * SS m β D + (∑ e ∈ D, xi g m β α e) * mbar m β D) ∧
    -- (f) direct sums, and the modular singleton
    ((∀ {E₁ E₂ : Type*} [Fintype E₁] [DecidableEq E₁] [Fintype E₂] [DecidableEq E₂]
        (σ : E₁ ⊕ E₂ ≃ E) {g₁ : Finset E₁ → ℝ} {g₂ : Finset E₂ → ℝ},
        Submodular g₁ → g₁ ∅ = 0 → Submodular g₂ → g₂ ∅ = 0 →
        (∀ S : Finset E, g S = g₁ (univ.filter fun a => σ (Sum.inl a) ∈ S) +
          g₂ (univ.filter fun b => σ (Sum.inr b) ∈ S)) → ∀ α : ℝ,
        ((∀ a, xi g m β α (σ (Sum.inl a)) =
            xi g₁ (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α a) ∧
          ∀ b, xi g m β α (σ (Sum.inr b)) =
            xi g₂ (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α b) ∧
        ((∀ a, rho g m β α (σ (Sum.inl a)) =
            rho g₁ (fun a => m (σ (Sum.inl a))) (fun a => β (σ (Sum.inl a))) α a) ∧
          ∀ b, rho g m β α (σ (Sum.inr b)) =
            rho g₂ (fun b => m (σ (Sum.inr b))) (fun b => β (σ (Sum.inr b))) α b)) ∧
      ∀ {Z : Type*} [Fintype Z] [Unique Z] [DecidableEq Z] {m β : Z → ℝ},
        (∀ z, 0 < m z) → (∀ z, 0 < β z) → ∀ (F α : ℝ) (τ₁ : Z),
        xi (modSingleton F) m β α τ₁ = F ∧
          rho (modSingleton F) m β α τ₁ = α * m τ₁ - β τ₁ * F) ∧
    -- (g) the embedding
    ∀ {Λ Θ : ℝ},
      IsRankFunction (fun S => g S + Λ * ∑ e ∈ S, m e / β e - Θ * ∑ e ∈ S, 1 / β e) →
      ∀ {α : ℝ}, -Λ ≤ α → (∀ e, 0 ≤ rho g m β α e + Θ) →
      bestResponse (fun S => g S + Λ * ∑ e ∈ S, m e / β e - Θ * ∑ e ∈ S, 1 / β e) m β
          (α + Λ) =
        fun e => xi g m β α e + Λ * (m e / β e) - Θ * (1 / β e) :=
  ⟨fullplane_a hg hg0 hm hβ, fullplane_b hg hg0 hm hβ, fullplane_c hg hg0 hm hβ,
    fullplane_d hg hg0 hm hβ, fullplane_e hg hg0 hm hβ,
    ⟨fun σ _ _ hg₁ hg₁0 hg₂ hg₂0 hgsum α =>
      fullplane_f σ hg₁ hg₁0 hg₂ hg₂0 hgsum hg hg0 hm hβ α, fullplane_f_singleton⟩,
    fullplane_g hg hg0 hm hβ⟩

/-- The setting (`appB-tools.tex:40`): for a polymatroid rank function `g`, `m, β > 0` and a share
`α ≥ 0` at which all full-plane marginals are nonnegative, `ξ^g(α) = x*(α)`, and `ρ^g(α)` is the
vector of the marginals `ρ_e(α)` of the best response (`lem:fullplane`(g) with `Λ = Θ = 0`). -/
theorem xi_eq_bestResponse (hg : IsRankFunction g) (hm : ∀ e, 0 < m e) (hβ : ∀ e, 0 < β e)
    {α : ℝ} (hα : 0 ≤ α) (hρ : ∀ e, 0 ≤ rho g m β α e) :
    xi g m β α = bestResponse g m β α ∧
      ∀ e, rho g m β α e = marg m β α (bestResponse g m β α) e := by
  have hf0 : (fun S => g S + 0 * ∑ e ∈ S, m e / β e - 0 * ∑ e ∈ S, 1 / β e) = g := by
    funext S
    ring
  have h := fullplane_g hg.submod hg.empty hm hβ (Λ := 0) (Θ := 0) (by rw [hf0]; exact hg)
    (α := α) (by linarith) (fun e => by rw [add_zero]; exact hρ e)
  rw [hf0, add_zero] at h
  have hξ : xi g m β α = bestResponse g m β α := by
    rw [h]
    funext e
    ring
  exact ⟨hξ, fun e => by rw [← hξ]; rfl⟩

end

end Hardness

end Stoc
