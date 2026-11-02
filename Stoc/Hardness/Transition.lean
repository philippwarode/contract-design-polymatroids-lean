-- stamp r8 2026-11-02
import Stoc.Hardness.OneLevel

/-!
# The transition: `lem:twosides` and `thm:transition`

The STOC version's `lem:twosides` and `thm:transition` (Appendix C.6, `sec:D-onelevel`, "The
transition", `stoc-sections/appD-hardness.tex:989-1163`), for the levels of `def:tower` built by
the parameter rule:

* `twosides`: `lem:twosides`, by induction on `k` (`twosides_aux`);
* `TransitionHyp`: the hypotheses (T1)–(T3) of `thm:transition`;
* `zeroF`, `zeroH`, `cuts`: the zeros of the differences `θ_b − ρ^f_e` and `θ_b − ρ^h_e`, at which
  the proof cuts the transition into pieces; `sign_on_piece`, `transition_piece`: the step (1)
  of the proof (on a piece the configuration is constant, and a weak configuration at every point
  of the closed piece); `monotoneOn_of_pieces`, `antitoneOn_of_pieces`: a function monotone on
  every piece is monotone on the interval;
* `transition`: `thm:transition` (`transition_aux`).

The exact statements `twosides` and `transition` are for an input `μ^in ∈ 𝔉` (`def:tower`) of
length at least `k + 1` and `k + 2`; they are derived from `twosides_aux` and `transition_aux`,
which carry the paper's proofs under the weaker hypothesis `μ^in_1 > 0` (the hypothesis `h0`, which
gives `μ_0 = 1/3`) and cite the auxiliary forms of `lem:closedforms`, `lem:fast`, `lem:onelevel`
and `lem:leftwindows`.

Taken over on 2026-10-20 from `Paper/Hardness/Transition.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

section Tower

variable {μin : ℕ → ℕ}

/-- The gap of level `j` changes by `q_j(α' − α)` minus the change of the reward, as `L_j` has
slope `q_j`. -/
lemma gapT_sub (j : ℕ) (α α' : ℝ) :
    gapT μin j α' - gapT μin j α = (lvl μin j).q * (α' - α) -
      (curve (gT μin j) (mT μin j) (βT μin j) α' - curve (gT μin j) (mT μin j) (βT μin j) α) := by
  simp only [gapT, gap]
  ring

/-- `ψ_{k+1} = (12/13)Δ_b²/β_δ ≥ 0`. -/
lemma ψ_nonneg (k : ℕ) : 0 ≤ (lvl μin k).ψ := by
  have := (lvl μin k).βδ_pos
  unfold Level.ψ
  positivity

/-! ### `lem:twosides` -/

/-- `lem:twosides` under the weaker hypothesis `μ^in_1 > 0` instead of `μ^in ∈ 𝔉` of length at
least `k + 1`, which is what the proofs below use (`stoc-sections/appD-hardness.tex:999-1011`,
proof lines 1013-1041): let `k ≥ 0`, and assume the hypotheses of `lem:onelevel` at the steps
`0 → 1, …, k − 1 → k`. Then
(a) on `[R_1^{(k)}, ∞)` the gap `L_k(α) − r(ξ^{(k)}(α))` of level `k` is nondecreasing, with the
value `7ε_0` at `R_1^{(k)}`, as for the base at `R_1^{(0)}`, so
`r(ξ^{(k)}(α')) − r(ξ^{(k)}(α)) ≤ q_k(α' − α)` for `R_1^{(k)} ≤ α ≤ α'`; and (b)
`L_k(α) − r(ξ^{(k)}(α)) = ζ_1 − α` for `α ∈ [R_0 − ι, R_0]`.

The proof's steps, by induction on `k`: (1) for `k = 0`, the proof of `prop:base`
(`Base.base_gap_pieces`) gives the gap `7(α − ζ_2)` on `[ζ_2, ∞)`, so the gap is `7ε_0` at
`R_1^{(0)} = ζ_2 + ε_0`, and it also gives the gap `ζ_1 − α` on `[−1/6, ζ_1]`, which contains
`[R_0 − ι, R_0]`; (2) for `k ≥ 1`, by `lem:onelevel`(b) at the step `k − 1 → k`, on
`[R_0 + μ_k, ∞) ⊇ [R_1^{(k)}, ∞)` the gap of level `k` at `α` is
`L_{k−1}(α − μ_k) − r(ξ^{(k−1)}(α − μ_k)) + ψ_k max(α − α_{τ_2}, 0)`, where
`α_{τ_2} > R_1^{(k−1)} + μ_k = R_1^{(k)}`; (3) for `α ≥ R_1^{(k)}` the first two terms are the gap
of level `k − 1` at `α − μ_k ≥ R_1^{(k−1)}`, nondecreasing by induction and `7ε_0` at
`α = R_1^{(k)}`, and the last term is nondecreasing and vanishes at `R_1^{(k)}`; this gives the
first claim of (a), and the second follows, as `L_k` has slope `q_k`; (4) for (b), let
`α ∈ [R_0 − ι, R_0]`: as `u_1^{(k)}` has slope `s_k` (`lem:closedforms`(b)), (W1) at the step
`k − 1 → k` gives `u_1^{(k)}(α) ≥ u_1^{(k)}(R_0) − s_kι > 0`; (5) so, by `lem:leftwindows`(c),
level `k` has the configuration `(E ∖ {τ_{1,k}}, E)` of its first window at `α`, and as in the proof
of `lem:onelevel`(b) (`gapT_config_τ₁`), `lem:dmt`(a) and (c) show that the gap of level `k` at `α`
is that of level `k − 1`, which is `ζ_1 − α` by induction. -/
theorem twosides_aux (h0 : 0 < μin 0) (k : ℕ) (hyp : ∀ i < k, OneLevelHyp μin i) :
    (MonotoneOn (gapT μin k) (Set.Ici (R1T μin k)) ∧ gapT μin k (R1T μin k) = 7 * ε₀ ∧
      ∀ α α', R1T μin k ≤ α → α ≤ α' →
        curve (gT μin k) (mT μin k) (βT μin k) α' - curve (gT μin k) (mT μin k) (βT μin k) α ≤
          (lvl μin k).q * (α' - α)) ∧
    ∀ α ∈ Set.Icc (R0 - ι) R0, gapT μin k α = ζ₁ - α := by
  -- "By induction on `k`."
  induction k with
  | zero =>
    -- (1) "For `k = 0`, the proof of `prop:base` gives `L_0(α) − r(ξ^{(0)}(α)) = 7(α − ζ_2)` on
    -- `[ζ_2, ∞)`, so the gap is `7ε_0` at `R_1^{(0)} = ζ_2 + ε_0`. It also gives
    -- `L_0(α) − r(ξ^{(0)}(α)) = ζ_1 − α` on `[−1/6, ζ_1]`, which contains `[R_0 − ι, R_0]`."
    obtain ⟨g₂, -, -, g₅⟩ := Base.base_gap_pieces
    have hε := ε₀_pos
    have hgap : ∀ α, gapT μin 0 α = L₀ α - curve Base.f₀ Base.m Base.β α := fun α => rfl
    have hR1 : R1T μin 0 = ζ₂ + ε₀ := by
      unfold R1T
      rw [sum_range_one, μT_zero h0]
      unfold ζ₁ ζ₂
      norm_num
    have hR : R0 = 3 / 10 := R0_eq
    refine ⟨⟨fun α hα α' hα' hαα => ?_, ?_, fun α α' hα hαα => ?_⟩, fun α hα => ?_⟩
    · rw [Set.mem_Ici, hR1] at hα hα'
      rw [hgap, hgap, g₅ α (by linarith), g₅ α' (by linarith)]
      linarith
    · -- "so the gap is `7ε_0` at `R_1^{(0)} = ζ_2 + ε_0`"
      rw [hgap, hR1, g₅ _ (by linarith)]
      ring
    · -- "… and the second follows, as `L_k` has slope `q_k`." (from the inductive step)
      -- The Lean: the same for `k = 0`, as `L_0` has slope `q_0`; the paper states it for `k ≥ 1`.
      rw [hR1] at hα
      have h1 := g₅ α (by linarith)
      have h2 := g₅ α' (by linarith)
      change curve Base.f₀ Base.m Base.β α' - curve Base.f₀ Base.m Base.β α ≤ q₀ * (α' - α)
      simp only [L₀] at h1 h2
      nlinarith
    · rw [hgap, g₂ α (by rw [hR] at hα; unfold ι at hα; linarith [hα.1])
        (by rw [hR] at hα; unfold ζ₁; linarith [hα.2])]
  | succ j ih =>
    have hj := hyp j (Nat.lt_succ_self j)
    obtain ⟨⟨ihmono, ihval, -⟩, ihb⟩ := ih fun i hi => hyp i (Nat.lt_succ_of_lt hi)
    have hμ := hj.μ_pos
    have hR0R1 := R0_lt_R1T (μin := μin) j
    -- (2) "Let `k ≥ 1`. By `lem:onelevel`(b) at the step `k − 1 → k`, on `[R_0 + μ_k, ∞)`, which
    -- contains `[R_1^{(k)}, ∞)`, the gap of level `k` at `α` is
    -- `L_{k−1}(α − μ_k) − r(ξ^{(k−1)}(α − μ_k)) + ψ_k max(α − α_{τ_2}, 0)`, where
    -- `α_{τ_2} > R_1^{(k−1)} + μ_k = R_1^{(k)}` is the point `α_{τ_2}` of that step."
    obtain ⟨-, hb2, hb3⟩ := onelevel_b_aux hj
    have hατ₂ := (onelevel_a_aux hj).1
    have hR1 : R1T μin (j + 1) = R1T μin j + μT μin (j + 1) := R1T_succ j
    have hgap : ∀ α, R1T μin (j + 1) ≤ α → gapT μin (j + 1) α =
        gapT μin j (α - μT μin (j + 1)) + (lvl μin j).ψ * max (α - ατ₂ μin j) 0 := by
      intro α hα
      rcases le_total α (ατ₂ μin j) with h1 | h1
      · rw [hb2 α ⟨by linarith, h1⟩, max_eq_right (by linarith)]
        ring
      · rw [hb3 α h1, max_eq_left (by linarith)]
    have hψ := ψ_nonneg (μin := μin) j
    -- (3) "For `α ≥ R_1^{(k)}`, the first two terms are the gap of level `k − 1` at
    -- `α − μ_k ≥ R_1^{(k−1)}`, which is nondecreasing in `α` by induction, with the value `7ε_0`
    -- at `α = R_1^{(k)}`. The last term is nondecreasing and vanishes at `R_1^{(k)}`. This gives
    -- the first claim of (a), and the second follows, as `L_k` has slope `q_k`."
    have hmono : MonotoneOn (gapT μin (j + 1)) (Set.Ici (R1T μin (j + 1))) := by
      intro α hα α' hα' hαα
      rw [Set.mem_Ici] at hα hα'
      rw [hgap α hα, hgap α' hα']
      have h1 := ihmono (a := α - μT μin (j + 1)) (b := α' - μT μin (j + 1))
        (by rw [Set.mem_Ici]; linarith) (by rw [Set.mem_Ici]; linarith) (by linarith)
      have h2 : max (α - ατ₂ μin j) 0 ≤ max (α' - ατ₂ μin j) 0 := max_le_max (by linarith) le_rfl
      nlinarith
    refine ⟨⟨hmono, ?_, fun α α' hα hαα => ?_⟩, fun α hα => ?_⟩
    · rw [hgap _ le_rfl, hR1, add_sub_cancel_right, ihval, max_eq_right (by linarith)]
      ring
    · have h1 := hmono (a := α) (b := α') hα (Set.mem_Ici.2 (hα.trans hαα)) hαα
      have h2 := gapT_sub (μin := μin) (j + 1) α α'
      linarith
    · -- (4) "As `u_1^{(k)}` has slope `s_k` (`lem:closedforms`(b)), (W1) at the step `k − 1 → k`
      -- gives `u_1^{(k)}(α) ≥ u_1^{(k)}(R_0) − s_kι > 0`."
      have hslope := (closedforms_b_aux j hμ).2.2.2.2.1 α R0
      have hs := s_pos (μin := μin) j
      have hu : 0 ≤ u1 μin j α := by
        have := mul_le_mul_of_nonneg_left (show R0 - α ≤ ι by linarith [hα.1]) hs.le
        linarith [hj.W1a]
      -- (5) "So, by `lem:leftwindows`(c), level `k` has the configuration `(E ∖ {τ_{1,k}}, E)` of
      -- its first window at `α`, with `E = E_{k−1} ∪ {τ_{1,k}, τ_{2,k}}`. As in the proof of
      -- `lem:onelevel`(b), `lem:dmt`(a) and (c) then show that the gap of level `k` at `α` is
      -- `L_{k−1}(α) − r(ξ^{(k−1)}(α))`, which is `ζ_1 − α` by induction."
      obtain ⟨hc, -, -⟩ := leftwindows_c_aux hj α hα.2 hu
      rw [gapT_config_τ₁ j hμ hc.weak, ihb α hα]

/-- **`lem:twosides`** (Lemma C.17, `stoc-sections/appD-hardness.tex:999-1011`, proof lines
1013-1041): let `μ^in ∈ 𝔉` have length at least `k + 1` (`def:tower`, so that level `k` is built),
let `k ≥ 0`, and assume the hypotheses of `lem:onelevel` at the steps `0 → 1, …, k − 1 → k`. Then
(a) on `[R_1^{(k)}, ∞)` the gap `L_k(α) − r(ξ^{(k)}(α))` of level `k` is nondecreasing, with the
value `7ε_0` at `R_1^{(k)}`, as for the base at `R_1^{(0)}`, so
`r(ξ^{(k)}(α')) − r(ξ^{(k)}(α)) ≤ q_k(α' − α)` for `R_1^{(k)} ≤ α ≤ α'`; and (b)
`L_k(α) − r(ξ^{(k)}(α)) = ζ_1 − α` for `α ∈ [R_0 − ι, R_0]`. The proof (by induction on `k`, steps
(1)–(5)) is that of `twosides_aux`, with `μ^in_1 > 0` as `μ^in ∈ 𝔉`; the length is not used. -/
theorem twosides {K : ℕ} (hF : InF μin K) (k : ℕ) (_hK : k + 1 ≤ K)
    (hyp : ∀ i < k, OneLevelHyp μin i) :
    (MonotoneOn (gapT μin k) (Set.Ici (R1T μin k)) ∧ gapT μin k (R1T μin k) = 7 * ε₀ ∧
      ∀ α α', R1T μin k ≤ α → α ≤ α' →
        curve (gT μin k) (mT μin k) (βT μin k) α' - curve (gT μin k) (mT μin k) (βT μin k) α ≤
          (lvl μin k).q * (α' - α)) ∧
    ∀ α ∈ Set.Icc (R0 - ι) R0, gapT μin k α = ζ₁ - α :=
  twosides_aux (μin0_pos hF) k hyp

/-! ### The hypotheses of `thm:transition` -/

variable (μin)

/-- The hypotheses (T1)–(T3) of `thm:transition` at the step `k → k + 1`, for old elements
`e_t, e_l ∈ E_k` (`stoc-sections/appD-hardness.tex:1053-1061`). The elements of level `k + 1` are
`b = none`, `τ_2 = some none`, `τ_1 = some (some none)` and the old `some (some (some e))`; `SSq` is
`SS` of level `k + 1`; the transition is `[R_1, R_0 + μ]`. -/
structure TransitionHyp (k : ℕ) (et el : Gr k) : Prop where
  /-- (T1), first part: `ψ_{k+1} ≥ SSq((E_k ∖ {e_t}) ∪ {b})` -/
  T1a : SS (mT μin (k + 1)) (βT μin (k + 1))
    (insert none ((univ.erase et).image fun c => some (some (some c)))) ≤ (lvl μin k).ψ
  /-- (T1), second part: `SSq({b, e_t}) ≥ q_{k+1}` -/
  T1b : (lvl μin (k + 1)).q ≤ SS (mT μin (k + 1)) (βT μin (k + 1)) {none, some (some (some et))}
  /-- (T1), third part: if `e_l ≠ e_t`, also `SSq({b, τ_2, e_l}) ≥ q_{k+1}` -/
  T1c : el ≠ et → (lvl μin (k + 1)).q ≤
    SS (mT μin (k + 1)) (βT μin (k + 1)) {none, some none, some (some (some el))}
  /-- (T2): on the transition, `ρ^h_{τ_1} < ρ^f_e < ρ^f_{τ_2} < ρ^h_{e'} ≤ ρ^h_{e_l}` for all
  `e, e' ∈ E_k` -/
  T2 : ∀ α ∈ Set.Icc (R1T μin k) (R0 + μT μin (k + 1)), ∀ c c' : Gr k,
    ρh μin k α (some none) < ρf μin k α (some (some c)) ∧
      ρf μin k α (some (some c)) < ρf μin k α none ∧
      ρf μin k α none < ρh μin k α (some (some c')) ∧
      ρh μin k α (some (some c')) ≤ ρh μin k α (some (some el))
  /-- (T3): `θ_2 ≤ ρ^h_{e_l}` at `R_0 + μ − ι` -/
  T3 : θ2 μin k (R0 + μT μin (k + 1) - ι) ≤ ρh μin k (R0 + μT μin (k + 1) - ι) (some (some el))

/-- The zero of `θ_b − ρ^f_e` (by `lem:fast`, there is at most one); if the difference has no
zero, `Classical.epsilon` gives an arbitrary real number. -/
def zeroF (k : ℕ) (e : Option (Option (Gr k))) : ℝ :=
  Classical.epsilon fun x => θb μin k x = ρf μin k x e

/-- The zero of `θ_b − ρ^h_e` (by `lem:fast`, there is at most one); if the difference has no
zero, an arbitrary real number. -/
def zeroH (k : ℕ) (e : Option (Option (Gr k))) : ℝ :=
  Classical.epsilon fun x => θb μin k x = ρh μin k x e

/-- The finitely many points at which the proof of `thm:transition` cuts the transition into
pieces: the zeros of the differences `θ_b − ρ^f_e` and `θ_b − ρ^h_e`, `e ∈ E` (`mem_cuts_f`,
`mem_cuts_h`). The set may contain further points, the values `zeroF`, `zeroH` of differences
without a zero, and zeros outside the transition; cutting there as well only gives finer pieces. -/
def cuts (k : ℕ) : Finset ℝ := univ.image (zeroF μin k) ∪ univ.image (zeroH μin k)

variable {μin}

/-- A zero of `θ_b − ρ^f_e` is a cut point, as the difference is strictly increasing
(`lem:fast`). -/
lemma mem_cuts_f {k : ℕ} (h6 : (lvl μin k).M < cfast μin k) {x : ℝ} {e : Option (Option (Gr k))}
    (hx : θb μin k x = ρf μin k x e) : x ∈ cuts μin k := by
  have hz : θb μin k (zeroF μin k e) = ρf μin k (zeroF μin k e) e :=
    Classical.epsilon_spec (p := fun x => θb μin k x = ρf μin k x e) ⟨x, hx⟩
  have : zeroF μin k e = x := ((fast_aux k h6).2 e).2.1.injective (by simp only [hz, hx, sub_self])
  exact mem_union_left _ (mem_image.2 ⟨e, mem_univ e, this⟩)

/-- A zero of `θ_b − ρ^h_e` is a cut point. -/
lemma mem_cuts_h {k : ℕ} (h6 : (lvl μin k).M < cfast μin k) {x : ℝ} {e : Option (Option (Gr k))}
    (hx : θb μin k x = ρh μin k x e) : x ∈ cuts μin k := by
  have hz : θb μin k (zeroH μin k e) = ρh μin k (zeroH μin k e) e :=
    Classical.epsilon_spec (p := fun x => θb μin k x = ρh μin k x e) ⟨x, hx⟩
  have : zeroH μin k e = x :=
    ((fast_aux k h6).2 e).2.2.2.injective (by simp only [hz, hx, sub_self])
  exact mem_union_right _ (mem_image.2 ⟨e, mem_univ e, this⟩)

/-! ### The pieces -/

/-- Signs on a piece (not in the paper: step (1) of the proof of `thm:transition`,
`stoc-sections/appD-hardness.tex:1070-1075`, leaves this implicit in "are constant", "As the
differences increase" and "by continuity"): let `φ` be continuous and strictly increasing without
zeros in `(c, c')`, and `x₀ ∈ (c, c')`. If `φ(x₀) < 0`, then `φ < 0` on `[c, c')` and
`φ(c') ≤ 0`; if `φ(x₀) > 0`, then `φ > 0` on `(c, c']` and `φ(c) ≥ 0` (by the monotonicity and the
intermediate value theorem). -/
lemma sign_on_piece {φ : ℝ → ℝ} (hc : Continuous φ) (hm : StrictMono φ) {c c' x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo c c') (hZ : ∀ x ∈ Set.Ioo c c', φ x ≠ 0) :
    (φ x₀ < 0 → (∀ x ∈ Set.Ico c c', φ x < 0) ∧ φ c' ≤ 0) ∧
      (0 < φ x₀ → (∀ x ∈ Set.Ioc c c', 0 < φ x) ∧ 0 ≤ φ c) := by
  constructor
  · intro hneg
    have hright : ∀ y, x₀ ≤ y → y < c' → φ y < 0 := by
      intro y hy hyc
      by_contra hcon
      push Not at hcon
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hy hc.continuousOn ⟨hneg.le, hcon⟩
      exact hZ z ⟨by linarith [hx₀.1, hz.1], lt_of_le_of_lt hz.2 hyc⟩ hz0
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases le_or_gt x x₀ with hxx | hxx
      · exact (hm.monotone hxx).trans_lt hneg
      · exact hright x hxx.le hx.2
    · by_contra hcon
      push Not at hcon
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hx₀.2.le hc.continuousOn
        ⟨hneg.le, hcon.le⟩
      have hzc : z ≠ c' := fun h => by rw [h] at hz0; linarith
      exact hZ z ⟨by linarith [hx₀.1, hz.1], lt_of_le_of_ne hz.2 hzc⟩ hz0
  · intro hpos
    have hleft : ∀ y, c < y → y ≤ x₀ → 0 < φ y := by
      intro y hy hyx
      by_contra hcon
      push Not at hcon
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hyx hc.continuousOn ⟨hcon, hpos.le⟩
      exact hZ z ⟨lt_of_lt_of_le hy hz.1, by linarith [hx₀.2, hz.2]⟩ hz0
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases le_or_gt x₀ x with hxx | hxx
      · exact hpos.trans_le (hm.monotone hxx)
      · exact hleft x hx.1 hxx.le
    · by_contra hcon
      push Not at hcon
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hx₀.1.le hc.continuousOn
        ⟨hcon.le, hpos.le⟩
      have hzc : z ≠ c := fun h => by rw [h] at hz0; linarith
      exact hZ z ⟨lt_of_le_of_ne hz.1 hzc.symm, by linarith [hx₀.2, hz.2]⟩ hz0

/-- `lem:windows`, before (a) (`stoc-sections/appB-tools.tex:408-409`), at the step: if `U` is an
upper level set of `ρ^f(α)` and `W` one of `ρ^h(α)` at the level `θ_b(α)`, strict or not, then
`(U, W)` is a weak configuration at `α`: the inequalities hold by the definition of the sets, and
the tightness by `lem:fullplane`(a) (`isWeakConfig_of_levelSets`). -/
lemma isWeakConfigT_of_levelSets {k : ℕ} {α : ℝ} {U W : Finset (Option (Option (Gr k)))}
    (hU : (∀ e, e ∈ U ↔ θb μin k α < ρf μin k α e) ∨ (∀ e, e ∈ U ↔ θb μin k α ≤ ρf μin k α e))
    (hW : (∀ e, e ∈ W ↔ θb μin k α < ρh μin k α e) ∨ (∀ e, e ∈ W ↔ θb μin k α ≤ ρh μin k α e)) :
    IsWeakConfigT μin k α U W := by
  have hU1 : ∀ e ∈ U, θb μin k α ≤ ρf μin k α e := fun e he => by
    rcases hU with hU | hU
    · exact ((hU e).1 he).le
    · exact (hU e).1 he
  have hU2 : ∀ e ∉ U, ρf μin k α e ≤ θb μin k α := fun e he => by
    rcases hU with hU | hU
    · exact not_lt.1 fun h => he ((hU e).2 h)
    · exact (not_le.1 fun h => he ((hU e).2 h)).le
  have hW1 : ∀ e ∈ W, θb μin k α ≤ ρh μin k α e := fun e he => by
    rcases hW with hW | hW
    · exact ((hW e).1 he).le
    · exact (hW e).1 he
  have hW2 : ∀ e ∉ W, ρh μin k α e ≤ θb μin k α := fun e he => by
    rcases hW with hW | hW
    · exact not_lt.1 fun h => he ((hW e).2 h)
    · exact (not_le.1 fun h => he ((hW e).2 h)).le
  have ht := isWeakConfig_of_levelSets (stepD_hyp k).fHyp.submod
    (stepD_hyp k).fHyp.empty (mT_pos (μin := μin) (k + 1)) (fpHyp_gT (k + 1)).pos
    (stepD_hyp k).d_nonneg α (U := U) (W := W)
    ⟨θb μin k α, by
      rcases hU with hU | hU
      · right
        ext e
        simp only [mem_filter, mem_univ, true_and]
        exact hU e
      · left
        ext e
        simp only [levelSet, mem_filter, mem_univ, true_and]
        exact hU e⟩
    ⟨θb μin k α, by
      rcases hW with hW | hW
      · right
        ext e
        simp only [mem_filter, mem_univ, true_and]
        exact hW e
      · left
        ext e
        simp only [levelSet, mem_filter, mem_univ, true_and]
        exact hW e⟩
  exact ⟨hU1, fun e he => ⟨hU2 e (mem_sdiff.1 he).2, hW1 e (mem_sdiff.1 he).1⟩, hW2, ht⟩

/-- **Step (1) of the proof of `thm:transition`** (`stoc-sections/appD-hardness.tex:1067-1079`),
under (W6): let `[c, c']` be a piece, that is, `c < c'` and no zero of the differences
`θ_b − ρ^f_e` and `θ_b − ρ^h_e`, `e ∈ E`, lies in `(c, c')`. Let `U := {e : ρ^f_e > θ_b}` and
`W := {e : ρ^h_e > θ_b}` at an interior point `x₀` (the midpoint). Then `U ⊆ W`
(`thm:splice`(a)); on the interior, `(U, W)` is the configuration; and `(U, W)` is a weak
configuration at every point of `[c, c']`.

The step's sentences: (1) by (W6) and `lem:fast`, every difference is continuous and strictly
increasing, so it has at most one zero, and the transition is cut at these zeros (`cuts`) into
pieces; (2) on the interior of a piece, `U` and `W` are constant (`sign_on_piece`); (3) as the
differences increase, `U` and `W` are also `{ρ^f > θ_b}` and `{ρ^h > θ_b}` at `c`, and
`{ρ^f ≥ θ_b}` and `{ρ^h ≥ θ_b}` at `c'`; (4) so at every point of `[c, c']` the inequalities of a
weak configuration hold for `(U, W)`, and `U` and `W` are upper level sets of `ρ^f` and of `ρ^h`;
hence `(U, W)` is a weak configuration there (`isWeakConfigT_of_levelSets`), and in the interior
it is the configuration. -/
theorem transition_piece {k : ℕ} (h6 : (lvl μin k).M < cfast μin k) {c c' : ℝ} (hcc : c < c')
    (hZ : ∀ z ∈ cuts μin k, z ∉ Set.Ioo c c') :
    (univ.filter fun e => θb μin k ((c + c') / 2) < ρf μin k ((c + c') / 2) e) ⊆
        univ.filter (fun e => θb μin k ((c + c') / 2) < ρh μin k ((c + c') / 2) e) ∧
      (∀ x ∈ Set.Ioo c c', IsConfig μin k x
        (univ.filter fun e => θb μin k ((c + c') / 2) < ρf μin k ((c + c') / 2) e)
        (univ.filter fun e => θb μin k ((c + c') / 2) < ρh μin k ((c + c') / 2) e)) ∧
      (∀ x ∈ Set.Icc c c', IsWeakConfigT μin k x
        (univ.filter fun e => θb μin k ((c + c') / 2) < ρf μin k ((c + c') / 2) e)
        (univ.filter fun e => θb μin k ((c + c') / 2) < ρh μin k ((c + c') / 2) e)) := by
  set x₀ := (c + c') / 2
  have hx₀ : x₀ ∈ Set.Ioo c c' := ⟨by simp only [x₀]; linarith, by simp only [x₀]; linarith⟩
  -- (1) "By (W6) and `lem:fast`, every difference `θ_b − ρ^f_e` and `θ_b − ρ^h_e`, `e ∈ E`, is
  -- continuous and strictly increasing, so it has at most one zero. We cut the transition at these
  -- finitely many zeros into pieces."
  have hf := (fast_aux k h6).2
  have hZf : ∀ e, ∀ x ∈ Set.Ioo c c', θb μin k x - ρf μin k x e ≠ 0 := fun e x hx h0 =>
    hZ x (mem_cuts_f h6 (sub_eq_zero.1 h0)) hx
  have hZh : ∀ e, ∀ x ∈ Set.Ioo c c', θb μin k x - ρh μin k x e ≠ 0 := fun e x hx h0 =>
    hZ x (mem_cuts_h h6 (sub_eq_zero.1 h0)) hx
  -- (2) "On the interior of a piece `[c, c']`, the sets `U := {e ∈ E : ρ^f_e > θ_b}` and
  -- `W := {e ∈ E : ρ^h_e > θ_b}` are constant, …" and (3) "As the differences increase, `U` and
  -- `W` are also `{e : ρ^f_e > θ_b}` and `{e : ρ^h_e > θ_b}` at `c`, and `{e : ρ^f_e ≥ θ_b}` and
  -- `{e : ρ^h_e ≥ θ_b}` at `c'`."
  have sf := fun e => sign_on_piece (hf e).1 (hf e).2.1 hx₀ (hZf e)
  have sh := fun e => sign_on_piece (hf e).2.2.1 (hf e).2.2.2 hx₀ (hZh e)
  have hUo : ∀ e, ∀ x ∈ Set.Ico c c',
      (θb μin k x₀ < ρf μin k x₀ e ↔ θb μin k x < ρf μin k x e) := by
    intro e x hx
    rcases lt_trichotomy (θb μin k x₀ - ρf μin k x₀ e) 0 with h | h | h
    · have := ((sf e).1 h).1 x hx
      constructor <;> intro _ <;> linarith
    · exact absurd h (hZf e x₀ hx₀)
    · constructor
      · intro h'
        linarith
      · intro h'
        rcases eq_or_lt_of_le hx.1 with hxc | hxc
        · subst hxc
          have := ((sf e).2 h).2
          linarith
        · have := ((sf e).2 h).1 x ⟨hxc, hx.2.le⟩
          linarith
  have hWo : ∀ e, ∀ x ∈ Set.Ico c c',
      (θb μin k x₀ < ρh μin k x₀ e ↔ θb μin k x < ρh μin k x e) := by
    intro e x hx
    rcases lt_trichotomy (θb μin k x₀ - ρh μin k x₀ e) 0 with h | h | h
    · have := ((sh e).1 h).1 x hx
      constructor <;> intro _ <;> linarith
    · exact absurd h (hZh e x₀ hx₀)
    · constructor
      · intro h'
        linarith
      · intro h'
        rcases eq_or_lt_of_le hx.1 with hxc | hxc
        · subst hxc
          have := ((sh e).2 h).2
          linarith
        · have := ((sh e).2 h).1 x ⟨hxc, hx.2.le⟩
          linarith
  have hUc' : ∀ e, (θb μin k x₀ < ρf μin k x₀ e ↔ θb μin k c' ≤ ρf μin k c' e) := by
    intro e
    rcases lt_trichotomy (θb μin k x₀ - ρf μin k x₀ e) 0 with h | h | h
    · have := ((sf e).1 h).2
      constructor <;> intro _ <;> linarith
    · exact absurd h (hZf e x₀ hx₀)
    · have := ((sf e).2 h).1 c' ⟨hcc, le_rfl⟩
      constructor <;> intro _ <;> linarith
  have hWc' : ∀ e, (θb μin k x₀ < ρh μin k x₀ e ↔ θb μin k c' ≤ ρh μin k c' e) := by
    intro e
    rcases lt_trichotomy (θb μin k x₀ - ρh μin k x₀ e) 0 with h | h | h
    · have := ((sh e).1 h).2
      constructor <;> intro _ <;> linarith
    · exact absurd h (hZh e x₀ hx₀)
    · have := ((sh e).2 h).1 c' ⟨hcc, le_rfl⟩
      constructor <;> intro _ <;> linarith
  refine ⟨fun e he => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- "and `U ⊆ W` by `thm:splice`(a)"
    rw [mem_filter] at he ⊢
    exact ⟨he.1, he.2.trans_le (ρf_le_ρh k x₀ e)⟩
  · -- "in the interior it is the configuration": there `{ρ^h > θ_b} = {ρ^h ≥ θ_b}`
    refine isConfig_iff.2 fun e => ⟨?_, ?_⟩
    · rw [mem_filter, hUo e x ⟨hx.1.le, hx.2⟩]
      simp
    · rw [mem_filter, hWo e x ⟨hx.1.le, hx.2⟩]
      simp only [mem_univ, true_and]
      constructor
      · exact le_of_lt
      · intro h'
        rcases eq_or_lt_of_le h' with h'' | h''
        · exact absurd (by rw [h'']; ring) (hZh e x hx)
        · exact h''
  · -- (4) "So, at every point of `[c, c']`, the inequalities of a weak configuration hold for
    -- `(U, W)` by continuity, and `U` and `W` are upper level sets of `ρ^f` and of `ρ^h`. Hence
    -- `(U, W)` is a weak configuration at every point of `[c, c']`, …"
    rcases eq_or_lt_of_le hx.2 with hxc | hxc
    · subst hxc
      exact isWeakConfigT_of_levelSets
        (Or.inr fun e => by rw [mem_filter]; simp only [mem_univ, true_and]; exact hUc' e)
        (Or.inr fun e => by rw [mem_filter]; simp only [mem_univ, true_and]; exact hWc' e)
    · exact isWeakConfigT_of_levelSets
        (Or.inl fun e => by
          rw [mem_filter]; simp only [mem_univ, true_and]; exact hUo e x ⟨hx.1, hxc⟩)
        (Or.inl fun e => by
          rw [mem_filter]; simp only [mem_univ, true_and]; exact hWo e x ⟨hx.1, hxc⟩)

/-- Cutting an interval into pieces (not in the paper: the proof of `thm:transition` leaves
implicit that a function nondecreasing on each piece of a cut of `[a, b]` at finitely many points
is nondecreasing on `[a, b]`): if `φ` is nondecreasing on every `[c, c'] ⊆ [a, b]` with `c < c'`
whose interior contains no point of the finite set `Z`, then `φ` is nondecreasing on `[a, b]` (by
induction on the number of points of `Z` in `(a, b)`). -/
lemma monotoneOn_of_pieces (Z : Finset ℝ) {φ : ℝ → ℝ} {a b : ℝ}
    (h : ∀ c c', a ≤ c → c < c' → c' ≤ b → (∀ z ∈ Z, z ∉ Set.Ioo c c') →
      MonotoneOn φ (Set.Icc c c')) : MonotoneOn φ (Set.Icc a b) := by
  suffices H : ∀ n, ∀ a : ℝ, (Z.filter (· ∈ Set.Ioo a b)).card = n →
      (∀ c c', a ≤ c → c < c' → c' ≤ b → (∀ z ∈ Z, z ∉ Set.Ioo c c') →
        MonotoneOn φ (Set.Icc c c')) → MonotoneOn φ (Set.Icc a b) from H _ a rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn h
  rcases le_or_gt b a with hba | hab
  · intro x hx y hy hxy
    have : x = y := le_antisymm hxy (by linarith [hx.1, hy.2])
    rw [this]
  · by_cases hZ : ∀ z ∈ Z, z ∉ Set.Ioo a b
    · exact h a b le_rfl hab le_rfl hZ
    · push Not at hZ
      have hS : (Z.filter (· ∈ Set.Ioo a b)).Nonempty := by
        obtain ⟨z, hz, hz'⟩ := hZ
        exact ⟨z, mem_filter.2 ⟨hz, hz'⟩⟩
      set z₀ := (Z.filter (· ∈ Set.Ioo a b)).min' hS
      have hz₀ : z₀ ∈ Z.filter (· ∈ Set.Ioo a b) := min'_mem _ _
      have hz₀' := (mem_filter.1 hz₀).2
      have h1 : MonotoneOn φ (Set.Icc a z₀) := h a z₀ le_rfl hz₀'.1 hz₀'.2.le fun z hz hz' => by
        have : z₀ ≤ z := min'_le _ _ (mem_filter.2 ⟨hz, hz'.1, hz'.2.trans hz₀'.2⟩)
        exact absurd hz'.2 (not_lt.2 this)
      have hlt : (Z.filter (· ∈ Set.Ioo z₀ b)).card < n := by
        rw [← hn]
        refine card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
        · rw [mem_filter] at hz ⊢
          exact ⟨hz.1, hz₀'.1.trans hz.2.1, hz.2.2⟩
        · have := (mem_filter.1 (hsub hz₀)).2.1
          exact lt_irrefl _ this
      have h2 : MonotoneOn φ (Set.Icc z₀ b) := ih _ hlt z₀ rfl fun c c' hc hcc hc' hZ' =>
        h c c' (hz₀'.1.le.trans hc) hcc hc' hZ'
      rw [← Set.Icc_union_Icc_eq_Icc hz₀'.1.le hz₀'.2.le]
      exact h1.union_right h2 (isGreatest_Icc hz₀'.1.le) (isLeast_Icc hz₀'.2.le)

/-- The mirror image of `monotoneOn_of_pieces` (not in the paper, as there). -/
lemma antitoneOn_of_pieces (Z : Finset ℝ) {φ : ℝ → ℝ} {a b : ℝ}
    (h : ∀ c c', a ≤ c → c < c' → c' ≤ b → (∀ z ∈ Z, z ∉ Set.Ioo c c') →
      AntitoneOn φ (Set.Icc c c')) : AntitoneOn φ (Set.Icc a b) := by
  have := monotoneOn_of_pieces Z (φ := fun x => -φ x) fun c c' h1 h2 h3 h4 =>
    fun x hx y hy hxy => neg_le_neg (h c c' h1 h2 h3 h4 hx hy hxy)
  exact fun x hx y hy hxy => neg_le_neg_iff.1 (this hx hy hxy)

/-! ### `thm:transition` -/

/-- `lem:fullplane`(f) at the step (as used in the proof of `thm:transition`,
`stoc-sections/appD-hardness.tex:1087-1088`): `r(ξ^f(α)) = r(ξ^{(k)}(α)) + m_δ(F_{τ_1} + F_{τ_2})`,
as `ξ^f(α) = (ξ^{(k)}(α), F_{τ_1}, F_{τ_2})` (`StepData.xi_f_old`, `xi_f_τ₁`, `xi_f_τ₂`). -/
lemma reward_xi_f (k : ℕ) (α : ℝ) :
    reward ((stepD μin k).mf (mT μin k)) (xi ((stepD μin k).fStep (gT μin k))
        ((stepD μin k).mf (mT μin k)) ((stepD μin k).βf (βT μin k)) α) =
      curve (gT μin k) (mT μin k) (βT μin k) α + (stepD μin k).mδ *
        ((stepD μin k).Fτ₁ + (stepD μin k).Fτ₂) := by
  have H := stepD_hyp (μin := μin) k
  unfold reward
  rw [StepData.sum_E]
  simp only [StepData.mf_none, StepData.mf_τ₁, StepData.mf_old, StepData.xi_f_τ₂ H,
    StepData.xi_f_τ₁ H, StepData.xi_f_old H, curve]
  ring

/-- `thm:transition` under the weaker hypothesis `μ^in_1 > 0` instead of `μ^in ∈ 𝔉` of length at
least `k + 2`, which is what the proofs below use (`stoc-sections/appD-hardness.tex:1050-1064`,
proof lines 1066-1156): let `k ≥ 0` and `e_t, e_l ∈ E_k`; assume the hypotheses of
`lem:onelevel` at the steps `0 → 1, …, k → k + 1` and (T1)–(T3) (`TransitionHyp`). Then the gap
`L_{k+1}(α) − r(ξ^{(k+1)}(α))` of level `k + 1` is at least `ε_0` for every `α` in the transition
`[R_1, R_0 + μ]`.

The proof's steps: (1) the pieces (`transition_piece`), and on every piece the increment
(`eq:D-increment`) of `lem:windows`(c), whose second bracket is nonnegative and whose first lies in
`[0, r(ξ^{(k)}(a')) − r(ξ^{(k)}(a))] ⊆ [0, q_k(a' − a)]` by `lem:fullplane`(f) (`reward_xi_f`) and
`lem:twosides`(a); (2) by `lem:onelevel`(a), (W1) and (W2), `ρ^f_{τ_1} < θ_b` at `R_1` and
`θ_b < ρ^h_{τ_2}` at `R_0 + μ`, so `ρ^f_{τ_1} < θ_b < ρ^h_{τ_2}` on the whole transition; (3) by
(W4) and (T2), `θ_b ≥ ρ^h_{e_l} ≥ ρ^h_{e_t} ≥ ρ^f_{e_t}` at `R_0 + μ`, while
`θ_b < ρ^f_{e_t} ≤ ρ^h_{e_l}` at `R_1`; the zeros `α̌` of `θ_b − ρ^f_{e_t}` and `α̂` of
`θ_b − ρ^h_{e_l}` exist by continuity, and `α̌ < α̂`; (4) "We first show that the gap of level
`k + 1` is nondecreasing on `[R_1, α̌]`, before `e_t` arrives in the block of `b`": there, `e_t` and
`τ_2` lie in `U`, only `τ_1` can lie outside `W`, and as `ξ^h_{τ_1}` is constant, the second bracket
vanishes; the block is `{b, τ_1}` or lies in `(E_k ∖ {e_t}) ∪ {b}`, so `SSq(D) ≤ ψ_{k+1}` and the
gap is nondecreasing; (5) "Next we show that the gap is nonincreasing on `[α̌, α̂]`, from the
arrival of `e_t` in the block until `e_l` leaves it": `e_t`, or `τ_2` and `e_l ≠ e_t`, are in the
block, so `SSq(D) ≥ q_{k+1}` and the gap is nonincreasing; (6) "Finally, we show that the gap is at
least `ε_0` on `[α̂, R_0 + μ]`, where `b` has passed every old element": `(∅, {τ_2})` is a weak
configuration there, the gap is `L_k(α − μ) − r(ξ^{(k)}(α − μ))` (as in the proof of
`lem:onelevel`(b), by `lem:dmt`(b), (c)), `θ_b = θ_2` (`lem:windows`(a)), and (T3) gives
`α̂ ≥ R_0 + μ − ι`, so `lem:twosides`(b) gives the gap `ζ_1 − (α − μ) ≥ ζ_1 − R_0 = ε_0`; (7) so the
gap is at least its value `7ε_0` at `R_1` on `[R_1, α̌]`, at least its value at `α̂` on `[α̌, α̂]`,
and at least `ε_0` on `[α̂, R_0 + μ]`; as `7ε_0 > ε_0` and the gap at `α̂` is at least `ε_0`, it is
at least `ε_0` on the whole transition. -/
theorem transition_aux (h0 : 0 < μin 0) {k : ℕ} {et el : Gr k}
    (hyp : ∀ i ≤ k, OneLevelHyp μin i) (hT : TransitionHyp μin k et el) :
    ∀ α ∈ Set.Icc (R1T μin k) (R0 + μT μin (k + 1)), ε₀ ≤ gapT μin (k + 1) α := by
  intro α hα
  have h := hyp k le_rfl
  have hμ := h.μ_pos
  have H := stepD_hyp (μin := μin) k
  have hβ := (fpHyp_gT (μin := μin) (k + 1)).pos
  have hfast := fast_aux k h.W6
  have hs := s_pos (μin := μin) k
  have hR0R1 := R0_lt_R1T (μin := μin) k
  set R1 := R1T μin k with hR1def
  set μ := μT μin (k + 1) with hμdef
  have hR : R1 ≤ R0 + μ := hα.1.trans hα.2
  have hT2 := hT.T2
  -- `lem:twosides` at level `k`
  obtain ⟨⟨-, hval, hinc⟩, hleft⟩ := twosides_aux h0 k fun i hi => hyp i hi.le
  -- the gap of level `k + 1` changes by `q_{k+1}(a' − a)` minus the change of the reward
  have hq : (lvl μin (k + 1)).q = (lvl μin k).q + (lvl μin k).ψ := q_succ k
  -- (1) "We cut the transition at these finitely many zeros into pieces. … By `lem:windows`(c),
  -- with `D = (W ∖ U) ∪ {b}`, the increment `r(ξ^{(k+1)}(a')) − r(ξ^{(k+1)}(a))` over every
  -- interval `[a, a'] ⊆ [c, c']` is
  -- `[∑_{e∈U} m_eξ^f_e]_a^{a'} + [∑_{e∈E∖W} m_eξ^h_e]_a^{a'} + (a' − a)SSq(D)` (`eq:D-increment`).
  -- Here the second bracket is nonnegative, and the first lies in
  -- `[0, r(ξ^{(k)}(a')) − r(ξ^{(k)}(a))] ⊆ [0, q_k(a' − a)]`, by `lem:fullplane`(f), which gives
  -- `r(ξ^f(α)) = r(ξ^{(k)}(α)) + m_δ(F_{τ_1} + F_{τ_2})`, and by `lem:twosides`(a), as `a ≥ R_1`."
  have hincr : ∀ c c', c < c' → (∀ z ∈ cuts μin k, z ∉ Set.Ioo c c') → ∀ a a', c ≤ a → a ≤ a' →
      a' ≤ c' →
      ∃ B₁ B₂ : ℝ, curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) a' -
          curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) a =
          B₁ + B₂ + (a' - a) * SS (mT μin (k + 1)) (βT μin (k + 1))
            (insertNone ((univ.filter fun e =>
                θb μin k ((c + c') / 2) < ρh μin k ((c + c') / 2) e) \
              univ.filter fun e => θb μin k ((c + c') / 2) < ρf μin k ((c + c') / 2) e)) ∧
        0 ≤ B₁ ∧ (R1 ≤ a → B₁ ≤ (lvl μin k).q * (a' - a)) ∧ 0 ≤ B₂ ∧
        B₂ = ∑ e ∈ (univ.filter fun e => θb μin k ((c + c') / 2) < ρh μin k ((c + c') / 2) e)ᶜ,
            mT μin (k + 1) (some e) * xi ((stepD μin k).hStep (gT μin k) (mT μin k) (βT μin k))
              ((stepD μin k).mf (mT μin k)) ((stepD μin k).βf (βT μin k)) a' e -
          ∑ e ∈ (univ.filter fun e => θb μin k ((c + c') / 2) < ρh μin k ((c + c') / 2) e)ᶜ,
            mT μin (k + 1) (some e) * xi ((stepD μin k).hStep (gT μin k) (mT μin k) (βT μin k))
              ((stepD μin k).mf (mT μin k)) ((stepD μin k).βf (βT μin k)) a e := by
    intro c c' hcc hZ a a' hca haa hac'
    obtain ⟨hUW, -, hweak⟩ := transition_piece h.W6 hcc hZ
    obtain ⟨hr, ⟨hB1, hB1'⟩, ⟨hB2, -⟩⟩ := windows_c (K := (stepD μin k).K)
      (stepD_hyp k).fHyp.submod (stepD_hyp k).fHyp.empty (mT_pos (μin := μin) (k + 1)) hβ
      (stepD_hyp k).d_nonneg hUW haa (hweak a ⟨hca, haa.trans hac'⟩)
      (hweak a' ⟨hca.trans haa, hac'⟩)
    refine ⟨_, _, hr, hB1, fun ha => ?_, hB2, rfl⟩
    -- the first bracket: `lem:fullplane`(f) and `lem:twosides`(a)
    have e1 := reward_xi_f (μin := μin) k a
    have e2 := reward_xi_f (μin := μin) k a'
    have := hinc a a' ha haa
    have hB1'' := hB1'
    change _ ≤ reward ((stepD μin k).mf (mT μin k)) (xi ((stepD μin k).fStep (gT μin k))
      ((stepD μin k).mf (mT μin k)) ((stepD μin k).βf (βT μin k)) a') -
        reward ((stepD μin k).mf (mT μin k)) (xi ((stepD μin k).fStep (gT μin k))
          ((stepD μin k).mf (mT μin k)) ((stepD μin k).βf (βT μin k)) a) at hB1''
    linarith
  -- (2) "By `lem:onelevel`(a), (W1) and (W2), `ρ^f_{τ_1} < θ_b` at `R_1` and `θ_b < ρ^h_{τ_2}` at
  -- `R_0 + μ`. As the differences increase, `ρ^f_{τ_1} < θ_b < ρ^h_{τ_2}` on the whole transition."
  obtain ⟨hατ₂, ha1, ha2, -⟩ := onelevel_a_aux h
  have hR1R : R1 ∈ Set.Icc R0 R1 := ⟨hR0R1.le, le_rfl⟩
  have hRμ : R0 + μ ∈ Set.Icc (R0 + μ) (ατ₂ μin k) := ⟨le_rfl, by linarith⟩
  have hτ₁_R1 : ρf μin k R1 (some none) < θb μin k R1 := by
    rw [(ha1 R1 hR1R).2]
    have h1 := u1_slope (μin := μin) k R0 R1
    have h2 := mul_nonneg hs.le (sub_nonneg.2 hR0R1.le)
    have h3 := mul_pos hs (show (0 : ℝ) < ι by unfold ι; norm_num)
    have := h.W1a
    unfold u1 at *
    linarith
  have hτ₂_R : θb μin k (R0 + μ) < ρh μin k (R0 + μ) none := by
    rw [(ha2 (R0 + μ) hRμ).2, (D_bands (μin := μin) k _).2.2.2.2.2]
    have h1 := u2_slope (μin := μin) k (R0 + μ) (R1 + μ)
    have h2 := mul_nonneg hs.le (show 0 ≤ R1 + μ - (R0 + μ) by linarith)
    have := h.W2b
    unfold u2 at *
    linarith
  have hτ₁τ₂ : ∀ x ∈ Set.Icc R1 (R0 + μ),
      ρf μin k x (some none) < θb μin k x ∧ θb μin k x < ρh μin k x none := by
    intro x hx
    constructor
    · rcases eq_or_lt_of_le hx.1 with hxe | hxe
      · rw [← hxe]
        exact hτ₁_R1
      · have := (hfast.2 (some none)).2.1 hxe
        simp only at this
        linarith
    · rcases eq_or_lt_of_le hx.2 with hxe | hxe
      · rw [hxe]
        exact hτ₂_R
      · have := (hfast.2 none).2.2.2 hxe
        simp only at this
        linarith
  -- (3) "By (W4) and (T2), `θ_b ≥ ρ^h_{e_l} ≥ ρ^h_{e_t} ≥ ρ^f_{e_t}` at `R_0 + μ`, where
  -- `θ_b = θ_2`, while `θ_b < ρ^f_{e_t} ≤ ρ^h_{e_l}` at `R_1`, where the configuration is
  -- `(E ∖ {τ_1}, E)`. Let `α̌` and `α̂` be the zeros of `θ_b − ρ^f_{e_t}` and of `θ_b − ρ^h_{e_l}`
  -- in the transition, which exist by continuity. Then `α̌ < α̂`, as `θ_b = ρ^h_{e_l} > ρ^f_{e_t}`
  -- at `α̂` by (T2)."
  have hRtr : R0 + μ ∈ Set.Icc R1 (R0 + μ) := ⟨hR, le_rfl⟩
  have hR1tr : R1 ∈ Set.Icc R1 (R0 + μ) := ⟨le_rfl, hR⟩
  have hlR : ρh μin k (R0 + μ) (some (some el)) < θb μin k (R0 + μ) := by
    rw [(ha2 (R0 + μ) hRμ).2]
    exact h.W4 el (R0 + μ) ⟨le_rfl, by linarith⟩
  have htR : ρf μin k (R0 + μ) (some (some et)) ≤ θb μin k (R0 + μ) := by
    -- (T2) with `e = e' = e_t`: `ρ^f_{e_t} < ρ^f_{τ_2} < ρ^h_{e_t} ≤ ρ^h_{e_l}`
    obtain ⟨-, h2, h3, h4⟩ := hT2 (R0 + μ) hRtr et et
    exact ((h2.trans h3).le.trans h4).trans hlR.le
  have ht1 : θb μin k R1 < ρf μin k R1 (some (some et)) := by
    have := ((isConfig_iff.1 (ha1 R1 hR1R).1) (some (some et))).1.1
    exact this (mem_erase.2 ⟨by simp, mem_univ _⟩)
  have hl1 : θb μin k R1 < ρh μin k R1 (some (some el)) := by
    obtain ⟨-, h2, h3, -⟩ := hT2 R1 hR1tr et el
    linarith
  obtain ⟨αc, hαc, hαc0⟩ := intermediate_value_Icc hR (hfast.2 (some (some et))).1.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (θb μin k R1 - ρf μin k R1 (some (some et)))
      (θb μin k (R0 + μ) - ρf μin k (R0 + μ) (some (some et))) from
      ⟨by linarith, by linarith⟩)
  obtain ⟨αh, hαh, hαh0⟩ := intermediate_value_Icc hR (hfast.2 (some (some el))).2.2.1.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (θb μin k R1 - ρh μin k R1 (some (some el)))
      (θb μin k (R0 + μ) - ρh μin k (R0 + μ) (some (some el))) from
      ⟨by linarith, by linarith⟩)
  have hαc0' : θb μin k αc = ρf μin k αc (some (some et)) := sub_eq_zero.1 hαc0
  have hαh0' : θb μin k αh = ρh μin k αh (some (some el)) := sub_eq_zero.1 hαh0
  have hlt : αc < αh := by
    have hgt : ρf μin k αh (some (some et)) < θb μin k αh := by
      obtain ⟨-, h2, h3, -⟩ := hT2 αh hαh et el
      linarith
    by_contra hcon
    have := (hfast.2 (some (some et))).2.1.monotone (not_lt.1 hcon)
    linarith
  -- (4) "We first show that the gap of level `k + 1` is nondecreasing on `[R_1, α̌]`, before `e_t`
  -- arrives in the block of `b`." (The paragraph's other sentences are quoted below, where the
  -- Lean proves them.)
  have hmono : MonotoneOn (gapT μin (k + 1)) (Set.Icc R1 αc) := by
    refine monotoneOn_of_pieces (cuts μin k) fun c c' hc hcc hc' hZ => ?_
    intro a ha a' ha' haa
    obtain ⟨B₁, B₂, hr, -, hB1', -, hB2eq⟩ := hincr c c' hcc hZ a a' ha.1 haa ha'.2
    set x₀ := (c + c') / 2
    set U := univ.filter fun e => θb μin k x₀ < ρf μin k x₀ e with hUdef
    set W := univ.filter fun e => θb μin k x₀ < ρh μin k x₀ e with hWdef
    have hx₀ : x₀ ∈ Set.Icc R1 (R0 + μ) := ⟨by simp only [x₀]; linarith,
      by simp only [x₀]; linarith [hαc.2]⟩
    have hx₀c : x₀ < αc := by simp only [x₀]; linarith
    have hT2x := hT2 x₀ hx₀
    -- "In the interior of each piece, `θ_b < ρ^f_{e_t} < ρ^f_{τ_2}`, so `e_t` and `τ_2` lie in `U`,
    -- above the block of `b`."
    have het : θb μin k x₀ < ρf μin k x₀ (some (some et)) := by
      have := (hfast.2 (some (some et))).2.1 hx₀c
      simp only at this
      linarith
    have hτ₂U : θb μin k x₀ < ρf μin k x₀ none := het.trans (hT2x et et).2.1
    -- "Moreover, `ρ^h_e > ρ^f_{τ_2} > θ_b` for every old element `e ∈ E_k`, so only `τ_1` can lie
    -- outside `W`."
    have hWτ₁ : ∀ e ∉ W, e = some none := by
      intro e he
      rcases e with _ | _ | c
      · exact absurd (by rw [hWdef, mem_filter]; exact ⟨mem_univ _,
          hτ₂U.trans_le (ρf_le_ρh k x₀ none)⟩) he
      · rfl
      · exact absurd (by rw [hWdef, mem_filter]; exact ⟨mem_univ _,
          hτ₂U.trans (hT2x c c).2.2.1⟩) he
    -- "As `ξ^h_{τ_1}` is constant, the second bracket of (`eq:D-increment`) vanishes."
    have hB2 : B₂ = 0 := by
      rw [hB2eq]
      refine sub_eq_zero.2 (sum_congr rfl fun e he => ?_)
      rw [hWτ₁ e (mem_compl.1 he)]
      have h1 := StepData.xi_h H a (some none)
      have h2 := StepData.xi_h H a' (some none)
      rw [StepData.xi_f_τ₁ H] at h1 h2
      rw [h1, h2]
    -- "If `τ_1` is in the block, no old element `e` is, since `ρ^f_e > ρ^h_{τ_1} ≥ θ_b`. So the
    -- block is `{b, τ_1}` or lies in `(E_k ∖ {e_t}) ∪ {b}`, and `SSq(D) ≤ ψ_{k+1}`, as
    -- `SSq({b, τ_1}) = ψ_{k+1}`, by (T1) and the monotonicity of `SSq`."
    have hSS : SS (mT μin (k + 1)) (βT μin (k + 1)) (insertNone (W \ U)) ≤ (lvl μin k).ψ := by
      by_cases hτ₁ : some none ∈ W \ U
      · have hτ₁W : θb μin k x₀ < ρh μin k x₀ (some none) := (mem_filter.1 (mem_sdiff.1 hτ₁).1).2
        have hWU : W \ U = {some none} := by
          ext e
          constructor
          · intro he
            rw [mem_sdiff, hWdef, hUdef, mem_filter, mem_filter] at he
            rcases e with _ | _ | c
            · exact absurd ⟨mem_univ _, hτ₂U⟩ he.2
            · exact mem_singleton_self _
            · exact absurd ⟨mem_univ _, hτ₁W.trans (hT2x c c).1⟩ he.2
          · intro he
            rw [mem_singleton.1 he]
            exact hτ₁
        have hD : insertNone (W \ U) =
            ({none, some (some none)} : Finset (Option (Option (Option (Gr k))))) := by
          rw [hWU]
          ext o
          rcases o with _ | _ | _ | c <;> simp [mem_insertNone]
        rw [hD]
        exact ((StepData.SS_block_τ₁ H).trans (stepD_ψ k)).le
      · refine (SS_mono hβ fun o ho => ?_).trans hT.T1a
        rcases o with _ | e
        · exact mem_insert_self _ _
        · have ho' := some_mem_insertNone.1 ho
          refine mem_insert_of_mem (mem_image.2 ?_)
          rcases e with _ | _ | c
          · exact absurd (by rw [hUdef, mem_filter]; exact ⟨mem_univ _, hτ₂U⟩)
              (mem_sdiff.1 ho').2
          · exact absurd ho' hτ₁
          · refine ⟨c, mem_erase.2 ⟨fun hc => ?_, mem_univ c⟩, rfl⟩
            subst hc
            exact (mem_sdiff.1 ho').2 (mem_filter.2 ⟨mem_univ _, het⟩)
    -- "Hence, by (`eq:D-increment`), the reward `r(ξ^{(k+1)}(α))` grows by at most
    -- `(q_k + ψ_{k+1})(a' − a) = q_{k+1}(a' − a)` on every interval `[a, a']` in a piece, and the
    -- gap of level `k + 1` is nondecreasing on `[R_1, α̌]`."
    have hr' : curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) a' -
        curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) a ≤
          (lvl μin (k + 1)).q * (a' - a) := by
      rw [hr, hB2, hq]
      have := hB1' (hc.trans ha.1)
      have := mul_le_mul_of_nonneg_left hSS (sub_nonneg.2 haa)
      nlinarith
    have := gapT_sub (μin := μin) (k + 1) a a'
    linarith
  -- (5) "Next we show that the gap is nonincreasing on `[α̌, α̂]`, from the arrival of `e_t` in the
  -- block until `e_l` leaves it. In the interior of each piece, `ρ^f_{e_t} < θ_b < ρ^h_{e_l}`. If
  -- `θ_b < ρ^h_{e_t}` there, then `e_t` is in the block. Otherwise
  -- `ρ^f_{e_l} < ρ^f_{τ_2} < ρ^h_{e_t} < θ_b < ρ^h_{e_l}` and `θ_b < ρ^h_{τ_2}`, so `τ_2` and
  -- `e_l ≠ e_t` are in the block. By (T1) and the monotonicity of `SSq`, `SSq(D) ≥ q_{k+1}` in both
  -- cases. So, by (`eq:D-increment`), whose two brackets are nonnegative, the reward
  -- `r(ξ^{(k+1)}(α))` grows by at least `q_{k+1}(a' − a)` on every interval `[a, a']` in a piece,
  -- and the gap of level `k + 1` is nonincreasing on `[α̌, α̂]`."
  have hanti : AntitoneOn (gapT μin (k + 1)) (Set.Icc αc αh) := by
    refine antitoneOn_of_pieces (cuts μin k) fun c c' hc hcc hc' hZ => ?_
    intro a ha a' ha' haa
    obtain ⟨B₁, B₂, hr, hB1, -, hB2, -⟩ := hincr c c' hcc hZ a a' ha.1 haa ha'.2
    set x₀ := (c + c') / 2
    set U := univ.filter fun e => θb μin k x₀ < ρf μin k x₀ e with hUdef
    set W := univ.filter fun e => θb μin k x₀ < ρh μin k x₀ e with hWdef
    have hx₀ : x₀ ∈ Set.Icc R1 (R0 + μ) := ⟨by simp only [x₀]; linarith [hαc.1],
      by simp only [x₀]; linarith [hαh.2]⟩
    have hx₀int : x₀ ∈ Set.Ioo c c' := ⟨by simp only [x₀]; linarith, by simp only [x₀]; linarith⟩
    have hT2x := hT2 x₀ hx₀
    have het : ρf μin k x₀ (some (some et)) < θb μin k x₀ := by
      have := (hfast.2 (some (some et))).2.1 (show αc < x₀ by simp only [x₀]; linarith)
      simp only at this
      linarith
    have hel : θb μin k x₀ < ρh μin k x₀ (some (some el)) := by
      have := (hfast.2 (some (some el))).2.2.2 (show x₀ < αh by simp only [x₀]; linarith)
      simp only at this
      linarith
    have hSS : (lvl μin (k + 1)).q ≤
        SS (mT μin (k + 1)) (βT μin (k + 1)) (insertNone (W \ U)) := by
      by_cases ht : θb μin k x₀ < ρh μin k x₀ (some (some et))
      · -- "If `θ_b < ρ^h_{e_t}` there, then `e_t` is in the block."
        have hetD : some (some (some et)) ∈ insertNone (W \ U) :=
          some_mem_insertNone.2 (mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, ht⟩,
            fun h' => absurd (mem_filter.1 h').2 (not_lt.2 het.le)⟩)
        exact hT.T1b.trans (SS_mono hβ (insert_subset none_mem_insertNone
          (singleton_subset_iff.2 hetD)))
      · -- "Otherwise `ρ^f_{e_l} < ρ^f_{τ_2} < ρ^h_{e_t} < θ_b < ρ^h_{e_l}` and `θ_b < ρ^h_{τ_2}`,
        -- so `τ_2` and `e_l ≠ e_t` are in the block."
        push Not at ht
        have ht' : ρh μin k x₀ (some (some et)) < θb μin k x₀ := by
          rcases eq_or_lt_of_le ht with ht'' | ht''
          · exact absurd hx₀int (hZ x₀ (mem_cuts_h h.W6 ht''.symm))
          · exact ht''
        have hne : el ≠ et := by
          rintro rfl
          linarith
        have hτ₂D : ρf μin k x₀ none < θb μin k x₀ := (hT2x et et).2.2.1.trans ht'
        have hτ₂ : some none ∈ insertNone (W \ U) :=
          some_mem_insertNone.2 (mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, (hτ₁τ₂ x₀ hx₀).2⟩,
            fun h' => absurd (mem_filter.1 h').2 (not_lt.2 hτ₂D.le)⟩)
        have hl : some (some (some el)) ∈ insertNone (W \ U) :=
          some_mem_insertNone.2 (mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, hel⟩,
            fun h' => absurd (mem_filter.1 h').2
              (not_lt.2 ((hT2x el el).2.1.trans hτ₂D).le)⟩)
        exact (hT.T1c hne).trans (SS_mono hβ (insert_subset none_mem_insertNone
          (insert_subset hτ₂ (singleton_subset_iff.2 hl))))
    have hr' : (lvl μin (k + 1)).q * (a' - a) ≤
        curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) a' -
          curve (gT μin (k + 1)) (mT μin (k + 1)) (βT μin (k + 1)) a := by
      rw [hr]
      have := mul_le_mul_of_nonneg_left hSS (sub_nonneg.2 haa)
      nlinarith
    have := gapT_sub (μin := μin) (k + 1) a a'
    linarith
  -- (6) "Finally, we show that the gap is at least `ε_0` on `[α̂, R_0 + μ]`, where `b` has passed
  -- every old element. Here every old element `e ∈ E_k` satisfies
  -- `θ_b ≥ ρ^h_{e_l} ≥ ρ^h_e > ρ^f_e > ρ^h_{τ_1}`, and `ρ^f_{τ_2} < ρ^h_{e_l} ≤ θ_b < ρ^h_{τ_2}`.
  -- So `{τ_2} = {e ∈ E : ρ^h_e > θ_b}`, and `(∅, {τ_2})` is a weak configuration. As in the proof
  -- of `lem:onelevel`(b), `lem:dmt`(b) and (c) then show that the gap of level `k + 1` at `α` is
  -- `L_k(α − μ) − r(ξ^{(k)}(α − μ))`. By `lem:windows`(a), `θ_b = θ_2` there, so `θ_2 = ρ^h_{e_l}`
  -- at `α̂`. As `θ_2 − ρ^h_{e_l}` increases (`θ_2` has slope `m̄ > M`), (T3) gives
  -- `α̂ ≥ R_0 + μ − ι`. So `α − μ ∈ [R_0 − ι, R_0]`, and `lem:twosides`(b) gives
  -- `L_{k+1}(α) − r(ξ^{(k+1)}(α)) = ζ_1 − (α − μ) ≥ ζ_1 − R_0 = ε_0`."
  have hconf6 : ∀ x ∈ Set.Icc αh (R0 + μ), IsWeakConfigT μin k x ∅ {none} ∧
      gapT μin (k + 1) x = gapT μin k (x - μ) ∧ θb μin k x = θ2 μin k x := by
    intro x hx
    have hxtr : x ∈ Set.Icc R1 (R0 + μ) := ⟨hαh.1.trans hx.1, hx.2⟩
    have hT2x := hT2 x hxtr
    have hlx : ρh μin k x (some (some el)) ≤ θb μin k x := by
      rcases eq_or_lt_of_le hx.1 with hxe | hxe
      · rw [← hxe, hαh0']
      · have := (hfast.2 (some (some el))).2.2.2 hxe
        simp only at this
        linarith
    have hold : ∀ c, ρf μin k x (some (some c)) < θb μin k x ∧
        ρh μin k x (some (some c)) ≤ θb μin k x := fun c =>
      ⟨((hT2x c c).2.1.trans (hT2x c c).2.2.1).trans_le ((hT2x c c).2.2.2.trans hlx),
        (hT2x c c).2.2.2.trans hlx⟩
    have hτ₁x : ρh μin k x (some none) < θb μin k x := (hT2x el el).1.trans (hold el).1
    have hτ₂x : ρf μin k x none < θb μin k x := (hT2x el el).2.2.1.trans_le hlx
    have hw : IsWeakConfigT μin k x ∅ {none} := by
      refine isWeakConfigT_of_levelSets (Or.inl fun e => ?_) (Or.inl fun e => ?_)
      · simp only [notMem_empty, false_iff, not_lt]
        rcases e with _ | _ | c
        · exact hτ₂x.le
        · exact (ρf_le_ρh k x _).trans hτ₁x.le
        · exact (hold c).1.le
      · rcases e with _ | _ | c
        · simp only [mem_singleton, true_iff]
          exact (hτ₁τ₂ x hxtr).2
        · simp only [mem_singleton, reduceCtorEq, false_iff, not_lt]
          exact hτ₁x.le
        · simp only [mem_singleton, reduceCtorEq, false_iff, not_lt]
          exact (hold c).2
    refine ⟨hw, gapT_config_τ₂ k hμ hw, ?_⟩
    have hθ := (windows_a (K := (stepD μin k).K) (stepD_hyp k).fHyp.submod
      (stepD_hyp k).fHyp.empty (mT_pos (μin := μin) (k + 1)) hβ (stepD_hyp k).d_nonneg
      (empty_subset _) hw).1
    rw [θ2_θUW]
    exact hθ
  have hαhι : R0 + μ - ι ≤ αh := by
    by_contra hcon
    push Not at hcon
    have h2 : θ2 μin k αh = ρh μin k αh (some (some el)) := by
      rw [← (hconf6 αh ⟨le_rfl, hαh.2⟩).2.2, hαh0']
    -- `θ_2 − ρ^h_{e_l}` increases, as `θ_2` has slope `m̄ > M`
    have hm := hfast.1
    have h3 : θ2 μin k (R0 + μ - ι) = θ2 μin k αh + (R0 + μ - ι - αh) * (lvl μin k).mbar := by
      rw [θ2_eq, θ2_eq]
      ring
    have h4 := (ρh_rate (μin := μin) k (some (some el))).2 αh (R0 + μ - ι - αh)
      (by linarith)
    simp only [add_sub_cancel] at h4
    have h5 := mul_lt_mul_of_pos_left hm (show 0 < R0 + μ - ι - αh by linarith)
    have := hT.T3
    linarith
  have hright : ∀ x ∈ Set.Icc αh (R0 + μ), ε₀ ≤ gapT μin (k + 1) x := by
    intro x hx
    rw [(hconf6 x hx).2.1, hleft (x - μ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    have : R0 = ζ₁ - ε₀ := rfl
    linarith [hx.2]
  -- (7) "So, on `[R_1, α̌]`, the gap of level `k + 1` is at least its value
  -- `L_k(R_1) − r(ξ^{(k)}(R_1)) = 7ε_0` at `R_1`, by `lem:onelevel`(b) and `lem:twosides`(a). On
  -- `[α̌, α̂]`, it is at least its value at `α̂`, and on `[α̂, R_0 + μ]`, it is at least `ε_0`."
  have hR1val : gapT μin (k + 1) R1 = 7 * ε₀ := by
    rw [(onelevel_b_aux h).1 R1 hR1R, hval]
  -- "As `7ε_0 > ε_0` and the gap at `α̂` is at least `ε_0`, the gap of level `k + 1` is at least
  -- `ε_0` on the whole transition."
  have h7 : ε₀ < 7 * ε₀ := by norm_num
  have hαhval := hright αh ⟨le_rfl, hαh.2⟩
  rcases le_or_gt α αc with h1 | h1
  · have := hmono (a := R1) (b := α) ⟨le_rfl, hαc.1⟩ ⟨hα.1, h1⟩ hα.1
    linarith
  · rcases le_or_gt α αh with h2 | h2
    · have := hanti (a := α) (b := αh) ⟨h1.le, h2⟩ ⟨hlt.le, le_rfl⟩ h2
      linarith
    · exact hright α ⟨h2.le, hα.2⟩

/-- **`thm:transition`** (Theorem C.18, `stoc-sections/appD-hardness.tex:1050-1064`, proof lines
1066-1156): let `μ^in ∈ 𝔉` have length at least `k + 2` (`def:tower`), let `k ≥ 0` and
`e_t, e_l ∈ E_k`, and assume the hypotheses of `lem:onelevel` at the steps `0 → 1, …, k → k + 1` and
(T1)–(T3) (`TransitionHyp`). Then the gap `L_{k+1}(α) − r(ξ^{(k+1)}(α))` of level `k + 1` is at
least `ε_0` for every `α` in the transition `[R_1, R_0 + μ]`. The proof (steps (1)–(7)) is that of
`transition_aux`, with `μ^in_1 > 0` as `μ^in ∈ 𝔉`; the length is not used. -/
theorem transition {K : ℕ} (hF : InF μin K) {k : ℕ} (_hK : k + 2 ≤ K) {et el : Gr k}
    (hyp : ∀ i ≤ k, OneLevelHyp μin i) (hT : TransitionHyp μin k et el) :
    ∀ α ∈ Set.Icc (R1T μin k) (R0 + μT μin (k + 1)), ε₀ ≤ gapT μin (k + 1) α :=
  transition_aux (μin0_pos hF) hyp hT

end Tower

end

end Hardness

end Stoc
