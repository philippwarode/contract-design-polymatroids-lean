-- stamp r5 2026-11-02
import Stoc.Hardness.Sizes
import Stoc.Hardness.Gadget

/-!
# The sizes of the comb gadget: the last part of the proof of `thm:gadget`

The STOC version's `thm:gadget` (Appendix C.3, `stoc-sections/appD-hardness.tex:193-199`) ends with
"All numbers computed have `O(k + log μ^in_k + log N)` bits." (line 198), and the last paragraph of
its proof (Appendix C.7, lines 1750-1783) shows it: "Finally, we show that the output lies in
`𝒞_cut`, that its numbers have polynomial size and that it is computed in polynomial time."
`Stoc/Hardness/Gadget.lean` proves the first part of that paragraph (the output lies in `𝒞_cut`,
with a cut form that exists); this file proves the rest, in the paper's order:

* the cut form, "computed along the construction": `formT` (the form of `g_j`, by `prop:base` and
  `lem:cutforms`(c), with `formT_fn`) and `gadgetForm` (the form of the output `I(μ^in, N)`, with
  `gadgetForm_fn`);
* the magnitudes: `|Θ| ≤ M_{k−1} + 4 max_S |g(S)|`, `Λ ≤ 12ϖ_{k−1}|Θ| + 2 max_S |g(S)|` and
  `Λ' ≤ δN` (`gΘ_le`, `gΛ_le`, `gΛ'_le`), so `N_min` has `O(k + log μ^in_k)` bits
  (`gNmin_le`);
* the denominators: `ζ_1 = 1/3`, the rewards are integers, `β_e ∈ (1/(9·8^k))ℤ`, so
  `Θ ∈ (1/(9·8^k𝔇_{k−1}))ℤ` (`gΘ_inZ`), `2t_e ∈ ℤ`, `1/β_e ∈ (1/4)ℤ`, `Λ' ∈ (δ/3)ℤ` and
  `κ ∈ (1/10)ℤ` (`gadget_items`);
* "The numbers of the output are …. Apart from `β_{e_g}`, each of them is a sum of `O(|E|)`
  products of at most three of the numbers …. So their denominators divide a common integer
  with `O(k + log μ^in_k + log N)` bits, and so do their magnitudes. Hence every number of the
  output, `β_{e_g}` included, has `O(k + log μ^in_k + log N)` bits": `GadgetNumber` lists the
  numbers, `𝔇g` is the common integer, and `gadget_sizes` is the conclusion, with the explicit
  bound `2^B`, `B = 300(k + ⌊log₂ μ^in_k⌋ + ⌊log₂ N⌋ + 1)` (`Bits`);
* "The values `g(E)`, `g(E ∖ {e})` and `g({e})` needed for `Θ` and `Λ` are `2|E| + 1` evaluations
  of `g`": `gadget_evals` (`Θ` and `Λ` depend on `g` only through these values).

Not formalised: "So the algorithm runs in polynomial time", a statement about Turing machines,
which are not formalised; arithmetic operations are not counted in this library.

Indices as in `Stoc/Hardness/Tower.lean` and `Stoc/Hardness/Sizes.lean`: `μin i` is `μ^in_{i+1}`,
`g = g_{k−1}` on `E = E_{k−1} = Gr (k − 1)`, `ϖ_{k−1}` is `ϖ μin (k − 1)`, and
`L = ⌊log₂ μ^in_k⌋` is `Nat.log 2 (μin (k − 1))`.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-! ### The operations on cut forms keep the numbers (not in the paper) -/

namespace CutForm

section

variable {E : Type*} [DecidableEq E]

omit [DecidableEq E] in
/-- The arcs of `F.addNode F_b` are those of `F`, with their capacities (not in the paper: the
form of `lem:cutforms`(c)(ii) adds no arc). -/
lemma addNode_cap (F : CutForm E) (Fb : ℝ) {a : Option E × Option E}
    (ha : a ∈ (F.addNode Fb).D) : ∃ a' ∈ F.D, (F.addNode Fb).cap a = F.cap a' := by
  obtain ⟨u, v, h, rfl⟩ := mem_someArcs.1 ha
  exact ⟨(u, v), h, rfl⟩

end

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The arcs of `F.extendForm hd K` are those of `F`, with their capacities, and the arcs `b → e`
of capacity `d_e` (not in the paper: the form of `lem:cutforms`(c)(iii)). -/
lemma extendForm_cap (F : CutForm E) {d : E → ℝ} (hd : ∀ e, 0 ≤ d e) (K : ℝ)
    {a : Option E × Option E} (ha : a ∈ (F.extendForm hd K).D) :
    (∃ a' ∈ F.D, (F.extendForm hd K).cap a = F.cap a') ∨
      ∃ e, (F.extendForm hd K).cap a = d e := by
  rcases mem_union.1 ha with ha | ha
  · obtain ⟨u, v, h, rfl⟩ := mem_someArcs.1 ha
    exact Or.inl ⟨(u, v), h, rfl⟩
  · obtain ⟨e, -, rfl⟩ := mem_map.1 ha
    exact Or.inr ⟨e, rfl⟩

end CutForm

/-! ### The cut form of `g_j`, computed along the construction -/

variable (μin : ℕ → ℕ) in
/-- The cut form of `g_j`, computed along the construction (the proof of `thm:gadget`: "By
`prop:base` and `lem:cutforms`(c), the output has a cut form, computed along the construction"):
the form of `prop:base` for `g_0 = f_0`, and for the step `j → j + 1` the two modular singletons
`π_{F_{τ_1}}`, `π_{F_{τ_2}}` as isolated nodes (`lem:cutforms`(c)(ii)) and the one-element extension
by `b_{j+1}` with `d_{j+1} ≥ 0` and `K_{j+1}` (`lem:cutforms`(c)(iii)), as in `hasCutForm_gT`. -/
def formT : (j : ℕ) → CutForm (Gr j)
  | 0 => Base.form
  | j + 1 => (((formT j).addNode (stepD μin j).Fτ₁).addNode (stepD μin j).Fτ₂).extendForm
      (stepD_hyp (μin := μin) j).d_nonneg (stepD μin j).K

variable {μin : ℕ → ℕ}

/-- `formT` is a cut form of `g_j` (not in the paper: part (4) of the proof of `thm:gadget` says
that the form is computed along the construction; here by induction on `j`, as in
`hasCutForm_gT`). -/
theorem formT_fn : ∀ j S, gT μin j S = (formT μin j).fn S
  | 0, S => Base.base.2.1 S
  | j + 1, S => by
    have h1 := (cutforms_c (E₂ := Unit) (formT_fn j)).2.1 (stepD μin j).Fτ₁
    have h2 := (cutforms_c (E₂ := Unit) h1).2.1 (stepD μin j).Fτ₂
    exact (cutforms_c (E₂ := Unit) h2).2.2.1 (stepD_hyp (μin := μin) j).d_nonneg
      (stepD μin j).K S

/-- The capacities of `g_{j+1}`'s form: those of `g_j`'s form, and the `d_e` of the step
`j → j + 1` on the arcs `b_{j+1} → e` (not in the paper). -/
lemma formT_succ_cap (j : ℕ) {a : Gr (j + 1) × Gr (j + 1)} (ha : a ∈ (formT μin (j + 1)).D) :
    (∃ a' ∈ (formT μin j).D, (formT μin (j + 1)).cap a = (formT μin j).cap a') ∨
      ∃ e, (formT μin (j + 1)).cap a = (lvl μin j).dE' (μT μin (j + 1)) e := by
  rcases CutForm.extendForm_cap _ (stepD_hyp (μin := μin) j).d_nonneg _ ha with
    ⟨a₁, ha₁, h₁⟩ | ⟨e, he⟩
  · obtain ⟨a₂, ha₂, h₂⟩ := CutForm.addNode_cap _ _ ha₁
    obtain ⟨a₃, ha₃, h₃⟩ := CutForm.addNode_cap _ _ ha₂
    exact Or.inl ⟨a₃, ha₃, h₁.trans (h₂.trans h₃)⟩
  · refine Or.inr ⟨e, he.trans ?_⟩
    exact Level.dStep_eq (lvl μin j) (μT μin (j + 1)) (R1T μin j) e

/-- The weights of `g_{j+1}`'s form: `K_{j+1} − d_{j+1}(E)` at `b`, `F_{τ_2}` at `τ_2`, `F_{τ_1}` at
`τ_1`, and those of `g_j`'s form at the old nodes (not in the paper). -/
lemma formT_succ_ω (j : ℕ) :
    (formT μin (j + 1)).ω none =
      (lvl μin j).K (μT μin (j + 1)) (R1T μin j) - (lvl μin j).dE (μT μin (j + 1)) ∧
    (formT μin (j + 1)).ω (some none) = (lvl μin j).Fτ₂ (μT μin (j + 1)) (R1T μin j) ∧
    (formT μin (j + 1)).ω (some (some none)) = (lvl μin j).Fτ₁ (μT μin (j + 1)) (R1T μin j) ∧
    ∀ e, (formT μin (j + 1)).ω (some (some (some e))) = (formT μin j).ω e := by
  refine ⟨?_, rfl, rfl, fun e => rfl⟩
  show (stepD μin j).K - ∑ e, (stepD μin j).dStep (mT μin j) (βT μin j) e = _
  exact congrArg _ (stepD_dE (μin := μin) j)

/-- `Ω_i ≤ Ω_j` for `i ≤ j < k` (not in the paper: the proof of `lem:sizes` says that `Ω_j` more
than doubles from level to level, `Ω_double`, for `j ≥ 1`; `Ω_0 = 16 ≤ Ω_1`). -/
lemma Ω_mono {k : ℕ} (hF : InF μin k) {i j : ℕ} (hij : i ≤ j) (hj : j < k) :
    Ω μin i ≤ Ω μin j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    refine (ih (by omega)).trans ?_
    rcases j with _ | j
    · -- `Ω_0 = 16 ≤ 1872 ≤ Ω_1`
      have h0 : Ω μin 0 = 16 := by
        unfold Ω
        rw [μT_zero (μin0_pos hF), M_eq]
        show (1 : ℝ) * (12 * 208 ^ 0) * (1 + 1 / 3) = 16
        norm_num
      have h1 : Ω μin 1 = 3 / 4 * (12 * 208) * (1 + μT μin 1) := by
        unfold Ω
        rw [ϖ_succ, M_eq]
        norm_num
      have := μT_nonneg (μin := μin) 1
      rw [h0, h1]
      nlinarith
    · have h2 := Ω_double hF (show j + 2 < k by omega)
      have := Ω_pos (μin := μin) (j + 1)
      linarith

/-- The denominators of `g_j`'s form, `j ≤ k − 1`: every capacity and every weight lies in
`(1/𝔇_j)ℤ` (not in the paper: the proof of `thm:gadget` counts the capacities and weights among
the numbers of the output and bounds them through the numbers of the parameter rule, whose
denominators are those of the proof of `lem:sizes`: `d_e ∈ (δ/4)ℤ`, `F_{τ_2} ∈ (1/𝔈_j)ℤ`,
`F_{τ_1}, K ∈ (1/𝔇_j)ℤ`, and the base numbers `1/3`, `1/2`, `2/3`). -/
lemma formT_den {k : ℕ} (hF : InF μin k) : ∀ j, j + 1 ≤ k →
    (∀ a ∈ (formT μin j).D, InZ (𝔇 μin j) ((formT μin j).cap a)) ∧
    ∀ e, InZ (𝔇 μin j) ((formT μin j).ω e)
  | 0, _ => by
    refine ⟨fun a ha => ?_, fun e => ?_⟩
    · change Fin 3 × Fin 3 at a
      change a ∈ ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3)) at ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact ⟨2, by simp [formT, Base.form, 𝔇]; norm_num⟩
      · exact ⟨3, by simp [formT, Base.form, 𝔇]; norm_num⟩
    · change Fin 3 at e
      fin_cases e
      · exact ⟨0, by simp [formT, Base.form, 𝔇]⟩
      · exact ⟨4, by simp [formT, Base.form, 𝔇]; norm_num⟩
      · exact ⟨4, by simp [formT, Base.form, 𝔇]; norm_num⟩
  | j + 1, hj => by
    obtain ⟨ihc, ihw⟩ := formT_den hF j (by omega)
    have hD : 𝔇 μin j ∣ 𝔇 μin (j + 1) := 𝔇_dvd_succ j
    have hE : 𝔈 μin (j + 1) ∣ 𝔇 μin (j + 1) := ⟨12, by rw [𝔇]; ring⟩
    have h4 : 4 * dδ μin ∣ 𝔇 μin (j + 1) := (dvd_𝔈 (μin := μin) j).2.2.2.2.1.trans hE
    obtain ⟨-, -, hdE', -, hdE, -⟩ := sizes_items hF j
    obtain ⟨hFτ₂, hFτ₁⟩ := sizes_Fτ₂_den hF j (by omega)
    obtain ⟨-, hK⟩ := sizes_K_den hF (show j + 2 ≤ k by omega)
    refine ⟨fun a ha => ?_, fun o => ?_⟩
    · rcases formT_succ_cap j ha with ⟨a', ha', h⟩ | ⟨e, h⟩
      · rw [h]
        exact (ihc a' ha').mono_nat hD
      · rw [h]
        exact (hdE' e).mono_cast (by push_cast; ring) h4
    · obtain ⟨hb, hτ₂, hτ₁, hold⟩ := formT_succ_ω (μin := μin) j
      rcases o with _ | _ | _ | e
      · rw [hb]
        exact hK.sub (hdE.mono_cast (by push_cast; ring) h4)
      · rw [hτ₂]
        exact hFτ₂.mono_nat hE
      · rw [hτ₁]
        exact hFτ₁
      · rw [hold]
        exact (ihw e).mono_nat hD

/-- The magnitudes of `g_j`'s form, `j ≤ k − 1`: every capacity lies in `[0, 2Ω_j]` and every
weight has absolute value at most `52Ω_j` (not in the paper, as `formT_den`: by the bounds of the
proof of `lem:sizes`, `d_j(E_j ∖ {b_j}) ≤ 2Ω_j`, `|F_{τ_2}| ≤ 2Ω_j`, `|F_{τ_1}| ≤ 3Ω_j`,
`|K_j| ≤ 50Ω_j`, and `Ω_i ≤ Ω_j` for `i ≤ j`). -/
lemma formT_mag {k : ℕ} (hF : InF μin k) : ∀ j, j + 1 ≤ k →
    (∀ a ∈ (formT μin j).D, 0 ≤ (formT μin j).cap a ∧ (formT μin j).cap a ≤ 2 * Ω μin j) ∧
    ∀ e, |(formT μin j).ω e| ≤ 52 * Ω μin j
  | 0, _ => by
    have h0 : Ω μin 0 = 16 := by
      unfold Ω
      rw [μT_zero (μin0_pos hF), M_eq]
      show (1 : ℝ) * (12 * 208 ^ 0) * (1 + 1 / 3) = 16
      norm_num
    rw [h0]
    refine ⟨fun a ha => ?_, fun e => ?_⟩
    · change Fin 3 × Fin 3 at a
      change a ∈ ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3)) at ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp [formT, Base.form]; norm_num
      · simp [formT, Base.form]; norm_num
    · change Fin 3 at e
      fin_cases e
      · simp [formT, Base.form]
      · simp [formT, Base.form]; norm_num [abs_of_pos]
      · simp [formT, Base.form]; norm_num [abs_of_pos]
  | j + 1, hj => by
    obtain ⟨ihc, ihw⟩ := formT_mag hF j (by omega)
    have hΩ : Ω μin j ≤ Ω μin (j + 1) := Ω_mono hF (Nat.le_succ j) (by omega)
    obtain ⟨-, -, -, hdE2, -, -, -, -⟩ := sizes_dE hF (show j + 2 ≤ k by omega)
    obtain ⟨-, hFτ₂, hFτ₁⟩ := sizes_F hF (show j + 2 ≤ k by omega)
    obtain ⟨-, hK⟩ := sizes_K hF (show j + 2 ≤ k by omega)
    have hd0 : 0 ≤ (lvl μin j).dE (μT μin (j + 1)) :=
      sum_nonneg fun e _ => dE'_nonneg (μin := μin) j e
    refine ⟨fun a ha => ?_, fun o => ?_⟩
    · rcases formT_succ_cap j ha with ⟨a', ha', h⟩ | ⟨e, h⟩
      · rw [h]
        obtain ⟨h1, h2⟩ := ihc a' ha'
        exact ⟨h1, by linarith⟩
      · rw [h]
        refine ⟨dE'_nonneg (μin := μin) j e, ?_⟩
        have : (lvl μin j).dE' (μT μin (j + 1)) e ≤ (lvl μin j).dE (μT μin (j + 1)) :=
          single_le_sum (fun e' _ => dE'_nonneg (μin := μin) j e') (mem_univ e)
        linarith
    · obtain ⟨hb, hτ₂, hτ₁, hold⟩ := formT_succ_ω (μin := μin) j
      have hΩ0 := Ω_pos (μin := μin) (j + 1)
      rcases o with _ | _ | _ | e
      · rw [hb]
        calc |(lvl μin j).K (μT μin (j + 1)) (R1T μin j) - (lvl μin j).dE (μT μin (j + 1))|
            ≤ |(lvl μin j).K (μT μin (j + 1)) (R1T μin j)| +
              |(lvl μin j).dE (μT μin (j + 1))| := abs_sub _ _
          _ ≤ 50 * Ω μin (j + 1) + 2 * Ω μin (j + 1) := by
            rw [abs_of_nonneg hd0]
            linarith
          _ = 52 * Ω μin (j + 1) := by ring
      · rw [hτ₂]
        linarith
      · rw [hτ₁]
        linarith
      · rw [hold]
        linarith [ihw e]

/-! ### The curvatures, the rewards and the ratios `t_e` of a level (not in the paper) -/

/-- `1/β_e > 0`, `1/β_e ≤ 12ϖ_j` and `1/β_e ∈ (1/4)ℤ` on every level `j` (the proof of `lem:sizes`
states them for `j ≥ 1`, `inv_βT_bounds`; on `E_0`, `1/β_e ∈ {1, 1/4}` and `ϖ_0 = 1`). -/
lemma inv_βT_le (j : ℕ) (e : Gr j) :
    0 < 1 / βT μin j e ∧ 1 / βT μin j e ≤ 12 * ϖ μin j ∧ InZ 4 (1 / βT μin j e) := by
  rcases j with _ | j
  · rcases inv_βT_mem (μin := μin) 0 e with h | h | ⟨i, hi, -⟩
    · rw [h]
      exact ⟨by norm_num, by show (1 : ℝ) ≤ 12 * 1; norm_num, ⟨4, by norm_num⟩⟩
    · rw [h]
      exact ⟨by norm_num, by show (1 / 4 : ℝ) ≤ 12 * 1; norm_num, ⟨1, by norm_num⟩⟩
    · omega
  · exact inv_βT_bounds j e

/-- `β_e ≤ 4` (the proof of `thm:gadget`: "since `ζ_1 < 1` and `β_e ≤ 4`"): `1/β_e ≥ 1/4` for every
`1/β_e ∈ {1, 1/4} ∪ {(3/4)·8^i, 9·8^i}` (`inv_βT_mem`). -/
lemma βT_le_four (j : ℕ) (e : Gr j) : βT μin j e ≤ 4 := by
  have hβ0 : 0 < βT μin j e := (fpHyp_gT (μin := μin) j).pos e
  have h4 : 1 / 4 ≤ 1 / βT μin j e := by
    have h8 : ∀ i, (1 : ℝ) ≤ 8 ^ i := fun i => one_le_pow₀ (by norm_num)
    -- (`rw` closes the case `1/β = 1/4` by `rfl`)
    rcases inv_βT_mem (μin := μin) j e with h | h | ⟨i, -, h | h⟩ <;> rw [h]
    · norm_num
    · linarith [h8 i]
    · linarith [h8 i]
  rw [div_le_div_iff₀ (by norm_num) hβ0] at h4
  linarith

/-- "`β_e ∈ (1/(9·8^k))ℤ`" (the proof of `thm:gadget`), here for the elements of `E_j` and
`9·8^{j+1}`: `β_e ∈ {1, 4} ∪ {4/(3·8^i), 1/(9·8^i) : i < j}` (`inv_βT_mem`). -/
lemma βT_inZ (j : ℕ) (e : Gr j) : InZ (9 * 8 ^ (j + 1)) (βT μin j e) := by
  have hβ0 : 0 < βT μin j e := (fpHyp_gT (μin := μin) j).pos e
  have key : βT μin j e = 1 / (1 / βT μin j e) := by field_simp
  rcases inv_βT_mem (μin := μin) j e with h | h | ⟨i, hi, h | h⟩ <;> rw [key, h]
  · exact ⟨9 * 8 ^ (j + 1), by push_cast; ring⟩
  · exact ⟨36 * 8 ^ (j + 1), by push_cast; ring⟩
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    refine ⟨12 * 8 ^ (d + 1), ?_⟩
    push_cast
    rw [show i + d + 1 = i + (d + 1) by ring, pow_add]
    field_simp
    ring
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    refine ⟨8 ^ (d + 1), ?_⟩
    push_cast
    rw [show i + d + 1 = i + (d + 1) by ring, pow_add]
    field_simp

/-- The ratios `t_e = m_e/β_e` of a level: `(5, 3, 1)` on `E_0`, `(9/2)·1664^i` for `τ_{1,i+1}` and
`τ_{2,i+1}` (`m_δ = 6·208^i`, `1/β_δ = (3/4)·8^i`) and `108·208^{i+1}·8^i` for `b_{i+1}`
(`m_b = 12·208^{i+1}`, `1/β_b = 9·8^i`) (not in the paper: the proof of `thm:gadget` uses
`2t_e ∈ ℤ` and `t_e ≥ 1` with the example "the dummies `τ_{1,1}` and `τ_{2,1}` have
`t_e = 9/2`"). -/
lemma t_mem (j : ℕ) (e : Gr j) :
    mT μin j e / βT μin j e = 5 ∨ mT μin j e / βT μin j e = 3 ∨ mT μin j e / βT μin j e = 1 ∨
    ∃ i < j, mT μin j e / βT μin j e = 9 / 2 * 1664 ^ i ∨
      mT μin j e / βT μin j e = 108 * 208 ^ (i + 1) * 8 ^ i := by
  induction j with
  | zero =>
    change Fin 3 at e
    show Base.m e / Base.β e = 5 ∨ Base.m e / Base.β e = 3 ∨ Base.m e / Base.β e = 1 ∨ _
    fin_cases e <;> norm_num [Base.m, Base.β]
  | succ j ih =>
    change Option (Option (Option (Gr j))) at e
    have hβ : 1 / (lvl μin j).βδ = 3 / 4 * 8 ^ j := by rw [Level.inv_βδ, lvl_k]
    have hM := M_eq (μin := μin) j
    have hδ0 : (lvl μin j).βδ ≠ 0 := (lvl μin j).βδ_pos.ne'
    have hmδ : (lvl μin j).mδ = (lvl μin j).M / 2 := rfl
    have h1664 : (1664 : ℝ) ^ j = 208 ^ j * 8 ^ j := by rw [← mul_pow]; norm_num
    have hτ₁ : (lvl μin j).mδ / (lvl μin j).βδ = 9 / 2 * 1664 ^ j := by
      rw [div_eq_mul_one_div, hβ, hmδ, hM, h1664]
      ring
    rcases e with _ | _ | _ | c
    · -- `b`: `m_b = M_{j+1} = 208M_j` and `1/β_b = 12/β_δ`
      refine Or.inr (Or.inr (Or.inr ⟨j, Nat.lt_succ_self j, Or.inr ?_⟩))
      show (lvl μin j).mb / (lvl μin j).βb = _
      have hmb : (lvl μin j).mb = 208 * (lvl μin j).M := by
        rw [← M_succ]
        exact M_succ_eq j
      have e1 : (lvl μin j).mb / (lvl μin j).βb =
          12 * (lvl μin j).mb * (1 / (lvl μin j).βδ) := by
        unfold Level.βb
        field_simp
      rw [e1, hβ, hmb, hM]
      ring
    · refine Or.inr (Or.inr (Or.inr ⟨j, Nat.lt_succ_self j, Or.inl ?_⟩))
      exact hτ₁
    · refine Or.inr (Or.inr (Or.inr ⟨j, Nat.lt_succ_self j, Or.inl ?_⟩))
      exact hτ₁
    · rcases ih c with h | h | h | ⟨i, hi, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨i, by omega, h⟩))

/-- "`2t_e ∈ ℤ`" and `t_e ≥ 1` (the proof of `thm:gadget`:
"`Λ ≤ 12ϖ_{k−1}|Θ| + 2 max_{S⊆E} |g(S)|`, since `1/β_e ≤ 12ϖ_{k−1}` and `t_e ≥ 1`", and
"`2t_e ∈ ℤ` (the dummies `τ_{1,1}` and `τ_{2,1}` have `t_e = 9/2`)"), on every level, by
`t_mem`. -/
lemma t_bounds (j : ℕ) (e : Gr j) :
    InZ 2 (mT μin j e / βT μin j e) ∧ 1 ≤ mT μin j e / βT μin j e := by
  rcases t_mem (μin := μin) j e with h | h | h | ⟨i, -, h | h⟩ <;> rw [h]
  · exact ⟨⟨10, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨6, by norm_num⟩, by norm_num⟩
  · exact ⟨⟨2, by norm_num⟩, le_rfl⟩
  · refine ⟨⟨9 * 1664 ^ i, by push_cast; ring⟩, ?_⟩
    have : (1 : ℝ) ≤ 1664 ^ i := one_le_pow₀ (by norm_num)
    linarith
  · refine ⟨⟨216 * 208 ^ (i + 1) * 8 ^ i, by push_cast; ring⟩, ?_⟩
    have h1 : (1 : ℝ) ≤ 208 ^ (i + 1) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ 8 ^ i := one_le_pow₀ (by norm_num)
    nlinarith

/-! ### The numbers of a level `l ≤ k − 1` (not in the paper: the bounds of the proof of
`lem:sizes` for `l ≥ 1`, and the base numbers for `l = 0`) -/

/-- The magnitudes and denominators of the values of `g_l`, of `q_l` and of `p_l` for every
level `l ≤ k − 1`, from the proof of `lem:sizes` (`sizes_g`, `sizes_p`, `sizes_items`,
`sizes_p_den`) for `l ≥ 1`, and from the base (`|f_0| ≤ 4/3`, `q_0 = 7`, `p_0 = 10`) for
`l = 0`. -/
lemma level_bounds {k : ℕ} (hF : InF μin k) {l : ℕ} (hl : l + 1 ≤ k) :
    (∀ S, |gT μin l S| ≤ 2 + 114 * Ω μin l) ∧
    0 < (lvl μin l).q ∧ (lvl μin l).q ≤ ϖ μin l * (lvl μin l).M ^ 2 ∧ InZ 13 (lvl μin l).q ∧
    |(lvl μin l).p| ≤ 10 + 120 * ((lvl μin l).M * Ω μin l) ∧ InZ (𝔓 μin) (lvl μin l).p := by
  rcases l with _ | j
  · have hΩ := Ω_pos (μin := μin) 0
    refine ⟨fun S => ?_, ?_, ?_, ⟨91, ?_⟩, ?_, ⟨10 * 𝔓 μin, ?_⟩⟩
    · have := abs_f₀_le S
      show |Base.f₀ S| ≤ _
      linarith
    · show (0 : ℝ) < q₀
      unfold q₀
      norm_num
    · show q₀ ≤ 1 * 12 ^ 2
      unfold q₀
      norm_num
    · show (13 : ℝ) * q₀ = ((91 : ℤ) : ℝ)
      unfold q₀
      norm_num
    · show |p₀| ≤ 10 + 120 * (12 * Ω μin 0)
      unfold p₀
      rw [abs_of_pos (by norm_num)]
      nlinarith
    · show (𝔓 μin : ℝ) * p₀ = (((10 * 𝔓 μin : ℕ) : ℤ) : ℝ)
      unfold p₀
      push_cast
      ring
  · have hj : j + 2 ≤ k := by omega
    obtain ⟨hq0, hq1, -, hp1⟩ := sizes_p hF hj
    exact ⟨fun S => (sizes_g hF hj S).2, hq0, hq1, (sizes_items hF j).2.2.2.2.2.2.2.2.2.1, hp1,
      sizes_p_den hF hj⟩

/-- The numbers of a level `l ≤ k − 1` in powers of `2`, with `L = ⌊log₂ μ^in_k⌋`:
`M_l ≤ 2^{8k}`, `ϖ_l ≤ 2^{3k}`, `1 + μ_l ≤ 2^{L+2}`, `Ω_l ≤ 2^{11k+L+2}`, `1/δ ≤ 2^{L+3}` and
`μ^in_k < 2^{L+1}` (not in the paper: the proof of `thm:gadget` says "`N_min` has
`O(k + log μ^in_k)` bits", from `log M_j, log ϖ_j = O(j)` and `μ_j ≤ μ^in_k` of the proof of
`lem:sizes`). -/
lemma level_pow {k : ℕ} (hF : InF μin k) {l : ℕ} (hl : l + 1 ≤ k) :
    (lvl μin l).M ≤ 2 ^ (8 * k) ∧ ϖ μin l ≤ 2 ^ (3 * k) ∧
    1 + μT μin l ≤ 2 ^ (Nat.log 2 (μin (k - 1)) + 2) ∧
    Ω μin l ≤ 2 ^ (11 * k + Nat.log 2 (μin (k - 1)) + 2) ∧
    (dδ μin : ℝ) ≤ 2 ^ (Nat.log 2 (μin (k - 1)) + 3) ∧
    (μin (k - 1) : ℝ) < 2 ^ (Nat.log 2 (μin (k - 1)) + 1) := by
  set L := Nat.log 2 (μin (k - 1))
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  have hμk : (μin (k - 1) : ℝ) < 2 ^ (L + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (μin (k - 1))
    exact_mod_cast this
  have hM : (lvl μin l).M ≤ 2 ^ (8 * k) := by
    rw [M_eq]
    calc (12 : ℝ) * 208 ^ l ≤ 2 ^ 4 * (2 ^ 8) ^ l := by
          gcongr <;> norm_num
      _ = 2 ^ (8 * l + 4) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ (8 * k) := two_pow _ _ (by omega)
  have hϖ : ϖ μin l ≤ 2 ^ (3 * k) := by
    rcases l with _ | j
    · show (1 : ℝ) ≤ _
      exact one_le_pow₀ (by norm_num)
    · rw [ϖ_succ]
      have h8 : (0 : ℝ) ≤ 8 ^ j := by positivity
      calc (3 : ℝ) / 4 * 8 ^ j ≤ 8 ^ j := by linarith
        _ = 2 ^ (3 * j) := by rw [pow_mul]; norm_num
        _ ≤ 2 ^ (3 * k) := two_pow _ _ (by omega)
  have hμ : 1 + μT μin l ≤ 2 ^ (L + 2) := by
    have := μT_le hF (show l < k by omega)
    have : (2 : ℝ) ^ (L + 2) = 2 * 2 ^ (L + 1) := by rw [pow_succ]; ring
    have : (1 : ℝ) ≤ 2 ^ (L + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hΩ : Ω μin l ≤ 2 ^ (11 * k + L + 2) := by
    have hϖ0 := ϖ_pos (μin := μin) l
    have hM0 := M_pos (μin := μin) l
    have hμ0 := μT_nonneg (μin := μin) l
    unfold Ω
    calc ϖ μin l * (lvl μin l).M * (1 + μT μin l)
        ≤ 2 ^ (3 * k) * 2 ^ (8 * k) * 2 ^ (L + 2) := by
          apply mul_le_mul (mul_le_mul hϖ hM hM0.le (by positivity)) hμ (by positivity)
            (by positivity)
      _ = 2 ^ (11 * k + L + 2) := by rw [← pow_add, ← pow_add]; ring_nf
  have hdδ : (dδ μin : ℝ) ≤ 2 ^ (L + 3) := by
    rw [dδ_cast]
    have h0 : (μin 0 : ℝ) ≤ μin (k - 1) := by
      exact_mod_cast μin_mono hF (Nat.zero_le _) (by omega)
    have : (2 : ℝ) ^ (L + 3) = 4 * 2 ^ (L + 1) := by
      rw [show L + 3 = L + 1 + 2 by ring, pow_add]; ring
    linarith
  exact ⟨hM, hϖ, hμ, hΩ, hdδ, hμk⟩

/-! ### `Θ`, `Λ`, `Λ'`, `κ` and `N_min`: part (4) of the proof of `thm:gadget` -/

variable (μin) in
/-- `max_{S⊆E} |g(S)|` for `g = g_{k−1}` (the proof of `thm:gadget`). -/
def gmax (k : ℕ) : ℝ :=
  (univ : Finset (Finset (Gr (k - 1)))).sup' univ_nonempty fun S => |gT μin (k - 1) S|

lemma le_gmax (k : ℕ) (S : Finset (Gr (k - 1))) : |gT μin (k - 1) S| ≤ gmax μin k :=
  le_sup' (fun S => |gT μin (k - 1) S|) (mem_univ S)

/-- `max_S |g(S)| ≤ 2 + 114Ω_{k−1}` (the proof of `lem:sizes`, `sizes_g`, and `|f_0| ≤ 4/3`). -/
lemma gmax_le {k : ℕ} (hF : InF μin k) : gmax μin k ≤ 2 + 114 * Ω μin (k - 1) :=
  sup'_le _ _ fun S _ => (level_bounds hF (show k - 1 + 1 ≤ k by have := hF.1; omega)).1 S

/-- `Θ` is attained (not in the paper: `Θ` is a maximum over the finite set `E`). -/
lemma gΘ_eq (k : ℕ) : ∃ e, gΘ μin k =
    βT μin (k - 1) e * gT μin (k - 1) {e} - ζ₁ * mT μin (k - 1) e := by
  obtain ⟨e, -, he⟩ := exists_mem_eq_sup' (univ_nonempty (α := Gr (k - 1))) fun e =>
    βT μin (k - 1) e * gT μin (k - 1) {e} - ζ₁ * mT μin (k - 1) e
  exact ⟨e, he⟩

/-- The proof of `thm:gadget`: "`|Θ| ≤ M_{k−1} + 4 max_{S⊆E} |g(S)|`, since `ζ_1 < 1` and
`β_e ≤ 4`". -/
lemma gΘ_le (k : ℕ) : |gΘ μin k| ≤ (lvl μin (k - 1)).M + 4 * gmax μin k := by
  obtain ⟨e, he⟩ := gΘ_eq (μin := μin) k
  have hβ0 : 0 < βT μin (k - 1) e := (fpHyp_gT (μin := μin) (k - 1)).pos e
  have hβ4 := βT_le_four (μin := μin) (k - 1) e
  have hm0 := mT_pos (μin := μin) (k - 1) e
  have hmM := mT_le_M (μin := μin) (k - 1) e
  have hg := le_gmax (μin := μin) k {e}
  rw [he]
  have hζ : ζ₁ = 1 / 3 := rfl
  have hζ0 : (0 : ℝ) < ζ₁ := by rw [hζ]; norm_num
  calc |βT μin (k - 1) e * gT μin (k - 1) {e} - ζ₁ * mT μin (k - 1) e|
      ≤ |βT μin (k - 1) e * gT μin (k - 1) {e}| + |ζ₁ * mT μin (k - 1) e| := abs_sub _ _
    _ = βT μin (k - 1) e * |gT μin (k - 1) {e}| + ζ₁ * mT μin (k - 1) e := by
        rw [abs_mul, abs_of_pos hβ0, abs_mul, abs_of_pos hζ0, abs_of_pos hm0]
    _ ≤ 4 * gmax μin k + (lvl μin (k - 1)).M := by
        have : βT μin (k - 1) e * |gT μin (k - 1) {e}| ≤ 4 * gmax μin k :=
          mul_le_mul hβ4 hg (abs_nonneg _) (by norm_num)
        rw [hζ]
        linarith
    _ = (lvl μin (k - 1)).M + 4 * gmax μin k := by ring

/-- `Λ ≥ 0`, and `Λ` is `0` or attained (not in the paper: `Λ` is a maximum of `0` and of a maximum
over the finite set `E`). -/
lemma gΛ_eq (k : ℕ) : 0 ≤ gΛ μin k ∧ (gΛ μin k = 0 ∨ ∃ e, gΛ μin k =
    (gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ + gT μin (k - 1) (univ.erase e)) /
      (mT μin (k - 1) e / βT μin (k - 1) e)) := by
  refine ⟨le_max_left _ _, ?_⟩
  obtain ⟨e, -, he⟩ := exists_mem_eq_sup' (univ_nonempty (α := Gr (k - 1))) fun e =>
    (gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ + gT μin (k - 1) (univ.erase e)) /
      (mT μin (k - 1) e / βT μin (k - 1) e)
  unfold gΛ
  rcases le_total (0 : ℝ) (univ.sup' univ_nonempty fun e =>
    (gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ + gT μin (k - 1) (univ.erase e)) /
      (mT μin (k - 1) e / βT μin (k - 1) e)) with h | h
  · exact Or.inr ⟨e, by rw [max_eq_right h, he]⟩
  · exact Or.inl (max_eq_left h)

/-- The proof of `thm:gadget`: "`Λ ≤ 12ϖ_{k−1}|Θ| + 2 max_{S⊆E} |g(S)|`, since
`1/β_e ≤ 12ϖ_{k−1}` and `t_e ≥ 1`". -/
lemma gΛ_le (k : ℕ) : gΛ μin k ≤ 12 * ϖ μin (k - 1) * |gΘ μin k| + 2 * gmax μin k := by
  have hg0 : 0 ≤ gmax μin k := (abs_nonneg _).trans (le_gmax (μin := μin) k ∅)
  have hϖ0 := ϖ_pos (μin := μin) (k - 1)
  refine max_le (by positivity) (sup'_le _ _ fun e _ => ?_)
  obtain ⟨hb0, hb1, -⟩ := inv_βT_le (μin := μin) (k - 1) e
  obtain ⟨-, ht1⟩ := t_bounds (μin := μin) (k - 1) e
  have hgE := le_gmax (μin := μin) k univ
  have hgE' := le_gmax (μin := μin) k (univ.erase e)
  have h1 : |gΘ μin k / βT μin (k - 1) e| ≤ 12 * ϖ μin (k - 1) * |gΘ μin k| := by
    rw [div_eq_mul_one_div, abs_mul, abs_of_pos hb0, mul_comm]
    exact mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
  have hy : |gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ +
      gT μin (k - 1) (univ.erase e)| ≤ 12 * ϖ μin (k - 1) * |gΘ μin k| + 2 * gmax μin k := by
    calc _ ≤ |gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ| +
          |gT μin (k - 1) (univ.erase e)| := abs_add_le _ _
      _ ≤ |gΘ μin k / βT μin (k - 1) e| + |gT μin (k - 1) univ| +
          |gT μin (k - 1) (univ.erase e)| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  calc _ ≤ |gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ +
        gT μin (k - 1) (univ.erase e)| / (mT μin (k - 1) e / βT μin (k - 1) e) := by
        gcongr
        exact le_abs_self _
    _ ≤ |gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ +
        gT μin (k - 1) (univ.erase e)| := div_le_self (abs_nonneg _) ht1
    _ ≤ _ := hy

/-- The proof of `thm:gadget`: "Also `Λ' ≤ δN`". -/
lemma gΛ'_le (N : ℕ) : gΛ' μin N ≤ δT μin * N := by
  unfold gΛ'
  have : (0 : ℝ) < ζ₁ := by unfold ζ₁; norm_num
  linarith

/-- `κ = min(1, μ^in_1/10)`, so `0 < κ ≤ 1` and "`κ ∈ (1/10)ℤ`" (the proof of `thm:gadget`). -/
lemma κT_spec {k : ℕ} (hF : InF μin k) : 0 < κT μin ∧ κT μin ≤ 1 ∧ InZ 10 (κT μin) := by
  have h0 : (0 : ℝ) < μin 0 := by exact_mod_cast μin0_pos hF
  have hκ : κT μin = min (1 : ℝ) ((μin 0 : ℝ) / 10) := by
    show min 1 ((1 / 30 : ℝ) / (1 / (3 * (μin 0 : ℝ)))) = _
    congr 1
    rw [div_div_eq_mul_div, div_one]
    ring
  refine ⟨(δT_κT_pos (μin0_pos hF)).2, by rw [hκ]; exact min_le_left _ _, ?_⟩
  rw [hκ]
  rcases min_choice (1 : ℝ) ((μin 0 : ℝ) / 10) with h | h <;> rw [h]
  · exact ⟨10, by norm_num⟩
  · exact ⟨μin 0, by push_cast; ring⟩

/-- The denominators of part (4) of the proof of `thm:gadget`: "For the denominators, `ζ_1 = 1/3`,
all rewards are integers and `β_e ∈ (1/(9·8^k))ℤ`, so `Θ ∈ (1/(9·8^k𝔇_{k−1}))ℤ` with `𝔇_{k−1}`
from the proof of `lem:sizes`. Moreover, `2t_e ∈ ℤ` …, `1/β_e ∈ (1/4)ℤ`,
`Λ' = δN − 1/3 ∈ (δ/3)ℤ` and `κ ∈ (1/10)ℤ`" (`x ∈ (δ/3)ℤ` is `InZ (3/δ) x`, `3/δ = 3·(1/δ)`). -/
lemma gadget_items {k : ℕ} (hF : InF μin k) (N : ℕ) :
    ζ₁ = 1 / 3 ∧ (∀ e, InZ 1 (mT μin (k - 1) e)) ∧
    (∀ e, InZ (9 * 8 ^ k) (βT μin (k - 1) e)) ∧
    InZ (9 * 8 ^ k * 𝔇 μin (k - 1)) (gΘ μin k) ∧
    (∀ e, InZ 2 (mT μin (k - 1) e / βT μin (k - 1) e)) ∧
    (∀ e, InZ 4 (1 / βT μin (k - 1) e)) ∧ InZ (3 * dδ μin) (gΛ' μin N) ∧ InZ 10 (κT μin) := by
  have hk : k - 1 + 1 = k := by have := hF.1; omega
  have hβ : ∀ e, InZ (9 * 8 ^ k) (βT μin (k - 1) e) := fun e =>
    (βT_inZ (μin := μin) (k - 1) e).den_eq (by rw [hk])
  refine ⟨rfl, mT_inZ (k - 1), hβ, ?_, fun e => (t_bounds (k - 1) e).1,
    fun e => (inv_βT_le (k - 1) e).2.2, ?_, (κT_spec hF).2.2⟩
  · -- `Θ = β_e g({e}) − ζ_1 m_e` for some `e`, with `β_e ∈ (1/(9·8^k))ℤ`, `g({e}) ∈ (1/𝔇_{k−1})ℤ`
    -- and `ζ_1 m_e ∈ (1/3)ℤ`
    obtain ⟨e, he⟩ := gΘ_eq (μin := μin) k
    rw [he]
    have hg := sizes_g_den hF (k - 1) (by omega) {e}
    have h1 := (hβ e).mul hg
    have h2 : InZ 3 (ζ₁ * mT μin (k - 1) e) := by
      obtain ⟨n, -, hv, -⟩ := (weights_b (μin := μin)).1 (k - 1) e
      rw [hv]
      exact ⟨n, by unfold ζ₁; push_cast; ring⟩
    refine h1.sub (h2.mono (3 * 8 ^ k * 𝔇 μin (k - 1)) ?_)
    push_cast
    ring
  · -- `Λ' = δN − 1/3`, and `(3/δ)(δN − 1/3) = 3N − 3μ^in_1`
    have h0 : (0 : ℝ) < μin 0 := by exact_mod_cast μin0_pos hF
    refine ⟨3 * N - 3 * μin 0, ?_⟩
    rw [dδ_cast]
    unfold gΛ' δT ζ₁
    push_cast
    field_simp

/-- `max_S |g(S)| ≤ 2^{11k+L+10}` and `|Θ| ≤ 2^{11k+L+13}`, with `L = ⌊log₂ μ^in_k⌋` (from
`gmax_le`, `gΘ_le` and `level_pow`; not in the paper, which leaves these powers of `2`
implicit). -/
lemma gmax_Θ_pow {k : ℕ} (hF : InF μin k) :
    gmax μin k ≤ 2 ^ (11 * k + Nat.log 2 (μin (k - 1)) + 10) ∧
    |gΘ μin k| ≤ 2 ^ (11 * k + Nat.log 2 (μin (k - 1)) + 13) := by
  set L := Nat.log 2 (μin (k - 1))
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  have hl : k - 1 + 1 ≤ k := by have := hF.1; omega
  obtain ⟨hM, -, -, hΩ, -, -⟩ := level_pow hF hl
  have hg := gmax_le hF
  have hΘ := gΘ_le (μin := μin) k
  have hg' : gmax μin k ≤ 2 ^ (11 * k + L + 10) := by
    have h1 : (2 : ℝ) ≤ 2 ^ (11 * k + L + 2) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ _ := two_pow _ _ (by omega)
    have h3 : (2 : ℝ) ^ (11 * k + L + 10) = 2 ^ 8 * 2 ^ (11 * k + L + 2) := by
      rw [← pow_add]; ring_nf
    rw [h3]
    linarith
  refine ⟨hg', ?_⟩
  have h1 : (lvl μin (k - 1)).M ≤ 2 ^ (11 * k + L + 12) := hM.trans (two_pow _ _ (by omega))
  have h2 : (2 : ℝ) ^ (11 * k + L + 13) = 2 * 2 ^ (11 * k + L + 12) := by rw [pow_succ]; ring
  have h3 : (2 : ℝ) ^ (11 * k + L + 12) = 4 * 2 ^ (11 * k + L + 10) := by
    rw [show 11 * k + L + 12 = 11 * k + L + 10 + 2 by ring, pow_add]; ring
  linarith

/-- The proof of `thm:gadget`: "So `N_min` has `O(k + log μ^in_k)` bits": `1 ≤ N_min ≤ 2^{2(20k +
L + 20) + 3}` with `L = ⌊log₂ μ^in_k⌋`, from `N_min = max(1, ⌈(ζ_1 + Λ)/δ⌉)`, the bounds on `Θ` and
`Λ` above, and the bounds of the proof of `lem:sizes` (`level_pow`). The intermediate bound
`Λ ≤ 2^{20k+L+20}` is the second conjunct. -/
lemma gNmin_le {k : ℕ} (hF : InF μin k) :
    1 ≤ gNmin μin k ∧ gΛ μin k ≤ 2 ^ (20 * k + Nat.log 2 (μin (k - 1)) + 20) ∧
    (gNmin μin k : ℝ) ≤ 2 ^ (2 * (20 * k + Nat.log 2 (μin (k - 1)) + 20) + 3) := by
  set L := Nat.log 2 (μin (k - 1))
  set U : ℝ := 2 ^ (20 * k + L + 20) with hUdef
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  have hl : k - 1 + 1 ≤ k := by have := hF.1; omega
  obtain ⟨-, hϖ, -, -, -, hμk⟩ := level_pow hF hl
  have hΛ := gΛ_le (μin := μin) k
  have hϖ0 := ϖ_pos (μin := μin) (k - 1)
  -- `max_S |g(S)| ≤ 2^{11k+L+10}`, `|Θ| ≤ 2^{11k+L+13}`, `Λ ≤ 2^{14k+L+18} ≤ U`
  obtain ⟨hg', hΘ'⟩ := gmax_Θ_pow hF
  have hΛ' : gΛ μin k ≤ U := by
    have h1 : 12 * ϖ μin (k - 1) ≤ 2 ^ (3 * k + 4) := by
      have : (2 : ℝ) ^ (3 * k + 4) = 16 * 2 ^ (3 * k) := by rw [pow_add]; ring
      linarith
    have h2 : 12 * ϖ μin (k - 1) * |gΘ μin k| ≤ 2 ^ (3 * k + 4) * 2 ^ (11 * k + L + 13) :=
      mul_le_mul h1 hΘ' (abs_nonneg _) (by positivity)
    have h3 : (2 : ℝ) ^ (3 * k + 4) * 2 ^ (11 * k + L + 13) = 2 ^ (14 * k + L + 17) := by
      rw [← pow_add]; ring_nf
    have h4 : 2 * gmax μin k ≤ 2 ^ (14 * k + L + 17) := by
      have h5 : (2 : ℝ) ^ (11 * k + L + 11) ≤ 2 ^ (14 * k + L + 17) := two_pow _ _ (by omega)
      have h6 : (2 : ℝ) ^ (11 * k + L + 11) = 2 * 2 ^ (11 * k + L + 10) := by
        rw [pow_succ]; ring
      linarith
    have h5 : (2 : ℝ) ^ (14 * k + L + 17) + 2 ^ (14 * k + L + 17) ≤ U := by
      have h6 : (2 : ℝ) ^ (14 * k + L + 18) ≤ U := two_pow _ _ (by omega)
      have h7 : (2 : ℝ) ^ (14 * k + L + 18) = 2 * 2 ^ (14 * k + L + 17) := by
        rw [pow_succ]; ring
      linarith
    linarith
  refine ⟨le_max_left _ _, hΛ', ?_⟩
  -- `N_min ≤ max(1, (ζ_1 + Λ)/δ + 1)` and `(ζ_1 + Λ)/δ = μ^in_1 + 3μ^in_1Λ ≤ U + 3U²`
  have hΛ0 := (gΛ_eq (μin := μin) k).1
  have hU1 : (1 : ℝ) ≤ U := one_le_pow₀ (by norm_num)
  have hμ0 : (μin 0 : ℝ) ≤ U := by
    have h1 : (μin 0 : ℝ) ≤ μin (k - 1) := by
      exact_mod_cast μin_mono hF (Nat.zero_le _) (by omega)
    have h2 : (2 : ℝ) ^ (L + 1) ≤ U := two_pow _ _ (by omega)
    linarith
  have hx : (ζ₁ + gΛ μin k) / δT μin = μin 0 + 3 * μin 0 * gΛ μin k := by
    have h0 : (0 : ℝ) < μin 0 := by exact_mod_cast μin0_pos hF
    unfold δT ζ₁
    field_simp
  have hx0 : 0 ≤ (ζ₁ + gΛ μin k) / δT μin := by
    rw [hx]
    positivity
  have hceil : (⌈(ζ₁ + gΛ μin k) / δT μin⌉₊ : ℝ) ≤ U + 3 * U * U + 1 := by
    have h1 := (Nat.ceil_lt_add_one hx0).le
    have h2 : 3 * (μin 0 : ℝ) * gΛ μin k ≤ 3 * U * U :=
      mul_le_mul (by linarith) hΛ' hΛ0 (by positivity)
    have h3 : (ζ₁ + gΛ μin k) / δT μin ≤ U + 3 * U * U := by
      rw [hx]
      linarith
    linarith
  have hU2 : U + 3 * U * U + 1 ≤ 2 ^ (2 * (20 * k + L + 20) + 3) := by
    have : (2 : ℝ) ^ (2 * (20 * k + L + 20) + 3) = 8 * (U * U) := by
      rw [hUdef, pow_add, two_mul, pow_add]; ring
    nlinarith
  unfold gNmin
  rcases le_total 1 ⌈(ζ₁ + gΛ μin k) / δT μin⌉₊ with h | h
  · rw [max_eq_right h]
    exact hceil.trans hU2
  · rw [max_eq_left h]
    push_cast
    have : (1 : ℝ) ≤ 2 ^ (2 * (20 * k + L + 20) + 3) := one_le_pow₀ (by norm_num)
    exact this

/-! ### The cut form of the output -/

variable (μin) in
/-- The modular function `y = Λ't − Θβ⁻¹` with `f_c = g + y`. -/
def gadgetY (k N : ℕ) (e : Gr (k - 1)) : ℝ :=
  gΛ' μin N * (mT μin (k - 1) e / βT μin (k - 1) e) - gΘ μin k * (1 / βT μin (k - 1) e)

variable (μin) in
/-- The cut form of the output `I(μ^in, N)`, "computed along the construction" (part (4) of the
proof of `thm:gadget`): the form of `g` (`formT`) with `ω` replaced by `ω + y` for
`f_c = g + Λ't − Θβ⁻¹` (`lem:cutforms`(c)(i)), and the capped linear summand `e_g`, a direct sum
with a modular singleton, as an isolated node of weight `C_g` (`lem:cutforms`(c)(ii), the disjoint
union with `CutForm.node`). -/
def gadgetForm (k N : ℕ) : CutForm (Gr (k - 1) ⊕ Unit) :=
  ((formT μin (k - 1)).addModular (gadgetY μin k N)).dsumForm (CutForm.node (gC μin k N))

/-- `gadgetForm` is a cut form of the rank function of the output (not in the paper: part (4) of
the proof of `thm:gadget` says that the cut form is computed along the construction). -/
theorem gadgetForm_fn (k N : ℕ) (T : Finset (Gr (k - 1) ⊕ Unit)) :
    gadgetF μin k N T = (gadgetForm μin k N).fn T := by
  have h1 : ∀ S, gfc μin k N S =
      ((formT μin (k - 1)).addModular (gadgetY μin k N)).fn S := by
    intro S
    rw [← (cutforms_c (E₂ := Unit) (formT_fn (μin := μin) (k - 1))).1 (gadgetY μin k N) S]
    simp only [gfc, gadgetY, sum_sub_distrib, mul_sum]
    ring
  have h2 : ∀ S, single (gC μin k N) S = (CutForm.node (gC μin k N)).fn S := by
    intro S
    rcases finset_unit S with rfl | rfl
    · simp [single, CutForm.fn, CutForm.cut, CutForm.node]
    · simp [single, CutForm.fn, CutForm.cut, CutForm.node]
  exact (cutforms_c h1).2.2.2 h2 T

/-- The arcs of the output's form are those of `g`'s form, with their capacities (not in the
paper). -/
lemma gadgetForm_cap (k N : ℕ) {a : (Gr (k - 1) ⊕ Unit) × (Gr (k - 1) ⊕ Unit)}
    (ha : a ∈ (gadgetForm μin k N).D) :
    ∃ a' ∈ (formT μin (k - 1)).D, (gadgetForm μin k N).cap a = (formT μin (k - 1)).cap a' := by
  rcases mem_union.1 ha with ha | ha
  · obtain ⟨⟨u, v⟩, h, rfl⟩ := mem_map.1 ha
    exact ⟨(u, v), h, rfl⟩
  · obtain ⟨⟨u, v⟩, h, -⟩ := mem_map.1 ha
    exact absurd h (notMem_empty _)

/-! ### The common denominator and the bits of the output -/

variable (μin) in
/-- A common integer for the denominators of the numbers of the output (part (4) of the proof of
`thm:gadget`: "So their denominators divide a common integer with `O(k + log μ^in_k + log N)`
bits"): `𝔇g = 36·8^k·𝔇_{k−1}·𝔓·390/δ` (not in the paper, which does not name it; it does not
depend on `N`). -/
def 𝔇g (k : ℕ) : ℕ := 36 * 8 ^ k * 𝔇 μin (k - 1) * 𝔓 μin * 390 * dδ μin

/-- The denominators that occur divide `𝔇g` (not in the paper). -/
lemma dvd_𝔇g (k : ℕ) :
    9 * 8 ^ k ∣ 𝔇g μin k ∧ 𝔇 μin (k - 1) ∣ 𝔇g μin k ∧
    9 * 8 ^ k * 𝔇 μin (k - 1) * 4 ∣ 𝔇g μin k ∧ 9 * 8 ^ k * 𝔇 μin (k - 1) * 2 ∣ 𝔇g μin k ∧
    𝔓 μin ∣ 𝔇g μin k ∧ 3 * dδ μin * 2 ∣ 𝔇g μin k ∧ 13 * (3 * dδ μin) ∣ 𝔇g μin k ∧
    130 * dδ μin ∣ 𝔇g μin k ∧ dδ μin ∣ 𝔇g μin k ∧
    13 ∣ 𝔇g μin k ∧ 10 ∣ 𝔇g μin k ∧ 2 ∣ 𝔇g μin k ∧ 1 ∣ 𝔇g μin k := by
  unfold 𝔇g
  set D := 𝔇 μin (k - 1)
  set P := 𝔓 μin
  set d := dδ μin
  set X := 8 ^ k
  exact ⟨⟨4 * D * P * 390 * d, by ring⟩, ⟨36 * X * P * 390 * d, by ring⟩,
    ⟨P * 390 * d, by ring⟩, ⟨2 * P * 390 * d, by ring⟩, ⟨36 * X * D * 390 * d, by ring⟩,
    ⟨65 * 36 * X * D * P, by ring⟩, ⟨10 * 36 * X * D * P, by ring⟩,
    ⟨3 * 36 * X * D * P, by ring⟩, ⟨390 * 36 * X * D * P, by ring⟩,
    ⟨30 * 36 * X * D * P * d, by ring⟩, ⟨39 * 36 * X * D * P * d, by ring⟩,
    ⟨18 * X * D * P * 390 * d, by ring⟩, ⟨36 * X * D * P * 390 * d, by ring⟩⟩

/-- `𝔇_{k−1} ≤ 2^{8k+L+29}` (from the proof of `lem:sizes`, `sizes_pow`, for `k ≥ 2`, and
`𝔇_0 = 6`; not in the paper). -/
lemma 𝔇_pred_le {k : ℕ} (hF : InF μin k) :
    (𝔇 μin (k - 1) : ℝ) ≤ 2 ^ (8 * k + Nat.log 2 (μin (k - 1)) + 29) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hF.1; omega
    show ((𝔇 μin 0 : ℕ) : ℝ) ≤ _
    have h6 : (𝔇 μin 0 : ℝ) = 6 := by simp [𝔇]
    rw [h6]
    calc (6 : ℝ) ≤ 2 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h := (sizes_pow hF (le_refl (j + 2))).2.2.2.2.2.1
    have e : j + 2 - 1 = j + 1 := by omega
    rw [e] at h ⊢
    exact h.trans (pow_le_pow_right₀ (by norm_num) (by omega))

/-- "a common integer with `O(k + log μ^in_k + log N)` bits": `0 < 𝔇g ≤ 2^{11k+3L+73}` (not in the
paper: the bounds of the proof of `lem:sizes` on `𝔇_{k−1}` and `𝔓`, and `1/δ ≤ 2^{L+3}`). -/
lemma 𝔇g_le {k : ℕ} (hF : InF μin k) :
    0 < 𝔇g μin k ∧ (𝔇g μin k : ℝ) ≤ 2 ^ (11 * k + 3 * Nat.log 2 (μin (k - 1)) + 73) := by
  set L := Nat.log 2 (μin (k - 1))
  have hl : k - 1 + 1 ≤ k := by have := hF.1; omega
  obtain ⟨-, -, -, -, hdδ, -⟩ := level_pow hF hl
  have hd0 : 0 < dδ μin := by unfold dδ; have := μin0_pos hF; omega
  have hD0 : 0 < 𝔇 μin (k - 1) := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by have := hF.1; omega
      show 0 < 6
      norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      show 0 < 12 * 𝔈 μin (j + 1)
      unfold 𝔈
      positivity
  have hP0 : 0 < 𝔓 μin := by unfold 𝔓; positivity
  refine ⟨by unfold 𝔇g; positivity, ?_⟩
  have hD := 𝔇_pred_le hF
  have hP : (𝔓 μin : ℝ) ≤ 2 ^ (L + 26) := by
    have e1 : (𝔓 μin : ℝ) = 6474000 * dδ μin := by unfold 𝔓; push_cast; ring
    have e2 : (2 : ℝ) ^ (L + 26) = 2 ^ 23 * 2 ^ (L + 3) := by rw [← pow_add]; ring_nf
    rw [e1, e2]
    have : (0 : ℝ) ≤ dδ μin := Nat.cast_nonneg _
    nlinarith
  have h36 : (36 : ℝ) * 8 ^ k ≤ 2 ^ (3 * k + 6) := by
    have : (2 : ℝ) ^ (3 * k + 6) = 64 * 8 ^ k := by rw [pow_add, pow_mul]; norm_num; ring
    rw [this]
    have : (0 : ℝ) ≤ 8 ^ k := by positivity
    linarith
  have h390 : (390 : ℝ) ≤ 2 ^ 9 := by norm_num
  unfold 𝔇g
  push_cast
  calc (36 : ℝ) * 8 ^ k * 𝔇 μin (k - 1) * 𝔓 μin * 390 * dδ μin
      ≤ 2 ^ (3 * k + 6) * 2 ^ (8 * k + L + 29) * 2 ^ (L + 26) * 2 ^ 9 * 2 ^ (L + 3) := by
        apply mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul h36 hD (by positivity)
          (by positivity)) hP (by positivity) (by positivity)) h390 (by norm_num)
          (by positivity)) hdδ (by positivity) (by positivity)
    _ = 2 ^ (11 * k + 3 * L + 73) := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
        ring_nf

/-- The denominators of the numbers of the output: all of them lie in `(1/𝔇g)ℤ`, by the
denominators of part (4) of the proof of `thm:gadget` (`gadget_items`) and of the proof of
`lem:sizes`, as each "is a sum of `O(|E|)` products of at most three of the numbers `Θ`, `Λ'`, `κ`,
`α_Γ = δN`, values of `g`, numbers of the parameter rule, rewards, `1/β_e` and `t_e`" (apart from
`β_{e_g}` and from `Λ`, which are quotients; the last conjunct is the numerator of `Λ`). -/
lemma gadget_den {k : ℕ} (hF : InF μin k) (N : ℕ) :
    InZ (𝔇g μin k) (gΘ μin k) ∧ InZ (𝔇g μin k) (gΛ' μin N) ∧ InZ (𝔇g μin k) (gαΓ μin N) ∧
    InZ (𝔇g μin k) (gC μin k N) ∧ InZ (𝔇g μin k) (gp μin k N) ∧ InZ (𝔇g μin k) (gq μin k) ∧
    InZ (𝔇g μin k) (δT μin) ∧ InZ (𝔇g μin k) (κT μin) ∧ InZ (𝔇g μin k) (gNmin μin k) ∧
    (∀ e, InZ (𝔇g μin k) (gadgetM μin k e)) ∧ (∀ e, InZ (𝔇g μin k) (βT μin (k - 1) e)) ∧
    (∀ e, InZ (𝔇g μin k) (mT μin (k - 1) e / βT μin (k - 1) e)) ∧
    (∀ S, InZ (𝔇g μin k) (gfc μin k N S)) ∧ (∀ T, InZ (𝔇g μin k) (gadgetF μin k N T)) ∧
    (∀ a ∈ (gadgetForm μin k N).D, InZ (𝔇g μin k) ((gadgetForm μin k N).cap a)) ∧
    (∀ e, InZ (𝔇g μin k) ((gadgetForm μin k N).ω e)) ∧
    ∀ e, InZ (𝔇g μin k) (gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ +
      gT μin (k - 1) (univ.erase e)) := by
  have hl : k - 1 + 1 ≤ k := by have := hF.1; omega
  obtain ⟨-, hm, hβ, hΘ, ht, hb, hΛ', hκ⟩ := gadget_items hF N
  have hg := sizes_g_den hF (k - 1) hl
  obtain ⟨-, -, -, hq13, -, hpP⟩ := level_bounds hF hl
  obtain ⟨hcap, hω⟩ := formT_den hF (k - 1) hl
  obtain ⟨d9, dD, d36, d18, dP, d6, d39, d130, d1, d13, d10, d2, d1'⟩ := dvd_𝔇g (μin := μin) k
  have h0 : (0 : ℝ) < μin 0 := by exact_mod_cast μin0_pos hF
  have hαΓ : InZ (dδ μin) (gαΓ μin N) := ⟨N, by rw [dδ_cast]; unfold gαΓ δT; field_simp; simp⟩
  have hδ : InZ (dδ μin) (δT μin) := ⟨1, by rw [dδ_cast]; unfold δT; field_simp; simp⟩
  have hqκ : InZ 130 (gq μin k + κT μin) :=
    (hq13.mono 10 (by norm_num)).add (hκ.mono 13 (by norm_num))
  have hC : InZ (𝔇g μin k) (gC μin k N) :=
    (hqκ.mul hαΓ).mono_cast (by push_cast; ring) d130
  have hΘ' : InZ (𝔇g μin k) (gΘ μin k) :=
    hΘ.mono_cast (by push_cast; ring) ((Dvd.intro 4 rfl).trans d36)
  have hY : ∀ e, InZ (𝔇g μin k) (gadgetY μin k N e) := fun e =>
    ((hΛ'.mul (ht e)).mono_cast (by push_cast; ring) d6).sub
      ((hΘ.mul (hb e)).mono_cast (by push_cast; ring) d36)
  have hfc : ∀ S, InZ (𝔇g μin k) (gfc μin k N S) := fun S => by
    have h1 : InZ (𝔇g μin k) (gΛ' μin N * ∑ e ∈ S, mT μin (k - 1) e / βT μin (k - 1) e) :=
      (hΛ'.mul (InZ.sum fun e _ => ht e)).mono_cast (by push_cast; ring) d6
    have h2 : InZ (𝔇g μin k) (gΘ μin k * ∑ e ∈ S, 1 / βT μin (k - 1) e) :=
      (hΘ.mul (InZ.sum fun e _ => hb e)).mono_cast (by push_cast; ring) d36
    exact (((hg S).mono_nat dD).add h1).sub h2
  refine ⟨hΘ', (hΛ'.mono_cast (by push_cast; ring) ((Dvd.intro 2 rfl).trans d6)),
    hαΓ.mono_nat d1, hC, ?_, hq13.mono_cast (by norm_num) d13, hδ.mono_nat d1,
    hκ.mono_cast (by norm_num) d10, (InZ.nat _).mono_cast (by norm_num) d1', fun e => ?_,
    fun e => (hβ e).mono_cast (by push_cast; ring) d9, fun e => (ht e).mono_cast (by norm_num) d2,
    hfc, fun T => ?_, fun a ha => ?_, fun e => ?_, fun e => ?_⟩
  · -- `p = p_{k−1} − qΛ' + Λ'm^⊤t − Θt(E) + C_g`
    have h1 : InZ (𝔇g μin k) (gq μin k * gΛ' μin N) :=
      (hq13.mul hΛ').mono_cast (by push_cast; ring) d39
    have h2 : InZ (𝔇g μin k) (gΛ' μin N * ∑ e, mT μin (k - 1) e *
        (mT μin (k - 1) e / βT μin (k - 1) e)) :=
      (hΛ'.mul (InZ.sum fun e _ => (hm e).mul (ht e))).mono_cast (by push_cast; ring) d6
    have h3 : InZ (𝔇g μin k) (gΘ μin k * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e) :=
      (hΘ.mul (InZ.sum fun e _ => ht e)).mono_cast (by push_cast; ring) d18
    exact ((((hpP.mono_nat dP).sub h1).add h2).sub h3).add hC
  · rcases e with e | u
    · exact (hm e).mono_cast (by norm_num) d1'
    · exact ⟨𝔇g μin k, by simp [gadgetM]⟩
  · -- the values `f_c(T ∩ E) + C_g[e_g ∈ T]`
    show InZ _ (gfc μin k N T.toLeft + single (gC μin k N) T.toRight)
    refine (hfc _).add ?_
    unfold single
    split_ifs
    · exact hC
    · exact InZ.zero
  · obtain ⟨a', ha', h⟩ := gadgetForm_cap (μin := μin) k N ha
    rw [h]
    exact (hcap a' ha').mono_nat dD
  · rcases e with e | u
    · exact ((hω e).mono_nat dD).add (hY e)
    · exact hC
  · rw [div_eq_mul_one_div]
    exact (((hΘ.mul (hb e)).mono_cast (by push_cast; ring) d36).sub ((hg _).mono_nat dD)).add
      ((hg _).mono_nat dD)

variable (μin) in
/-- `U = 2^{20k+L+20}`, `L = ⌊log₂ μ^in_k⌋`, a bound for the numbers of the level `k − 1` that do
not depend on `N` (not in the paper). -/
def gU (k : ℕ) : ℝ := 2 ^ (20 * k + Nat.log 2 (μin (k - 1)) + 20)

/-- The basic magnitudes of part (4) of the proof of `thm:gadget`, in terms of `U = gU`: the
numbers of the level `k − 1`, `Θ`, `Λ`, the rewards, the curvatures, the `1/β_e` and `t_e` are at
most `U`, `|E| ≤ U`, `κ, δ ≤ 1`, and `|Λ'|, α_Γ ≤ N` (not in the paper: the bounds above and those
of the proof of `lem:sizes`, in powers of `2`). -/
lemma gadget_basic {k : ℕ} (hF : InF μin k) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ gU μin k ∧ gmax μin k ≤ gU μin k ∧ |gΘ μin k| ≤ gU μin k ∧ 0 ≤ gΛ μin k ∧
    gΛ μin k ≤ gU μin k ∧ 0 < gq μin k ∧ gq μin k ≤ gU μin k ∧
    |(lvl μin (k - 1)).p| ≤ gU μin k ∧ (Fintype.card (Gr (k - 1)) : ℝ) ≤ gU μin k ∧
    (∀ e, 0 < mT μin (k - 1) e ∧ mT μin (k - 1) e ≤ gU μin k) ∧
    (∀ e, 0 < βT μin (k - 1) e ∧ βT μin (k - 1) e ≤ gU μin k) ∧
    (∀ e, 0 < 1 / βT μin (k - 1) e ∧ 1 / βT μin (k - 1) e ≤ gU μin k) ∧
    (∀ e, 1 ≤ mT μin (k - 1) e / βT μin (k - 1) e ∧
      mT μin (k - 1) e / βT μin (k - 1) e ≤ gU μin k) ∧
    0 < κT μin ∧ κT μin ≤ 1 ∧ 0 < δT μin ∧ δT μin ≤ 1 ∧
    |gΛ' μin N| ≤ N ∧ 0 < gαΓ μin N ∧ gαΓ μin N ≤ N ∧
    (∀ a ∈ (formT μin (k - 1)).D,
      0 ≤ (formT μin (k - 1)).cap a ∧ (formT μin (k - 1)).cap a ≤ gU μin k) ∧
    ∀ e, |(formT μin (k - 1)).ω e| ≤ gU μin k := by
  set L := Nat.log 2 (μin (k - 1))
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  have hU : gU μin k = 2 ^ (20 * k + L + 20) := rfl
  have hk1 := hF.1
  have hl : k - 1 + 1 ≤ k := by omega
  obtain ⟨hM, hϖ, -, hΩ, -, -⟩ := level_pow hF hl
  obtain ⟨hg, hΘ⟩ := gmax_Θ_pow hF
  obtain ⟨-, hΛ, -⟩ := gNmin_le hF
  obtain ⟨-, hq0, hq1, -, hp1, -⟩ := level_bounds hF hl
  obtain ⟨hcap, hω⟩ := formT_mag hF (k - 1) hl
  have hU1 : (1 : ℝ) ≤ gU μin k := one_le_pow₀ (by norm_num)
  have hϖ0 := ϖ_pos (μin := μin) (k - 1)
  have hM0 := M_pos (μin := μin) (k - 1)
  have hΩ0 := Ω_pos (μin := μin) (k - 1)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (1 : ℝ) ≤ μin 0 := by exact_mod_cast μin0_pos hF
  have hMU : (lvl μin (k - 1)).M ≤ gU μin k := hM.trans (two_pow _ _ (by omega))
  have h12ϖ : 12 * ϖ μin (k - 1) ≤ 2 ^ (3 * k + 4) := by
    have : (2 : ℝ) ^ (3 * k + 4) = 16 * 2 ^ (3 * k) := by rw [pow_add]; ring
    linarith
  have hq : gq μin k ≤ gU μin k := by
    show (lvl μin (k - 1)).q ≤ _
    calc (lvl μin (k - 1)).q ≤ ϖ μin (k - 1) * (lvl μin (k - 1)).M ^ 2 := hq1
      _ ≤ 2 ^ (3 * k) * (2 ^ (8 * k)) ^ 2 := by gcongr
      _ = 2 ^ (19 * k) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ gU μin k := two_pow _ _ (by omega)
  have hp : |(lvl μin (k - 1)).p| ≤ gU μin k := by
    have h1 : (lvl μin (k - 1)).M * Ω μin (k - 1) ≤ 2 ^ (19 * k + L + 2) := by
      calc _ ≤ 2 ^ (8 * k) * 2 ^ (11 * k + L + 2) := mul_le_mul hM hΩ hΩ0.le (by positivity)
        _ = 2 ^ (19 * k + L + 2) := by rw [← pow_add]; ring_nf
    have h3 : (2 : ℝ) ^ (19 * k + L + 10) = 256 * 2 ^ (19 * k + L + 2) := by
      rw [show 19 * k + L + 10 = 19 * k + L + 2 + 8 by ring, pow_add]; ring
    have h4 : (1 : ℝ) ≤ 2 ^ (19 * k + L + 2) := one_le_pow₀ (by norm_num)
    have h5 : (2 : ℝ) ^ (19 * k + L + 10) ≤ gU μin k := two_pow _ _ (by omega)
    linarith
  have hcard : (Fintype.card (Gr (k - 1)) : ℝ) ≤ gU μin k := by
    have h1 : Fintype.card (Gr (k - 1)) ≤ 2 ^ (20 * k + L + 20) := by
      rw [card_Gr]
      exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [hU]
    exact_mod_cast h1
  have hb : ∀ e, 0 < 1 / βT μin (k - 1) e ∧ 1 / βT μin (k - 1) e ≤ gU μin k := fun e => by
    obtain ⟨h1, h2, -⟩ := inv_βT_le (μin := μin) (k - 1) e
    exact ⟨h1, h2.trans (h12ϖ.trans (two_pow _ _ (by omega)))⟩
  have hδ0 : 0 < δT μin := by unfold δT; positivity
  have hδ1 : δT μin ≤ 1 := by
    unfold δT
    rw [div_le_one (by positivity)]
    linarith
  refine ⟨hU1, hg.trans (two_pow _ _ (by omega)), hΘ.trans (two_pow _ _ (by omega)),
    (gΛ_eq (μin := μin) k).1, hΛ, hq0, hq, hp, hcard, fun e => ?_, fun e => ?_, hb,
    fun e => ?_, (κT_spec hF).1, (κT_spec hF).2.1, hδ0, hδ1, ?_, ?_, ?_, fun a ha => ?_,
    fun e => ?_⟩
  · exact ⟨mT_pos (k - 1) e, (mT_le_M (k - 1) e).trans hMU⟩
  · refine ⟨(fpHyp_gT (μin := μin) (k - 1)).pos e, (βT_le_four (k - 1) e).trans ?_⟩
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ gU μin k := two_pow _ _ (by omega)
  · obtain ⟨-, ht1⟩ := t_bounds (μin := μin) (k - 1) e
    obtain ⟨hb0, hb1, -⟩ := inv_βT_le (μin := μin) (k - 1) e
    refine ⟨ht1, ?_⟩
    rw [div_eq_mul_one_div]
    calc mT μin (k - 1) e * (1 / βT μin (k - 1) e)
        ≤ 2 ^ (8 * k) * 2 ^ (3 * k + 4) :=
          mul_le_mul ((mT_le_M (k - 1) e).trans hM) (hb1.trans h12ϖ) hb0.le (by positivity)
      _ = 2 ^ (11 * k + 4) := by rw [← pow_add]; ring_nf
      _ ≤ gU μin k := two_pow _ _ (by omega)
  · -- `|Λ'| = |δN − 1/3| ≤ N`
    unfold gΛ' ζ₁
    have h1 : δT μin * N ≤ N := by nlinarith
    have h2 : 0 ≤ δT μin * N := by positivity
    rw [abs_le]
    constructor <;> linarith
  · unfold gαΓ
    positivity
  · unfold gαΓ
    nlinarith
  · obtain ⟨h1, h2⟩ := hcap a ha
    refine ⟨h1, h2.trans ?_⟩
    have : 2 * Ω μin (k - 1) ≤ 2 ^ (11 * k + L + 3) := by
      rw [pow_succ]; linarith
    exact this.trans (two_pow _ _ (by omega))
  · refine (hω e).trans ?_
    have : 52 * Ω μin (k - 1) ≤ 2 ^ (11 * k + L + 8) := by
      have e1 : (2 : ℝ) ^ (11 * k + L + 8) = 64 * 2 ^ (11 * k + L + 2) := by
        rw [show 11 * k + L + 8 = 11 * k + L + 2 + 6 by ring, pow_add]; ring
      linarith
    exact this.trans (two_pow _ _ (by omega))

/-- The monotonicity facts `U ≤ U² ≤ U³ ≤ U³N`, `N ≤ U³N`, `UN ≤ U³N` and `U²N ≤ U³N` for
`U = gU ≥ 1` and `N ≥ 1` (not in the paper). -/
lemma gU_facts {k N : ℕ} (hN : 1 ≤ N) :
    1 ≤ gU μin k ∧ (1 : ℝ) ≤ N ∧ gU μin k ≤ gU μin k ^ 2 ∧ gU μin k ^ 2 ≤ gU μin k ^ 3 ∧
    gU μin k ^ 3 ≤ gU μin k ^ 3 * N ∧ (N : ℝ) ≤ gU μin k ^ 3 * N ∧
    gU μin k * N ≤ gU μin k ^ 3 * N ∧ gU μin k ^ 2 * N ≤ gU μin k ^ 3 * N := by
  have hU1 : (1 : ℝ) ≤ gU μin k := one_le_pow₀ (by norm_num)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hU3 : (1 : ℝ) ≤ gU μin k ^ 3 := one_le_pow₀ hU1
  have h12 : gU μin k ≤ gU μin k ^ 2 := le_self_pow₀ hU1 (by norm_num)
  have h23 : gU μin k ^ 2 ≤ gU μin k ^ 3 := pow_le_pow_right₀ hU1 (by norm_num)
  refine ⟨hU1, hn1, h12, h23, le_mul_of_one_le_right (by positivity) hn1,
    le_mul_of_one_le_left (by positivity) hU3,
    mul_le_mul_of_nonneg_right (h12.trans h23) (by positivity),
    mul_le_mul_of_nonneg_right h23 (by positivity)⟩

/-- The sums over subsets of `E` of nonnegative terms at most `c` are at most `Uc`, as `|E| ≤ U`
(not in the paper). -/
lemma gadget_sum_le {k : ℕ} (hF : InF μin k) {N : ℕ} (hN : 1 ≤ N) (S : Finset (Gr (k - 1)))
    (f : Gr (k - 1) → ℝ) (c : ℝ) (h0 : ∀ e, 0 ≤ f e) (h1 : ∀ e, f e ≤ c) (hc : 0 ≤ c) :
    0 ≤ ∑ e ∈ S, f e ∧ ∑ e ∈ S, f e ≤ gU μin k * c := by
  have hcard := (gadget_basic hF hN).2.2.2.2.2.2.2.2.1
  refine ⟨sum_nonneg fun e _ => h0 e, ?_⟩
  calc ∑ e ∈ S, f e ≤ ∑ e ∈ S, c := sum_le_sum fun e _ => h1 e
    _ = S.card * c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ gU μin k * c := by
        apply mul_le_mul_of_nonneg_right _ hc
        have : (S.card : ℝ) ≤ Fintype.card (Gr (k - 1)) := by exact_mod_cast card_le_univ S
        exact this.trans hcard

/-- `C_g = (q + κ)α_Γ ∈ (0, 2UN]`, `|f_c(S)| ≤ 3U³N` and `|y_e| ≤ 2U³N` (not in the paper: the
magnitudes of part (4) of the proof of `thm:gadget`, `f_c = g + Λ't − Θβ⁻¹`). -/
lemma gadget_mag_fc {k : ℕ} (hF : InF μin k) {N : ℕ} (hN : 1 ≤ N) :
    0 < gC μin k N ∧ gC μin k N ≤ 2 * gU μin k * N ∧
    (∀ S, |gfc μin k N S| ≤ 3 * (gU μin k ^ 3 * N)) ∧
    ∀ e, |gadgetY μin k N e| ≤ 2 * (gU μin k ^ 3 * N) := by
  obtain ⟨hU1, hg, hΘ, -, -, hq0, hq, -, -, -, -, hb, ht, hκ0, hκ1, -, -, hΛ', hαΓ0,
    hαΓ, -, -⟩ := gadget_basic hF hN
  obtain ⟨-, hn1, -, -, hU3n, -, hUn, hU2n⟩ := gU_facts (μin := μin) (k := k) hN
  have hU0 : (0 : ℝ) ≤ gU μin k := by linarith
  have hgS : ∀ S, |gT μin (k - 1) S| ≤ gU μin k := fun S => (le_gmax (μin := μin) k S).trans hg
  have ht0 : ∀ e, (0 : ℝ) ≤ mT μin (k - 1) e / βT μin (k - 1) e := fun e => by
    linarith [(ht e).1]
  refine ⟨mul_pos (by linarith) hαΓ0, ?_, fun S => ?_, fun e => ?_⟩
  · show (gq μin k + κT μin) * gαΓ μin N ≤ _
    have h1 : gq μin k + κT μin ≤ 2 * gU μin k := by linarith
    calc (gq μin k + κT μin) * gαΓ μin N ≤ (2 * gU μin k) * N :=
          mul_le_mul h1 hαΓ hαΓ0.le (by positivity)
      _ = 2 * gU μin k * N := by ring
  · obtain ⟨hs0, hs1⟩ := gadget_sum_le hF hN S _ _ ht0 (fun e => (ht e).2) hU0
    obtain ⟨hb0, hb1⟩ := gadget_sum_le hF hN S _ _ (fun e => (hb e).1.le) (fun e => (hb e).2) hU0
    have h1 : |gΛ' μin N * ∑ e ∈ S, mT μin (k - 1) e / βT μin (k - 1) e| ≤
        gU μin k ^ 2 * N := by
      rw [abs_mul, abs_of_nonneg hs0]
      calc |gΛ' μin N| * ∑ e ∈ S, mT μin (k - 1) e / βT μin (k - 1) e
          ≤ N * (gU μin k * gU μin k) := mul_le_mul hΛ' hs1 hs0 (by positivity)
        _ = gU μin k ^ 2 * N := by ring
    have h2 : |gΘ μin k * ∑ e ∈ S, 1 / βT μin (k - 1) e| ≤ gU μin k ^ 3 := by
      rw [abs_mul, abs_of_nonneg hb0]
      calc |gΘ μin k| * ∑ e ∈ S, 1 / βT μin (k - 1) e ≤ gU μin k * (gU μin k * gU μin k) :=
            mul_le_mul hΘ hb1 hb0 hU0
        _ = gU μin k ^ 3 := by ring
    have h3 : |gfc μin k N S| ≤ |gT μin (k - 1) S| +
        |gΛ' μin N * ∑ e ∈ S, mT μin (k - 1) e / βT μin (k - 1) e| +
        |gΘ μin k * ∑ e ∈ S, 1 / βT μin (k - 1) e| := by
      unfold gfc
      refine (abs_sub _ _).trans ?_
      gcongr
      exact abs_add_le _ _
    have h4 := hgS S
    have h5 : gU μin k ≤ gU μin k ^ 3 * N := by
      obtain ⟨-, -, h12, h23, h3n, -, -, -⟩ := gU_facts (μin := μin) (k := k) hN
      linarith
    linarith
  · have h1 : |gΛ' μin N * (mT μin (k - 1) e / βT μin (k - 1) e)| ≤ gU μin k * N := by
      rw [abs_mul, abs_of_nonneg (ht0 e)]
      calc |gΛ' μin N| * (mT μin (k - 1) e / βT μin (k - 1) e) ≤ N * gU μin k :=
            mul_le_mul hΛ' (ht e).2 (ht0 e) (by positivity)
        _ = gU μin k * N := by ring
    have h2 : |gΘ μin k * (1 / βT μin (k - 1) e)| ≤ gU μin k ^ 2 := by
      rw [abs_mul, abs_of_pos (hb e).1]
      calc |gΘ μin k| * (1 / βT μin (k - 1) e) ≤ gU μin k * gU μin k :=
            mul_le_mul hΘ (hb e).2 (hb e).1.le hU0
        _ = gU μin k ^ 2 := by ring
    have h3 : |gadgetY μin k N e| ≤ |gΛ' μin N * (mT μin (k - 1) e / βT μin (k - 1) e)| +
        |gΘ μin k * (1 / βT μin (k - 1) e)| := by
      unfold gadgetY
      exact abs_sub _ _
    have h5 : gU μin k ^ 2 ≤ gU μin k ^ 3 * N := by
      obtain ⟨-, -, -, h23, h3n, -, -, -⟩ := gU_facts (μin := μin) (k := k) hN
      linarith
    linarith

/-- `|p| ≤ 6U³N` for `p = p_{k−1} − qΛ' + Λ'm^⊤t − Θt(E) + C_g` (not in the paper: the magnitudes
of part (4) of the proof of `thm:gadget`). -/
lemma gadget_mag_p {k : ℕ} (hF : InF μin k) {N : ℕ} (hN : 1 ≤ N) :
    |gp μin k N| ≤ 6 * (gU μin k ^ 3 * N) := by
  obtain ⟨hU1, -, hΘ, -, -, hq0, hq, hp, -, hm, -, -, ht, -, -, -, -, hΛ', -, -, -, -⟩ :=
    gadget_basic hF hN
  obtain ⟨-, hn1, h12, h23, hU3n, -, hUn, -⟩ := gU_facts (μin := μin) (k := k) hN
  obtain ⟨hC0, hC, -, -⟩ := gadget_mag_fc hF hN
  have hU0 : (0 : ℝ) ≤ gU μin k := by linarith
  have ht0 : ∀ e, (0 : ℝ) ≤ mT μin (k - 1) e / βT μin (k - 1) e := fun e => by
    linarith [(ht e).1]
  obtain ⟨ht0', ht1⟩ := gadget_sum_le hF hN univ _ _ ht0 (fun e => (ht e).2) hU0
  obtain ⟨hmt0, hmt1⟩ := gadget_sum_le hF hN univ
    (fun e => mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e)) (gU μin k * gU μin k)
    (fun e => mul_nonneg (hm e).1.le (ht0 e))
    (fun e => mul_le_mul (hm e).2 (ht e).2 (ht0 e) hU0) (by positivity)
  have h1 : |gq μin k * gΛ' μin N| ≤ gU μin k * N := by
    rw [abs_mul, abs_of_pos hq0]
    exact mul_le_mul hq hΛ' (abs_nonneg _) hU0
  have h2 : |gΛ' μin N * ∑ e, mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e)| ≤
      gU μin k ^ 3 * N := by
    rw [abs_mul, abs_of_nonneg hmt0]
    calc |gΛ' μin N| * ∑ e, mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e)
        ≤ N * (gU μin k * (gU μin k * gU μin k)) := mul_le_mul hΛ' hmt1 hmt0 (by positivity)
      _ = gU μin k ^ 3 * N := by ring
  have h3 : |gΘ μin k * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e| ≤ gU μin k ^ 3 := by
    rw [abs_mul, abs_of_nonneg ht0']
    calc |gΘ μin k| * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e
        ≤ gU μin k * (gU μin k * gU μin k) := mul_le_mul hΘ ht1 ht0' hU0
      _ = gU μin k ^ 3 := by ring
  have h4 : |gp μin k N| ≤ |(lvl μin (k - 1)).p| + |gq μin k * gΛ' μin N| +
      |gΛ' μin N * ∑ e, mT μin (k - 1) e * (mT μin (k - 1) e / βT μin (k - 1) e)| +
      |gΘ μin k * ∑ e, mT μin (k - 1) e / βT μin (k - 1) e| + |gC μin k N| := by
    unfold gp
    refine (abs_add_le _ _).trans ?_
    gcongr
    refine (abs_sub _ _).trans ?_
    gcongr
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_sub _ _
  rw [abs_of_pos hC0] at h4
  have h5 : gU μin k ≤ gU μin k ^ 3 * N := (h12.trans h23).trans hU3n
  have h6 : 2 * gU μin k * N ≤ 2 * (gU μin k ^ 3 * N) := by linarith
  linarith

/-- The magnitudes of the numbers of the output: all of them are at most `8U³N`, `U = gU`, and
`C_g > 0` (not in the paper: part (4) of the proof of `thm:gadget` says that each number "is a sum
of `O(|E|)` products of at most three of the numbers" above, and "So their denominators divide a
common integer with `O(k + log μ^in_k + log N)` bits, and so do their magnitudes"; `β_{e_g}` and
`Λ` are quotients, the second-to-last conjunct is the numerator of `Λ`). -/
lemma gadget_mag {k : ℕ} (hF : InF μin k) {N : ℕ} (hN : 1 ≤ N) :
    |gΘ μin k| ≤ 8 * gU μin k ^ 3 * N ∧ |gΛ' μin N| ≤ 8 * gU μin k ^ 3 * N ∧
    |gαΓ μin N| ≤ 8 * gU μin k ^ 3 * N ∧ |gC μin k N| ≤ 8 * gU μin k ^ 3 * N ∧
    |gp μin k N| ≤ 8 * gU μin k ^ 3 * N ∧ |gq μin k| ≤ 8 * gU μin k ^ 3 * N ∧
    |δT μin| ≤ 8 * gU μin k ^ 3 * N ∧ |κT μin| ≤ 8 * gU μin k ^ 3 * N ∧
    |(gNmin μin k : ℝ)| ≤ 8 * gU μin k ^ 3 * N ∧
    (∀ e, |gadgetM μin k e| ≤ 8 * gU μin k ^ 3 * N) ∧
    (∀ e, |βT μin (k - 1) e| ≤ 8 * gU μin k ^ 3 * N) ∧
    (∀ e, |mT μin (k - 1) e / βT μin (k - 1) e| ≤ 8 * gU μin k ^ 3 * N) ∧
    (∀ S, |gfc μin k N S| ≤ 8 * gU μin k ^ 3 * N) ∧
    (∀ T, |gadgetF μin k N T| ≤ 8 * gU μin k ^ 3 * N) ∧
    (∀ a ∈ (gadgetForm μin k N).D, |(gadgetForm μin k N).cap a| ≤ 8 * gU μin k ^ 3 * N) ∧
    (∀ e, |(gadgetForm μin k N).ω e| ≤ 8 * gU μin k ^ 3 * N) ∧
    (∀ e, |gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ + gT μin (k - 1) (univ.erase e)| ≤
      8 * gU μin k ^ 3 * N) ∧
    0 < gC μin k N := by
  obtain ⟨hU1, hg, hΘ, -, -, hq0, hq, -, -, hm, hβ, hb, ht, hκ0, hκ1, hδ0, hδ1, hΛ', hαΓ0,
    hαΓ, hcap, hω⟩ := gadget_basic hF hN
  obtain ⟨-, hn1, h12, h23, hU3n, hnU, hUn, hU2n⟩ := gU_facts (μin := μin) (k := k) hN
  obtain ⟨hC0, hC, hfc, hY⟩ := gadget_mag_fc hF hN
  have hpm := gadget_mag_p hF hN
  obtain ⟨-, -, hNmin⟩ := gNmin_le hF
  have hW0 : (0 : ℝ) ≤ gU μin k ^ 3 * N := by positivity
  -- every bound below is at most `6U³N ≤ 8U³N`
  have h8 : ∀ {y : ℝ}, |y| ≤ 6 * (gU μin k ^ 3 * N) → |y| ≤ 8 * gU μin k ^ 3 * N :=
    fun h => by linarith
  have hU : gU μin k ≤ gU μin k ^ 3 * N := (h12.trans h23).trans hU3n
  have hgS : ∀ S, |gT μin (k - 1) S| ≤ gU μin k := fun S => (le_gmax (μin := μin) k S).trans hg
  have hNm : (gNmin μin k : ℝ) ≤ 8 * gU μin k ^ 2 := by
    have e1 : (2 : ℝ) ^ (2 * (20 * k + Nat.log 2 (μin (k - 1)) + 20) + 3) =
        8 * gU μin k ^ 2 := by
      unfold gU
      rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      ring
    linarith
  have mΘ : |gΘ μin k| ≤ 8 * gU μin k ^ 3 * N := h8 (by linarith)
  have mΛ' : |gΛ' μin N| ≤ 8 * gU μin k ^ 3 * N := h8 (by linarith)
  have mαΓ : |gαΓ μin N| ≤ 8 * gU μin k ^ 3 * N := h8 (by rw [abs_of_pos hαΓ0]; linarith)
  have mC : |gC μin k N| ≤ 8 * gU μin k ^ 3 * N := h8 (by rw [abs_of_pos hC0]; linarith)
  have mq : |gq μin k| ≤ 8 * gU μin k ^ 3 * N := h8 (by rw [abs_of_pos hq0]; linarith)
  have mδ : |δT μin| ≤ 8 * gU μin k ^ 3 * N := h8 (by rw [abs_of_pos hδ0]; linarith)
  have mκ : |κT μin| ≤ 8 * gU μin k ^ 3 * N := h8 (by rw [abs_of_pos hκ0]; linarith)
  have mN : |(gNmin μin k : ℝ)| ≤ 8 * gU μin k ^ 3 * N := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have : gU μin k ^ 2 ≤ gU μin k ^ 3 * N := h23.trans hU3n
    linarith
  have mM : ∀ e, |gadgetM μin k e| ≤ 8 * gU μin k ^ 3 * N := fun e => by
    rcases e with e | u
    · show |mT μin (k - 1) e| ≤ _
      exact h8 (by rw [abs_of_pos (hm e).1]; linarith [(hm e).2])
    · show |(1 : ℝ)| ≤ _
      exact h8 (by rw [abs_one]; linarith)
  have mβ : ∀ e, |βT μin (k - 1) e| ≤ 8 * gU μin k ^ 3 * N := fun e =>
    h8 (by rw [abs_of_pos (hβ e).1]; linarith [(hβ e).2])
  have mt : ∀ e, |mT μin (k - 1) e / βT μin (k - 1) e| ≤ 8 * gU μin k ^ 3 * N := fun e => by
    have ht0 : (0 : ℝ) ≤ mT μin (k - 1) e / βT μin (k - 1) e := by linarith [(ht e).1]
    exact h8 (by rw [abs_of_nonneg ht0]; linarith [(ht e).2])
  have mfc : ∀ S, |gfc μin k N S| ≤ 8 * gU μin k ^ 3 * N := fun S => h8 (by linarith [hfc S])
  have mF : ∀ T, |gadgetF μin k N T| ≤ 8 * gU μin k ^ 3 * N := fun T => by
    show |gfc μin k N T.toLeft + single (gC μin k N) T.toRight| ≤ _
    have hs : |single (gC μin k N) T.toRight| ≤ 2 * gU μin k * N := by
      unfold single
      split_ifs
      · rw [abs_of_pos hC0]; exact hC
      · rw [abs_zero]; positivity
    refine h8 ((abs_add_le _ _).trans ?_)
    linarith [hfc T.toLeft]
  have mcap : ∀ a ∈ (gadgetForm μin k N).D,
      |(gadgetForm μin k N).cap a| ≤ 8 * gU μin k ^ 3 * N := fun a ha => by
    obtain ⟨a', ha', h⟩ := gadgetForm_cap (μin := μin) k N ha
    rw [h]
    exact h8 (by rw [abs_of_nonneg (hcap a' ha').1]; linarith [(hcap a' ha').2])
  have mω : ∀ e, |(gadgetForm μin k N).ω e| ≤ 8 * gU μin k ^ 3 * N := fun e => by
    rcases e with e | u
    · show |(formT μin (k - 1)).ω e + gadgetY μin k N e| ≤ _
      refine h8 ((abs_add_le _ _).trans ?_)
      linarith [hω e, hY e]
    · show |gC μin k N| ≤ _
      exact mC
  have mnum : ∀ e, |gΘ μin k / βT μin (k - 1) e - gT μin (k - 1) univ +
      gT μin (k - 1) (univ.erase e)| ≤ 8 * gU μin k ^ 3 * N := fun e => by
    have h1 : |gΘ μin k / βT μin (k - 1) e| ≤ gU μin k ^ 2 := by
      rw [div_eq_mul_one_div, abs_mul, abs_of_pos (hb e).1]
      calc |gΘ μin k| * (1 / βT μin (k - 1) e) ≤ gU μin k * gU μin k :=
            mul_le_mul hΘ (hb e).2 (hb e).1.le (by linarith)
        _ = gU μin k ^ 2 := by ring
    have h2 := abs_sub (gΘ μin k / βT μin (k - 1) e) (gT μin (k - 1) univ)
    have h3 : gU μin k ^ 2 ≤ gU μin k ^ 3 * N := h23.trans hU3n
    refine h8 ((abs_add_le _ _).trans ?_)
    linarith [hgS univ, hgS (univ.erase e)]
  exact ⟨mΘ, mΛ', mαΓ, mC, h8 hpm, mq, mδ, mκ, mN, mM, mβ, mt, mfc, mF, mcap, mω, mnum, hC0⟩

/-- A number of the output with a denominator dividing `𝔇g` and magnitude at most `8U³N` has at
most `100(k + L + ⌊log₂ N⌋ + 1)` bits, `L = ⌊log₂ μ^in_k⌋` (not in the paper: `𝔇g ≤ 2^{11k+3L+73}`
and `8U³N ≤ 2^{60k+3L+⌊log₂ N⌋+64}`). -/
lemma gadget_bits {k : ℕ} (hF : InF μin k) {N : ℕ} {x : ℝ} (hx : InZ (𝔇g μin k) x)
    (hmag : |x| ≤ 8 * gU μin k ^ 3 * N) :
    Bits (100 * (k + Nat.log 2 (μin (k - 1)) + Nat.log 2 N + 1)) x := by
  set L := Nat.log 2 (μin (k - 1))
  set LN := Nat.log 2 N
  have two_pow : ∀ a b : ℕ, a ≤ b → (2 : ℝ) ^ a ≤ 2 ^ b := fun a b h =>
    pow_le_pow_right₀ (by norm_num) h
  obtain ⟨hpos, hle⟩ := 𝔇g_le hF
  have hNle : (N : ℝ) ≤ 2 ^ (LN + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
    exact_mod_cast this.le
  have hk1 := hF.1
  refine bits_of (𝔇g μin k) rfl hpos hx (hle.trans (two_pow _ _ (by omega))) (hmag.trans ?_)
  calc 8 * gU μin k ^ 3 * N ≤ 2 ^ 3 * (2 ^ (20 * k + L + 20)) ^ 3 * 2 ^ (LN + 1) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
        exact mul_le_mul_of_nonneg_left hNle (by unfold gU; positivity)
    _ = 2 ^ (60 * k + 3 * L + LN + 64) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
    _ ≤ 2 ^ (100 * (k + L + LN + 1)) := two_pow _ _ (by omega)

variable (μin) in
/-- The numbers computed for the output `I(μ^in, N)` (`thm:gadget`, "All numbers computed"; part
(4) of its proof: "The numbers of the output are the rewards and curvatures (among them
`β_{e_g} = 1/(q + κ)` of `e_g`), the values of `f_c`, the capacities and weights of its cut form,
`C_g`, `p`, `q`, `δ` and `κ`"), with `N_min`, `Θ`, `Λ`, `Λ' = δN − ζ_1` and `α_Γ = δN`, which the
algorithm computes on the way, and the values of the output's rank function. The numbers of the
parameter rule and the values of `g` are those of `lem:sizes` (`sizes`). -/
def GadgetNumber (k N : ℕ) (x : ℝ) : Prop :=
  x = gNmin μin k ∨ x = gΘ μin k ∨ x = gΛ μin k ∨ x = gΛ' μin N ∨ x = gαΓ μin N ∨
    x = gC μin k N ∨ x = gp μin k N ∨ x = gq μin k ∨ x = δT μin ∨ x = κT μin ∨
    (∃ e, x = gadgetM μin k e) ∨ (∃ e, x = gadgetB μin k N e) ∨ (∃ S, x = gfc μin k N S) ∨
    (∃ T, x = gadgetF μin k N T) ∨
    (∃ a ∈ (gadgetForm μin k N).D, x = (gadgetForm μin k N).cap a) ∨
    ∃ e, x = (gadgetForm μin k N).ω e

/-- **The sizes in `thm:gadget`** (`stoc-sections/appD-hardness.tex:198`, "All numbers computed have
`O(k + log μ^in_k + log N)` bits", and part (4) of the proof, lines 1750-1783): for `μ^in ∈ 𝔉` of
length `k` and an integer `N ≥ N_min`, every number of the output `I(μ^in, N)` and of its cut form
(`GadgetNumber`, with `N_min`, `Θ`, `Λ`, `Λ'` and `α_Γ`) is a rational whose magnitude and
denominator are at most `2^B` with `B = 300(k + ⌊log₂ μ^in_k⌋ + ⌊log₂ N⌋ + 1)` (`Bits`), as
`lem:sizes` (`sizes`) says for the numbers of the parameter rule and the values of `g`.

The proof's steps: (1) the output has a cut form, computed along the construction (`formT`,
`gadgetForm`, `gadgetForm_fn`); (2) "For the sizes, `lem:sizes` applies to `g`, `m` and `β`"
(`level_bounds`, `level_pow`); (3) "`|Θ| ≤ M_{k−1} + 4 max_{S⊆E} |g(S)|` … and
`Λ ≤ 12ϖ_{k−1}|Θ| + 2 max_{S⊆E} |g(S)|` …. Also `Λ' ≤ δN`. So `N_min` has `O(k + log μ^in_k)`
bits" (`gΘ_le`, `gΛ_le`, `gΛ'_le`, `gNmin_le`); (4) the denominators of `ζ_1`, the rewards, `β_e`,
`Θ`, `t_e`, `1/β_e`, `Λ'` and `κ` (`gadget_items`); (5) "Apart from `β_{e_g}`, each of them is a
sum of `O(|E|)` products of at most three of the numbers …. So their denominators divide a
common integer with `O(k + log μ^in_k + log N)` bits, and so do their magnitudes" (`𝔇g`, `𝔇g_le`,
`gadget_den`, `gadget_mag`, `gadget_bits`); (6) "Hence every number of the output, `β_{e_g}`
included, has `O(k + log μ^in_k + log N)` bits" (`β_{e_g} = α_Γ/C_g` and `Λ`, a quotient by `t_e`,
by `Bits.div`). The count of the evaluations of `g` is `gadget_evals`; that the algorithm runs in
polynomial time is not formalised (Turing machines and arithmetic operations are not). -/
theorem gadget_sizes {k : ℕ} (hF : InF μin k) {N : ℕ} (hN : gNmin μin k ≤ N) (x : ℝ)
    (hx : GadgetNumber μin k N x) :
    Bits (300 * (k + Nat.log 2 (μin (k - 1)) + Nat.log 2 N + 1)) x := by
  -- (1) "By `prop:base` and `lem:cutforms`(c), the output has a cut form, computed along the
  -- construction." (`gadgetForm`, `gadgetForm_fn`; its capacities and weights are numbers of
  -- `GadgetNumber`)
  -- (2) "For the sizes, `lem:sizes` applies to `g`, `m` and `β`." (`level_bounds`, `level_pow`,
  -- in the lemmas below)
  -- (3) "Moreover, `|Θ| ≤ M_{k−1} + 4 max_{S⊆E} |g(S)|`, since `ζ_1 < 1` and `β_e ≤ 4`, and
  -- `Λ ≤ 12ϖ_{k−1}|Θ| + 2 max_{S⊆E} |g(S)|`, since `1/β_e ≤ 12ϖ_{k−1}` and `t_e ≥ 1`. Also
  -- `Λ' ≤ δN`. So `N_min` has `O(k + log μ^in_k)` bits." (`gΘ_le`, `gΛ_le`, `gΛ'_le` in
  -- `gadget_mag`, and `gNmin_le`)
  have hN1 : 1 ≤ N := (gNmin_le hF).1.trans hN
  set B := 100 * (k + Nat.log 2 (μin (k - 1)) + Nat.log 2 N + 1) with hBdef
  have hB : 300 * (k + Nat.log 2 (μin (k - 1)) + Nat.log 2 N + 1) = 3 * B := by
    rw [hBdef]; ring
  rw [hB]
  -- (4) "For the denominators, `ζ_1 = 1/3`, all rewards are integers and `β_e ∈ (1/(9·8^k))ℤ`, so
  -- `Θ ∈ (1/(9·8^k𝔇_{k−1}))ℤ` with `𝔇_{k−1}` from the proof of `lem:sizes`. Moreover, `2t_e ∈ ℤ`
  -- (the dummies `τ_{1,1}` and `τ_{2,1}` have `t_e = 9/2`), `1/β_e ∈ (1/4)ℤ`,
  -- `Λ' = δN − 1/3 ∈ (δ/3)ℤ` and `κ ∈ (1/10)ℤ`." (`gadget_items`, in `gadget_den`)
  -- (5) "The numbers of the output are the rewards and curvatures (among them
  -- `β_{e_g} = 1/(q + κ)` of `e_g`), the values of `f_c`, the capacities and weights of its cut
  -- form, `C_g`, `p`, `q`, `δ` and `κ`. Apart from `β_{e_g}`, each of them is a sum of `O(|E|)`
  -- products of at most three of the numbers `Θ`, `Λ'`, `κ`, `α_Γ = δN`, values of `g`, numbers
  -- of the parameter rule, rewards, `1/β_e` and `t_e`. So their denominators divide a common
  -- integer with `O(k + log μ^in_k + log N)` bits, and so do their magnitudes." (`GadgetNumber`;
  -- the common integer `𝔇g` in `gadget_den`, the magnitudes in `gadget_mag`, and `gadget_bits`)
  obtain ⟨dΘ, dΛ', dαΓ, dC, dp, dq, dδ', dκ, dN, dM, dβ, dt, dfc, dF, dcap, dω, dnum⟩ :=
    gadget_den hF N
  obtain ⟨mΘ, mΛ', mαΓ, mC, mp, mq, mδ, mκ, mN, mM, mβ, mt, mfc, mF, mcap, mω, mnum, hC0⟩ :=
    gadget_mag hF hN1
  have prim : ∀ {y : ℝ}, InZ (𝔇g μin k) y → |y| ≤ 8 * gU μin k ^ 3 * N → Bits B y :=
    fun hy hm => gadget_bits hF hy hm
  have prim3 : ∀ {y : ℝ}, InZ (𝔇g μin k) y → |y| ≤ 8 * gU μin k ^ 3 * N → Bits (3 * B) y :=
    fun hy hm => (prim hy hm).mono (by omega)
  -- (6) "Hence every number of the output, `β_{e_g}` included, has `O(k + log μ^in_k + log N)`
  -- bits." (`β_{e_g} = α_Γ/C_g` and `Λ`, a quotient by `t_e`, by `Bits.div`)
  rcases hx with h | h | h | h | h | h | h | h | h | h | ⟨e, h⟩ | ⟨e, h⟩ | ⟨S, h⟩ | ⟨T, h⟩ |
    ⟨a, ha, h⟩ | ⟨e, h⟩ <;> rw [h]
  · exact prim3 dN mN
  · exact prim3 dΘ mΘ
  · -- `Λ`: `0`, or the quotient of a number of `(1/𝔇g)ℤ` by `t_e ≥ 1`
    rcases (gΛ_eq (μin := μin) k).2 with h0 | ⟨e, he⟩
    · rw [h0]
      exact prim3 InZ.zero (by rw [abs_zero]; unfold gU; positivity)
    · rw [he]
      have ht1 := (t_bounds (μin := μin) (k - 1) e).2
      exact (prim (dnum e) (mnum e)).div (prim (dt e) (mt e)) (by linarith)
  · exact prim3 dΛ' mΛ'
  · exact prim3 dαΓ mαΓ
  · exact prim3 dC mC
  · exact prim3 dp mp
  · exact prim3 dq mq
  · exact prim3 dδ' mδ
  · exact prim3 dκ mκ
  · exact prim3 (dM e) (mM e)
  · -- the curvatures: `β_e` on `E`, and `β_{e_g} = α_Γ/C_g`
    rcases e with e | u
    · exact prim3 (dβ e) (mβ e)
    · exact (prim dαΓ mαΓ).div (prim dC mC) hC0.ne'
  · exact prim3 (dfc S) (mfc S)
  · exact prim3 (dF T) (mF T)
  · exact prim3 (dcap a ha) (mcap a ha)
  · exact prim3 (dω e) (mω e)

/-- The sets at which the algorithm evaluates `g` for `Θ` and `Λ`: `E`, `E ∖ {e}` and `{e}`. -/
def gQueries (k : ℕ) : Finset (Finset (Gr (k - 1))) :=
  insert univ ((univ.image fun e => univ.erase e) ∪ univ.image fun e => {e})

/-- The proof of `thm:gadget` (part (4)): "The values `g(E)`, `g(E ∖ {e})` and `g({e})` needed for
`Θ` and `Λ` are `2|E| + 1` evaluations of `g`": there are at most `2|E| + 1` such sets
(`gQueries`), and `Θ` and `Λ` are the same for every function that agrees with `g` on them. -/
theorem gadget_evals (k : ℕ) :
    (gQueries k).card ≤ 2 * Fintype.card (Gr (k - 1)) + 1 ∧
    ∀ g' : Finset (Gr (k - 1)) → ℝ, (∀ S ∈ gQueries k, g' S = gT μin (k - 1) S) →
      gΘ μin k = univ.sup' univ_nonempty (fun e =>
        βT μin (k - 1) e * g' {e} - ζ₁ * mT μin (k - 1) e) ∧
      gΛ μin k = max 0 (univ.sup' univ_nonempty fun e =>
        (gΘ μin k / βT μin (k - 1) e - g' univ + g' (univ.erase e)) /
          (mT μin (k - 1) e / βT μin (k - 1) e)) := by
  refine ⟨?_, fun g' hg' => ⟨?_, ?_⟩⟩
  · unfold gQueries
    calc _ ≤ ((univ.image fun e => univ.erase e) ∪
          univ.image fun e => ({e} : Finset (Gr (k - 1)))).card + 1 := card_insert_le _ _
      _ ≤ (univ.image fun e => univ.erase e).card +
          (univ.image fun e => ({e} : Finset (Gr (k - 1)))).card + 1 := by
          gcongr
          exact card_union_le _ _
      _ ≤ Fintype.card (Gr (k - 1)) + Fintype.card (Gr (k - 1)) + 1 := by
          gcongr <;> exact card_image_le.trans_eq card_univ
      _ = 2 * Fintype.card (Gr (k - 1)) + 1 := by ring
  · unfold gΘ
    refine sup'_congr _ rfl fun e _ => ?_
    rw [hg' {e} (mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (mem_univ e))))]
  · unfold gΛ
    congr 1
    refine sup'_congr _ rfl fun e _ => ?_
    rw [hg' univ (mem_insert_self _ _),
      hg' (univ.erase e) (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_univ e))))]

end

end Hardness

end Stoc
