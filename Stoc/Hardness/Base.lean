-- stamp r9 2026-11-02
import Stoc.Hardness.CutForms
import Stoc.Hardness.Combs

/-!
# The base

The STOC version's `prop:base` (Appendix C.5, `sec:D-base`, "The base",
`stoc-sections/appD-hardness.tex`: the statement at lines 457-500, the proof at lines 502-549).

On `E₀ = {C₀, C₁, C₂}` (here `0, 1, 2 : Fin 3`) with `m = (5, 12, 4)` and `β = (1, 4, 4)`, the set
function `f₀` is given by its eight values (`Base.f₀`). The proposition says that `f₀` is a
polymatroid rank function, given by the cut form with the arcs `C₀ → C₁` (capacity `1/3`) and
`C₁ → C₂` (capacity `1/2`) and the weights `0, 2/3, 2/3` (`Base.form`), gives the marginals
`ρ = ρ^{f₀}` and the reward `r(ξ^{(0)}(α))` of its full-plane best response on five pieces (the
rows `Base.row₁`, …, `Base.row₅`), and states (B1)–(B3).

* `base`: `prop:base`, all parts.
* `base_step1`, `base_table`, `base_gap_pieces`: the steps (1) and (2) of its proof and the
  differences of step (3), in our numbering of the proof's three paragraphs ("We first show that
  the cut form gives `f₀`", "Next we show that the rows of the table are the full-plane
  marginals", "Finally, we derive (B1)–(B3)").

The gap `L(α) − r(ξ^g(α))` of `def:tower` is `Stoc.Hardness.gap`, defined here, where it is first
used; the constants `ζ_1`, `ζ_2`, `L_0 = p_0 + q_0 α`, `ε_0` and `R_0` of `prop:base` are `ζ₁`,
`ζ₂`, `L₀` (with `p₀`, `q₀`), `ε₀` and `R0`.

Taken over on 2026-10-20 from `Paper/Hardness/Base.lean` and `Paper/Hardness/BaseCert.lean` (the
paper at Overleaf f035b19) for the STOC version (`stoc.tex`); from then on this copy follows the
STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

/-- The gap `L(α) − r(ξ^g(α))` of the line `L(α) = p + qα` over the reward of the full-plane best
response of `g` (`def:tower`: "We call `L_j(α) − r(ξ^{(j)}(α))` the gap of level `j` at `α`"). -/
def gap {E : Type*} [Fintype E] (g : Finset E → ℝ) (m β : E → ℝ) (p q α : ℝ) : ℝ :=
  p + q * α - curve g m β α

/-! ### The constants of `prop:base` -/

/-- `ζ_1 = 1/3`, the first contact of the base. -/
def ζ₁ : ℝ := 1 / 3

/-- `ζ_2 = 2/3`, the second contact of the base. -/
def ζ₂ : ℝ := 2 / 3

/-- `p_0 = 10`. -/
def p₀ : ℝ := 10

/-- `q_0 = 7`. -/
def q₀ : ℝ := 7

/-- The line `L_0(α) = p_0 + q_0 α` of the base. -/
def L₀ (α : ℝ) : ℝ := p₀ + q₀ * α

/-- `ε_0 = 1/30` (`prop:base`): the gap of the base is `ε_0` at `R_0 = ζ_1 − ε_0` and `7ε_0` at
`ζ_2 + ε_0`, and `R_1^{(j)}` lies `ε_0` above the largest contact of level `j` (`def:tower`). It is
an `abbrev`, so that `norm_num`, `ring` and `positivity` compute with its value. -/
abbrev ε₀ : ℝ := 1 / 30

lemma ε₀_pos : 0 < ε₀ := by norm_num

/-- `R_0 = ζ_1 − ε_0 = 3/10`, the left end of the windows (`prop:base`). -/
def R0 : ℝ := ζ₁ - ε₀

lemma R0_eq : R0 = 3 / 10 := by
  unfold R0 ζ₁
  norm_num

namespace Base

/-! ### The data -/

/-- The values of `f₀` by membership of `C₀`, `C₁`, `C₂`. -/
def tab : Bool → Bool → Bool → ℝ
  | false, false, false => 0
  | true, false, false => 1 / 3
  | false, true, false => 7 / 6
  | false, false, true => 2 / 3
  | true, true, false => 7 / 6
  | true, false, true => 1
  | false, true, true => 4 / 3
  | true, true, true => 4 / 3

/-- The set function `f₀` of `prop:base`: `f₀(∅) = 0`, `f₀(C₀) = 1/3`, `f₀(C₁) = 7/6`,
`f₀(C₂) = 2/3`, `f₀(C₀C₁) = 7/6`, `f₀(C₀C₂) = 1`, `f₀(C₁C₂) = 4/3`, `f₀(E₀) = 4/3`. -/
def f₀ (A : Finset (Fin 3)) : ℝ :=
  tab (decide (0 ∈ A)) (decide (1 ∈ A)) (decide (2 ∈ A))

/-- The rewards `m = (5, 12, 4)`. -/
def m : Fin 3 → ℝ := ![5, 12, 4]

/-- The curvatures `β = (1, 4, 4)`. -/
def β : Fin 3 → ℝ := ![1, 4, 4]

lemma β_pos : ∀ e, 0 < β e := by
  intro e; fin_cases e <;> simp [β]

/-- The cut form of `prop:base`: the arcs `C₀ → C₁` of capacity `1/3` and `C₁ → C₂` of capacity
`1/2`, and the weights `0, 2/3, 2/3` on `C₀, C₁, C₂`. -/
def form : CutForm (Fin 3) where
  D := {(0, 1), (1, 2)}
  loopless := by decide
  cap a := if a = (0, 1) then 1 / 3 else if a = (1, 2) then 1 / 2 else 0
  cap_nonneg a ha := by
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl <;> norm_num
  ω := ![0, 2 / 3, 2 / 3]

lemma sum_fin3 (A : Finset (Fin 3)) (y : Fin 3 → ℝ) :
    ∑ e ∈ A, y e =
      (if 0 ∈ A then y 0 else 0) + (if 1 ∈ A then y 1 else 0) + (if 2 ∈ A then y 2 else 0) := by
  have h : ∑ e ∈ A, y e = ∑ e, if e ∈ A then y e else 0 := by
    rw [sum_ite_mem, univ_inter]
  rw [h, Fin.sum_univ_three]

/-- The value of the cut form at `S`:
`ω(S) + (1/3)[C₀ ∈ S, C₁ ∉ S] + (1/2)[C₁ ∈ S, C₂ ∉ S]`. -/
lemma form_fn (S : Finset (Fin 3)) :
    form.fn S = ∑ e ∈ S, form.ω e + (if 0 ∈ S ∧ 1 ∉ S then 1 / 3 else 0) +
      (if 1 ∈ S ∧ 2 ∉ S then 1 / 2 else 0) := by
  unfold CutForm.fn CutForm.cut form
  dsimp only
  rw [sum_filter, sum_pair (by decide)]
  simp only [show ((1 : Fin 3), (2 : Fin 3)) ≠ (0, 1) by decide, ↓reduceIte]
  ring

/-! ### The cut form: step (1) of the proof -/

/-- Step (1) of the proof of `prop:base` (`stoc-sections/appD-hardness.tex:503-510`), "We first
show that the cut form gives `f₀`": the cut form gives the eight values of `f₀`, and as the weights
are at least the capacities entering their nodes, `f₀` is a polymatroid rank function by
`lem:cutforms`(b). -/
theorem base_step1 : (∀ S, f₀ S = form.fn S) ∧ IsRankFunction f₀ := by
  -- (1) "For `S ⊆ E₀`, the form gives the value
  -- `ω(S) + (1/3)[C₀ ∈ S, C₁ ∉ S] + (1/2)[C₁ ∈ S, C₂ ∉ S]`, where a bracket is `1` if the
  -- conditions in it hold and `0` otherwise. These eight values agree with `f₀`, for instance
  -- `f₀(C₀C₂) = 0 + 2/3 + 1/3 = 1`."
  have hval : ∀ S, f₀ S = form.fn S := by
    intro S
    rw [form_fn, sum_fin3]
    unfold f₀
    by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
      by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2, tab, form] <;> norm_num
  refine ⟨hval, ?_⟩
  -- "The weights `0, 2/3, 2/3` are at least the capacities `0, 1/3, 1/2` of the arcs entering
  -- `C₀, C₁, C₂`, so `f₀` is a polymatroid rank function by `lem:cutforms`(b)."
  have hin : ∀ e, ∑ a ∈ form.D with a.2 = e, form.cap a ≤ form.ω e := by
    intro e
    simp only [form, sum_filter, sum_pair (show ((0 : Fin 3), (1 : Fin 3)) ≠ (1, 2) by decide)]
    fin_cases e <;> simp <;> norm_num
  have hf : f₀ = form.fn := funext hval
  rw [hf]
  exact (cutforms_b form).2 hin

lemma fpHyp_f₀ : FPHyp f₀ β :=
  ⟨base_step1.2.submod, base_step1.2.empty, β_pos⟩

/-! ### The table: step (2) of the proof -/

/-- The first row of the table, on `(−∞, −1/6]`: `ρ = (5α − 1/3, 12α − 4/3, 4α − 8/3)`. -/
def row₁ (α : ℝ) : Fin 3 → ℝ := ![5 * α - 1 / 3, 12 * α - 4 / 3, 4 * α - 8 / 3]

/-- The second row, on `[−1/6, 1/3]`: `ρ = (5α − 1/3, 8α − 2, 8α − 2)`. -/
def row₂ (α : ℝ) : Fin 3 → ℝ := ![5 * α - 1 / 3, 8 * α - 2, 8 * α - 2]

/-- The third row, on `[1/3, 3/7]`: `ρ = (5α − 1/3, 12α − 10/3, 4α − 2/3)`. -/
def row₃ (α : ℝ) : Fin 3 → ℝ := ![5 * α - 1 / 3, 12 * α - 10 / 3, 4 * α - 2 / 3]

/-- The fourth row, on `[3/7, 2/3]`: `ρ = (32α/5 − 14/15, 32α/5 − 14/15, 4α − 2/3)`. -/
def row₄ (α : ℝ) : Fin 3 → ℝ :=
  ![32 * α / 5 - 14 / 15, 32 * α / 5 - 14 / 15, 4 * α - 2 / 3]

/-- The fifth row, on `[2/3, ∞)`: `ρ = (5α, 12α − 14/3, 4α − 2/3)`. -/
def row₅ (α : ℝ) : Fin 3 → ℝ := ![5 * α, 12 * α - 14 / 3, 4 * α - 2 / 3]

/-- `y = αt − ρ(α)/β` (componentwise), for a row `ρ` of the table. -/
def yOf (ρ : Fin 3 → ℝ) (α : ℝ) : Fin 3 → ℝ := fun e => α * (m e / β e) - ρ e / β e

/-- The marginals of `y = αt − ρ/β` at the share `α` are `ρ`. -/
lemma marg_yOf (ρ : Fin 3 → ℝ) (α : ℝ) (e : Fin 3) : marg m β α (yOf ρ α) e = ρ e := by
  have := (β_pos e).ne'
  unfold marg yOf
  field_simp
  ring

/-- On a bounded piece `[a, b]`, `y(α)` is affine in `α`, so if `y(S) ≤ f₀(S)` for all `S` at both
end points, then at every point of `[a, b]` (the check at the end points in step (2) of the proof of
`prop:base`): `y(α)` is a convex combination of `y(a)` and `y(b)`. -/
lemma mem_fpPoly_of_ends {y : ℝ → Fin 3 → ℝ} (hy : ∀ α e, y α e = y 0 e + α * (y 1 e - y 0 e))
    {a b α : ℝ} (hab : a < b) (ha : y a ∈ fpPoly f₀) (hb : y b ∈ fpPoly f₀) (h1 : a ≤ α)
    (h2 : α ≤ b) : y α ∈ fpPoly f₀ := by
  intro S
  set t := (α - a) / (b - a)
  have hba : 0 < b - a := sub_pos.2 hab
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 h1) hba.le
  have ht1 : t ≤ 1 := (div_le_one hba).2 (by linarith)
  have hcomb : ∀ e, y α e = (1 - t) * y a e + t * y b e := by
    intro e
    rw [hy α e, hy a e, hy b e]
    simp only [t]
    field_simp
    ring
  have hsum : ∑ e ∈ S, y α e = (1 - t) * ∑ e ∈ S, y a e + t * ∑ e ∈ S, y b e := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => hcomb e
  rw [hsum]
  have := mul_le_mul_of_nonneg_left (ha S) (sub_nonneg.2 ht1)
  have := mul_le_mul_of_nonneg_left (hb S) ht0
  linarith

/-- On a bounded piece `[a, b]`, `y(α)` is affine in `α`, so a sum `y(S)` that has the same value
`c` at both end points has it at every `α` (the check at the end points in step (2) of the proof of
`prop:base`, for `y(E₀) = 4/3` and for the tightness of the listed level sets). -/
lemma sum_eq_of_ends {y : ℝ → Fin 3 → ℝ} (hy : ∀ α e, y α e = y 0 e + α * (y 1 e - y 0 e))
    {a b c : ℝ} (hab : a < b) (S : Finset (Fin 3)) (ha : ∑ e ∈ S, y a e = c)
    (hb : ∑ e ∈ S, y b e = c) (α : ℝ) : ∑ e ∈ S, y α e = c := by
  have h : ∀ x, ∑ e ∈ S, y x e = ∑ e ∈ S, y 0 e + x * ∑ e ∈ S, (y 1 e - y 0 e) := fun x => by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => hy x e
  rw [h] at ha hb ⊢
  have h0 : (b - a) * ∑ e ∈ S, (y 1 e - y 0 e) = 0 := by linarith
  have h1 : ∑ e ∈ S, (y 1 e - y 0 e) = 0 :=
    (mul_eq_zero.1 h0).resolve_left (sub_pos.2 hab).ne'
  rw [h1] at ha ⊢
  linarith

/-- The level criterion for `f₀` at a share `α`, with the candidate `y = αt − ρ/β`: if
`y(S) ≤ f₀(S)` for all `S` and every upper level set of `ρ` is tight for `y`, then `y = ξ^{(0)}(α)`
(`lem:fullplane`(a)). -/
lemma xi_of_row {ρ : Fin 3 → ℝ} {α : ℝ} (hy : ∀ S, ∑ e ∈ S, yOf ρ α e ≤ f₀ S)
    (ht : ∀ θ, ∑ e ∈ univ.filter (fun e => θ ≤ ρ e), yOf ρ α e =
      f₀ (univ.filter fun e => θ ≤ ρ e)) :
    xi f₀ m β α = yOf ρ α := by
  refine (eq_xi_of_levelSets fpHyp_f₀ hy fun θ => ?_).symm
  have hset : levelSet m β α (yOf ρ α) θ = univ.filter fun e => θ ≤ ρ e := by
    ext e
    simp [levelSet, marg_yOf]
  unfold IsTight
  rw [hset]
  exact ht θ

/-- The level criterion on a piece of the table, as step (2) of the proof of `prop:base` uses it: if
every upper level set `{e : θ ≤ ρ_e}` of `ρ(α)` is empty or one of the listed sets `𝓛`, the listed
sets are tight for `y = αt − ρ/β`, and `y(S) ≤ f₀(S)` for all `S`, then `y = ξ^{(0)}(α)`
(`xi_of_row`; the empty set is tight, as `f₀(∅) = 0`). -/
lemma xi_of_listed {ρ : Fin 3 → ℝ} {α : ℝ} {𝓛 : Finset (Finset (Fin 3))}
    (hls : ∀ θ, univ.filter (fun e => θ ≤ ρ e) = ∅ ∨ univ.filter (fun e => θ ≤ ρ e) ∈ 𝓛)
    (ht : ∀ A ∈ 𝓛, ∑ e ∈ A, yOf ρ α e = f₀ A) (hy : ∀ S, ∑ e ∈ S, yOf ρ α e ≤ f₀ S) :
    xi f₀ m β α = yOf ρ α := by
  refine xi_of_row hy fun θ => ?_
  rcases hls θ with h | h
  · rw [h, sum_empty]
    simp [f₀, tab]
  · exact ht _ h

/-- An upper level set `{e : θ ≤ ρ_e}` of a row of the table, given by which of `C₀`, `C₁`, `C₂` it
contains. -/
lemma levelSet_eq {ρ : Fin 3 → ℝ} {θ : ℝ} (A : Finset (Fin 3)) (h0 : θ ≤ ρ 0 ↔ 0 ∈ A)
    (h1 : θ ≤ ρ 1 ↔ 1 ∈ A) (h2 : θ ≤ ρ 2 ↔ 2 ∈ A) : univ.filter (fun e => θ ≤ ρ e) = A := by
  ext e
  fin_cases e
  · simpa using h0
  · simpa using h1
  · simpa using h2

/-- Step (2) of the proof of `prop:base` (`stoc-sections/appD-hardness.tex:512-537`), "Next we show
that the rows of the table are the full-plane marginals": on each piece `I` with row `ρ_I`,
`y = αt − ρ_I(α)/β` is `ξ^{(0)}(α)`, by the level criterion `lem:fullplane`(a) (`xi_of_listed`).
The step's sentences: (1) the second table gives `y` and the
upper level sets of `ρ(α)` in the interior of the piece (`yᵢ` and `hls`; on `(−∞, −1/6]` they are
`C₂` or `C₀`, `C₀C₂` and `E₀`; on `[−1/6, 1/3]` `C₀` and `E₀`; on `[1/3, 3/7]` `C₀`, `C₀C₁` and
`E₀`; on `[3/7, 2/3]` `C₀C₁` and `E₀`; on `[2/3, ∞)` `C₁`, `C₀C₁` and `E₀`); at the ends of a piece,
two marginals may coincide, which only merges two level sets (so `hls` holds on the closed piece);
(2) on every piece, `y(E₀) = 4/3`, the listed level sets are tight, and `y(S) ≤ f₀(S)` for all `S`;
on the bounded pieces `y` is affine, so this is checked at the end points (`sum_eq_of_ends`,
`mem_fpPoly_of_ends`), and on the two unbounded pieces `y` is constant; (3) by `lem:fullplane`(a),
`y = ξ^{(0)}(α)`, so `ρ^{f₀}(α) = ρ_I(α)` and `r(ξ^{(0)}(α)) = m^⊤y` (`base_rows`). -/
theorem base_table :
    (∀ α, α ≤ -1 / 6 → xi f₀ m β α = yOf (row₁ α) α) ∧
    (∀ α, -1 / 6 ≤ α → α ≤ ζ₁ → xi f₀ m β α = yOf (row₂ α) α) ∧
    (∀ α, ζ₁ ≤ α → α ≤ 3 / 7 → xi f₀ m β α = yOf (row₃ α) α) ∧
    (∀ α, 3 / 7 ≤ α → α ≤ ζ₂ → xi f₀ m β α = yOf (row₄ α) α) ∧
    (∀ α, ζ₂ ≤ α → xi f₀ m β α = yOf (row₅ α) α) := by
  unfold ζ₁ ζ₂
  -- (1) "The following table gives `y` and the upper level sets of `ρ(α)` in the interior of the
  -- piece": the vectors `y` of the second table
  have y₁ : ∀ α, yOf (row₁ α) α = ![1 / 3, 1 / 3, 2 / 3] := fun α => by
    funext e; fin_cases e <;> simp [yOf, row₁, m, β] <;> ring
  have y₂ : ∀ α, yOf (row₂ α) α = ![1 / 3, α + 1 / 2, 1 / 2 - α] := fun α => by
    funext e; fin_cases e <;> simp [yOf, row₂, m, β] <;> ring
  have y₃ : ∀ α, yOf (row₃ α) α = ![1 / 3, 5 / 6, 1 / 6] := fun α => by
    funext e; fin_cases e <;> simp [yOf, row₃, m, β] <;> ring
  have y₄ : ∀ α, yOf (row₄ α) α = ![14 / 15 - 7 * α / 5, 7 * α / 5 + 7 / 30, 1 / 6] := fun α => by
    funext e; fin_cases e <;> simp [yOf, row₄, m, β] <;> ring
  have y₅ : ∀ α, yOf (row₅ α) α = ![0, 7 / 6, 1 / 6] := fun α => by
    funext e; fin_cases e <;> simp [yOf, row₅, m, β] <;> ring
  -- the check of `y(S) ≤ f₀(S)` for one vector `y` (all eight `S`)
  have hfp : ∀ y₀ y₁ y₂ : ℝ, (∀ S : Finset (Fin 3), (if 0 ∈ S then y₀ else 0) +
      (if 1 ∈ S then y₁ else 0) + (if 2 ∈ S then y₂ else 0) ≤ f₀ S) →
      ∀ S, ∑ e ∈ S, ![y₀, y₁, y₂] e ≤ f₀ S := fun y₀ y₁ y₂ h S => by
    rw [sum_fin3]
    exact h S
  refine ⟨fun α h => ?_, fun α h1 h2 => ?_, fun α h1 h2 => ?_, fun α h1 h2 => ?_, fun α h => ?_⟩
  · -- `(−∞, −1/6]`: `y = (1/3, 1/3, 2/3)`; the upper level sets are `C₂` or `C₀`, `C₀C₂` and `E₀`
    have hls : ∀ θ, univ.filter (fun e => θ ≤ row₁ α e) = ∅ ∨ univ.filter (fun e => θ ≤ row₁ α e)
        ∈ ({{2}, {0}, {0, 2}, univ} : Finset (Finset (Fin 3))) := by
      intro θ
      have r0 : row₁ α 0 = 5 * α - 1 / 3 := rfl
      have r1 : row₁ α 1 = 12 * α - 4 / 3 := rfl
      have r2 : row₁ α 2 = 4 * α - 8 / 3 := rfl
      by_cases a1 : θ ≤ 12 * α - 4 / 3
      · rw [levelSet_eq univ (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2]; linarith)]
        simp
      by_cases a0 : θ ≤ 5 * α - 1 / 3 <;> by_cases a2 : θ ≤ 4 * α - 8 / 3
      · rw [levelSet_eq {0, 2} (by simp [r0]; linarith) (by simp [r1, not_le]; linarith)
          (by simp [r2]; linarith)]
        simp
      · rw [levelSet_eq {0} (by simp [r0]; linarith) (by simp [r1, not_le]; linarith)
          (by simp [r2, not_le]; linarith)]
        simp
      · rw [levelSet_eq {2} (by simp [r0, not_le]; linarith) (by simp [r1, not_le]; linarith)
          (by simp [r2]; linarith)]
        simp
      · exact Or.inl (levelSet_eq ∅ (by simp [r0, not_le]; linarith)
          (by simp [r1, not_le]; linarith) (by simp [r2, not_le]; linarith))
    -- (2) "On every piece, `y(E₀) = 4/3`, the listed level sets are tight, and `y(S) ≤ f₀(S)` for
    -- all `S ⊆ E₀`", here with `y` constant
    have hE : ∑ e, yOf (row₁ α) α e = 4 / 3 := by
      rw [y₁, Fin.sum_univ_three]; simp; norm_num
    have hC₂ : ∑ e ∈ {2}, yOf (row₁ α) α e = f₀ {2} := by
      rw [y₁]; simp [f₀, tab]
    have hC₀ : ∑ e ∈ {0}, yOf (row₁ α) α e = f₀ {0} := by
      rw [y₁]; simp [f₀, tab]
    have hC₀C₂ : ∑ e ∈ {0, 2}, yOf (row₁ α) α e = f₀ {0, 2} := by
      rw [y₁]; simp [f₀, tab]; norm_num
    have hy : ∀ S, ∑ e ∈ S, yOf (row₁ α) α e ≤ f₀ S := by
      rw [y₁]
      refine hfp _ _ _ fun S => ?_
      unfold f₀
      by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
        by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2, tab] <;> norm_num
    -- (3) "By `lem:fullplane`(a), `y = ξ^{(0)}(α)` …"
    refine xi_of_listed hls (fun A hA => ?_) hy
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact hC₂
    · exact hC₀
    · exact hC₀C₂
    · rw [hE]; simp [f₀, tab]
  · -- `[−1/6, 1/3]`: `y = (1/3, α + 1/2, 1/2 − α)`; the upper level sets are `C₀` and `E₀`
    have hls : ∀ θ, univ.filter (fun e => θ ≤ row₂ α e) = ∅ ∨ univ.filter (fun e => θ ≤ row₂ α e)
        ∈ ({{0}, univ} : Finset (Finset (Fin 3))) := by
      intro θ
      have r0 : row₂ α 0 = 5 * α - 1 / 3 := rfl
      have r1 : row₂ α 1 = 8 * α - 2 := rfl
      have r2 : row₂ α 2 = 8 * α - 2 := rfl
      by_cases a1 : θ ≤ 8 * α - 2
      · rw [levelSet_eq univ (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2]; linarith)]
        simp
      by_cases a0 : θ ≤ 5 * α - 1 / 3
      · rw [levelSet_eq {0} (by simp [r0]; linarith) (by simp [r1, not_le]; linarith)
          (by simp [r2, not_le]; linarith)]
        simp
      · exact Or.inl (levelSet_eq ∅ (by simp [r0, not_le]; linarith)
          (by simp [r1, not_le]; linarith) (by simp [r2, not_le]; linarith))
    -- (2) "On the bounded pieces `y` is affine, so it suffices to check this at the end points, …"
    have haff : ∀ α e, yOf (row₂ α) α e =
        yOf (row₂ 0) 0 e + α * (yOf (row₂ 1) 1 e - yOf (row₂ 0) 0 e) := fun α e => by
      rw [y₂, y₂, y₂]
      fin_cases e <;> simp <;> ring
    have hE : ∑ e, yOf (row₂ α) α e = 4 / 3 :=
      sum_eq_of_ends haff (a := -1 / 6) (b := 1 / 3) (by norm_num) univ
        (by rw [y₂, Fin.sum_univ_three]; simp; norm_num)
        (by rw [y₂, Fin.sum_univ_three]; simp; norm_num) α
    have hC₀ : ∑ e ∈ {0}, yOf (row₂ α) α e = f₀ {0} :=
      sum_eq_of_ends haff (a := -1 / 6) (b := 1 / 3) (by norm_num) {0}
        (by rw [y₂]; simp [f₀, tab]) (by rw [y₂]; simp [f₀, tab]) α
    have hy : ∀ S, ∑ e ∈ S, yOf (row₂ α) α e ≤ f₀ S := fun S =>
      mem_fpPoly_of_ends (y := fun α => yOf (row₂ α) α) haff (a := -1 / 6) (b := 1 / 3)
        (by norm_num) (fun S => ?_) (fun S => ?_) h1 h2 S
    · -- (3) "By `lem:fullplane`(a), `y = ξ^{(0)}(α)` …"
      refine xi_of_listed hls (fun A hA => ?_) hy
      simp only [mem_insert, mem_singleton] at hA
      rcases hA with rfl | rfl
      · exact hC₀
      · rw [hE]
        simp [f₀, tab]
    all_goals
      rw [y₂]
      refine hfp _ _ _ (fun S => ?_) S
      unfold f₀
      by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
        by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2, tab] <;> norm_num
  · -- `[1/3, 3/7]`: `y = (1/3, 5/6, 1/6)`; the upper level sets are `C₀`, `C₀C₁` and `E₀`
    have hls : ∀ θ, univ.filter (fun e => θ ≤ row₃ α e) = ∅ ∨ univ.filter (fun e => θ ≤ row₃ α e)
        ∈ ({{0}, {0, 1}, univ} : Finset (Finset (Fin 3))) := by
      intro θ
      have r0 : row₃ α 0 = 5 * α - 1 / 3 := rfl
      have r1 : row₃ α 1 = 12 * α - 10 / 3 := rfl
      have r2 : row₃ α 2 = 4 * α - 2 / 3 := rfl
      by_cases a2 : θ ≤ 4 * α - 2 / 3
      · rw [levelSet_eq univ (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2]; linarith)]
        simp
      by_cases a1 : θ ≤ 12 * α - 10 / 3
      · rw [levelSet_eq {0, 1} (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2, not_le]; linarith)]
        simp
      by_cases a0 : θ ≤ 5 * α - 1 / 3
      · rw [levelSet_eq {0} (by simp [r0]; linarith) (by simp [r1, not_le]; linarith)
          (by simp [r2, not_le]; linarith)]
        simp
      · exact Or.inl (levelSet_eq ∅ (by simp [r0, not_le]; linarith)
          (by simp [r1, not_le]; linarith) (by simp [r2, not_le]; linarith))
    -- (2) "On the bounded pieces `y` is affine, so it suffices to check this at the end points, …"
    have haff : ∀ α e, yOf (row₃ α) α e =
        yOf (row₃ 0) 0 e + α * (yOf (row₃ 1) 1 e - yOf (row₃ 0) 0 e) := fun α e => by
      rw [y₃, y₃, y₃]
      ring
    have hE : ∑ e, yOf (row₃ α) α e = 4 / 3 :=
      sum_eq_of_ends haff (a := 1 / 3) (b := 3 / 7) (by norm_num) univ
        (by rw [y₃, Fin.sum_univ_three]; simp; norm_num)
        (by rw [y₃, Fin.sum_univ_three]; simp; norm_num) α
    have hC₀ : ∑ e ∈ {0}, yOf (row₃ α) α e = f₀ {0} :=
      sum_eq_of_ends haff (a := 1 / 3) (b := 3 / 7) (by norm_num) {0}
        (by rw [y₃]; simp [f₀, tab]) (by rw [y₃]; simp [f₀, tab]) α
    have hC₀C₁ : ∑ e ∈ {0, 1}, yOf (row₃ α) α e = f₀ {0, 1} :=
      sum_eq_of_ends haff (a := 1 / 3) (b := 3 / 7) (by norm_num) {0, 1}
        (by rw [y₃]; simp [f₀, tab]; norm_num) (by rw [y₃]; simp [f₀, tab]; norm_num) α
    have hy : ∀ S, ∑ e ∈ S, yOf (row₃ α) α e ≤ f₀ S := fun S =>
      mem_fpPoly_of_ends (y := fun α => yOf (row₃ α) α) haff (a := 1 / 3) (b := 3 / 7)
        (by norm_num) (fun S => ?_) (fun S => ?_) h1 h2 S
    · -- (3) "By `lem:fullplane`(a), `y = ξ^{(0)}(α)` …"
      refine xi_of_listed hls (fun A hA => ?_) hy
      simp only [mem_insert, mem_singleton] at hA
      rcases hA with rfl | rfl | rfl
      · exact hC₀
      · exact hC₀C₁
      · rw [hE]
        simp [f₀, tab]
    all_goals
      rw [y₃]
      refine hfp _ _ _ (fun S => ?_) S
      unfold f₀
      by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
        by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2, tab] <;> norm_num
  · -- `[3/7, 2/3]`: `y = (14/15 − 7α/5, 7α/5 + 7/30, 1/6)`; the upper level sets are `C₀C₁` and
    -- `E₀`
    have hls : ∀ θ, univ.filter (fun e => θ ≤ row₄ α e) = ∅ ∨ univ.filter (fun e => θ ≤ row₄ α e)
        ∈ ({{0, 1}, univ} : Finset (Finset (Fin 3))) := by
      intro θ
      have r0 : row₄ α 0 = 32 * α / 5 - 14 / 15 := rfl
      have r1 : row₄ α 1 = 32 * α / 5 - 14 / 15 := rfl
      have r2 : row₄ α 2 = 4 * α - 2 / 3 := rfl
      by_cases a2 : θ ≤ 4 * α - 2 / 3
      · rw [levelSet_eq univ (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2]; linarith)]
        simp
      by_cases a0 : θ ≤ 32 * α / 5 - 14 / 15
      · rw [levelSet_eq {0, 1} (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2, not_le]; linarith)]
        simp
      · exact Or.inl (levelSet_eq ∅ (by simp [r0, not_le]; linarith)
          (by simp [r1, not_le]; linarith) (by simp [r2, not_le]; linarith))
    -- (2) "On the bounded pieces `y` is affine, so it suffices to check this at the end points, …"
    have haff : ∀ α e, yOf (row₄ α) α e =
        yOf (row₄ 0) 0 e + α * (yOf (row₄ 1) 1 e - yOf (row₄ 0) 0 e) := fun α e => by
      rw [y₄, y₄, y₄]
      fin_cases e <;> simp <;> ring
    have hE : ∑ e, yOf (row₄ α) α e = 4 / 3 :=
      sum_eq_of_ends haff (a := 3 / 7) (b := 2 / 3) (by norm_num) univ
        (by rw [y₄, Fin.sum_univ_three]; simp; norm_num)
        (by rw [y₄, Fin.sum_univ_three]; simp; norm_num) α
    have hC₀C₁ : ∑ e ∈ {0, 1}, yOf (row₄ α) α e = f₀ {0, 1} :=
      sum_eq_of_ends haff (a := 3 / 7) (b := 2 / 3) (by norm_num) {0, 1}
        (by rw [y₄]; simp [f₀, tab]; norm_num) (by rw [y₄]; simp [f₀, tab]; norm_num) α
    have hy : ∀ S, ∑ e ∈ S, yOf (row₄ α) α e ≤ f₀ S := fun S =>
      mem_fpPoly_of_ends (y := fun α => yOf (row₄ α) α) haff (a := 3 / 7) (b := 2 / 3)
        (by norm_num) (fun S => ?_) (fun S => ?_) h1 h2 S
    · -- (3) "By `lem:fullplane`(a), `y = ξ^{(0)}(α)` …"
      refine xi_of_listed hls (fun A hA => ?_) hy
      simp only [mem_insert, mem_singleton] at hA
      rcases hA with rfl | rfl
      · exact hC₀C₁
      · rw [hE]
        simp [f₀, tab]
    all_goals
      rw [y₄]
      refine hfp _ _ _ (fun S => ?_) S
      unfold f₀
      by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
        by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2, tab] <;> norm_num
  · -- `[2/3, ∞)`: `y = (0, 7/6, 1/6)`; the upper level sets are `C₁`, `C₀C₁` and `E₀`
    have hls : ∀ θ, univ.filter (fun e => θ ≤ row₅ α e) = ∅ ∨ univ.filter (fun e => θ ≤ row₅ α e)
        ∈ ({{1}, {0, 1}, univ} : Finset (Finset (Fin 3))) := by
      intro θ
      have r0 : row₅ α 0 = 5 * α := rfl
      have r1 : row₅ α 1 = 12 * α - 14 / 3 := rfl
      have r2 : row₅ α 2 = 4 * α - 2 / 3 := rfl
      by_cases a2 : θ ≤ 4 * α - 2 / 3
      · rw [levelSet_eq univ (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2]; linarith)]
        simp
      by_cases a0 : θ ≤ 5 * α
      · rw [levelSet_eq {0, 1} (by simp [r0]; linarith) (by simp [r1]; linarith)
          (by simp [r2, not_le]; linarith)]
        simp
      by_cases a1 : θ ≤ 12 * α - 14 / 3
      · rw [levelSet_eq {1} (by simp [r0, not_le]; linarith) (by simp [r1]; linarith)
          (by simp [r2, not_le]; linarith)]
        simp
      · exact Or.inl (levelSet_eq ∅ (by simp [r0, not_le]; linarith)
          (by simp [r1, not_le]; linarith) (by simp [r2, not_le]; linarith))
    -- (2) "On every piece, `y(E₀) = 4/3`, the listed level sets are tight, and `y(S) ≤ f₀(S)` for
    -- all `S ⊆ E₀`", here with `y` constant
    have hE : ∑ e, yOf (row₅ α) α e = 4 / 3 := by
      rw [y₅, Fin.sum_univ_three]; simp; norm_num
    have hC₁ : ∑ e ∈ {1}, yOf (row₅ α) α e = f₀ {1} := by
      rw [y₅]; simp [f₀, tab]
    have hC₀C₁ : ∑ e ∈ {0, 1}, yOf (row₅ α) α e = f₀ {0, 1} := by
      rw [y₅]; simp [f₀, tab]
    have hy : ∀ S, ∑ e ∈ S, yOf (row₅ α) α e ≤ f₀ S := by
      rw [y₅]
      refine hfp _ _ _ fun S => ?_
      unfold f₀
      by_cases a0 : (0 : Fin 3) ∈ S <;> by_cases a1 : (1 : Fin 3) ∈ S <;>
        by_cases a2 : (2 : Fin 3) ∈ S <;> simp [a0, a1, a2, tab] <;> norm_num
    -- (3) "By `lem:fullplane`(a), `y = ξ^{(0)}(α)` …"
    refine xi_of_listed hls (fun A hA => ?_) hy
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact hC₁
    · exact hC₀C₁
    · rw [hE]; simp [f₀, tab]

/-- On a piece with row `ρ`, the marginals of `ξ^{(0)}(α) = αt − ρ/β` are `ρ`. -/
lemma rho_of_xi {ρ : Fin 3 → ℝ} {α : ℝ} (h : xi f₀ m β α = yOf ρ α) (e : Fin 3) :
    rho f₀ m β α e = ρ e := by
  rw [rho, h, marg_yOf]

/-- The table of `prop:base`: on each of the five pieces, the marginals `ρ^{f₀}(α)` are the row
and the reward `r(ξ^{(0)}(α)) = m^⊤y` is the last column, `25/3`, `8α + 29/3`, `37/3`,
`49α/5 + 122/15` and `44/3`. -/
theorem base_rows :
    (∀ α, α ≤ -1 / 6 → (∀ e, rho f₀ m β α e = row₁ α e) ∧ curve f₀ m β α = 25 / 3) ∧
    (∀ α, -1 / 6 ≤ α → α ≤ ζ₁ →
      (∀ e, rho f₀ m β α e = row₂ α e) ∧ curve f₀ m β α = 8 * α + 29 / 3) ∧
    (∀ α, ζ₁ ≤ α → α ≤ 3 / 7 → (∀ e, rho f₀ m β α e = row₃ α e) ∧ curve f₀ m β α = 37 / 3) ∧
    (∀ α, 3 / 7 ≤ α → α ≤ ζ₂ →
      (∀ e, rho f₀ m β α e = row₄ α e) ∧ curve f₀ m β α = 49 * α / 5 + 122 / 15) ∧
    (∀ α, ζ₂ ≤ α → (∀ e, rho f₀ m β α e = row₅ α e) ∧ curve f₀ m β α = 44 / 3) := by
  -- (3) "By `lem:fullplane`(a), `y = ξ^{(0)}(α)` and `ρ(α) = ρ^{f₀}(α)`, and
  -- `r(ξ^{(0)}(α)) = m^⊤y`, which is the last column of the first table." (`base_table`)
  obtain ⟨t₁, t₂, t₃, t₄, t₅⟩ := base_table
  have hc : ∀ {ρ : Fin 3 → ℝ} {α : ℝ}, xi f₀ m β α = yOf ρ α →
      curve f₀ m β α = ∑ e, m e * yOf ρ α e := fun h => by rw [curve, h]
  refine ⟨fun α h => ⟨rho_of_xi (t₁ α h), ?_⟩, fun α h1 h2 => ⟨rho_of_xi (t₂ α h1 h2), ?_⟩,
    fun α h1 h2 => ⟨rho_of_xi (t₃ α h1 h2), ?_⟩, fun α h1 h2 => ⟨rho_of_xi (t₄ α h1 h2), ?_⟩,
    fun α h => ⟨rho_of_xi (t₅ α h), ?_⟩⟩
  · rw [hc (t₁ α h), Fin.sum_univ_three]; simp [yOf, row₁, m, β]; ring
  · rw [hc (t₂ α h1 h2), Fin.sum_univ_three]; simp [yOf, row₂, m, β]; ring
  · rw [hc (t₃ α h1 h2), Fin.sum_univ_three]; simp [yOf, row₃, m, β]; ring
  · rw [hc (t₄ α h1 h2), Fin.sum_univ_three]; simp [yOf, row₄, m, β]; ring
  · rw [hc (t₅ α h), Fin.sum_univ_three]; simp [yOf, row₅, m, β]; ring

/-- The differences of step (3) of the proof of `prop:base`
(`stoc-sections/appD-hardness.tex:539-544`), "Finally, we derive (B1)–(B3)": on the four pieces
right of `−1/6`, the difference `L₀(α) − r(ξ^{(0)}(α))` equals `ζ₁ − α`, `7(α − ζ₁)`,
`(14/5)(ζ₂ − α)` and `7(α − ζ₂)`. -/
theorem base_gap_pieces :
    (∀ α, -1 / 6 ≤ α → α ≤ ζ₁ → L₀ α - curve f₀ m β α = ζ₁ - α) ∧
    (∀ α, ζ₁ ≤ α → α ≤ 3 / 7 → L₀ α - curve f₀ m β α = 7 * (α - ζ₁)) ∧
    (∀ α, 3 / 7 ≤ α → α ≤ ζ₂ → L₀ α - curve f₀ m β α = 14 / 5 * (ζ₂ - α)) ∧
    (∀ α, ζ₂ ≤ α → L₀ α - curve f₀ m β α = 7 * (α - ζ₂)) := by
  obtain ⟨-, r₂, r₃, r₄, r₅⟩ := base_rows
  refine ⟨fun α h1 h2 => ?_, fun α h1 h2 => ?_, fun α h1 h2 => ?_, fun α h => ?_⟩
  · rw [(r₂ α h1 h2).2, L₀, p₀, q₀, ζ₁]; ring
  · rw [(r₃ α h1 h2).2, L₀, p₀, q₀, ζ₁]; ring
  · rw [(r₄ α h1 h2).2, L₀, p₀, q₀, ζ₂]; ring
  · rw [(r₅ α h).2, L₀, p₀, q₀, ζ₂]; ring

/-- **`prop:base`** (Proposition C.10, `stoc-sections/appD-hardness.tex:457-500`, proof lines
502-549): `f₀` is a polymatroid rank function, given by the cut form `form`; its full-plane best
response `ξ^{(0)} = ξ^{f₀}` has the marginals `ρ^{f₀}` and the reward `r(ξ^{(0)}(α))` of the table
(`base_rows`); and
* (B1) the slopes of `α ↦ r(ξ^{(0)}(α))` on the five pieces are `0, 8, 0, 49/5, 0`;
* (B2) on `[−1/6, ∞)`, `L₀ ≥ r(ξ^{(0)})` with equality exactly at `ζ₁` and `ζ₂`; on
  `[−1/6, ζ₁]`, `L₀(α) − r(ξ^{(0)}(α)) = ζ₁ − α`; `L₀(α) − r(ξ^{(0)}(α)) ≥ dist(α, {ζ₁, ζ₂})`
  for `α ∈ [R₀, ∞)`; in particular the difference is `ε₀` at `R₀` and `7ε₀` at `ζ₂ + ε₀`;
* (B3) on `(−7/3, ζ₁]`, `ρ_{C₀}` is the strict maximum of the three marginals; at `R₀` they are
  `(7/6, 2/5, 2/5)`, so `max_e ρ_e(R₀) = ρ_{C₀}(R₀) = 7/6`.
Here `ζ₁ = 1/3`, `ζ₂ = 2/3`, `L₀(α) = p₀ + q₀α = 10 + 7α`, `ε₀ = 1/30` and `R₀ = ζ₁ − ε₀ = 3/10`.

The proof's steps, its three paragraphs in our numbering: (1) "We first show that the cut form
gives `f₀`": the cut form gives the eight values of `f₀`, and its weights are at least the
capacities entering their nodes, so `f₀` is a rank function by `lem:cutforms`(b) (`base_step1`);
(2) "Next we show that the rows of the table are the full-plane marginals": on each piece, for
`y = αt − ρ(α)/β` of the second table, `y(E₀) = 4/3`, the listed upper level sets of `ρ(α)` are
tight and `y(S) ≤ f₀(S)` for all `S` (checked at the end points on the bounded pieces, where `y` is
affine, and directly on the two unbounded pieces, where `y` is constant), so `y = ξ^{(0)}(α)` by
`lem:fullplane`(a), and the reward is `m^⊤y` (`base_table`, `base_rows`);
(3) "Finally, we derive (B1)–(B3)": (B1) and (B3) are read off the first table, and on the four
pieces
right of `−1/6` the difference is `ζ₁ − α`, `7(α − ζ₁)`, `(14/5)(ζ₂ − α)`, `7(α − ζ₂)`
(`base_gap_pieces`), with all coefficients at least `1`, which gives (B2), with the values `ε₀` at
`R₀` and `7ε₀` at `ζ₂ + ε₀`. -/
theorem base :
    IsRankFunction f₀ ∧ (∀ S, f₀ S = form.fn S) ∧
    -- the table
    ((∀ α, α ≤ -1 / 6 → (∀ e, rho f₀ m β α e = row₁ α e) ∧ curve f₀ m β α = 25 / 3) ∧
      (∀ α, -1 / 6 ≤ α → α ≤ ζ₁ →
        (∀ e, rho f₀ m β α e = row₂ α e) ∧ curve f₀ m β α = 8 * α + 29 / 3) ∧
      (∀ α, ζ₁ ≤ α → α ≤ 3 / 7 → (∀ e, rho f₀ m β α e = row₃ α e) ∧ curve f₀ m β α = 37 / 3) ∧
      (∀ α, 3 / 7 ≤ α → α ≤ ζ₂ →
        (∀ e, rho f₀ m β α e = row₄ α e) ∧ curve f₀ m β α = 49 * α / 5 + 122 / 15) ∧
      (∀ α, ζ₂ ≤ α → (∀ e, rho f₀ m β α e = row₅ α e) ∧ curve f₀ m β α = 44 / 3)) ∧
    -- (B1)
    ((∀ α α', α ≤ -1 / 6 → α' ≤ -1 / 6 → curve f₀ m β α' - curve f₀ m β α = 0 * (α' - α)) ∧
      (∀ α α', -1 / 6 ≤ α → α ≤ ζ₁ → -1 / 6 ≤ α' → α' ≤ ζ₁ →
        curve f₀ m β α' - curve f₀ m β α = 8 * (α' - α)) ∧
      (∀ α α', ζ₁ ≤ α → α ≤ 3 / 7 → ζ₁ ≤ α' → α' ≤ 3 / 7 →
        curve f₀ m β α' - curve f₀ m β α = 0 * (α' - α)) ∧
      (∀ α α', 3 / 7 ≤ α → α ≤ ζ₂ → 3 / 7 ≤ α' → α' ≤ ζ₂ →
        curve f₀ m β α' - curve f₀ m β α = 49 / 5 * (α' - α)) ∧
      (∀ α α', ζ₂ ≤ α → ζ₂ ≤ α' → curve f₀ m β α' - curve f₀ m β α = 0 * (α' - α))) ∧
    -- (B2)
    ((∀ α, -1 / 6 ≤ α → curve f₀ m β α ≤ L₀ α ∧ (curve f₀ m β α = L₀ α ↔ α = ζ₁ ∨ α = ζ₂)) ∧
      (∀ α, -1 / 6 ≤ α → α ≤ ζ₁ → L₀ α - curve f₀ m β α = ζ₁ - α) ∧
      (∀ α, R0 ≤ α → distTo α {ζ₁, ζ₂} ≤ ((L₀ α - curve f₀ m β α : ℝ) : WithTop ℝ)) ∧
      L₀ R0 - curve f₀ m β R0 = ε₀ ∧
      L₀ (ζ₂ + ε₀) - curve f₀ m β (ζ₂ + ε₀) = 7 * ε₀) ∧
    -- (B3)
    ((∀ α, -7 / 3 < α → α ≤ ζ₁ → ∀ e, e ≠ 0 → rho f₀ m β α e < rho f₀ m β α 0) ∧
      (rho f₀ m β R0 0 = 7 / 6 ∧ rho f₀ m β R0 1 = 2 / 5 ∧ rho f₀ m β R0 2 = 2 / 5) ∧
      univ.sup' univ_nonempty (rho f₀ m β R0) = rho f₀ m β R0 0) := by
  -- (1) "We first show that the cut form gives `f₀`."
  obtain ⟨hform, hrank⟩ := base_step1
  -- (2) "Next we show that the rows of the table are the full-plane marginals."
  have hrows := base_rows
  obtain ⟨r₁, r₂, r₃, r₄, r₅⟩ := hrows
  -- (3) "Finally, we derive (B1)–(B3). (B1) is read off the first table. On the four pieces right
  -- of `−1/6`, the difference `L₀(α) − r(ξ^{(0)}(α))` equals `ζ₁ − α`, `7(α − ζ₁)`,
  -- `(14/5)(ζ₂ − α)` and `7(α − ζ₂)`, respectively. For example,
  -- `L₀(α) − r(ξ^{(0)}(α)) = 10 + 7α − (8α + 29/3) = 1/3 − α` on `[−1/6, 1/3]`. All four
  -- coefficients are at least `1`, which gives (B2), with the values `ε₀` at `R₀` and `7ε₀` at
  -- `ζ₂ + ε₀`. (B3) is read off the first table, with `ρ_{C₀}(R₀) = 5R₀ − 1/3 = 7/6` and
  -- `ρ_{C₁}(R₀) = ρ_{C₂}(R₀) = 8R₀ − 2 = 2/5`."
  obtain ⟨g₂, g₃, g₄, g₅⟩ := base_gap_pieces
  have hz : ζ₁ = 1 / 3 := rfl
  have hz2 : ζ₂ = 2 / 3 := rfl
  have hR : R0 = 3 / 10 := R0_eq
  refine ⟨hrank, hform, ⟨r₁, r₂, r₃, r₄, r₅⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, g₂, ?_, ?_, ?_⟩, ?_⟩
  · intro α α' h h'; rw [(r₁ α h).2, (r₁ α' h').2]; ring
  · intro α α' h1 h2 h1' h2'; rw [(r₂ α h1 h2).2, (r₂ α' h1' h2').2]; ring
  · intro α α' h1 h2 h1' h2'; rw [(r₃ α h1 h2).2, (r₃ α' h1' h2').2]; ring
  · intro α α' h1 h2 h1' h2'; rw [(r₄ α h1 h2).2, (r₄ α' h1' h2').2]; ring
  · intro α α' h h'; rw [(r₅ α h).2, (r₅ α' h').2]; ring
  · -- (B2), first part: the four differences are nonnegative, and zero exactly at `ζ₁`, `ζ₂`.
    intro α h
    rcases le_total α ζ₁ with a2 | a2
    · have := g₂ α h a2
      refine ⟨by linarith, ⟨fun e => Or.inl (by linarith), fun e => ?_⟩⟩
      rcases e with e | e
      · subst e; linarith
      · rw [e, hz, hz2] at a2; norm_num at a2
    rcases le_total α (3 / 7) with a3 | a3
    · have := g₃ α a2 a3
      refine ⟨by nlinarith, ⟨fun e => Or.inl (by linarith), fun e => ?_⟩⟩
      rcases e with e | e
      · subst e; linarith
      · rw [e, hz2] at a3; norm_num at a3
    rcases le_total α ζ₂ with a4 | a4
    · have := g₄ α a3 a4
      refine ⟨by nlinarith, ⟨fun e => Or.inr (by linarith), fun e => ?_⟩⟩
      rcases e with e | e
      · rw [e, hz] at a3; norm_num at a3
      · subst e; linarith
    · have := g₅ α a4
      refine ⟨by nlinarith, ⟨fun e => Or.inr (by linarith), fun e => ?_⟩⟩
      rcases e with e | e
      · rw [e, hz, hz2] at a4; norm_num at a4
      · subst e; linarith
  · -- (B2): `L₀(α) − r(ξ^{(0)}(α)) ≥ dist(α, {ζ₁, ζ₂})` on `[R₀, ∞)`, as the coefficients are
    -- at least `1`.
    intro α h
    rw [hR] at h
    rcases le_total α ζ₁ with a2 | a2
    · refine (distTo_le (γ := ζ₁) (by simp)).trans (WithTop.coe_le_coe.2 ?_)
      rw [g₂ α (by linarith) a2, abs_of_nonpos (by linarith)]
      linarith
    rcases le_total α (3 / 7) with a3 | a3
    · refine (distTo_le (γ := ζ₁) (by simp)).trans (WithTop.coe_le_coe.2 ?_)
      rw [g₃ α a2 a3, abs_of_nonneg (by linarith)]
      linarith
    rcases le_total α ζ₂ with a4 | a4
    · refine (distTo_le (γ := ζ₂) (by simp)).trans (WithTop.coe_le_coe.2 ?_)
      rw [g₄ α a3 a4, abs_of_nonpos (by linarith)]
      linarith
    · refine (distTo_le (γ := ζ₂) (by simp)).trans (WithTop.coe_le_coe.2 ?_)
      rw [g₅ α a4, abs_of_nonneg (by linarith)]
      linarith
  · -- (B2): "with the values `ε₀` at `R₀`"
    rw [g₂ R0 (by rw [hR]; norm_num) (by rw [hR, hz]; norm_num), hR, hz]; norm_num
  · -- "and `7ε₀` at `ζ₂ + ε₀`"
    rw [g₅ _ (by linarith [ε₀_pos]), hz2]; norm_num
  · refine ⟨fun α h1 h2 e he => ?_, ?_, ?_⟩
    · -- (B3) on `(−7/3, ζ₁]`, from the first two rows.
      rcases le_total α (-1 / 6) with a | a
      · obtain ⟨hρ, -⟩ := r₁ α a
        rw [hρ, hρ]
        fin_cases e
        · exact absurd rfl he
        · simp [row₁]; linarith
        · simp [row₁]; linarith
      · obtain ⟨hρ, -⟩ := r₂ α a h2
        rw [hρ, hρ]
        rw [hz] at h2
        fin_cases e
        · exact absurd rfl he
        · simp [row₂]; linarith
        · simp [row₂]; linarith
    · obtain ⟨hρ, -⟩ := r₂ R0 (by rw [hR]; norm_num) (by rw [hR, hz]; norm_num)
      rw [hρ, hρ, hρ, hR]
      simp [row₂]
      norm_num
    · obtain ⟨hρ, -⟩ := r₂ R0 (by rw [hR]; norm_num) (by rw [hR, hz]; norm_num)
      refine le_antisymm (sup'_le _ _ fun e _ => ?_) (le_sup' _ (mem_univ 0))
      rw [hρ, hρ, hR]
      fin_cases e <;> simp [row₂] <;> norm_num

end Base

end

end Hardness

end Stoc
