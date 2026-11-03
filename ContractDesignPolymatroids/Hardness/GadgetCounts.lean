-- stamp r1 2026-11-03
import ContractDesignPolymatroids.Hardness.ReductionCounts

/-!
# The algorithm of `thm:gadget`, counted

The STOC version's `thm:gadget` (`stoc-sections/appD-hardness.tex:191-197`, proof lines 1660-1780)
states "There is a polynomial-time algorithm that computes, for `μ^in ∈ 𝔉` of length `k`, an integer
`N_min(μ^in) ≥ 1` and, for every integer `N ≥ N_min(μ^in)`, an instance `I(μ^in, N) ∈ 𝒞_cut` with
`3k + 1` elements, a cut form of it, and rationals `p` and `q > 0`, …". Part (1) of its proof
(lines 1664-1679, "We first define the output and the numbers that come with it") defines `Θ`,
`Λ`, `N_min`, `Λ'`, `f_c`, `q`, `α_Γ`, `C_g` and `p`; part (4) (lines 1748-1779) says that the
output has a cut form "computed along the construction" and counts the work in prose: "The values
`g(E)`, `g(E ∖ {e})`, and `g({e})` needed for `Θ` and `Λ` are `2|E| + 1` evaluations of `g`. So the
algorithm runs in polynomial time." The proof of `thm:nphard` uses the algorithm four times in
step (2) of `def:reduction` (line 1886: "the algorithm of `thm:gadget` computes `N_0` and both combs
in polynomial time"), and `ContractDesignPolymatroids/Hardness/ReductionCounts.lean` counts the reduction with the cost
of these calls as a parameter (`SubsetSum.GadgetCost`).

This file counts the algorithm in the cost model of `Stoc.Counted` (not in the paper: the paper
counts in prose). Its programs run the counted parameter rule `ruleC` for the levels
`1, …, k − 1` and evaluate `g = g_{k−1}` by the counted formula `gTC` (`ContractDesignPolymatroids/Hardness/Sizes.lean`),
from the numbers of the steps that the rule returns:
* `formωC`: the weights of the cut form of `g_j` (`formT`), along the construction;
* `gΘC` and `gΛC`: `Θ` (`|E|` evaluations of `g`, at the singletons) and `Λ` (`|E| + 1`
  evaluations, at `E` and the sets `E ∖ {e}`), the `2|E| + 1` evaluations of part (4);
* `nminCount`: `N_min(μ^in)` (`nminCount_val`), with at most `18k³ + 70k² + 37k` arithmetic
  operations (`nminCount_cost`);
* `combTail` and `combCount`: the comb `I(μ^in, N)` with its cut form, rewards, curvatures, width
  `δ`, dip `κ` and line `p + qα` (`combCount_val`: the comb `SubsetSum.gadgetComb` of the
  reduction), with at most `9k³ + 41k² + 71k` arithmetic operations (`combCount_cost`);
* `gadgetCost`: the cost of the algorithm, from these programs, and `reductionC_gadget`: the
  reduction of `def:reduction` with this cost takes at most `2^{35}⟨(a, T)⟩ + 2^9⟨(a, T)⟩³`
  arithmetic operations and no oracle calls.

Each evaluation of `g` takes `O(k|E|)` operations (`lem:sizes`), so the `2|E| + 1` evaluations
take `O(k³)`, which dominates. `N_min(μ^in)` and the comb are counted as separate runs, each with
its own run of the rule and of `Θ` (`gadgetCost`), an upper bound on an algorithm that shares them;
the counts do not depend on the sizes of `μ^in` and `N`. The numbers
have `O(k + log μ^in_k + log N)` bits by part (4) of the proof of `thm:gadget`
(`ContractDesignPolymatroids/Hardness/GadgetSizes.lean`, `gadget_sizes`), and those of the reduction are polynomial in
`⟨(a, T)⟩` (`reduction_sizes`); the intermediate results inside the formulas of the parameter rule
are not bounded (`lem:sizes`). Not formalised: the step from the counts to the running time of a
Turing machine (`stoc-sections/01-introduction.tex:31`).
-/

namespace Stoc

namespace Hardness

open Finset Counted

noncomputable section

/-! ### The programs -/

/-- The weights of the cut form of `g_j` (`formT`), counted along the construction from the numbers
of the steps that the counted rule returns (part (4) of the proof of `thm:gadget`: "By `prop:base`
and `lem:cutforms`(c), the output has a cut form, computed along the construction"): the weights of
`f_0`'s form (`prop:base`), and at the step `j → j + 1` the weights `F_{τ_1}` of `τ_1` and
`F_{τ_2}` of `τ_2` (`lem:cutforms`(c)(ii)) and `K − d(E)` of `b` (`lem:cutforms`(c)(iii); the sum
`d(E)`, `|E_j| + 2` additions, and one subtraction). The arcs and their capacities, the `d_e` of
the steps, take no arithmetic operation (not in the paper). -/
def formωC : (j : ℕ) → StepNums j → Counted (Gr j → ℝ)
  | 0, _ => ret Base.form.ω
  | j + 1, .cons ns F1 F2 K d => formωC j ns >>=ᶜ fun ω =>
      Counted.sum univ (fun e => ret (d e)) >>=ᶜ fun dE =>
      Counted.ops 1 (K - dE) >>=ᶜ fun wb =>
      ret fun (o : Option (Option (Option (Gr j)))) =>
        Option.elim o wb fun o' => Option.elim o' F2 fun o'' => Option.elim o'' F1 ω

/-- `Θ = max_{e∈E} (β_e g({e}) − ζ_1 m_e)` (part (1) of the proof of `thm:gadget`), counted, from
the data `L` of level `k − 1` and the numbers `ns` of the steps: for each `e ∈ E`, the value
`g({e})` (`gTC`) and three operations, and one comparison per element for the maximum (not in the
paper). -/
def gΘC (k : ℕ) (L : Level (Gr (k - 1))) (ns : StepNums (k - 1)) : Counted ℝ :=
  supC univ univ_nonempty fun e =>
    gTC (k - 1) ns {e} >>=ᶜ fun ge => Counted.ops 3 (L.β e * ge - ζ₁ * L.m e)

/-- `Λ = max(0, max_{e∈E} (Θ/β_e − g(E) + g(E ∖ {e}))/t_e)` with `t_e = m_e/β_e` (part (1) of the
proof of `thm:gadget`), counted: the value `g(E)`, for each `e ∈ E` the value `g(E ∖ {e})` and five
operations, one comparison per element for the maximum, and one for the maximum with `0` (not in
the paper). -/
def gΛC (k : ℕ) (L : Level (Gr (k - 1))) (ns : StepNums (k - 1)) (Θ : ℝ) : Counted ℝ :=
  gTC (k - 1) ns univ >>=ᶜ fun gE =>
  supC univ univ_nonempty (fun e => gTC (k - 1) ns (univ.erase e) >>=ᶜ fun gEe =>
    Counted.ops 5 ((Θ / L.β e - gE + gEe) / (L.m e / L.β e))) >>=ᶜ fun s =>
  Counted.ops 1 (max 0 s)

/-- `N_min(μ^in)`, counted (part (1) of the proof of `thm:gadget`:
"`N_min := max(1, ⌈(ζ_1 + Λ)/δ⌉)`"): the counted parameter rule for the levels `1, …, k − 1`
(`ruleC`), `δ = 1/(3μ^in_1)` (two operations), `Θ` (`gΘC`), `Λ` (`gΛC`), and four operations: the
sum `ζ_1 + Λ`, the quotient by `δ`, the ceiling (one operation) and the maximum with `1` (not in
the paper). -/
def nminCount (μin : ℕ → ℕ) (k : ℕ) : Counted ℕ :=
  ruleC μin (k - 1) >>=ᶜ fun r =>
  Counted.ops 2 ((1 : ℝ) / (3 * μin 0)) >>=ᶜ fun δ =>
  gΘC k r.1 r.2.2 >>=ᶜ fun Θ =>
  gΛC k r.1 r.2.2 Θ >>=ᶜ fun Λ =>
  Counted.ops 4 (max 1 ⌈(ζ₁ + Λ) / δ⌉₊)

/-- The comb `I(μ^in, N)` from the data `L` of level `k − 1`, `Θ` and the weights `ω_g` of the cut
form of `g`, counted (part (1) of the proof of `thm:gadget`: "For an integer `N ≥ N_min`, put
`Λ' := δN − ζ_1 ≥ Λ`, `f_c := g + Λ't − Θβ⁻¹`, `q := q_{k−1}`, and `α_Γ := δN`. The output
`I(μ^in, N)` is the instance `(f_c, m, β)` plus a capped linear summand `e_g` (`lem:ops`(c)) with
the capacity `C_g := (q + κ)α_Γ` and the share `α_∘ := α_Γ`, so that `β_{e_g} = 1/(q + κ)`. It
comes with `q` and `p := p_{k−1} − qΛ' + Λ'm^⊤t − Θt(E) + C_g`."): `δ` (two operations), `Λ'`,
`α_Γ`, `κ = min(1, ε_0/δ)` and `C_g` (seven), the weights `ω_g(e) + Λ't_e − Θ/β_e` of the cut form
of `f_c` (`lem:cutforms`(c)(i); six per element), `β_{e_g} = α_Γ/C_g` (one), the sums `m^⊤t` and
`t(E)` (three and two per element) and `p` (seven); the cut form of the output is that of `f_c`
with an isolated node of weight `C_g` for `e_g` (`lem:cutforms`(c)(ii)), and the rewards and the
other curvatures are those of level `k − 1`: no arithmetic operation (not in the paper). -/
def combTail (μin : ℕ → ℕ) (k N : ℕ) (L : Level (Gr (k - 1))) (Θ : ℝ)
    (ωg : Gr (k - 1) → ℝ) : Counted (SubsetSum.Comb k) :=
  Counted.ops 2 ((1 : ℝ) / (3 * μin 0)) >>=ᶜ fun δ =>
  Counted.ops 2 (δ * N - ζ₁) >>=ᶜ fun Λ' =>
  Counted.ops 1 (δ * N) >>=ᶜ fun αΓ =>
  Counted.ops 2 (min 1 (ε₀ / δ)) >>=ᶜ fun κ =>
  Counted.ops 2 ((L.q + κ) * αΓ) >>=ᶜ fun Cg =>
  table (fun e => Counted.ops 6 (ωg e + (Λ' * (L.m e / L.β e) - Θ * (1 / L.β e)))) >>=ᶜ fun ω =>
  Counted.ops 1 (αΓ / Cg) >>=ᶜ fun βg =>
  Counted.sum univ (fun e => Counted.ops 2 (L.m e * (L.m e / L.β e))) >>=ᶜ fun smt =>
  Counted.sum univ (fun e => Counted.ops 1 (L.m e / L.β e)) >>=ᶜ fun st =>
  Counted.ops 7 (L.p - L.q * Λ' + Λ' * smt - Θ * st + Cg) >>=ᶜ fun p =>
  ret ⟨(⟨(formT μin (k - 1)).D, (formT μin (k - 1)).loopless, (formT μin (k - 1)).cap,
      (formT μin (k - 1)).cap_nonneg, ω⟩ : CutForm (Gr (k - 1))).dsumForm (CutForm.node Cg),
    Sum.elim L.m fun _ => 1, Sum.elim L.β fun _ => βg, δ, κ, p, L.q⟩

/-- The comb `I(μ^in, N)` with its cut form, rewards, curvatures, width, dip and line, counted: the
counted parameter rule for the levels `1, …, k − 1` (`ruleC`), `Θ` (`gΘC`), the weights of the cut
form of `g` (`formωC`), and the rest (`combTail`) (not in the paper). -/
def combCount (μin : ℕ → ℕ) (k N : ℕ) : Counted (SubsetSum.Comb k) :=
  ruleC μin (k - 1) >>=ᶜ fun r =>
  gΘC k r.1 r.2.2 >>=ᶜ fun Θ =>
  formωC (k - 1) r.2.2 >>=ᶜ fun ωg =>
  combTail μin k N r.1 Θ ωg

variable {μin : ℕ → ℕ}

/-- The counted weights are those of the cut form of `g_j` (not in the paper). -/
lemma formωC_val : ∀ j (ns : StepNums j), ns.OK μin → (formωC j ns).val = (formT μin j).ω
  | 0, .nil, _ => rfl
  | j + 1, .cons ns F1 F2 K d, ⟨hns, h1, h2, h3, h4⟩ => by
    subst h1 h2 h3 h4
    have ih := formωC_val j ns hns
    have hd : ∑ e, (lvl μin j).dE' (μT μin (j + 1)) e =
        ∑ e, (stepD μin j).dStep (mT μin j) (βT μin j) e :=
      sum_congr rfl fun e _ => (Level.dStep_eq (lvl μin j) (μT μin (j + 1)) (R1T μin j) e).symm
    funext o
    rcases o with _ | _ | _ | c
    · simp only [formωC, val_bind, val_sum, val_ret, val_ops, ih, hd, Option.elim]
      rfl
    · simp only [formωC, val_bind, val_sum, val_ret, val_ops, ih, Option.elim]
      rfl
    · simp only [formωC, val_bind, val_sum, val_ret, val_ops, ih, Option.elim]
      rfl
    · simp only [formωC, val_bind, val_sum, val_ret, val_ops, ih, Option.elim]
      rfl

/-- `gΘC` returns `Θ` (not in the paper). -/
lemma gΘC_val (k : ℕ) {ns : StepNums (k - 1)} (hns : ns.OK μin) :
    (gΘC k (lvl μin (k - 1)) ns).val = gΘ μin k := by
  simp only [gΘC, val_supC, val_bind, val_ops, gTC_val (k - 1) ns hns]
  rfl

/-- `gΛC` returns `Λ` (not in the paper). -/
lemma gΛC_val (k : ℕ) {ns : StepNums (k - 1)} (hns : ns.OK μin) :
    (gΛC k (lvl μin (k - 1)) ns (gΘ μin k)).val = gΛ μin k := by
  simp only [gΛC, val_supC, val_bind, val_ops, gTC_val (k - 1) ns hns]
  rfl

/-- The counted algorithm returns `N_min(μ^in)` (not in the paper). -/
lemma nminCount_val (k : ℕ) : (nminCount μin k).val = gNmin μin k := by
  obtain ⟨h1, -, h3⟩ := ruleC_val (μin := μin) (k - 1)
  have e1 : (nminCount μin k).val = max 1 ⌈(ζ₁ + (gΛC k (ruleC μin (k - 1)).val.1
      (ruleC μin (k - 1)).val.2.2 (gΘC k (ruleC μin (k - 1)).val.1
        (ruleC μin (k - 1)).val.2.2).val).val) / (1 / (3 * (μin 0 : ℝ)))⌉₊ := rfl
  rw [e1, h1, gΘC_val k h3, gΛC_val k h3]
  rfl

/-- The counted algorithm returns the comb `I(μ^in, N)` of the reduction (not in the paper). -/
lemma combCount_val (k N : ℕ) : (combCount μin k N).val = SubsetSum.gadgetComb μin k N := by
  obtain ⟨h1, -, h3⟩ := ruleC_val (μin := μin) (k - 1)
  have e1 : (combCount μin k N).val = (combTail μin k N (ruleC μin (k - 1)).val.1
      (gΘC k (ruleC μin (k - 1)).val.1 (ruleC μin (k - 1)).val.2.2).val
      (formωC (k - 1) (ruleC μin (k - 1)).val.2.2).val).val := rfl
  rw [e1, formωC_val (k - 1) _ h3, h1, gΘC_val k h3]
  rfl

/-- The weights of the cut form of `g_j` take `(3j² + 9j)/2` operations (not in the paper). -/
lemma formωC_cost : ∀ j (ns : StepNums j),
    2 * (formωC j ns).cost.1 = 3 * j ^ 2 + 9 * j ∧ (formωC j ns).cost.2 = 0
  | 0, .nil => ⟨rfl, rfl⟩
  | j + 1, .cons ns F1 F2 K d => by
    have ih := formωC_cost j ns
    have hc : Fintype.card (Option (Option (Gr j))) = 3 * (j + 1) + 2 := by
      simp only [Fintype.card_option, card_Gr_eq]
    have h : (formωC (j + 1) (.cons ns F1 F2 K d)).cost = (formωC j ns).cost +
        ((∑ e : Option (Option (Gr j)), (ret (d e)).cost + ((univ : Finset _).card, 0, 0)) +
          ((1, 0, 0) + (ret (0 : ℝ)).cost)) := rfl
    rw [h]
    simp only [cost_ret, sum_const_zero, zero_add, add_zero, Prod.fst_add, Prod.snd_add, card_univ,
      hc, ih.2]
    refine ⟨?_, rfl⟩
    have := ih.1
    nlinarith

/-- `Θ` takes at most `|E|(c + 4)` operations, where `c = 3(k − 1)² + 15(k − 1) + 3` bounds one
evaluation of `g` (`gTC_cost`) and `|E| = 3k` (not in the paper). -/
lemma gΘC_cost {k : ℕ} (hk : 1 ≤ k) (L : Level (Gr (k - 1))) (ns : StepNums (k - 1)) :
    (gΘC k L ns).cost.1 ≤ 3 * k * (3 * (k - 1) ^ 2 + 15 * (k - 1) + 7) ∧
      (gΘC k L ns).cost.2 = 0 := by
  have hg := fun S => gTC_cost (k - 1) ns S
  have hcard : Fintype.card (Gr (k - 1)) ≤ 3 * k := by rw [card_Gr_eq]; omega
  simp only [gΘC, cost_supC, cost_bind, cost_ops, Prod.fst_add, Prod.fst_sum, Prod.snd_add,
    Prod.snd_sum, card_univ]
  constructor
  · have h1 : ∀ e ∈ (univ : Finset (Gr (k - 1))),
        (gTC (k - 1) ns {e}).cost.1 + 3 ≤ 3 * (k - 1) ^ 2 + 15 * (k - 1) + 6 :=
      fun e _ => by have := (hg {e}).1; omega
    have h2 := sum_le_sum h1
    rw [sum_const, card_univ, smul_eq_mul] at h2
    have h3 : Fintype.card (Gr (k - 1)) * (3 * (k - 1) ^ 2 + 15 * (k - 1) + 7) ≤
        3 * k * (3 * (k - 1) ^ 2 + 15 * (k - 1) + 7) := Nat.mul_le_mul_right _ hcard
    nlinarith
  · simp [(hg _).2]

/-- `Λ` takes at most `c + 1 + |E|(c + 6)` operations, with `c` and `|E| = 3k` as for `Θ` (not in
the paper). -/
lemma gΛC_cost {k : ℕ} (hk : 1 ≤ k) (L : Level (Gr (k - 1))) (ns : StepNums (k - 1))
    (Θ : ℝ) :
    (gΛC k L ns Θ).cost.1 ≤
      3 * (k - 1) ^ 2 + 15 * (k - 1) + 4 + 3 * k * (3 * (k - 1) ^ 2 + 15 * (k - 1) + 9) ∧
      (gΛC k L ns Θ).cost.2 = 0 := by
  have hg := fun S => gTC_cost (k - 1) ns S
  have hcard : Fintype.card (Gr (k - 1)) ≤ 3 * k := by rw [card_Gr_eq]; omega
  simp only [gΛC, cost_supC, cost_bind, cost_ops, Prod.fst_add, Prod.fst_sum, Prod.snd_add,
    Prod.snd_sum, card_univ]
  constructor
  · have h1 : ∀ e ∈ (univ : Finset (Gr (k - 1))),
        (gTC (k - 1) ns (univ.erase e)).cost.1 + 5 ≤ 3 * (k - 1) ^ 2 + 15 * (k - 1) + 8 :=
      fun e _ => by have := (hg (univ.erase e)).1; omega
    have h2 := sum_le_sum h1
    rw [sum_const, card_univ, smul_eq_mul] at h2
    have h3 : Fintype.card (Gr (k - 1)) * (3 * (k - 1) ^ 2 + 15 * (k - 1) + 9) ≤
        3 * k * (3 * (k - 1) ^ 2 + 15 * (k - 1) + 9) := Nat.mul_le_mul_right _ hcard
    have h4 := (hg univ).1
    nlinarith
  · simp [(hg _).2]

/-- The rest of the comb takes `17 + 11|E|` operations (not in the paper). -/
lemma combTail_cost (μin : ℕ → ℕ) (k N : ℕ) (L : Level (Gr (k - 1))) (Θ : ℝ)
    (ωg : Gr (k - 1) → ℝ) :
    (combTail μin k N L Θ ωg).cost = (17 + 11 * Fintype.card (Gr (k - 1)), 0, 0) := by
  simp only [combTail, cost_bind, cost_ops, cost_table, cost_sum, cost_ret, sum_const, card_univ,
    Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, by simp⟩
  simp
  ring

/-- `N_min(μ^in)` takes at most `18k³ + 70k² + 37k` arithmetic operations, `O(k³)`: the rule's
`O(k²)` and the `2|E| + 1` evaluations of `g`, `O(k²)` each (part (4) of the proof of
`thm:gadget`), and no oracle calls (not in the paper). -/
lemma nminCount_cost {k : ℕ} (hk : 1 ≤ k) :
    (nminCount μin k).cost.1 ≤ 18 * k ^ 3 + 70 * k ^ 2 + 37 * k ∧
      (nminCount μin k).cost.2 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hr, hr2⟩ := ruleC_cost (μin := μin) (j + 1 - 1)
  have hΘ := gΘC_cost hk (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2
  have hΛ := gΛC_cost hk (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2
    (gΘC (j + 1) (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2).val
  have h : (nminCount μin (j + 1)).cost = (ruleC μin (j + 1 - 1)).cost + ((2, 0, 0) +
      ((gΘC (j + 1) (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2).cost +
      ((gΛC (j + 1) (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2
        (gΘC (j + 1) (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2).val).cost +
      (4, 0, 0)))) := rfl
  rw [h, Prod.fst_add, Prod.fst_add, Prod.fst_add, Prod.fst_add, Prod.snd_add, Prod.snd_add,
    Prod.snd_add, Prod.snd_add, hr2, hΘ.2, hΛ.2]
  refine ⟨?_, rfl⟩
  have e1 := hΘ.1
  have e2 := hΛ.1
  simp only [Nat.add_sub_cancel] at hr e1 e2 ⊢
  nlinarith

/-- The comb takes at most `9k³ + 41k² + 71k` arithmetic operations, `O(k³)`: the rule's `O(k²)`,
the `|E|` evaluations of `g` for `Θ`, the weights of the cut form (`O(k²)`) and the rest
(`O(k)`), and no oracle calls (not in the paper). -/
lemma combCount_cost {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    (combCount μin k N).cost.1 ≤ 9 * k ^ 3 + 41 * k ^ 2 + 71 * k ∧
      (combCount μin k N).cost.2 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hr, hr2⟩ := ruleC_cost (μin := μin) (j + 1 - 1)
  have hΘ := gΘC_cost hk (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2
  obtain ⟨hω, hω2⟩ := formωC_cost (j + 1 - 1) (ruleC μin (j + 1 - 1)).val.2.2
  have ht := combTail_cost μin (j + 1) N (ruleC μin (j + 1 - 1)).val.1
    (gΘC (j + 1) (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2).val
    (formωC (j + 1 - 1) (ruleC μin (j + 1 - 1)).val.2.2).val
  have h : (combCount μin (j + 1) N).cost = (ruleC μin (j + 1 - 1)).cost +
      ((gΘC (j + 1) (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2).cost +
      ((formωC (j + 1 - 1) (ruleC μin (j + 1 - 1)).val.2.2).cost +
      (combTail μin (j + 1) N (ruleC μin (j + 1 - 1)).val.1
        (gΘC (j + 1) (ruleC μin (j + 1 - 1)).val.1 (ruleC μin (j + 1 - 1)).val.2.2).val
        (formωC (j + 1 - 1) (ruleC μin (j + 1 - 1)).val.2.2).val).cost)) := rfl
  rw [h, ht, Prod.fst_add, Prod.fst_add, Prod.fst_add, Prod.snd_add, Prod.snd_add, Prod.snd_add,
    hr2, hΘ.2, hω2]
  refine ⟨?_, rfl⟩
  have e1 := hΘ.1
  rw [card_Gr_eq]
  simp only [Nat.add_sub_cancel] at hr e1 hω ⊢
  nlinarith

/-- The cost of the algorithm of `thm:gadget` (`SubsetSum.GadgetCost`, the parameter of the counted
reduction): the costs of the counted programs `nminCount` and `combCount`, which return
`N_min(μ^in)` and the comb `I(μ^in, N)` (`nminCount_val`, `combCount_val`) (not in the paper).
The two are counted as separate runs: each runs the parameter rule (`ruleC`) and computes `δ` and
`Θ` itself, so the four calls of the reduction count the rule and `Θ` four times, where the
algorithm of `thm:gadget` would compute them once for each input `μ^in`; the counts are upper bounds
on that algorithm (not in the paper). -/
def gadgetCost : SubsetSum.GadgetCost :=
  ⟨fun μin k => (nminCount μin k).cost, fun μin k N => (combCount μin k N).cost⟩

/-- **The reduction of `def:reduction`, counted with the algorithm of `thm:gadget`** (the proof of
`thm:nphard`, `stoc-sections/appD-hardness.tex:1885-1887`: "The reduction of `def:reduction` runs in
time polynomial in the encoding length of `(a, T)`. Indeed, the algorithm of `thm:gadget` computes
`N_0` and both combs in polynomial time, …"): with the cost `gadgetCost` of the four calls of the
algorithm of `thm:gadget`, the counted reduction returns the pair after step (1) and the output of
`def:reduction` with at most `2^{35}⟨(a, T)⟩ + 2^9⟨(a, T)⟩³` arithmetic operations and no oracle
calls (not in the paper: the paper counts in prose).

The steps: (1) the reduction without the gadget, at most `2^{35}⟨(a, T)⟩` operations
(`SubsetSum.reductionC_spec`); (2) the four calls, `N_min(μ)`, `N_min(μ')`, `I_1` and `I_2`, at most
`2(18k'³ + 70k'² + 37k') + 2(9k'³ + 41k'² + 71k') ≤ 2^9 k'³` operations (`nminCount_cost`,
`combCount_cost`), with `1 ≤ k' ≤ k ≤ ⟨(a, T)⟩` items after step (1) (`SubsetSum.step1_k_le`,
`SubsetSum.k_le_encLen`). -/
theorem reductionC_gadget (P : SubsetSum) :
    (SubsetSum.reductionC gadgetCost P).val = ⟨P.step1, P.step1.output⟩ ∧
    (SubsetSum.reductionC gadgetCost P).cost.1 ≤ 2 ^ 35 * P.encLen + 2 ^ 9 * P.encLen ^ 3 ∧
    (SubsetSum.reductionC gadgetCost P).cost.2 = 0 := by
  obtain ⟨hval, J, -, -, -, hc1, hc2⟩ := SubsetSum.reductionC_spec gadgetCost P
  have hk := P.step1.one_le_k
  have hkE : P.step1.k ≤ P.encLen :=
    (SubsetSum.step1_k_le P).trans (SubsetSum.k_le_encLen P).1
  obtain ⟨n1, n1'⟩ := nminCount_cost (μin := P.step1.μ) hk
  obtain ⟨n2, n2'⟩ := nminCount_cost (μin := P.step1.μ') hk
  obtain ⟨c1, c1'⟩ := combCount_cost (μin := P.step1.μ) hk P.step1.N₀
  obtain ⟨c2, c2'⟩ := combCount_cost (μin := P.step1.μ') hk P.step1.N₂
  have htot : (gadgetCost.total P.step1).1 ≤ 2 ^ 9 * P.encLen ^ 3 := by
    simp only [SubsetSum.GadgetCost.total, gadgetCost, Prod.fst_add]
    have h3 : P.step1.k ^ 3 ≤ P.encLen ^ 3 := Nat.pow_le_pow_left hkE 3
    have h2 : P.step1.k ^ 2 ≤ P.step1.k ^ 3 := Nat.pow_le_pow_right hk (by norm_num)
    have h1 : P.step1.k ≤ P.step1.k ^ 3 := by
      calc P.step1.k = P.step1.k ^ 1 := (pow_one _).symm
        _ ≤ P.step1.k ^ 3 := Nat.pow_le_pow_right hk (by norm_num)
    nlinarith
  refine ⟨hval, hc1.trans (by omega), ?_⟩
  rw [hc2]
  simp only [SubsetSum.GadgetCost.total, gadgetCost, Prod.snd_add, n1', n2', c1', c2']
  rfl

end

end Hardness

end Stoc
