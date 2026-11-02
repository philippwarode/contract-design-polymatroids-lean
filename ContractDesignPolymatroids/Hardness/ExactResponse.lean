-- stamp r11 2026-11-02
import ContractDesignPolymatroids.Hardness.CutForms

/-!
# Exact best responses: `lem:exactbr`

The STOC version's `lem:exactbr` (Appendix C.8, `sec:D-npcomplete`, "Exact best responses and
NP-completeness", `stoc-sections/appD-hardness.tex:1799-1807`, proof lines 1809-1881). The lemma is
about the bit model: for an instance `(f, m, β)` of `𝒞_cut` with the cut form `(D, cap, ω)` and a
rational share `α ≥ 0`, (a) `x*(α)` is rational with short coordinates, (b) `x = x*(α)` is decided
and (c) `x*(α)` is computed in polynomial time, by maximum flows. The encoding lengths, the test of
(b) and the search of (c) are in `ContractDesignPolymatroids/Hardness/ExactBits.lean`; the maximum flows (Edmonds-Karp,
which the paper cites from `[Sch03, Thm. 10.5]`, and the criterion for minimum cuts by residual
networks, cited from `[GGT89, §2.1–2.2]`) are cited, and arithmetic operations are not counted. As
in the paper, `y ∈ ℚ^E` (here `y : E → ℝ`) is a vector, `cut_D + y` is the function
`S ↦ cut_D(S) + y(S)`, and `G_y` is the network of (b). This file formalises the mathematics of the
three parts of the proof:

* (a): `chainA` (`A_0 = ∅`, `A_i = A_{ϱ_i}(α)`) and `blockD` (`D_i = A_i ∖ A_{i−1}`) for the
  distinct positive values `ϱ_1 > ⋯ > ϱ_k` of `ρ = ρ(α)` (`theta ρ 0`, as in the proof of
  `prop:optchar`; indices from `0`: `theta ρ 0 i` is `ϱ_{i+1}`); `marg_blockD`: step (3) of the
  proof; the D3 lemmas `chainA_subset` (`A_{i−1} ⊆ A_i`), `blockD_nonempty` (`D_i ≠ ∅`) and
  `exists_mem_blockD` (every element of `A_k` lies in a block); `exactbr_a`: `eq:D-explicit`, and
  that `x*(α)` is rational for rational data;
* (b): the network `G_y` (`netCap`, `netCut`, `srcSide`): `netCut_srcSide` (the capacity of the
  cut `{s} ∪ S`), `isMinimiser_iff` (minimizers of `cut_D + y` are the source sides of minimum
  cuts), and `exactbr_b`: the criterion of `prop:optchar` with the at most `|E|` level sets at the
  positive values of `ρ(x)`, and the condition `x ∈ P₊(f)` as a minimum of `cut_D + (ω − x)`;
* (c): `exactbr_c`: the steps of the proof that hold for every `θ`, `A_θ(α) = A_i` for
  `ϱ_{i+1} < θ ≤ ϱ_i`, and `A_θ(α)` is the largest minimizer of `F_{α,θ} = cut_D + (ω − αt + θβ⁻¹)`
  (`thm:levelsets`); the steps of the search for `A_1, …, A_k`, with the step `h = 2^{−2Ω}` and the
  shares `jh` of the bit model, are `varrho_bounds` and `searchRound_spec` in
  `ContractDesignPolymatroids/Hardness/ExactBits.lean`.

Taken over on 2026-10-20 from `Paper/Hardness/ExactResponse.lean` (the paper at Overleaf f035b19)
for the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace Hardness

open Finset

noncomputable section

section Exact

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ} {α : ℝ}

/-- The chain of the proof of `lem:exactbr`(a): `A_0 := ∅` and `A_i := A_{ϱ_i}(α)` for `i ≥ 1`,
where `ϱ_i = theta ρ 0 (i − 1)` is the `i`-th largest positive value of `ρ = ρ(x)`. -/
def chainA (m β : E → ℝ) (α : ℝ) (x : E → ℝ) : ℕ → Finset E
  | 0 => ∅
  | i + 1 => levelSet m β α x (theta (marg m β α x) 0 i)

/-- The blocks `D_i := A_i ∖ A_{i−1}` (`i ≥ 1`). -/
def blockD (m β : E → ℝ) (α : ℝ) (x : E → ℝ) (i : ℕ) : Finset E :=
  chainA m β α x (i + 1) \ chainA m β α x i

/-- A real number is rational: it lies in the image of `ℚ` (the subfield
`(Rat.castHom ℝ).fieldRange`). -/
def IsRat (r : ℝ) : Prop := r ∈ (Rat.castHom ℝ).fieldRange

omit [DecidableEq E] in
/-- `ϱ_i > 0` for `i ≤ k` and `ϱ_{k+1} = 0`, so all `theta ρ 0 j` are nonnegative (not in the
paper: the proof of `lem:exactbr` leaves this implicit). -/
lemma theta_nonneg {ρ : E → ℝ} (j : ℕ) : 0 ≤ theta ρ 0 j := by
  rcases lt_or_ge j (numVals ρ 0) with hj | hj
  · exact (c_lt_theta hj).le
  · rw [theta_of_le hj]

omit [DecidableEq E] in
/-- A value of `ρ` above `ϱ_{i+2}` is at least `ϱ_{i+1}` (indices from `0`: above `theta (i + 1)`
it is at least `theta i`), as the `ϱ_j` are all the positive values of `ρ` (not in the paper: the
proof of `lem:exactbr` leaves this implicit). -/
lemma theta_le_of_lt {ρ : E → ℝ} {i : ℕ} (hi : i < numVals ρ 0) {e : E}
    (he : theta ρ 0 (i + 1) < ρ e) : theta ρ 0 i ≤ ρ e := by
  obtain ⟨j, hj, hθj⟩ := exists_theta_eq ((theta_nonneg (i + 1)).trans_lt he)
  rw [← hθj] at he ⊢
  have hji : j ≤ i := by
    by_contra h'
    push Not at h'
    have : theta ρ 0 j ≤ theta ρ 0 (i + 1) := by
      rcases (show i + 1 ≤ j by omega).lt_or_eq with hlt | heq
      · exact (theta_lt_theta hlt hj.le).le
      · rw [heq]
    linarith
  exact (theta_le_theta_iff hi hj).2 hji

omit [DecidableEq E] in
/-- The chain increases: `A_{i−1} ⊆ A_i` for `i ≤ k` (indices from `0`: `A_i ⊆ A_{i+1}` for
`i < k`), as `ϱ_i > ϱ_{i+1}` (not in the paper: the proof of `lem:exactbr`(a) leaves this
implicit). -/
lemma chainA_subset {x : E → ℝ} {i : ℕ} (hi : i < numVals (marg m β α x) 0) :
    chainA m β α x i ⊆ chainA m β α x (i + 1) := by
  intro e he
  rcases i with _ | i
  · exact absurd he (notMem_empty e)
  · simp only [chainA, levelSet, mem_filter, mem_univ, true_and] at he ⊢
    exact (theta_lt_theta (Nat.lt_succ_self i) hi.le).le.trans he

/-- The blocks are nonempty: `D_i ≠ ∅` for `i ≤ k`, as `ϱ_i` is a value of `ρ` (indices from `0`)
(not in the paper: the proof of `lem:exactbr`(a) uses `D_i ≠ ∅` without proof). -/
lemma blockD_nonempty {x : E → ℝ} {i : ℕ} (hi : i < numVals (marg m β α x) 0) :
    (blockD m β α x i).Nonempty := by
  obtain ⟨e, -, he⟩ := mem_image.1 (mem_filter.1 (theta_mem hi)).1
  refine ⟨e, mem_sdiff.2 ⟨?_, ?_⟩⟩
  · simp only [chainA, levelSet, mem_filter, mem_univ, true_and]
    exact he.ge
  · rcases i with _ | i
    · exact notMem_empty e
    · simp only [chainA, levelSet, mem_filter, mem_univ, true_and, not_le]
      rw [he]
      exact theta_lt_theta (Nat.lt_succ_self i) hi.le

/-- Step (3) of the proof of `lem:exactbr`(a), for `ρ ≥ 0`: "Then `ρ_e = ϱ_i` for `e ∈ D_i`, also
if `x_e = 0`, and `ρ_e = 0` for `e ∈ E ∖ A_k`" (indices from `0`). -/
lemma marg_blockD {x : E → ℝ} (hρ : ∀ e, 0 ≤ marg m β α x e) :
    (∀ i < numVals (marg m β α x) 0, ∀ e ∈ blockD m β α x i,
      marg m β α x e = theta (marg m β α x) 0 i) ∧
    (∀ e, e ∉ chainA m β α x (numVals (marg m β α x) 0) → marg m β α x e = 0) := by
  refine ⟨fun i hi e he => ?_, fun e he => ?_⟩
  · obtain ⟨he1, he2⟩ := mem_sdiff.1 he
    simp only [chainA, levelSet, mem_filter, mem_univ, true_and] at he1
    obtain ⟨j, hj, hθj⟩ := exists_theta_eq ((c_lt_theta hi).trans_le he1)
    rw [← hθj] at he1 ⊢
    have hji : j ≤ i := (theta_le_theta_iff hi hj).1 he1
    rcases hji.lt_or_eq with hlt | rfl
    · exfalso
      rcases i with _ | i
      · omega
      · apply he2
        simp only [chainA, levelSet, mem_filter, mem_univ, true_and]
        rw [← hθj]
        exact (theta_le_theta_iff (by omega) hj).2 (by omega)
    · rfl
  · rcases (hρ e).lt_or_eq with hlt | heq
    · exfalso
      obtain ⟨j, hj, hθj⟩ := exists_theta_eq hlt
      apply he
      obtain ⟨k', hk'⟩ : ∃ k', numVals (marg m β α x) 0 = k' + 1 :=
        ⟨numVals (marg m β α x) 0 - 1, by omega⟩
      rw [hk']
      simp only [chainA, levelSet, mem_filter, mem_univ, true_and]
      rw [← hθj]
      exact (theta_le_theta_iff (by omega) hj).2 (by omega)
    · exact heq.symm

/-- Every element of `A_k` lies in a block `D_j`, `j ≤ k` (indices from `0`), so that
`eq:D-explicit` gives `x_e` for every `e ∈ E` (not in the paper: the proof of `lem:exactbr`(a)
leaves `A_k = D_1 ∪ ⋯ ∪ D_k` implicit). -/
lemma exists_mem_blockD {x : E → ℝ} {e : E}
    (he : e ∈ chainA m β α x (numVals (marg m β α x) 0)) :
    ∃ j < numVals (marg m β α x) 0, e ∈ blockD m β α x j := by
  have hρe : 0 < marg m β α x e := by
    rcases hk : numVals (marg m β α x) 0 with _ | k
    · rw [hk] at he
      exact absurd he (notMem_empty e)
    · rw [hk] at he
      simp only [chainA, levelSet, mem_filter, mem_univ, true_and] at he
      exact (c_lt_theta (show k < numVals (marg m β α x) 0 by omega)).trans_le he
  obtain ⟨j, hj, hθj⟩ := exists_theta_eq hρe
  refine ⟨j, hj, mem_sdiff.2 ⟨?_, ?_⟩⟩
  · simp only [chainA, levelSet, mem_filter, mem_univ, true_and]
    exact hθj.le
  · rcases j with _ | j
    · exact notMem_empty e
    · simp only [chainA, levelSet, mem_filter, mem_univ, true_and, not_le]
      rw [← hθj]
      exact theta_lt_theta (Nat.lt_succ_self j) hj.le

/-- **`lem:exactbr`(a)** (`stoc-sections/appD-hardness.tex:1802`, proof lines 1814-1841), its
mathematical part: let `(f, m, β)` be an instance of `𝒞_cut` and `α ≥ 0`, let `x := x*(α)` with
the marginals `ρ = αm − βx`, the distinct positive values `ϱ_1 > ⋯ > ϱ_k` of `ρ` (`theta ρ 0`,
indices from `0`), `A_0 := ∅`, `A_i := A_{ϱ_i}(α)` and `D_i := A_i ∖ A_{i−1}`. Then
(`eq:D-explicit`) `ϱ_i = (αt(D_i) − f(A_i) + f(A_{i−1}))/β⁻¹(D_i)`,
`x_e = (αm_e − ϱ_i)/β_e` for `e ∈ D_i`, and `x_e = αt_e` for `e ∈ E ∖ A_k`; in particular, if `α`,
the rewards, the curvatures and the capacities and weights of a cut form of `f` are rational, then
`x*(α)` is a rational vector. (The encoding-length bound `6⟨α⟩ + 31⟨I⟩` is `exactbr_a_enc`.)

The proof's steps: (1) by `prop:optchar`, `ρ ≥ 0`, and every level set `A_θ(α)`, `θ > 0`, is
tight for `x`; (2) with the distinct positive values `ϱ_1 > ⋯ > ϱ_k` (as in the proof of
`prop:optchar`) the sets `A_i` are tight; (3) `ρ_e = ϱ_i` for `e ∈ D_i`, also if `x_e = 0`, and
`ρ_e = 0` for `e ∈ E ∖ A_k` (`marg_blockD`); (4) summing `x_e = (αm_e − ρ_e)/β_e` over `D_i` gives
`f(A_i) − f(A_{i−1}) = x(D_i) = αt(D_i) − ϱ_iβ⁻¹(D_i)`, one linear equation for `ϱ_i`, with
`β⁻¹(D_i) > 0` as `D_i ≠ ∅`; (5) hence `eq:D-explicit`; (6) in particular, `x` is rational.
The D3 lemmas: `chainA_subset` (`A_{i−1} ⊆ A_i`, used in (4)), `blockD_nonempty` (`D_i ≠ ∅`,
used in (4)) and `exists_mem_blockD` (every `e ∈ A_k` lies in a block, used in (6)). -/
theorem exactbr_a (hI : Ccut f m β) (hα : 0 ≤ α) {x : E → ℝ} (hx : x = bestResponse f m β α) :
    (∀ i < numVals (marg m β α x) 0, theta (marg m β α x) 0 i =
      (α * ∑ e ∈ blockD m β α x i, m e / β e - f (chainA m β α x (i + 1)) +
        f (chainA m β α x i)) / ∑ e ∈ blockD m β α x i, 1 / β e) ∧
    (∀ i < numVals (marg m β α x) 0, ∀ e ∈ blockD m β α x i,
      x e = (α * m e - theta (marg m β α x) 0 i) / β e) ∧
    (∀ e, e ∉ chainA m β α x (numVals (marg m β α x) 0) → x e = α * (m e / β e)) ∧
    ∀ F : CutForm E, (∀ S, f S = F.fn S) → (∀ a ∈ F.D, IsRat (F.cap a)) → (∀ e, IsRat (F.ω e)) →
      (∀ e, IsRat (m e)) → (∀ e, IsRat (β e)) → IsRat α → ∀ e, IsRat (x e) := by
  have hf := hI.rank
  have hβ := hI.β_pos
  have hm : ∀ e, 0 ≤ α * m e := fun e => mul_nonneg hα (hI.m_pos e).le
  -- (1) "By `prop:optchar`, `ρ ≥ 0`, and every level set `A_θ(α) = {e ∈ E : ρ_e ≥ θ}` with
  -- `θ > 0` is tight for `x`."
  obtain ⟨-, hρ, htight⟩ := (isBestResponse_iff_levelSets hf hβ hm).1
    (hx ▸ isBestResponse_bestResponse hf m β α)
  -- (2) "As in the proof of `prop:optchar`, let `ϱ_1 > ⋯ > ϱ_k` be the distinct positive values
  -- of `ρ`, and let `A_i := A_{ϱ_i}(α)` for `i = 1, …, k`. These sets are tight for `x`."
  -- (`A_0 = ∅` is tight as well.)
  have hA : ∀ i ≤ numVals (marg m β α x) 0, IsTight f x (chainA m β α x i) := by
    intro i hi
    rcases i with _ | i
    · simp [chainA, IsTight, hf.empty]
    · exact htight _ (c_lt_theta (by omega))
  -- (3) "Then `ρ_e = ϱ_i` for `e ∈ D_i`, also if `x_e = 0`, and `ρ_e = 0` for `e ∈ E ∖ A_k`."
  obtain ⟨hblock, hout⟩ := marg_blockD (m := m) (β := β) (α := α) (x := x) hρ
  -- (4) "Summing `x_e = (αm_e − ρ_e)/β_e` over `D_i` gives
  -- `f(A_i) − f(A_{i−1}) = x(D_i) = αt(D_i) − ϱ_iβ⁻¹(D_i)`, one linear equation for `ϱ_i`, with
  -- `β⁻¹(D_i) > 0` as `D_i ≠ ∅`."
  have hcoord : ∀ e, x e = (α * m e - marg m β α x e) / β e := fun e => by
    have := (hβ e).ne'
    simp only [marg]
    field_simp
    ring
  have hlin : ∀ i < numVals (marg m β α x) 0,
      f (chainA m β α x (i + 1)) - f (chainA m β α x i) =
        α * ∑ e ∈ blockD m β α x i, m e / β e -
          theta (marg m β α x) 0 i * ∑ e ∈ blockD m β α x i, 1 / β e := by
    intro i hi
    have h1 := hA (i + 1) hi
    have h2 := hA i hi.le
    unfold IsTight at h1 h2
    have hsplit : ∑ e ∈ chainA m β α x (i + 1), x e =
        ∑ e ∈ blockD m β α x i, x e + ∑ e ∈ chainA m β α x i, x e :=
      (sum_sdiff (chainA_subset hi)).symm
    rw [← h1, ← h2, hsplit, add_sub_cancel_right, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun e he => ?_
    rw [hcoord e, hblock i hi e he]
    have := (hβ e).ne'
    field_simp
  have hpos : ∀ i < numVals (marg m β α x) 0, 0 < ∑ e ∈ blockD m β α x i, 1 / β e := fun i hi =>
    sum_pos (fun e _ => one_div_pos.2 (hβ e)) (blockD_nonempty hi)
  -- (5) "Hence `ϱ_i = (αt(D_i) − f(A_i) + f(A_{i−1}))/β⁻¹(D_i)` for `i = 1, …, k`,
  -- `x_e = (αm_e − ϱ_i)/β_e` for `e ∈ D_i` and `i = 1, …, k`, `x_e = αt_e` for `e ∈ E ∖ A_k`."
  -- (`eq:D-explicit`)
  have h5a : ∀ i < numVals (marg m β α x) 0, theta (marg m β α x) 0 i =
      (α * ∑ e ∈ blockD m β α x i, m e / β e - f (chainA m β α x (i + 1)) +
        f (chainA m β α x i)) / ∑ e ∈ blockD m β α x i, 1 / β e := by
    intro i hi
    rw [eq_div_iff (hpos i hi).ne']
    linarith [hlin i hi]
  have h5b : ∀ i < numVals (marg m β α x) 0, ∀ e ∈ blockD m β α x i,
      x e = (α * m e - theta (marg m β α x) 0 i) / β e :=
    fun i hi e he => by rw [hcoord e, hblock i hi e he]
  have h5c : ∀ e, e ∉ chainA m β α x (numVals (marg m β α x) 0) → x e = α * (m e / β e) :=
    fun e he => by rw [hcoord e, hout e he, sub_zero, mul_div_assoc]
  refine ⟨h5a, h5b, h5c, fun F hF hcap hω hmq hβq hαq e => ?_⟩
  -- (6) "In particular, `x` is rational."
  set K := (Rat.castHom ℝ).fieldRange
  have hfq : ∀ S, IsRat (f S) := fun S => by
    rw [hF S]
    exact K.add_mem (K.sum_mem fun a ha => hcap a (mem_filter.1 ha).1) (K.sum_mem fun e _ => hω e)
  have htq : ∀ S : Finset E, IsRat (∑ e ∈ S, m e / β e) := fun S =>
    K.sum_mem fun e _ => K.div_mem (hmq e) (hβq e)
  have hbq : ∀ S : Finset E, IsRat (∑ e ∈ S, 1 / β e) := fun S =>
    K.sum_mem fun e _ => K.div_mem K.one_mem (hβq e)
  by_cases he : e ∈ chainA m β α x (numVals (marg m β α x) 0)
  · -- `e` lies in some block `D_j` (`exists_mem_blockD`)
    obtain ⟨j, hj, heD⟩ := exists_mem_blockD he
    rw [h5b j hj e heD, h5a j hj]
    exact K.div_mem (K.sub_mem (K.mul_mem hαq (hmq e))
      (K.div_mem (K.add_mem (K.sub_mem (K.mul_mem hαq (htq _)) (hfq _)) (hfq _)) (hbq _)))
      (hβq e)
  · rw [h5c e he]
    exact K.mul_mem hαq (K.div_mem (hmq e) (hβq e))

end Exact

/-! ### (b): the network `G_y` -/

section Network

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The network `G_y` of `lem:exactbr`(b) on the nodes `Option (Option E)`: the source
`s = none`, the sink `s' = some none` and the nodes `some (some e)` of `E`, with the arcs of `D`
and their capacities, an arc `s → e` of capacity `max(−y_e, 0)` and an arc `e → s'` of capacity
`max(y_e, 0)` for every `e ∈ E`; `netCap a b` is the capacity of the arc `a → b` (`0` if there is
none). -/
def netCap (F : CutForm E) (y : E → ℝ) : Option (Option E) → Option (Option E) → ℝ
  | none, some (some e) => max (-y e) 0
  | some (some e), some none => max (y e) 0
  | some (some u), some (some v) => if (u, v) ∈ F.D then F.cap (u, v) else 0
  | _, _ => 0

/-- The total capacity of the arcs of `G_y` that leave a set `U` of nodes. -/
def netCut (F : CutForm E) (y : E → ℝ) (U : Finset (Option (Option E))) : ℝ :=
  ∑ a, ∑ b, if a ∈ U ∧ b ∉ U then netCap F y a b else 0

/-- The source side `{s} ∪ S`. -/
def srcSide (S : Finset E) : Finset (Option (Option E)) :=
  insert none (S.image fun e => some (some e))

omit [Fintype E] in
@[simp] lemma none_mem_srcSide (S : Finset E) : none ∈ srcSide S := mem_insert_self _ _

omit [Fintype E] in
@[simp] lemma some_none_notMem_srcSide (S : Finset E) : some none ∉ srcSide S := by
  simp [srcSide]

omit [Fintype E] in
@[simp] lemma some_some_mem_srcSide (S : Finset E) (e : E) :
    some (some e) ∈ srcSide S ↔ e ∈ S := by
  simp [srcSide]

/-- **`lem:exactbr`(b)**, the capacity of a cut (`stoc-sections/appD-hardness.tex:1845-1850`): the
arcs of `G_y` that leave `{s} ∪ S` have total capacity
`cut_D(S) + ∑_{e∈S} max(y_e, 0) + ∑_{e∈E∖S} max(−y_e, 0) = cut_D(S) + y(S) + ∑_e max(−y_e, 0)`, as
`max(y_e, 0) − max(−y_e, 0) = y_e`. -/
theorem netCut_srcSide (F : CutForm E) (y : E → ℝ) (S : Finset E) :
    netCut F y (srcSide S) = F.cut S + ∑ e ∈ S, y e + ∑ e, max (-y e) 0 := by
  have key : ∀ e : E, ((if e ∉ S then max (-y e) 0 else 0) + if e ∈ S then max (y e) 0 else 0) =
      max (-y e) 0 + if e ∈ S then y e else 0 := by
    intro e
    by_cases he : e ∈ S
    · simp only [he, not_true_eq_false, ↓reduceIte, zero_add]
      rcases le_total 0 (y e) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring
    · simp [he]
  have hsum := sum_congr (s₁ := (univ : Finset E)) rfl fun e _ => key e
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have hy : ∑ e ∈ S, y e = ∑ e, if e ∈ S then y e else 0 := by
    rw [sum_ite_mem, univ_inter]
  have hcut : F.cut S = ∑ u, ∑ v, if u ∈ S ∧ v ∉ S then
      (if (u, v) ∈ F.D then F.cap (u, v) else 0) else 0 := by
    have h1 : F.cut S = ∑ a : E × E,
        (if a.1 ∈ S ∧ a.2 ∉ S then (if a ∈ F.D then F.cap a else 0) else 0) := by
      unfold CutForm.cut
      rw [sum_filter]
      calc ∑ a ∈ F.D, (if a.1 ∈ S ∧ a.2 ∉ S then F.cap a else 0)
          = ∑ a ∈ F.D, (if a.1 ∈ S ∧ a.2 ∉ S then (if a ∈ F.D then F.cap a else 0) else 0) :=
            sum_congr rfl fun a ha => by simp [ha]
        _ = ∑ a, (if a.1 ∈ S ∧ a.2 ∉ S then (if a ∈ F.D then F.cap a else 0) else 0) :=
            sum_subset (subset_univ _) fun a _ ha => by simp [ha]
    rw [h1, Fintype.sum_prod_type]
  unfold netCut
  rw [hcut]
  simp only [Fintype.sum_option, none_mem_srcSide, some_none_notMem_srcSide,
    some_some_mem_srcSide, true_and, false_and, not_true_eq_false, not_false_eq_true, and_true,
    and_false, ↓reduceIte, netCap, zero_add, sum_const_zero, sum_add_distrib]
  rw [hy]
  linarith

/-- Every set of nodes that contains `s` and not `s'` is the source side `{s} ∪ S` of the set `S`
of its nodes in `E` (not in the paper: the proof of `lem:exactbr`(b) uses this without proof). -/
theorem eq_srcSide {U : Finset (Option (Option E))} (hs : none ∈ U) (hs' : some none ∉ U) :
    U = srcSide (univ.filter fun e => some (some e) ∈ U) := by
  ext a
  rcases a with _ | _ | e <;> simp [hs, hs']

/-- **`lem:exactbr`(b)**, the minimizers (`stoc-sections/appD-hardness.tex:1851`): `S` minimizes
`cut_D + y` if and only if `{s} ∪ S` is the source side of a minimum `s`-`s'` cut of `G_y`. -/
theorem isMinimiser_iff (F : CutForm E) (y : E → ℝ) (S : Finset E) :
    (∀ S', F.cut S + ∑ e ∈ S, y e ≤ F.cut S' + ∑ e ∈ S', y e) ↔
      ∀ U : Finset (Option (Option E)), none ∈ U → some none ∉ U →
        netCut F y (srcSide S) ≤ netCut F y U := by
  constructor
  · intro h U hs hs'
    rw [eq_srcSide hs hs', netCut_srcSide, netCut_srcSide]
    linarith [h (univ.filter fun e => some (some e) ∈ U)]
  · intro h S'
    have := h (srcSide S') (by simp) (by simp)
    rw [netCut_srcSide, netCut_srcSide] at this
    linarith

variable {f : Finset E → ℝ} {m β : E → ℝ} {α : ℝ}

/-- **`lem:exactbr`(b)** (`stoc-sections/appD-hardness.tex:1856-1860`), its mathematical part: for
`α ≥ 0` and `x ∈ ℝ^E`, by `prop:optchar`, `x = x*(α)` if and only if `x ≥ 0`, `ρ(x) ≥ 0`,
`x(S) ≤ f(S)` for every `S ⊆ E`, and the at most `|E|` sets `A_θ(x)`, for the positive values `θ`
of `ρ(x)`, are tight for `x`; and the third condition says that `cut_D + (ω − x)`, which vanishes
at `∅`, has minimum `0`, that is, that `{s}` is the source side of a minimum cut of `G_{ω−x}`.
(The decision procedure, with its comparisons, evaluations and maximum flow, is `exactbr_b_enc`.)

The proof's steps: (1) `prop:optchar`, (2) "Indeed, every set `A_θ(x)` with `θ > 0` is one of them
or empty" (`levelSet_eq_theta`), (3) the third condition as a minimum of `cut_D + (ω − x)`
(`isMinimiser_iff`). -/
theorem exactbr_b (hI : Ccut f m β) (hα : 0 ≤ α) {F : CutForm E} (hF : ∀ S, f S = F.fn S)
    (x : E → ℝ) :
    (x = bestResponse f m β α ↔
      (∀ e, 0 ≤ x e) ∧ (∀ e, 0 ≤ marg m β α x e) ∧ (∀ S, ∑ e ∈ S, x e ≤ f S) ∧
        ∀ i < numVals (marg m β α x) 0,
          IsTight f x (levelSet m β α x (theta (marg m β α x) 0 i))) ∧
    ((∀ S, ∑ e ∈ S, x e ≤ f S) ↔
      ∀ U : Finset (Option (Option E)), none ∈ U → some none ∉ U →
        netCut F (fun e => F.ω e - x e) (srcSide ∅) ≤ netCut F (fun e => F.ω e - x e) U) := by
  have hf := hI.rank
  have hβ := hI.β_pos
  have hm : ∀ e, 0 ≤ α * m e := fun e => mul_nonneg hα (hI.m_pos e).le
  refine ⟨?_, ?_⟩
  · -- (1) "By `prop:optchar`, `x = x*(α)` if and only if `x ≥ 0`, `ρ(x) ≥ 0`, `x(S) ≤ f(S)` for
    -- every `S ⊆ E`, and the at most `|E|` sets `A_θ(x)`, for the positive values `θ` of `ρ(x)`,
    -- are tight for `x`."
    constructor
    · rintro rfl
      obtain ⟨hx, hρ, ht⟩ := (isBestResponse_iff_levelSets hf hβ hm).1
        (isBestResponse_bestResponse hf m β α)
      exact ⟨hx.1, hρ, hx.2, fun i hi => ht _ (c_lt_theta hi)⟩
    · rintro ⟨hx0, hρ, hxf, ht⟩
      refine ((isBestResponse_iff_levelSets hf hβ hm).2
        ⟨⟨hx0, hxf⟩, hρ, fun θ hθ => ?_⟩).eq_bestResponse hβ hf
      -- (2) "Indeed, every set `A_θ(x)` with `θ > 0` is one of them or empty."
      rcases levelSet_eq_theta (ρ := marg m β α x) hθ with h | ⟨i, hi, h⟩
      · rw [show levelSet m β α x θ = ∅ from h]
        simp [IsTight, hf.empty]
      · rw [show levelSet m β α x θ = levelSet m β α x (theta (marg m β α x) 0 i) from h]
        exact ht i hi
  · -- (3) "The third condition says that `cut_D + (ω − x)`, which vanishes at `∅`, has minimum
    -- `0`, and one maximum flow in `G_{ω−x}` decides it."
    -- The Lean: the minimum is `0` if and only if `{s}` is the source side of a minimum cut of
    -- `G_{ω−x}` (`isMinimiser_iff`); the maximum flow is cited (`exactbr_b_enc`).
    rw [← isMinimiser_iff]
    have h0 : F.cut ∅ = 0 := by simp [CutForm.cut]
    simp only [h0, sum_empty, zero_add]
    refine forall_congr' fun S => ?_
    rw [hF S]
    unfold CutForm.fn
    rw [sum_sub_distrib]
    constructor <;> intro h <;> linarith

end Network

/-! ### (c): the level sets and the search -/

section Search

variable {E : Type*} [Fintype E] [DecidableEq E] {f : Finset E → ℝ} {m β : E → ℝ} {α : ℝ}

/-- **`lem:exactbr`(c)** (`stoc-sections/appD-hardness.tex:1862-1880`), its first two steps, which
the paper states for every `θ`: for `(f, m, β) ∈ 𝒞_cut` with the cut form `(D, cap, ω)`, `α ≥ 0`,
`x = x*(α)`, `ρ = ρ(α)`, `ϱ_1 > ⋯ > ϱ_k` and `A_0, …, A_k` as in (a) (`theta ρ 0`, `chainA`;
`ϱ_{k+1} := 0`): (1) `A_θ(α) = A_i` for `ϱ_{i+1} < θ ≤ ϱ_i` (`i = 1, …, k`), and
`A_θ(α) = A_0 = ∅` for `θ > ϱ_1`; (2) by `thm:levelsets`, `A_θ(α)` is the largest minimizer of
`F_{α,θ} = f − αt + θβ⁻¹ = cut_D + (ω − αt + θβ⁻¹)`, so `{s} ∪ A_θ(α)` is the source side of a
minimum cut of `G_{ω−αt+θβ⁻¹}`. The rest of the proof works in the bit model, with
`h := 2^{−2Ω}` and the shares `θ = jh`, `j ∈ {1, …, 2^{3Ω}}`: the bounds on the `ϱ_i` are
`varrho_bounds`, and the round of the search ("As `0 < h < ϱ_k`, …", "Otherwise `i < k`, …" and the
binary search) is `searchRound_spec`, both in `ContractDesignPolymatroids/Hardness/ExactBits.lean`. -/
theorem exactbr_c (hI : Ccut f m β) (hα : 0 ≤ α) {F : CutForm E} (hF : ∀ S, f S = F.fn S)
    {x : E → ℝ} (hx : x = bestResponse f m β α) :
    -- (1)
    (∀ θ, theta (marg m β α x) 0 0 < θ → levelSet m β α x θ = chainA m β α x 0) ∧
    (∀ i < numVals (marg m β α x) 0, ∀ θ, theta (marg m β α x) 0 (i + 1) < θ →
      θ ≤ theta (marg m β α x) 0 i → levelSet m β α x θ = chainA m β α x (i + 1)) ∧
    -- (2)
    ∀ θ, 0 < θ →
      (∀ S, levelFun f m β α θ S =
        F.cut S + ∑ e ∈ S, (F.ω e - α * (m e / β e) + θ * (1 / β e))) ∧
      (∀ S, levelFun f m β α θ (levelSet m β α x θ) ≤ levelFun f m β α θ S) ∧
      (∀ S, levelFun f m β α θ S ≤ levelFun f m β α θ (levelSet m β α x θ) →
        S ⊆ levelSet m β α x θ) ∧
      ∀ U : Finset (Option (Option E)), none ∈ U → some none ∉ U →
        netCut F (fun e => F.ω e - α * (m e / β e) + θ * (1 / β e))
            (srcSide (levelSet m β α x θ)) ≤
          netCut F (fun e => F.ω e - α * (m e / β e) + θ * (1 / β e)) U := by
  have hf := hI.rank
  have hβ := hI.β_pos
  have hm : ∀ e, 0 ≤ α * m e := fun e => mul_nonneg hα (hI.m_pos e).le
  have hxb : IsBestResponse (indepPoly f) m β α x := hx ▸ isBestResponse_bestResponse hf m β α
  -- (1) "Then `A_θ(α) = A_i` for `ϱ_{i+1} < θ ≤ ϱ_i` and `i = 0, …, k`."
  have h1 : ∀ i < numVals (marg m β α x) 0, ∀ θ, theta (marg m β α x) 0 (i + 1) < θ →
      θ ≤ theta (marg m β α x) 0 i → levelSet m β α x θ = chainA m β α x (i + 1) := by
    intro i hi θ hθ1 hθ2
    ext e
    simp only [chainA, levelSet, mem_filter, mem_univ, true_and]
    exact ⟨fun he => theta_le_of_lt hi (hθ1.trans_le he), fun he => hθ2.trans he⟩
  have h0 : ∀ θ, theta (marg m β α x) 0 0 < θ → levelSet m β α x θ = chainA m β α x 0 := by
    intro θ hθ
    refine eq_empty_iff_forall_notMem.2 fun e he => ?_
    simp only [levelSet, mem_filter, mem_univ, true_and] at he
    obtain ⟨j, hj, hθj⟩ := exists_theta_eq ((theta_nonneg 0).trans_lt (hθ.trans_le he))
    have := (theta_le_theta_iff hj (show 0 < numVals (marg m β α x) 0 by omega)).2
      (Nat.zero_le j)
    change theta (marg m β α x) 0 j ≤ theta (marg m β α x) 0 0 at this
    rw [hθj] at this
    linarith
  refine ⟨h0, h1, fun θ hθ => ?_⟩
  -- (2) "By `thm:levelsets`, `A_θ(α)` is the largest minimizer of
  -- `F_{α,θ}(S) = f(S) − αt(S) + θβ⁻¹(S) = cut_D(S) + (ω − αt + θβ⁻¹)(S)`, where `t` and `β⁻¹`
  -- also denote the vectors `(t_e)_{e∈E}` and `(β_e^{−1})_{e∈E}`."
  have hF' : ∀ S, levelFun f m β α θ S =
      F.cut S + ∑ e ∈ S, (F.ω e - α * (m e / β e) + θ * (1 / β e)) := fun S => by
    simp only [levelFun, hF S, CutForm.fn, sum_add_distrib, sum_sub_distrib, mul_sum]
    ring
  obtain ⟨hmin, hmax⟩ := hxb.levelSet_isMaxMinimiser hf hβ hm hθ
  refine ⟨hF', hmin, hmax, ?_⟩
  -- "So, for rational `θ`, it is computed by one maximum flow in `G_{ω−αt+θβ⁻¹}`, as in (b)."
  refine (isMinimiser_iff F _ _).1 fun S' => ?_
  have := hmin S'
  rw [hF', hF'] at this
  exact this

end Search

end

end Hardness

end Stoc
