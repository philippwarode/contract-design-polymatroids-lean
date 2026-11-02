-- stamp r8 2026-11-02
import Stoc.Preliminaries.Polymatroid

/-!
# The greedy algorithm for polymatroids

Edmonds' greedy theorem, which the STOC version cites in Appendix A.2 (`sec:A-linear`,
`stoc-sections/appA-proofs.tex:28`): "We use Edmonds' greedy theorem [Edm03, (16)–(19)], allowing
activities with zero coefficient to receive their greedy allocation, since this does not change the
objective value." Appendix A.2 applies it to the greedy response (`appA-proofs.tex:31, 54, 67, 81`;
`Stoc.Linear.xstar_max`, `Stoc.Linear.tiebreak`); the proofs of `prop:optchar`
(`appB-quadratic.tex:25-27`) and `thm:polybits` (`appC-bits.tex:283-285`) cite it as
[Edm03, (19)].

* `greedy_pos`: Edmonds' greedy theorem as Edmonds states it (not in the paper: the STOC version
  cites it), for an enumeration `e₁, …, eₙ` of `E` (here `σ`, with `e_{j+1} = σ j`) along which
  `a` is nonincreasing and `k` the number of elements with `a_e > 0`: the vector `x̄` with
  `x̄_{e_i} = f(S_i) − f(S_{i−1})` for `i ≤ k` and `x̄_{e_i} = 0` for `i > k` (`edmondsVec`) lies
  in `P₊(f)` and maximizes `aᵀx` over `P₊(f)`. Proved here by the greedy argument below. The
  proofs of `prop:optchar` and `thm:polybits` use this form.
* `greedy`: the theorem as Appendix A.2 uses it, with `k` the number of elements with `a_e ≥ 0`:
  the activities with zero coefficient receive their greedy allocation, "since this does not change
  the objective value". It follows from `greedy_pos` by that sentence.
* `sortEquiv`: the enumeration of `E` along an injective key. The STOC version's orders by
  nonincreasing weights (the permutation `π` of Appendix A.2, the order of the marginals in the
  proof of `prop:optchar`) are given by keys.
* `eq_prefixSet_card`, `sum_prefixSet_edmondsVec`: a set that contains, with each element, all
  earlier ones is a prefix `S_j`, and `x̄(S_j) = f(S_j)` for `j ≤ k` (used with Edmonds' greedy
  theorem in the proof of `prop:optchar`).

The greedy argument, for the cited theorem: the elements are ordered by an injective key
`κ : E → K`, and the greedy vector is filled on a set `F` that comes first in this order
(`IsInitial`). `greedyVec_mem`: the greedy vector lies in `P₊(f)` (`x̄(S) ≤ f(S)` by induction
over `S`, with diminishing returns). `greedyVec_optimal`: it maximizes `aᵀx` over `P₊(f)` if `a`
is nonincreasing along the order on `F`, nonnegative on `F` and nonpositive outside `F` (induction
over `F`, removing its last element `e*`: on `F`, `a = a_{e*} + (a − a_{e*})`; the constant part
gives `a_{e*} x(F) ≤ a_{e*} f(F) = a_{e*} x̄(F)`, and `a − a_{e*}` is again nonnegative and
nonincreasing on `F ∖ {e*}`).

Taken over on 2026-10-20 from `Paper/Linear/Greedy.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version. Until Max Klimm's final
revision (repository 429ca68) the STOC version stated and proved the theorem as `thm:greedy`
(Theorem A.2); it now cites it, and `greedy` follows the sentence that cites it.
-/

namespace Stoc

open Finset Function

variable {E : Type*} [Fintype E] [DecidableEq E] {K : Type*} [LinearOrder K]

/-- The elements that come strictly before `e` in the order given by the key `κ`. -/
def before (κ : E → K) (e : E) : Finset E :=
  univ.filter fun e' => κ e' < κ e

/-- The greedy increment `f(before e ∪ {e}) − f(before e)` of `e`. -/
def greedyStep (f : Finset E → ℝ) (κ : E → K) (e : E) : ℝ :=
  f (insert e (before κ e)) - f (before κ e)

/-- The greedy vector along `κ`, filled on `F`: the greedy increment on `F`, zero elsewhere. -/
def greedyVec (f : Finset E → ℝ) (κ : E → K) (F : Finset E) (e : E) : ℝ :=
  if e ∈ F then greedyStep f κ e else 0

/-- `F` comes first in the order given by `κ`. -/
def IsInitial (κ : E → K) (F : Finset E) : Prop :=
  ∀ e ∈ F, ∀ e', κ e' < κ e → e' ∈ F

variable {f : Finset E → ℝ} {κ : E → K}

theorem greedyStep_nonneg (hf : IsRankFunction f) (e : E) : 0 ≤ greedyStep f κ e :=
  sub_nonneg.2 (hf.mono (subset_insert _ _))

omit [DecidableEq E] in
theorem subset_before (hκ : Injective κ) {a : E} {s : Finset E} (ha : a ∉ s)
    (hs : ∀ x ∈ s, κ x ≤ κ a) : s ⊆ before κ a := by
  intro x hx
  simp only [before, mem_filter, mem_univ, true_and]
  exact lt_of_le_of_ne (hs x hx) fun h => ha (hκ h ▸ hx)

omit [DecidableEq E] in
theorem not_mem_before (a : E) : a ∉ before κ a := by
  simp [before]

theorem before_eq_of_isInitial (hκ : Injective κ) {a : E} {s : Finset E}
    (hF : IsInitial κ (insert a s)) (ha : a ∉ s) (hs : ∀ x ∈ s, κ x ≤ κ a) :
    before κ a = s := by
  refine Subset.antisymm (fun x hx => ?_) (subset_before hκ ha hs)
  have hx' : κ x < κ a := by simpa [before] using hx
  rcases mem_insert.1 (hF a (mem_insert_self a s) x hx') with rfl | h
  · exact absurd hx' (lt_irrefl _)
  · exact h

omit [Fintype E] in
theorem IsInitial.of_insert {a : E} {s : Finset E} (hF : IsInitial κ (insert a s))
    (hs : ∀ x ∈ s, κ x ≤ κ a) : IsInitial κ s := by
  intro e he e' he'
  rcases mem_insert.1 (hF e (mem_insert_of_mem he) e' he') with rfl | h
  · exact absurd (lt_of_lt_of_le he' (hs e he)) (lt_irrefl _)
  · exact h

/-- Telescoping: on a set that comes first, the greedy increments add up to `f(F)`. -/
theorem sum_greedyStep (hf : f ∅ = 0) (hκ : Injective κ) (F : Finset E)
    (hF : IsInitial κ F) : ∑ e ∈ F, greedyStep f κ e = f F := by
  induction F using Finset.induction_on_max_value κ with
  | empty => simp [hf]
  | insert a s ha hs ih =>
    rw [sum_insert ha, ih (hF.of_insert hs)]
    unfold greedyStep
    rw [before_eq_of_isInitial hκ hF ha hs]
    ring

/-- The greedy increments of any set `S` add up to at most `f(S)`. -/
theorem sum_greedyStep_le (hf : IsRankFunction f) (hκ : Injective κ) (S : Finset E) :
    ∑ e ∈ S, greedyStep f κ e ≤ f S := by
  induction S using Finset.induction_on_max_value κ with
  | empty => simp [hf.empty]
  | insert a s ha hs ih =>
    rw [sum_insert ha]
    have h : greedyStep f κ a ≤ f (insert a s) - f s :=
      hf.submod.diminishingReturns (subset_before hκ ha hs) (not_mem_before a)
    linarith

/-- Feasibility: the greedy vector lies in `P₊(f)`. -/
theorem greedyVec_mem (hf : IsRankFunction f) (hκ : Injective κ) (F : Finset E) :
    greedyVec f κ F ∈ indepPoly f := by
  have hle : ∀ e, greedyVec f κ F e ≤ greedyStep f κ e := fun e => by
    unfold greedyVec
    split_ifs
    · exact le_rfl
    · exact greedyStep_nonneg hf e
  refine ⟨fun e => ?_, fun S => (sum_le_sum fun e _ => hle e).trans (sum_greedyStep_le hf hκ S)⟩
  unfold greedyVec
  split_ifs
  · exact greedyStep_nonneg hf e
  · exact le_rfl

/-- The core of optimality: on a set `F` that comes first, weights that are nonnegative and
nonincreasing along the order give `aᵀy ≤ aᵀx̄` on `F`. -/
theorem sum_mul_le_sum_mul_greedyStep (hf : IsRankFunction f) (hκ : Injective κ)
    {y : E → ℝ} (hy : y ∈ indepPoly f) (F : Finset E) (hF : IsInitial κ F) (a : E → ℝ)
    (ha : ∀ e ∈ F, ∀ e' ∈ F, κ e ≤ κ e' → a e' ≤ a e) (ha0 : ∀ e ∈ F, 0 ≤ a e) :
    ∑ e ∈ F, a e * y e ≤ ∑ e ∈ F, a e * greedyStep f κ e := by
  induction F using Finset.induction_on_max_value κ generalizing a with
  | empty => simp
  | insert b s hb hs ih =>
    set c := a b with hc
    have hc0 : 0 ≤ c := ha0 b (mem_insert_self b s)
    have ih' := ih (hF.of_insert hs) (fun e => a e - c)
      (fun e he e' he' hle => by
        have := ha e (mem_insert_of_mem he) e' (mem_insert_of_mem he') hle
        linarith)
      (fun e he => by
        have := ha e (mem_insert_of_mem he) b (mem_insert_self b s) (hs e he)
        linarith)
    have hyF := hy.2 (insert b s)
    have htel := sum_greedyStep hf.empty hκ (insert b s) hF
    -- Split off the constant part `c = a(b)` of the weights.
    have split : ∀ z : E → ℝ, ∑ e ∈ insert b s, a e * z e =
        c * ∑ e ∈ insert b s, z e + ∑ e ∈ s, (a e - c) * z e := by
      intro z
      rw [sum_insert hb, sum_insert hb]
      have : ∑ e ∈ s, (a e - c) * z e = ∑ e ∈ s, a e * z e - c * ∑ e ∈ s, z e := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun e _ => by ring
      rw [this]
      ring
    rw [split y, split (greedyStep f κ), htel]
    have := mul_le_mul_of_nonneg_left hyF hc0
    linarith

/-- Optimality of the greedy vector. -/
theorem greedyVec_optimal (hf : IsRankFunction f) (hκ : Injective κ) (F : Finset E)
    (hF : IsInitial κ F) (a : E → ℝ)
    (ha : ∀ e ∈ F, ∀ e' ∈ F, κ e ≤ κ e' → a e' ≤ a e) (ha0 : ∀ e ∈ F, 0 ≤ a e)
    (ha1 : ∀ e ∉ F, a e ≤ 0) {y : E → ℝ} (hy : y ∈ indepPoly f) :
    ∑ e, a e * y e ≤ ∑ e, a e * greedyVec f κ F e := by
  have h1 : ∑ e, a e * y e ≤ ∑ e ∈ F, a e * y e := by
    rw [← sum_add_sum_compl F (fun e => a e * y e)]
    have : ∑ e ∈ Fᶜ, a e * y e ≤ 0 :=
      sum_nonpos fun e he => mul_nonpos_of_nonpos_of_nonneg (ha1 e (mem_compl.1 he)) (hy.1 e)
    linarith
  have h2 : ∑ e, a e * greedyVec f κ F e = ∑ e ∈ F, a e * greedyStep f κ e := by
    simp only [greedyVec, mul_ite, mul_zero]
    rw [sum_ite_mem, univ_inter]
  rw [h2]
  exact h1.trans (sum_mul_le_sum_mul_greedyStep hf hκ hy F hF a ha ha0)

/-! ### Edmonds' greedy theorem -/

variable {n : ℕ}

/-- `S_i = {e₁, …, e_i}` for the enumeration `e_{j+1} = σ j`. -/
def prefixSet (σ : Fin n ≃ E) (i : ℕ) : Finset E :=
  univ.filter fun e => (σ.symm e : ℕ) < i

/-- The vector of Edmonds' greedy theorem: `x̄_{e_i} = f(S_i) − f(S_{i−1})` for `i ≤ k` and
`x̄_{e_i} = 0` for `i > k`. For `e = e_i` we have `σ.symm e = i − 1`. -/
def edmondsVec (f : Finset E → ℝ) (σ : Fin n ≃ E) (k : ℕ) (e : E) : ℝ :=
  if (σ.symm e : ℕ) < k then f (prefixSet σ (σ.symm e + 1)) - f (prefixSet σ (σ.symm e))
  else 0

omit [DecidableEq E] in
theorem card_filter_symm_lt (σ : Fin n ≃ E) (j : Fin n) :
    #(univ.filter fun e => σ.symm e < j) = j := by
  have : (univ.filter fun e => σ.symm e < j) = (Iio j).map σ.toEmbedding := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Iio, Equiv.coe_toEmbedding]
    constructor
    · intro h
      exact ⟨σ.symm e, h, σ.apply_symm_apply e⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [this, card_map, Fin.card_Iio]

omit [DecidableEq E] in
theorem card_filter_symm_le (σ : Fin n ≃ E) (j : Fin n) :
    #(univ.filter fun e => σ.symm e ≤ j) = j + 1 := by
  have : (univ.filter fun e => σ.symm e ≤ j) = (Iic j).map σ.toEmbedding := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_map, mem_Iic, Equiv.coe_toEmbedding]
    constructor
    · intro h
      exact ⟨σ.symm e, h, σ.apply_symm_apply e⟩
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  rw [this, card_map, Fin.card_Iic]

omit [DecidableEq E] in
/-- For weights that are nonincreasing along the enumeration, the first `k` elements are
exactly those with nonnegative weight (not in the paper: the STOC version uses this without proof
where it lets the activities with zero coefficient receive their greedy allocation, `greedy`, and
where it identifies the greedy response of (`eq:A-greedy`), with its increments at the weakly
profitable elements `ρ_e ≥ 0`, with the vector of Edmonds' greedy theorem,
`Stoc.Linear.greedyResp_eq_edmondsVec`). -/
theorem lt_card_nonneg_iff (σ : Fin n ≃ E) {a : E → ℝ} (ha : Antitone (a ∘ σ)) (e : E) :
    (σ.symm e : ℕ) < #(univ.filter fun e => 0 ≤ a e) ↔ 0 ≤ a e := by
  have hae : ∀ e', a e' = (a ∘ σ) (σ.symm e') := fun e' => by simp
  constructor
  · intro h
    by_contra hneg
    rw [not_le] at hneg
    have hsub : (univ.filter fun e => 0 ≤ a e) ⊆ univ.filter fun e' => σ.symm e' < σ.symm e := by
      intro e' he'
      simp only [mem_filter, mem_univ, true_and] at he' ⊢
      by_contra hlt
      rw [not_lt] at hlt
      have := ha hlt
      rw [← hae, ← hae] at this
      linarith
    have := card_le_card hsub
    rw [card_filter_symm_lt] at this
    omega
  · intro h
    by_contra hge
    rw [not_lt] at hge
    have hsub : (univ.filter fun e' => σ.symm e' ≤ σ.symm e) ⊆ univ.filter fun e => 0 ≤ a e := by
      intro e' he'
      simp only [mem_filter, mem_univ, true_and] at he' ⊢
      have := ha he'
      rw [← hae, ← hae] at this
      linarith
    have := card_le_card hsub
    rw [card_filter_symm_le] at this
    omega

omit [DecidableEq E] in
theorem prefixSet_eq_before (σ : Fin n ≃ E) (e : E) :
    prefixSet σ (σ.symm e) = before σ.symm e := by
  ext e'
  simp only [prefixSet, before, mem_filter, mem_univ, true_and]
  exact Fin.lt_def.symm

theorem prefixSet_succ_eq_insert_before (σ : Fin n ≃ E) (e : E) :
    prefixSet σ (σ.symm e + 1) = insert e (before σ.symm e) := by
  ext e'
  simp only [prefixSet, before, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inr (Fin.lt_def.2 h)
    · exact Or.inl (σ.symm.injective (Fin.ext h))
  · rintro (rfl | h)
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (Fin.lt_def.1 h)

omit [DecidableEq E] in
/-- A set that contains, with each of its elements, all earlier elements of the enumeration is the
prefix `S_j` with `j = |A|` (not in the paper: the STOC version uses this without proof in the
proof of `prop:optchar`, where the level sets `A_i` are prefixes of the order in which it applies
Edmonds' greedy theorem). -/
theorem eq_prefixSet_card (σ : Fin n ≃ E) {A : Finset E}
    (hA : ∀ e ∈ A, ∀ e', σ.symm e' ≤ σ.symm e → e' ∈ A) : A = prefixSet σ #A := by
  ext e
  simp only [prefixSet, mem_filter, mem_univ, true_and]
  constructor
  · -- The `σ⁻¹(e) + 1` elements up to `e` lie in `A`.
    intro he
    have hsub : (univ.filter fun e' => σ.symm e' ≤ σ.symm e) ⊆ A := fun e' he' =>
      hA e he e' (mem_filter.1 he').2
    have := card_le_card hsub
    rw [card_filter_symm_le] at this
    omega
  · -- Otherwise `A` lies among the `σ⁻¹(e)` elements before `e`.
    intro he
    by_contra heA
    have hsub : A ⊆ univ.filter fun e' => σ.symm e' < σ.symm e := by
      intro e' he'
      simp only [mem_filter, mem_univ, true_and]
      by_contra h
      exact heA (hA e' he' e (not_lt.1 h))
    have := card_le_card hsub
    rw [card_filter_symm_lt] at this
    omega

/-- The increments of `x̄` add up along a prefix: `x̄(S_j) = f(S_j)` for `j ≤ k` (not in the paper:
the STOC version uses this without proof in the proof of `prop:optchar`, "By Edmonds' greedy
theorem [Edm03, (19)], the maximum over `P₊(f)` is `∑_{i=1}^k (θ_i − θ_{i+1}) f(A_i)`"). -/
theorem sum_prefixSet_edmondsVec (hf0 : f ∅ = 0) (σ : Fin n ≃ E) {j k : ℕ} (hjk : j ≤ k)
    (hjn : j ≤ n) : ∑ e ∈ prefixSet σ j, edmondsVec f σ k e = f (prefixSet σ j) := by
  induction j with
  | zero => simp [prefixSet, hf0]
  | succ j ih =>
    have hj : j < n := by omega
    have hins : prefixSet σ (j + 1) = insert (σ ⟨j, hj⟩) (prefixSet σ j) := by
      ext e
      have key : e = σ ⟨j, hj⟩ ↔ (σ.symm e : ℕ) = j := by
        rw [← σ.symm_apply_eq, Fin.ext_iff]
      simp only [prefixSet, mem_filter, mem_univ, true_and, mem_insert, key]
      omega
    have hnot : σ ⟨j, hj⟩ ∉ prefixSet σ j := by simp [prefixSet]
    have hval : edmondsVec f σ k (σ ⟨j, hj⟩) = f (prefixSet σ (j + 1)) - f (prefixSet σ j) := by
      simp [edmondsVec, show j < k by omega]
    rw [hins, sum_insert hnot, ih (by omega) (by omega), hval, hins]
    ring

omit [DecidableEq E] in
/-- For weights that are nonincreasing along the enumeration, the first `k` elements, `k` the
number of elements with positive weight, are exactly those with positive weight (not in the
paper: the STOC version cites Edmonds' greedy theorem with this `k`, `greedy_pos`, and uses this
without proof where it lets the activities with zero coefficient receive their greedy allocation,
`greedy`; as `lt_card_nonneg_iff`). -/
theorem lt_card_pos_iff (σ : Fin n ≃ E) {a : E → ℝ} (ha : Antitone (a ∘ σ)) (e : E) :
    (σ.symm e : ℕ) < #(univ.filter fun e => 0 < a e) ↔ 0 < a e := by
  have hae : ∀ e', a e' = (a ∘ σ) (σ.symm e') := fun e' => by simp
  constructor
  · intro h
    by_contra hneg
    rw [not_lt] at hneg
    have hsub : (univ.filter fun e => 0 < a e) ⊆ univ.filter fun e' => σ.symm e' < σ.symm e := by
      intro e' he'
      simp only [mem_filter, mem_univ, true_and] at he' ⊢
      by_contra hlt
      rw [not_lt] at hlt
      have := ha hlt
      rw [← hae, ← hae] at this
      linarith
    have := card_le_card hsub
    rw [card_filter_symm_lt] at this
    omega
  · intro h
    by_contra hge
    rw [not_lt] at hge
    have hsub : (univ.filter fun e' => σ.symm e' ≤ σ.symm e) ⊆ univ.filter fun e => 0 < a e := by
      intro e' he'
      simp only [mem_filter, mem_univ, true_and] at he' ⊢
      have := ha he'
      rw [← hae, ← hae] at this
      linarith
    have := card_le_card hsub
    rw [card_filter_symm_le] at this
    omega

/-- The vector `x̄` of Edmonds' greedy theorem is the greedy vector along the enumeration, filled
on `S_k` (the greedy argument above with the key `σ⁻¹`). -/
theorem edmondsVec_eq_greedyVec (σ : Fin n ≃ E) (k : ℕ) :
    edmondsVec f σ k = greedyVec f σ.symm (prefixSet σ k) := by
  funext e
  rw [edmondsVec, greedyVec, greedyStep, prefixSet_succ_eq_insert_before, prefixSet_eq_before]
  simp [prefixSet]

/-- The vector `x̄` lies in `P₊(f)` for every `k` (not in the paper: the STOC version leaves
implicit that the vector stays in `P₊(f)` when the activities with zero coefficient receive their
greedy allocation, `stoc-sections/appA-proofs.tex:28`; for `k` the number of elements with
`a_e > 0` it is part of Edmonds' greedy theorem, `greedy_pos`). Its increments are those of the
greedy argument (`greedyVec_mem`). -/
theorem edmondsVec_mem (hf : IsRankFunction f) (σ : Fin n ≃ E) (k : ℕ) :
    edmondsVec f σ k ∈ indepPoly f := by
  rw [edmondsVec_eq_greedyVec]
  exact greedyVec_mem hf σ.symm.injective _

/-- Edmonds' greedy theorem [Edm03, (16)–(19)] (not in the paper: the STOC version cites it,
`stoc-sections/appA-proofs.tex:28`, and as [Edm03, (19)] in the proofs of `prop:optchar` and
`thm:polybits`): for a rank function `f`, an enumeration `e₁, …, eₙ` of `E`
(`e_{j+1} = σ j`) with `a_{e₁} ≥ ⋯ ≥ a_{eₙ}` and `k` the number of elements with `a_e > 0`, the
vector `x̄` with `x̄_{e_i} = f(S_i) − f(S_{i−1})` for `i ≤ k` and `x̄_{e_i} = 0` for `i > k` lies in
`P₊(f)` and maximizes `aᵀx` over `P₊(f)`. Proved by the greedy argument (`edmondsVec_mem`,
`greedyVec_optimal`): `S_k` comes first in the order, and the weights are positive on it
(`lt_card_pos_iff`) and nonpositive off it. -/
theorem greedy_pos (hf : IsRankFunction f) (σ : Fin n ≃ E) (a : E → ℝ) (ha : Antitone (a ∘ σ)) :
    edmondsVec f σ #(univ.filter fun e => 0 < a e) ∈ indepPoly f ∧
      ∀ x ∈ indepPoly f,
        ∑ e, a e * x e ≤ ∑ e, a e * edmondsVec f σ #(univ.filter fun e => 0 < a e) e := by
  set k := #(univ.filter fun e => 0 < a e)
  have hS : ∀ e, e ∈ prefixSet σ k ↔ 0 < a e := fun e => by
    simp only [prefixSet, mem_filter, mem_univ, true_and]
    exact lt_card_pos_iff σ ha e
  have hae : ∀ e', a e' = (a ∘ σ) (σ.symm e') := fun e' => by simp
  refine ⟨edmondsVec_mem hf σ k, fun x hx => ?_⟩
  rw [edmondsVec_eq_greedyVec]
  refine greedyVec_optimal hf σ.symm.injective (prefixSet σ k) (fun e he e' he' => ?_) a
    (fun e _ e' _ hle => ?_) (fun e he => ((hS e).1 he).le)
    (fun e he => not_lt.1 fun h => he ((hS e).2 h)) hx
  · simp only [prefixSet, mem_filter, mem_univ, true_and] at he ⊢
    exact lt_trans (Fin.lt_def.1 he') he
  · have := ha hle
    rwa [← hae, ← hae] at this

/-- Edmonds' greedy theorem as Appendix A.2 uses it (`stoc-sections/appA-proofs.tex:28`): "We use
Edmonds' greedy theorem [Edm03, (16)–(19)], allowing activities with zero coefficient to receive
their greedy allocation, since this does not change the objective value." For a rank function `f`,
an enumeration `e₁, …, eₙ` of `E` (`e_{j+1} = σ j`) with `a_{e₁} ≥ ⋯ ≥ a_{eₙ}` and `k` the number
of elements with `a_e ≥ 0`, the vector `x̄` with `x̄_{e_i} = f(S_i) − f(S_{i−1})` for `i ≤ k` and
`x̄_{e_i} = 0` for `i > k` lies in `P₊(f)` and maximizes `aᵀx` over `P₊(f)`.

The steps of the sentence: (1) Edmonds' greedy theorem (`greedy_pos`), with `k'` the number of
elements with `a_e > 0`; (2) the activities with zero coefficient, `e_i` with `k' < i ≤ k`, receive
their greedy allocation, which does not change the objective value `aᵀx̄`. That the vector stays in
`P₊(f)`, which the sentence leaves implicit, is `edmondsVec_mem` (not in the paper). -/
theorem greedy (hf : IsRankFunction f) (σ : Fin n ≃ E) (a : E → ℝ) (ha : Antitone (a ∘ σ)) :
    edmondsVec f σ #(univ.filter fun e => 0 ≤ a e) ∈ indepPoly f ∧
      ∀ x ∈ indepPoly f,
        ∑ e, a e * x e ≤ ∑ e, a e * edmondsVec f σ #(univ.filter fun e => 0 ≤ a e) e := by
  set k := #(univ.filter fun e => 0 ≤ a e)
  set k' := #(univ.filter fun e => 0 < a e)
  -- (1) "We use Edmonds' greedy theorem [Edm03, (16)–(19)]": Edmonds' vector, with `k'`, maximizes
  -- `aᵀx` over `P₊(f)`.
  obtain ⟨-, hmax⟩ := greedy_pos hf σ a ha
  -- (2) "allowing activities with zero coefficient to receive their greedy allocation, since this
  -- does not change the objective value": the two vectors differ only at elements with `a_e = 0`
  -- (`lt_card_pos_iff`, `lt_card_nonneg_iff`).
  have heq : ∑ e, a e * edmondsVec f σ k e = ∑ e, a e * edmondsVec f σ k' e := by
    refine sum_congr rfl fun e _ => ?_
    rcases lt_trichotomy (a e) 0 with hneg | hzero | hpos
    · have h1 : ¬ (σ.symm e : ℕ) < k := fun h =>
        absurd ((lt_card_nonneg_iff σ ha e).1 h) (not_le.2 hneg)
      have h2 : ¬ (σ.symm e : ℕ) < k' := fun h =>
        absurd ((lt_card_pos_iff σ ha e).1 h) (not_lt.2 hneg.le)
      simp only [edmondsVec, h1, h2, ↓reduceIte]
    · rw [hzero, zero_mul, zero_mul]
    · have h1 : (σ.symm e : ℕ) < k := (lt_card_nonneg_iff σ ha e).2 hpos.le
      have h2 : (σ.symm e : ℕ) < k' := (lt_card_pos_iff σ ha e).2 hpos
      simp only [edmondsVec, h1, h2, ↓reduceIte]
  refine ⟨edmondsVec_mem hf σ k, fun x hx => ?_⟩
  rw [heq]
  exact hmax x hx

/-! ### The enumeration along a key

The STOC version orders `E` by nonincreasing weights with a rule for ties: the permutation `π` of
the greedy response (Appendix A.2, `stoc-sections/appA-proofs.tex:36-44`), and the order of the
marginals in the proof of `prop:optchar`, where it applies Edmonds' greedy theorem. An injective key
`κ : E → K` encodes such an order (an element with a smaller key comes first), and
`sortEquiv κ hκ` is the enumeration `e₁, …, eₙ` of `E` along it (`e_{j+1} = sortEquiv κ hκ j`,
indices from 0). -/

/-- The position of `e` in the order given by `κ`, from 0: the number of elements before it. -/
def keyPos (κ : E → K) (e : E) : Fin (Fintype.card E) :=
  ⟨#(before κ e), card_lt_univ_of_notMem (not_mem_before e)⟩

omit [DecidableEq E] in
theorem keyPos_lt_iff {e e' : E} : keyPos κ e < keyPos κ e' ↔ κ e < κ e' := by
  rw [Fin.lt_def]
  show #(before κ e) < #(before κ e') ↔ κ e < κ e'
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hsub : before κ e' ⊆ before κ e := fun x hx => by
      simp only [before, mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.trans_le hle
    exact absurd (card_le_card hsub) (not_le.2 h)
  · intro h
    refine card_lt_card ((ssubset_iff_of_subset fun x hx => ?_).2 ⟨e, ?_, not_mem_before e⟩)
    · simp only [before, mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.trans h
    · simpa [before] using h

omit [DecidableEq E] in
theorem keyPos_injective (hκ : Injective κ) : Injective (keyPos κ) := by
  intro e e' h
  by_contra hne
  rcases lt_or_gt_of_ne (hκ.ne hne) with hlt | hlt
  · exact (keyPos_lt_iff.2 hlt).ne h
  · exact (keyPos_lt_iff.2 hlt).ne' h

/-- The enumeration of `E` along the key `κ`: `sortEquiv κ hκ j` is the element at position `j`. -/
noncomputable def sortEquiv (κ : E → K) (hκ : Injective κ) : Fin (Fintype.card E) ≃ E :=
  (Equiv.ofBijective (keyPos κ) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨keyPos_injective hκ, (Fintype.card_fin _).symm⟩)).symm

omit [DecidableEq E] in
theorem sortEquiv_symm_apply (hκ : Injective κ) (e : E) :
    (sortEquiv κ hκ).symm e = keyPos κ e := by
  simp only [sortEquiv, Equiv.symm_symm, Equiv.ofBijective_apply]

omit [DecidableEq E] in
/-- The enumeration runs along the key: `κ(e_{i+1}) < κ(e_{j+1})` exactly for `i < j`. -/
theorem sortEquiv_lt_iff (hκ : Injective κ) {i j : Fin (Fintype.card E)} :
    κ (sortEquiv κ hκ i) < κ (sortEquiv κ hκ j) ↔ i < j := by
  rw [← keyPos_lt_iff, ← sortEquiv_symm_apply hκ, ← sortEquiv_symm_apply hκ,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

omit [DecidableEq E] in
/-- Weights that do not increase along the key do not increase along the enumeration. -/
theorem antitone_comp_sortEquiv (hκ : Injective κ) {a : E → ℝ}
    (ha : ∀ e e', κ e < κ e' → a e' ≤ a e) : Antitone (a ∘ sortEquiv κ hκ) := by
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · exact ha _ _ ((sortEquiv_lt_iff hκ).2 hlt)
  · exact le_rfl

omit [DecidableEq E] in
/-- Keys that compare the elements in the same way give the same enumeration. -/
theorem sortEquiv_congr {K' : Type*} [LinearOrder K'] {κ' : E → K'} (hκ : Injective κ)
    (hκ' : Injective κ') (h : ∀ e e', κ e < κ e' ↔ κ' e < κ' e') :
    sortEquiv κ hκ = sortEquiv κ' hκ' := by
  have hpos : ∀ e, keyPos κ e = keyPos κ' e := fun e => by
    ext
    simp only [keyPos, before, h]
  refine Equiv.ext fun i => (sortEquiv κ' hκ').symm.injective ?_
  rw [Equiv.symm_apply_apply, sortEquiv_symm_apply hκ', ← hpos, ← sortEquiv_symm_apply hκ,
    Equiv.symm_apply_apply]

end Stoc
