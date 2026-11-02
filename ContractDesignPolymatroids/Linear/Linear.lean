-- stamp r8 2026-11-02
import ContractDesignPolymatroids.Preliminaries.Greedy

/-!
# Linear costs

The STOC version, Section 2, the paragraph "Warm-up: linear costs" (`stoc-sections/04-linear.tex`,
Theorem `thm:linear`), with the proofs in Appendix A.2 (`sec:A-linear`,
`stoc-sections/appA-proofs.tex:23-196`).

Throughout Appendix A.2 the costs are `c(x) = ∑_e c_e x_e` with `c_e ≥ 0`, and `n ≥ 1`; the
rewards `m ≥ 0` are those of the model (Section 2). The agent's utility is
`U_A(x | α) = α r(x) − c(x) = ρ(α)ᵀx` with `ρ_e(α) = α m_e − c_e` (`utilA_eq`). The contract model
of Section 2 also has a reward bound `r̄ > 0` with `r(x) ≤ r̄` on `P₊(f)`
(`stoc-sections/02-preliminaries.tex:12`); the results of this file do not use it and are stated
without it.

* The greedy response (`stoc-sections/appA-proofs.tex:30-55`): the fixed enumeration of `E` is
  the linear order on `E`; the weakly profitable elements, those with `ρ_e(α) ≥ 0`
  (`weaklyProfitable`); the permutation `π = π(α)` (`perm`) orders `E` by nonincreasing `ρ_e`,
  ties by nonincreasing `m_e` and the remaining ties by the enumeration (`sortKey`); the prefix
  `S^π_i` is `prefixSet (perm m c α) i`; and `xstar` is the greedy response of (`eq:A-greedy`),
  the construction `greedyResp` for `π` and `ρ`.
* `tiebreak`: `lem:A-tiebreak`.
* The candidate breakpoints (`stoc-sections/appA-proofs.tex:92-132`): `type1` with
  (`eq:A-type1`) (`type1_iff`) and `type2` with (`eq:A-type2`) (`type2_iff`), generated as
  multisets (one for each element, one for each pair); the candidate shares `candidates` (the
  candidate breakpoints in `[0, 1]` with `0` and `1`, without duplicates) and their sorted
  enumeration `cand`, `0 = α^(0) < ⋯ < α^(K) = 1` with `K = numK m c`.
* `candidates_lemma`: `lem:A-candidates`.
* `lineartime`: `lem:A-lineartime`, with the shares that its proof evaluates (`evalShares`),
  without the running time.
* `linear`: `thm:linear`, without the running time, for every `n` (Section 2 assumes a nonempty
  ground set, and Appendix A.2 settles `E = ∅` in a parenthetical); `linear_of_isEmpty` is that
  case.
* `const_on_intervals`: the warm-up's sentence on the intervals between consecutive candidate
  shares (`stoc-sections/04-linear.tex:5`), which `thm:linear` no longer states.

Indices from 0: `perm m c α i` is the STOC version's `e_{π(i+1)}`.

The running times of `lem:A-lineartime` and `thm:linear` are not formalised (Lean has no cost
model): the greedy algorithm is the construction (`eq:A-greedy`) itself, and of the optimal contract
the Lean proves that a share of maximum utility among the at most `n(n + 1)/2 + 1` shares that the
proof of `lem:A-lineartime` evaluates is optimal.

Taken over on 2026-10-20 from `Paper/Linear/Linear.lean` (the paper at Overleaf f035b19) for the
STOC version (`stoc.tex`); from then on this copy follows the STOC version. Rewritten on
2026-10-25 so that every proof takes the STOC version's steps. Adapted on 2026-11-02 to Max Klimm's
final STOC version (repository 429ca68): `thm:linear` states only that an optimal contract can be
computed, so `linear` states that a retained share is an optimal contract of the model, and its
former parts on the intervals are the warm-up's sentence (`const_on_intervals`); `thm:greedy` is
cited as Edmonds' greedy theorem (`Stoc.greedy`).
-/

namespace Stoc

namespace Linear

open Finset Function Filter Topology

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E] [LinearOrder E]
variable {f : Finset E → ℝ} {m c : E → ℝ} {α : ℝ}

/-! ### The greedy response -/

/-- The coefficient `ρ_e(α) = α m_e − c_e` of `e` at the share `α`. -/
def rho (m c : E → ℝ) (α : ℝ) (e : E) : ℝ :=
  α * m e - c e

/-- The agent's utility `U_A(x | α) = α r(x) − c(x)` for linear costs `c(x) = ∑ c_e x_e`. -/
def utilA (m c : E → ℝ) (α : ℝ) (x : E → ℝ) : ℝ :=
  α * reward m x - ∑ e, c e * x e

omit [DecidableEq E] [LinearOrder E] in
/-- `U_A(x | α) = ρ(α)ᵀx` (Section 2). -/
theorem utilA_eq (m c : E → ℝ) (α : ℝ) (x : E → ℝ) :
    utilA m c α x = ∑ e, rho m c α e * x e := by
  simp only [utilA, reward, rho, mul_sum, sub_mul, sum_sub_distrib, mul_assoc]

/-- `x` is agent-optimal at the share `α`: `x ∈ argmax_{x ∈ P₊(f)} U_A(x | α)` (Section 2). -/
def IsAgentOpt (f : Finset E → ℝ) (m c : E → ℝ) (α : ℝ) (x : E → ℝ) : Prop :=
  x ∈ indepPoly f ∧ ∀ y ∈ indepPoly f, utilA m c α y ≤ utilA m c α x

/-- The weakly profitable elements at the share `α`, those with `ρ_e(α) ≥ 0`
(`stoc-sections/appA-proofs.tex:35-36`). -/
def weaklyProfitable (m c : E → ℝ) (α : ℝ) : Finset E :=
  univ.filter fun e => 0 ≤ rho m c α e

omit [DecidableEq E] [LinearOrder E] in
theorem mem_weaklyProfitable {e : E} : e ∈ weaklyProfitable m c α ↔ 0 ≤ rho m c α e := by
  simp [weaklyProfitable]

/-- The order of `π(α)` as an injective key: nonincreasing `ρ_e(α)`, ties by nonincreasing `m_e`,
remaining ties by the fixed enumeration (the linear order on `E`). An element with a smaller key
comes first. -/
def sortKey (m c : E → ℝ) (α : ℝ) (e : E) : ℝ ×ₗ ℝ ×ₗ E :=
  toLex (-rho m c α e, toLex (-m e, e))

omit [Fintype E] [DecidableEq E] [LinearOrder E] in
theorem sortKey_injective (m c : E → ℝ) (α : ℝ) : Injective (sortKey m c α) := by
  intro e e' h
  simp only [sortKey, toLex_inj, Prod.mk.injEq] at h
  exact h.2.2

omit [Fintype E] [DecidableEq E] in
theorem sortKey_lt_iff {e e' : E} :
    sortKey m c α e < sortKey m c α e' ↔
      rho m c α e' < rho m c α e ∨
        (rho m c α e = rho m c α e' ∧ (m e' < m e ∨ (m e = m e' ∧ e < e'))) := by
  simp only [sortKey, Prod.Lex.toLex_lt_toLex, neg_lt_neg_iff, neg_inj]

/-- The permutation `π = π(α)`: `perm m c α i` is the STOC version's `e_{π(i+1)}`, the element at
position `i` (from 0) when `E` is ordered by nonincreasing `ρ_e`, ties by nonincreasing `m_e` and
the remaining ties by the fixed enumeration. -/
def perm (m c : E → ℝ) (α : ℝ) : Fin (Fintype.card E) ≃ E :=
  sortEquiv (sortKey m c α) (sortKey_injective m c α)

omit [DecidableEq E] in
/-- The order of `π` (`stoc-sections/appA-proofs.tex:36-44`): `ρ_{e_{π(i)}} ≥ ρ_{e_{π(j)}}` for
positions `i < j`, as `π` orders the elements by nonincreasing `ρ_e`; the first displayed property
is the case `j = i + 1`. -/
theorem perm_rho_le {i j : Fin (Fintype.card E)} (hij : i < j) :
    rho m c α (perm m c α j) ≤ rho m c α (perm m c α i) := by
  have h := (sortEquiv_lt_iff (sortKey_injective m c α)).2 hij
  rcases sortKey_lt_iff.1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

omit [DecidableEq E] in
/-- The order of `π` on ties (`stoc-sections/appA-proofs.tex:36-44`): of two tied elements, the
first has the larger reward, `ρ_{e_{π(i)}} = ρ_{e_{π(j)}} ⟹ m_{e_{π(i)}} ≥ m_{e_{π(j)}}` for
positions `i < j`, as `π` breaks ties by nonincreasing `m_e`; the second displayed property is the
case `j = i + 1`. -/
theorem perm_m_le {i j : Fin (Fintype.card E)} (hij : i < j)
    (h : rho m c α (perm m c α i) = rho m c α (perm m c α j)) :
    m (perm m c α j) ≤ m (perm m c α i) := by
  have h' := (sortEquiv_lt_iff (sortKey_injective m c α)).2 hij
  rcases sortKey_lt_iff.1 h' with h' | ⟨-, h' | ⟨h', -⟩⟩
  · exact absurd h (ne_of_gt h')
  · exact h'.le
  · exact h'.ge

omit [DecidableEq E] in
theorem perm_antitone : Antitone (rho m c α ∘ perm m c α) := by
  intro i j hij
  rcases hij.lt_or_eq with hij | rfl
  · exact perm_rho_le hij
  · exact le_rfl

/-- The greedy construction of (`eq:A-greedy`) (`stoc-sections/appA-proofs.tex:45-53`) for an
enumeration `π` of `E` (`e_{π(i+1)} = π i`) and coefficients `a`:
`x_{e_{π(i)}} = f(S^π_i) − f(S^π_{i−1})` if `a_{e_{π(i)}} ≥ 0`, and `0` otherwise. For `a = ρ` the
condition is that `e_{π(i)}` is weakly profitable, `ρ_{e_{π(i)}} ≥ 0`; the proof of `lem:A-tiebreak`
applies the same construction to the perturbed coefficients `a = ρ^s`. -/
def greedyResp (f : Finset E → ℝ) {n : ℕ} (π : Fin n ≃ E) (a : E → ℝ) (e : E) : ℝ :=
  if 0 ≤ a e then f (prefixSet π (π.symm e + 1)) - f (prefixSet π (π.symm e)) else 0

/-- The greedy response `x*(α)` (`eq:A-greedy`): the greedy construction for `π = π(α)` and
`ρ = ρ(α)`, with `x*_{e_{π(i)}}(α) = f(S^π_i) − f(S^π_{i−1})` if `e_{π(i)}` is weakly profitable,
that is, `ρ_{e_{π(i)}} ≥ 0`, and `0` otherwise. -/
def xstar (f : Finset E → ℝ) (m c : E → ℝ) (α : ℝ) : E → ℝ :=
  greedyResp f (perm m c α) (rho m c α)

omit [DecidableEq E] [LinearOrder E] in
/-- The proof of `lem:A-tiebreak` (`stoc-sections/appA-proofs.tex:76-78`): "The greedy vector in
(`eq:A-greedy`) is determined solely by the order `π` and the set `{e ∈ E : ρ_e ≥ 0}` of weakly
profitable elements", here for any coefficients `a`: coefficients with the same set
`{e ∈ E : a_e ≥ 0}` give the same greedy construction. -/
theorem greedyResp_congr {n : ℕ} (π : Fin n ≃ E) {a a' : E → ℝ}
    (h : univ.filter (fun e => 0 ≤ a e) = univ.filter fun e => 0 ≤ a' e) :
    greedyResp f π a = greedyResp f π a' := by
  have h' : ∀ e, 0 ≤ a e ↔ 0 ≤ a' e := fun e => by
    simpa using congrArg (e ∈ ·) h
  funext e
  simp only [greedyResp, h']

omit [DecidableEq E] [LinearOrder E] in
/-- For coefficients that do not increase along `π`, the greedy construction is the vector `x̄` of
Edmonds' greedy theorem in the form of Appendix A.2 (`edmondsVec`, `greedy`): the first
`k = #{e | a_e ≥ 0}` elements are those with `a_e ≥ 0` (`lt_card_nonneg_iff`). Not in the paper: the
STOC version applies Edmonds' greedy theorem to (`eq:A-greedy`) without this identification
(`stoc-sections/appA-proofs.tex:54-55, 81-82`). -/
theorem greedyResp_eq_edmondsVec {n : ℕ} (π : Fin n ≃ E) {a : E → ℝ} (ha : Antitone (a ∘ π)) :
    greedyResp f π a = edmondsVec f π #(univ.filter fun e => 0 ≤ a e) := by
  funext e
  simp only [greedyResp, edmondsVec, lt_card_nonneg_iff π ha e]

/-- "By Edmonds' greedy theorem [Edm03], `x*(α)` maximizes `ρᵀx` over `P₊(f)`"
(`stoc-sections/appA-proofs.tex:54-55`): Edmonds' greedy theorem in the form of Appendix A.2
(`greedy`, `stoc-sections/appA-proofs.tex:28`) for the coefficients `ρ` and the order `π`. -/
theorem xstar_max (hf : IsRankFunction f) :
    xstar f m c α ∈ indepPoly f ∧
      ∀ y ∈ indepPoly f, ∑ e, rho m c α e * y e ≤ ∑ e, rho m c α e * xstar f m c α e := by
  have h := greedy hf (perm m c α) (rho m c α) perm_antitone
  rw [← greedyResp_eq_edmondsVec _ perm_antitone] at h
  exact h

/-- **`lem:A-tiebreak`** (Lemma A.2, statement `stoc-sections/appA-proofs.tex:57-64`, proof
:66-90): let `α ∈ [0, 1]` be fixed. Then (i) `x*(α)` is agent-optimal, that is,
`x*(α) ∈ argmax{ρᵀx : x ∈ P₊(f)}`, and (ii) `x*(α)` maximizes the principal's reward
`r(x) = mᵀx` among all agent-optimal solutions.

The STOC version's proof: (i) follows from Edmonds' greedy theorem [Edm03] (`xstar_max`). For (ii):
(1) the perturbed
coefficients `ρ^s_e = ρ_e + s m_e + s²`; (2) for all sufficiently small `s > 0`, every strict
comparison between the original coefficients is preserved and every negative coefficient remains
negative; (3) when `ρ_e = ρ_{e'}`, the perturbed coefficients are ordered by `m_e` and `m_{e'}`,
consistently with `π`; (4) `ρ^s_e > 0` whenever `ρ_e ≥ 0`, since `m_e ≥ 0`; (5) the greedy vector
in (`eq:A-greedy`) is determined solely by the order `π` and the set `{e ∈ E : ρ_e ≥ 0}` of weakly
profitable elements (`greedyResp_congr`); (6) `π` is a nonincreasing order also for `ρ^s`, and
`{e ∈ E : ρ^s_e ≥ 0} = {e ∈ E : ρ_e ≥ 0}`, so the greedy construction for `ρ^s` yields the same
vector `x*(α)`; (7) by Edmonds' greedy theorem [Edm03] (`greedy`), (`eq:A-perturb`)
`ρᵀ(x* − y) + s mᵀ(x* − y) + s² 1ᵀ(x* − y) ≥ 0` for every `y ∈ P₊(f)` and all sufficiently
small `s > 0`; (8) for an agent-optimal `y`, `ρᵀ(x* − y) = 0` by (i); (9) dividing
(`eq:A-perturb`) by `s` and letting `s → 0` gives `mᵀx* ≥ mᵀy`.

The hypotheses are the STOC version's: `f` a rank function, `m ≥ 0` (Section 2), the standing
assumptions `c ≥ 0` and `n ≥ 1` of Appendix A.2, and `α ∈ [0, 1]`. The proof does not use
`c ≥ 0`, `n ≥ 1` or `α ∈ [0, 1]`. -/
theorem tiebreak [Nonempty E] (hf : IsRankFunction f) (hm : ∀ e, 0 ≤ m e)
    (_hc : ∀ e, 0 ≤ c e) (_hα : α ∈ Set.Icc (0 : ℝ) 1) :
    IsAgentOpt f m c α (xstar f m c α) ∧
      ∀ y, IsAgentOpt f m c α y → reward m y ≤ reward m (xstar f m c α) := by
  -- (i) "Part (i) follows from Edmonds' greedy theorem [Edm03]."
  have hi : IsAgentOpt f m c α (xstar f m c α) := by
    obtain ⟨hmem, hmax⟩ := xstar_max (m := m) (c := c) (α := α) hf
    exact ⟨hmem, fun y hy => by rw [utilA_eq, utilA_eq]; exact hmax y hy⟩
  set π := perm m c α with hπ
  set ρ := rho m c α with hρ
  set xs := xstar f m c α with hxs
  -- (1) "For part (ii), consider the perturbed coefficients `ρ^s_e := ρ_e + s m_e + s²` for
  -- `e ∈ E`."
  set ρs : ℝ → E → ℝ := fun s e => ρ e + s * m e + s ^ 2 with hρs
  have hcont : ∀ e, Tendsto (fun s => ρs s e) (𝓝[>] 0) (𝓝 (ρ e)) := by
    intro e
    have h : Tendsto (fun s : ℝ => ρ e + s * m e + s ^ 2) (𝓝 0)
        (𝓝 (ρ e + 0 * m e + 0 ^ 2)) :=
      (by fun_prop : Continuous fun s : ℝ => ρ e + s * m e + s ^ 2).tendsto 0
    rw [zero_mul, add_zero, zero_pow two_ne_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- (2) "Since `E` is finite, for all sufficiently small `s > 0` every strict comparison between
  -- the original coefficients is preserved and every negative coefficient remains negative."
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∀ e e', ρ e < ρ e' → ρs s e < ρs s e') ∧ ∀ e, ρ e < 0 → ρs s e < 0 := by
    refine (eventually_all.2 fun e => eventually_all.2 fun e' => ?_).and
      (eventually_all.2 fun e => ?_)
    · by_cases h : ρ e < ρ e'
      · exact ((hcont e).eventually_lt (hcont e') h).mono fun s hs _ => hs
      · exact Eventually.of_forall fun s h' => absurd h' h
    · by_cases h : ρ e < 0
      · exact ((hcont e).eventually_lt_const h).mono fun s hs _ => hs
      · exact Eventually.of_forall fun s h' => absurd h' h
  -- (3) "When `ρ_e = ρ_{e'}`, the perturbed coefficients are ordered by `m_e` and `m_{e'}`,
  -- consistently with `π`."
  have h3 : ∀ s > 0, ∀ e e', ρ e = ρ e' → (ρs s e' ≤ ρs s e ↔ m e' ≤ m e) := by
    intro s hs e e' h
    simp only [ρs, h]
    constructor
    · intro h'
      nlinarith
    · intro h'
      nlinarith
  -- (4) "Moreover, `ρ^s_e > 0` whenever `ρ_e ≥ 0`, since `m_e ≥ 0`."
  have h4 : ∀ s > 0, ∀ e, 0 ≤ ρ e → 0 < ρs s e := by
    intro s hs e he
    have := mul_nonneg hs.le (hm e)
    have := pow_pos hs 2
    simp only [ρs]
    linarith
  -- (5) "The greedy vector in (`eq:A-greedy`) is determined solely by the order `π` and the set
  -- `{e ∈ E : ρ_e ≥ 0}` of weakly profitable elements" (`greedyResp_congr`).
  -- (6) "Since `π` is a nonincreasing order also for `ρ^s`, and
  -- `{e ∈ E : ρ^s_e ≥ 0} = {e ∈ E : ρ_e ≥ 0}`, the greedy construction for `ρ^s` yields the same
  -- vector `x*(α)`."
  have h6 : ∀ᶠ s in 𝓝[>] (0 : ℝ), Antitone (ρs s ∘ π) ∧ greedyResp f π (ρs s) = xs := by
    filter_upwards [h2, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
    obtain ⟨hstrict, hneg⟩ := hs
    -- `π` is a nonincreasing order also for `ρ^s`, by (2) and (3)
    have hanti : Antitone (ρs s ∘ π) := by
      intro i j hij
      rcases hij.lt_or_eq with hij | rfl
      · rcases (perm_rho_le hij).lt_or_eq with hlt | heq
        · exact (hstrict _ _ hlt).le
        · exact (h3 s hs0 _ _ heq.symm).2 (perm_m_le hij heq.symm)
      · exact le_rfl
    -- `{e ∈ E : ρ^s_e ≥ 0} = {e ∈ E : ρ_e ≥ 0}`, by (2) and (4)
    have hset : univ.filter (fun e => 0 ≤ ρs s e) = weaklyProfitable m c α := by
      ext e
      rw [mem_weaklyProfitable, mem_filter]
      refine ⟨fun h => ?_, fun h => ⟨mem_univ e, (h4 s hs0 e h).le⟩⟩
      by_contra hlt
      exact absurd h.2 (not_le.2 (hneg e (not_le.1 hlt)))
    exact ⟨hanti, greedyResp_congr π hset⟩
  -- (7) "By Edmonds' greedy theorem [Edm03], it satisfies
  -- (`eq:A-perturb`) `ρᵀ(x*(α) − y) + s mᵀ(x*(α) − y) + s² 1ᵀ(x*(α) − y) ≥ 0`
  -- for every `y ∈ P₊(f)` and all sufficiently small `s > 0`, where `1` is the all-ones vector."
  have h7 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ y ∈ indepPoly f, 0 ≤ ∑ e, ρ e * (xs e - y e) +
      s * ∑ e, m e * (xs e - y e) + s ^ 2 * ∑ e, (xs e - y e) := by
    filter_upwards [h6] with s hs
    obtain ⟨hanti, hsame⟩ := hs
    intro y hy
    have hg := (greedy hf π (ρs s) hanti).2 y hy
    rw [← greedyResp_eq_edmondsVec π hanti, hsame] at hg
    have hexp : ∑ e, ρs s e * xs e - ∑ e, ρs s e * y e = ∑ e, ρ e * (xs e - y e) +
        s * ∑ e, m e * (xs e - y e) + s ^ 2 * ∑ e, (xs e - y e) := by
      simp only [ρs, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun e _ => by ring
    linarith
  refine ⟨hi, fun y hy => ?_⟩
  -- (8) "If `y` is agent-optimal, then `ρᵀ(x*(α) − y) = 0` by part (i)."
  have h8 : ∑ e, ρ e * (xs e - y e) = 0 := by
    have h1 := hi.2 y hy.1
    have h2 := hy.2 xs hi.1
    rw [utilA_eq, utilA_eq] at h1 h2
    have hsplit : ∑ e, ρ e * (xs e - y e) = ∑ e, ρ e * xs e - ∑ e, ρ e * y e := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun e _ => by ring
    linarith
  -- (9) "Dividing (`eq:A-perturb`) by `s` and letting `s → 0` gives `mᵀx*(α) ≥ mᵀy`, proving
  -- part (ii)."
  have h9 : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      0 ≤ ∑ e, m e * (xs e - y e) + s * ∑ e, (xs e - y e) := by
    filter_upwards [h7, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
    have hs := hs y hy.1
    rw [h8, zero_add] at hs
    have hmul : 0 ≤ s * (∑ e, m e * (xs e - y e) + s * ∑ e, (xs e - y e)) := by
      have : s * (∑ e, m e * (xs e - y e) + s * ∑ e, (xs e - y e)) =
          s * ∑ e, m e * (xs e - y e) + s ^ 2 * ∑ e, (xs e - y e) := by ring
      rw [this]
      exact hs
    exact (mul_nonneg_iff_of_pos_left hs0).1 hmul
  have hlim : Tendsto (fun s => ∑ e, m e * (xs e - y e) + s * ∑ e, (xs e - y e)) (𝓝[>] 0)
      (𝓝 (∑ e, m e * (xs e - y e))) := by
    have h : Tendsto (fun s : ℝ => ∑ e, m e * (xs e - y e) + s * ∑ e, (xs e - y e)) (𝓝 0)
        (𝓝 (∑ e, m e * (xs e - y e) + 0 * ∑ e, (xs e - y e))) :=
      (by fun_prop : Continuous fun s : ℝ =>
        ∑ e, m e * (xs e - y e) + s * ∑ e, (xs e - y e)).tendsto 0
    rw [zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hM := ge_of_tendsto hlim h9
  have hr : ∑ e, m e * (xs e - y e) = reward m xs - reward m y := by
    simp only [reward, ← sum_sub_distrib, mul_sub]
  linarith

/-! ### Candidate breakpoints -/

/-- The principal's utility `U_P(α) = (1 − α) mᵀx*(α)`. -/
def utilP (f : Finset E → ℝ) (m c : E → ℝ) (α : ℝ) : ℝ :=
  (1 - α) * reward m (xstar f m c α)

theorem reward_xstar_nonneg (hf : IsRankFunction f) (hm : ∀ e, 0 ≤ m e) :
    0 ≤ reward m (xstar f m c α) :=
  sum_nonneg fun e _ => mul_nonneg (hm e) ((xstar_max (m := m) (c := c) (α := α) hf).1.1 e)

/-- The Type 1 candidate breakpoints `α_e = c_e / m_e` for `e ∈ E` with `m_e > 0`, where an
element becomes weakly profitable (`stoc-sections/appA-proofs.tex:94-98`): one for each such `e`,
generated as a multiset, as two elements can give the same share. -/
def type1 (m c : E → ℝ) : Multiset ℝ :=
  (univ.filter fun e => 0 < m e).val.map fun e => c e / m e

omit [DecidableEq E] [LinearOrder E] in
theorem mem_type1 {e : E} (he : 0 < m e) : c e / m e ∈ type1 m c :=
  Multiset.mem_map.2 ⟨e, mem_filter.2 ⟨mem_univ e, he⟩, rfl⟩

omit [Fintype E] [DecidableEq E] [LinearOrder E] in
/-- (`eq:A-type1`): an element with `m_e > 0` is weakly profitable exactly for the shares at or
above its Type 1 candidate breakpoint, `α ≥ α_e ⟺ ρ_e(α) ≥ 0`. -/
theorem type1_iff {e : E} (he : 0 < m e) (α : ℝ) : c e / m e ≤ α ↔ 0 ≤ rho m c α e := by
  rw [div_le_iff₀ he]
  simp only [rho]
  constructor <;> intro h <;> linarith

omit [DecidableEq E] [LinearOrder E] in
/-- An element with `m_e = 0` is weakly profitable for every share if `c_e = 0`, and for no share
if `c_e > 0` (`stoc-sections/appA-proofs.tex:104-105`). -/
theorem mem_weaklyProfitable_of_m_eq_zero (hc : ∀ e, 0 ≤ c e) {e : E} (he : m e = 0) (α : ℝ) :
    e ∈ weaklyProfitable m c α ↔ c e = 0 := by
  simp only [mem_weaklyProfitable, rho, he, mul_zero, zero_sub, neg_nonneg]
  exact ⟨fun h => le_antisymm h (hc e), fun h => h.le⟩

/-- The Type 2 candidate breakpoints `α_{e,e'} = (c_e − c_{e'}) / (m_e − m_{e'})` for `e, e' ∈ E`
with `m_e > m_{e'}`, where two coefficients exchange order
(`stoc-sections/appA-proofs.tex:105-109`): one for each such pair, generated as a multiset. -/
def type2 (m c : E → ℝ) : Multiset ℝ :=
  (univ.filter fun p : E × E => m p.2 < m p.1).val.map fun p => (c p.1 - c p.2) / (m p.1 - m p.2)

omit [DecidableEq E] [LinearOrder E] in
theorem mem_type2 {e e' : E} (h : m e' < m e) : (c e - c e') / (m e - m e') ∈ type2 m c :=
  Multiset.mem_map.2 ⟨(e, e'), mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩

omit [Fintype E] [DecidableEq E] [LinearOrder E] in
/-- For `m_e > m_{e'}`: `ρ_e − ρ_{e'} = (m_e − m_{e'})(α − α_{e,e'})`. -/
theorem rho_sub_rho {e e' : E} (h : m e' < m e) (α : ℝ) :
    rho m c α e - rho m c α e' = (m e - m e') * (α - (c e - c e') / (m e - m e')) := by
  have hd : m e - m e' ≠ 0 := (sub_pos.2 h).ne'
  simp only [rho]
  field_simp
  ring

omit [Fintype E] [DecidableEq E] [LinearOrder E] in
/-- (`eq:A-type2`): for `m_e > m_{e'}`, `α ≥ α_{e,e'} ⟺ ρ_e(α) ≥ ρ_{e'}(α)`. -/
theorem type2_iff {e e' : E} (h : m e' < m e) (α : ℝ) :
    (c e - c e') / (m e - m e') ≤ α ↔ rho m c α e' ≤ rho m c α e := by
  have hdiff := rho_sub_rho (c := c) h α
  have hd := sub_pos.2 h
  constructor
  · intro hα
    nlinarith
  · intro hρ
    by_contra hlt
    rw [not_le] at hlt
    nlinarith

omit [Fintype E] [DecidableEq E] [LinearOrder E] in
/-- Elements with equal rewards: `ρ_e − ρ_{e'} = c_{e'} − c_e` does not depend on the share. -/
theorem rho_sub_rho_of_m_eq {e e' : E} (h : m e = m e') (α : ℝ) :
    rho m c α e - rho m c α e' = c e' - c e := by
  simp only [rho, h]
  ring

omit [Fintype E] [DecidableEq E] in
/-- The order of `π(α)` on a pair with `m_e > m_{e'}`: `e` comes first exactly when
`ρ_e(α) ≥ ρ_{e'}(α)`. -/
theorem sortKey_lt_iff_of_gt {e e' : E} (h : m e' < m e) :
    sortKey m c α e < sortKey m c α e' ↔ rho m c α e' ≤ rho m c α e := by
  rw [sortKey_lt_iff]
  constructor
  · rintro (h' | ⟨h', -⟩)
    · exact h'.le
    · exact h'.ge
  · intro h'
    rcases h'.lt_or_eq with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h'.symm, Or.inl h⟩

omit [Fintype E] [DecidableEq E] in
/-- The order of `π(α)` on a pair with `m_e < m_{e'}`: `e` comes first exactly when
`ρ_e(α) > ρ_{e'}(α)`. -/
theorem sortKey_lt_iff_of_lt {e e' : E} (h : m e < m e') :
    sortKey m c α e < sortKey m c α e' ↔ rho m c α e' < rho m c α e := by
  rw [sortKey_lt_iff]
  constructor
  · rintro (h' | ⟨-, h' | ⟨h', -⟩⟩)
    · exact h'
    · exact absurd h' (not_lt.2 h.le)
    · exact absurd h' h.ne
  · exact Or.inl

omit [Fintype E] [DecidableEq E] in
/-- The order of `π(α)` on a pair with equal rewards does not depend on the share: their
coefficients differ by `c_{e'} − c_e`, and their ties are resolved by the fixed enumeration. -/
theorem sortKey_lt_iff_of_eq {e e' : E} (h : m e = m e') :
    sortKey m c α e < sortKey m c α e' ↔ c e < c e' ∨ (c e = c e' ∧ e < e') := by
  have hd := rho_sub_rho_of_m_eq (c := c) h α
  rw [sortKey_lt_iff]
  constructor
  · rintro (h' | ⟨h', h'' | ⟨-, h''⟩⟩)
    · left
      linarith
    · exact absurd h'' (not_lt.2 h.le)
    · right
      exact ⟨by linarith, h''⟩
  · rintro (h' | ⟨h', h''⟩)
    · left
      linarith
    · exact Or.inr ⟨by linarith, Or.inr ⟨h, h''⟩⟩

/-- The candidate shares (`stoc-sections/appA-proofs.tex:118-122`): "The candidate breakpoints in
`[0, 1]` are the candidate shares of `sec:linear`. We add `0` and `1`, remove duplicates"
(`Multiset.toFinset`); `cand` sorts them. -/
def candidates (m c : E → ℝ) : Finset ℝ :=
  (0 ::ₘ 1 ::ₘ (type1 m c + type2 m c).filter fun β => 0 ≤ β ∧ β ≤ 1).toFinset

/-- `K`: the candidate shares are `α^(0) < ⋯ < α^(K)`. -/
def numK (m c : E → ℝ) : ℕ :=
  #(candidates m c) - 1

/-- The candidate shares sorted, `0 = α^(0) < α^(1) < ⋯ < α^(K) = 1`: `cand m c i` is `α^(i)`
for `i ≤ K` (and `1` beyond). -/
def cand (m c : E → ℝ) (i : ℕ) : ℝ :=
  if h : i < #(candidates m c) then (candidates m c).orderEmbOfFin rfl ⟨i, h⟩ else 1

omit [DecidableEq E] [LinearOrder E] in
theorem mem_candidates {β : ℝ} :
    β ∈ candidates m c ↔ β = 0 ∨ β = 1 ∨ (β ∈ type1 m c + type2 m c ∧ 0 ≤ β ∧ β ≤ 1) := by
  simp only [candidates, Multiset.mem_toFinset, Multiset.mem_cons, Multiset.mem_filter]

omit [DecidableEq E] [LinearOrder E] in
theorem zero_mem_candidates : (0 : ℝ) ∈ candidates m c :=
  mem_candidates.2 (Or.inl rfl)

omit [DecidableEq E] [LinearOrder E] in
theorem one_mem_candidates : (1 : ℝ) ∈ candidates m c :=
  mem_candidates.2 (Or.inr (Or.inl rfl))

omit [DecidableEq E] [LinearOrder E] in
theorem mem_candidates_bounds {β : ℝ} (hβ : β ∈ candidates m c) : 0 ≤ β ∧ β ≤ 1 := by
  rcases mem_candidates.1 hβ with rfl | rfl | ⟨-, h⟩
  · norm_num
  · norm_num
  · exact h

omit [DecidableEq E] [LinearOrder E] in
theorem card_candidates : #(candidates m c) = numK m c + 1 := by
  have h2 : 2 ≤ #(candidates m c) := by
    have hsub : ({0, 1} : Finset ℝ) ⊆ candidates m c := by
      intro β hβ
      simp only [mem_insert, mem_singleton] at hβ
      rcases hβ with rfl | rfl
      · exact zero_mem_candidates
      · exact one_mem_candidates
    have := card_le_card hsub
    rwa [card_pair zero_ne_one] at this
  unfold numK
  omega

omit [DecidableEq E] [LinearOrder E] in
/-- `K ≥ 1`. -/
theorem one_le_numK : 1 ≤ numK m c := by
  have h2 : 2 ≤ #(candidates m c) := by
    have hsub : ({0, 1} : Finset ℝ) ⊆ candidates m c := by
      intro β hβ
      simp only [mem_insert, mem_singleton] at hβ
      rcases hβ with rfl | rfl
      · exact zero_mem_candidates
      · exact one_mem_candidates
    have := card_le_card hsub
    rwa [card_pair zero_ne_one] at this
  unfold numK
  omega

omit [DecidableEq E] [LinearOrder E] in
theorem cand_mem {i : ℕ} (hi : i ≤ numK m c) : cand m c i ∈ candidates m c := by
  have hi' : i < #(candidates m c) := by rw [card_candidates]; omega
  simp only [cand, hi', dite_true]
  exact orderEmbOfFin_mem _ _ _

omit [DecidableEq E] [LinearOrder E] in
theorem cand_lt_cand {i j : ℕ} (hij : i < j) (hj : j ≤ numK m c) : cand m c i < cand m c j := by
  have hj' : j < #(candidates m c) := by rw [card_candidates]; omega
  have hi' : i < #(candidates m c) := by omega
  simp only [cand, hi', hj', dite_true]
  exact (candidates m c).orderEmbOfFin rfl |>.strictMono (Fin.mk_lt_mk.2 hij)

omit [DecidableEq E] [LinearOrder E] in
theorem cand_le_cand {i j : ℕ} (hij : i ≤ j) (hj : j ≤ numK m c) : cand m c i ≤ cand m c j := by
  rcases hij.lt_or_eq with hij | rfl
  · exact (cand_lt_cand hij hj).le
  · exact le_rfl

omit [DecidableEq E] [LinearOrder E] in
/-- Every candidate share is some `α^(j)`, `j ≤ K`. -/
theorem exists_cand_eq {β : ℝ} (hβ : β ∈ candidates m c) : ∃ j ≤ numK m c, cand m c j = β := by
  have hrange := Set.ext_iff.1 ((candidates m c).range_orderEmbOfFin rfl) β
  obtain ⟨⟨j, hj⟩, hjβ⟩ := hrange.2 (mem_coe.2 hβ)
  refine ⟨j, by rw [card_candidates] at hj; omega, ?_⟩
  simp only [cand, hj, dite_true]
  exact hjβ

omit [DecidableEq E] [LinearOrder E] in
/-- `α^(0) = 0`. -/
theorem cand_zero : cand m c 0 = 0 := by
  obtain ⟨j, hj, hj0⟩ := exists_cand_eq (zero_mem_candidates (m := m) (c := c))
  have h1 := cand_le_cand (Nat.zero_le j) hj
  have h2 := (mem_candidates_bounds (cand_mem (m := m) (c := c) (Nat.zero_le (numK m c)))).1
  linarith

omit [DecidableEq E] [LinearOrder E] in
/-- `α^(K) = 1`. -/
theorem cand_numK : cand m c (numK m c) = 1 := by
  obtain ⟨j, hj, hj1⟩ := exists_cand_eq (one_mem_candidates (m := m) (c := c))
  have h1 := cand_le_cand hj le_rfl
  have h2 := (mem_candidates_bounds (cand_mem (m := m) (c := c) (le_refl (numK m c)))).2
  linarith

omit [DecidableEq E] [LinearOrder E] in
/-- The intervals `[α^(i), α^(i+1))`, `i < K`, cover `[0, 1)` (not in the paper: the STOC
version leaves this implicit in "There is an optimal contract in `{α^(0), …, α^(K−1)}`"). -/
theorem exists_cand_interval {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    ∃ i < numK m c, α ∈ Set.Ico (cand m c i) (cand m c (i + 1)) := by
  -- The largest `i ≤ K` with `α^(i) ≤ α`.
  set L := (range (numK m c + 1)).filter fun i => cand m c i ≤ α
  have hL : L.Nonempty :=
    ⟨0, mem_filter.2 ⟨mem_range.2 (Nat.succ_pos _), by rw [cand_zero]; exact h0⟩⟩
  obtain ⟨i, hiL, hmax⟩ := L.exists_max_image id hL
  obtain ⟨hi, hiα⟩ := mem_filter.1 hiL
  have hiK : i ≤ numK m c := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have hiK' : i < numK m c := by
    rcases hiK.lt_or_eq with h | rfl
    · exact h
    · rw [cand_numK] at hiα
      linarith
  refine ⟨i, hiK', hiα, ?_⟩
  by_contra hle
  rw [not_lt] at hle
  have := hmax (i + 1) (mem_filter.2 ⟨mem_range.2 (by omega), hle⟩)
  simp only [id] at this
  omega

/-- From the proof of `lem:A-candidates`: where `x*(α) = x*(a)`, `U_P(α) = (1 − α) mᵀx*(a)` is
affine in `α` with the slope `−mᵀx*(a)`, which is nonpositive since `m ≥ 0` and `x*(a) ≥ 0`. -/
theorem utilP_affine (hf : IsRankFunction f) (hm : ∀ e, 0 ≤ m e) {a α : ℝ}
    (h : xstar f m c α = xstar f m c a) :
    utilP f m c α = reward m (xstar f m c a) + (-reward m (xstar f m c a)) * α ∧
      -reward m (xstar f m c a) ≤ 0 := by
  refine ⟨?_, neg_nonpos.2 (reward_xstar_nonneg hf hm)⟩
  simp only [utilP, h]
  ring

/-- **`lem:A-candidates`** (Lemma A.3, statement `stoc-sections/appA-proofs.tex:124-132`, proof
:134-165): for every `i ∈ {0, …, K − 1}`, the response `x*(α)` is constant on `[α^(i), α^(i+1))`,
and `U_P(α^(i)) ≥ U_P(α)` for all `α ∈ [α^(i), α^(i+1))`. There is an optimal contract in
`{α^(0), …, α^(K−1)}`, so evaluating the utility at these shares yields an optimal contract (a share
of maximum utility among them is at least as good as the optimal one among them).

The STOC version's proof, for a fixed `i`: (1) the interval `(α^(i), α^(i+1))` contains no
candidate breakpoint; (2) by (`eq:A-type1`) and (`eq:A-type2`), and since elements with `m_e = 0`
and pairs with equal rewards behave the same for every share, the set of weakly profitable
elements and the ordering `π` are constant on this interval; (3) the left endpoint: a coefficient
that is zero at `α^(i)` remains nonnegative immediately to its right, nonzero coefficients retain
their signs nearby, a tie at `α^(i)` with unequal rewards is resolved at `α^(i)` as immediately to
its right, ties with equal rewards persist and strict comparisons persist nearby, so the set of
weakly profitable elements and the ordering at `α^(i)` agree with those on the open interval;
(4) by (`eq:A-greedy`), `x*(α) = x*(α^(i))` throughout `[α^(i), α^(i+1))`; (5) so
`U_P(α) = (1 − α) mᵀx*(α^(i))` there, affine with the nonpositive slope `−mᵀx*(α^(i))`, and
`U_P(α^(i)) ≥ U_P(α)`; (6) finally `U_P(1) = 0 ≤ U_P(0)`, so the share `1` need not be evaluated.
Then a share of maximum utility among the finitely many `α^(0), …, α^(K−1)` is optimal, as the
intervals cover `[0, 1)`, which the STOC version leaves implicit (`exists_cand_interval`).

The hypotheses are the STOC version's: `f` a rank function, `m ≥ 0`, and the standing assumptions
`c ≥ 0` and `n ≥ 1` of Appendix A.2; `n ≥ 1` is not used. -/
theorem candidates_lemma [Nonempty E] (hf : IsRankFunction f) (hm : ∀ e, 0 ≤ m e)
    (hc : ∀ e, 0 ≤ c e) :
    (∀ i < numK m c, ∀ α ∈ Set.Ico (cand m c i) (cand m c (i + 1)),
        xstar f m c α = xstar f m c (cand m c i) ∧ utilP f m c α ≤ utilP f m c (cand m c i)) ∧
      ∃ i < numK m c, ∀ α ∈ Set.Icc (0 : ℝ) 1, utilP f m c α ≤ utilP f m c (cand m c i) := by
  have hcontρ : ∀ e a, Tendsto (fun α => rho m c α e) (𝓝[>] a) (𝓝 (rho m c a e)) := by
    intro e a
    exact ((by fun_prop : Continuous fun α : ℝ => α * m e - c e).tendsto a).mono_left
      nhdsWithin_le_nhds
  have hconst : ∀ i < numK m c, ∀ α ∈ Set.Ico (cand m c i) (cand m c (i + 1)),
      xstar f m c α = xstar f m c (cand m c i) ∧ utilP f m c α ≤ utilP f m c (cand m c i) := by
    -- "Fix `i ∈ {0, …, K − 1}`."
    intro i hi
    set a := cand m c i with ha
    set b := cand m c (i + 1) with hb
    have hab : a < b := cand_lt_cand (Nat.lt_succ_self i) hi
    -- (1) "The interval `(α^(i), α^(i+1))` contains no candidate breakpoint."
    have h1 : ∀ β ∈ type1 m c + type2 m c, β ∉ Set.Ioo a b := by
      intro β hβ hβab
      have h0a := (mem_candidates_bounds (cand_mem (m := m) (c := c) hi.le)).1
      have hb1 := (mem_candidates_bounds (cand_mem (m := m) (c := c) hi)).2
      have hβc : β ∈ candidates m c :=
        mem_candidates.2 (Or.inr (Or.inr ⟨hβ, by linarith [hβab.1], by linarith [hβab.2]⟩))
      obtain ⟨j, hj, rfl⟩ := exists_cand_eq hβc
      have hij : i < j := by
        by_contra h
        exact absurd (cand_le_cand (not_lt.1 h) hi.le) (not_le.2 hβab.1)
      have hji : j < i + 1 := by
        by_contra h
        exact absurd (cand_le_cand (not_lt.1 h) hj) (not_le.2 hβab.2)
      omega
    -- A candidate breakpoint lies on the same side of any two shares of the open interval.
    have hside : ∀ β ∈ type1 m c + type2 m c, ∀ α ∈ Set.Ioo a b, ∀ α' ∈ Set.Ioo a b,
        (β ≤ α ↔ β ≤ α') := by
      intro β hβ α hα α' hα'
      constructor
      · intro h
        by_contra h'
        exact h1 β hβ ⟨hα'.1.trans (not_le.1 h'), h.trans_lt hα.2⟩
      · intro h
        by_contra h'
        exact h1 β hβ ⟨hα.1.trans (not_le.1 h'), h.trans_lt hα'.2⟩
    -- (2) "By (`eq:A-type1`) and (`eq:A-type2`), and since elements with `m_e = 0` and pairs with
    -- equal rewards behave the same for every share, the set of weakly profitable elements and
    -- the ordering `π` are constant on this interval."
    have h2 : ∀ α ∈ Set.Ioo a b, ∀ α' ∈ Set.Ioo a b,
        weaklyProfitable m c α = weaklyProfitable m c α' ∧ perm m c α = perm m c α' := by
      intro α hα α' hα'
      refine ⟨ext fun e => ?_, sortEquiv_congr _ _ fun e e' => ?_⟩
      · rcases (hm e).lt_or_eq with he | he
        · have hβ : c e / m e ∈ type1 m c + type2 m c :=
            Multiset.mem_add.2 (Or.inl (mem_type1 he))
          rw [mem_weaklyProfitable, mem_weaklyProfitable, ← type1_iff he, ← type1_iff he]
          exact hside _ hβ α hα α' hα'
        · rw [mem_weaklyProfitable_of_m_eq_zero hc he.symm,
            mem_weaklyProfitable_of_m_eq_zero hc he.symm]
      · rcases lt_trichotomy (m e') (m e) with hlt | heq | hgt
        · have hβ : (c e - c e') / (m e - m e') ∈ type1 m c + type2 m c :=
            Multiset.mem_add.2 (Or.inr (mem_type2 hlt))
          rw [sortKey_lt_iff_of_gt hlt, sortKey_lt_iff_of_gt hlt, ← type2_iff hlt,
            ← type2_iff hlt]
          exact hside _ hβ α hα α' hα'
        · rw [sortKey_lt_iff_of_eq heq.symm, sortKey_lt_iff_of_eq heq.symm]
        · have hβ : (c e' - c e) / (m e' - m e) ∈ type1 m c + type2 m c :=
            Multiset.mem_add.2 (Or.inr (mem_type2 hgt))
          rw [sortKey_lt_iff_of_lt hgt, sortKey_lt_iff_of_lt hgt, ← not_le, ← not_le,
            ← type2_iff hgt, ← type2_iff hgt]
          exact not_congr (hside _ hβ α hα α' hα')
    -- (3) "We next include the left endpoint `α^(i)`."
    -- "Every coefficient `ρ_e` that is zero at `α^(i)` remains nonnegative immediately to its
    -- right, since `m_e ≥ 0`. All nonzero coefficients retain their signs in a sufficiently small
    -- neighborhood. Thus the set of weakly profitable elements at `α^(i)` agrees with that on
    -- `(α^(i), α^(i+1))`."
    have h3a : ∀ e, ∀ᶠ α in 𝓝[>] a,
        (e ∈ weaklyProfitable m c α ↔ e ∈ weaklyProfitable m c a) := by
      intro e
      simp only [mem_weaklyProfitable]
      rcases lt_trichotomy (rho m c a e) 0 with hneg | hzero | hpos
      · filter_upwards [(hcontρ e a).eventually_lt_const hneg] with α hα
        exact ⟨fun h => absurd h (not_le.2 hα), fun h => absurd h (not_le.2 hneg)⟩
      · filter_upwards [self_mem_nhdsWithin] with α (hα : a < α)
        have hshift : rho m c α e = rho m c a e + (α - a) * m e := by
          simp only [rho]
          ring
        have hnn : 0 ≤ rho m c α e := by
          rw [hshift, hzero, zero_add]
          exact mul_nonneg (sub_nonneg.2 hα.le) (hm e)
        exact ⟨fun _ => hzero.ge, fun _ => hnn⟩
      · filter_upwards [(hcontρ e a).eventually_const_lt hpos] with α hα
        exact ⟨fun _ => hpos.le, fun _ => hα.le⟩
    -- "For any pair of coefficients tied at `α^(i)` with unequal rewards, the element with the
    -- larger reward precedes the other immediately to the right of `α^(i)`, and the tie-breaking
    -- rule gives the same order at `α^(i)`. Ties between elements with equal rewards persist and
    -- are resolved by the fixed enumeration, while strict comparisons persist in a sufficiently
    -- small neighborhood. Hence the ordering at `α^(i)` also agrees with that on
    -- `(α^(i), α^(i+1))`."
    have h3b : ∀ e e', ∀ᶠ α in 𝓝[>] a,
        (sortKey m c α e < sortKey m c α e' ↔ sortKey m c a e < sortKey m c a e') := by
      intro e e'
      have hshift : ∀ α, rho m c α e - rho m c α e' =
          (rho m c a e - rho m c a e') + (α - a) * (m e - m e') := fun α => by
        simp only [rho]
        ring
      rcases lt_trichotomy (m e') (m e) with hlt | heq | hgt
      · rw [eventually_congr (Eventually.of_forall fun α => by rw [sortKey_lt_iff_of_gt hlt]),
          sortKey_lt_iff_of_gt hlt]
        rcases lt_trichotomy (rho m c a e) (rho m c a e') with h | h | h
        · filter_upwards [(hcontρ e a).eventually_lt (hcontρ e' a) h] with α hα
          exact ⟨fun h' => absurd h' (not_le.2 hα), fun h' => absurd h' (not_le.2 h)⟩
        · -- A tie at `α^(i)` with `m_e > m_{e'}`: `e` precedes `e'` immediately to the right.
          filter_upwards [self_mem_nhdsWithin] with α (hα : a < α)
          have := hshift α
          have hpos : 0 < (α - a) * (m e - m e') := mul_pos (sub_pos.2 hα) (sub_pos.2 hlt)
          exact ⟨fun _ => h.ge, fun _ => by linarith⟩
        · filter_upwards [(hcontρ e' a).eventually_lt (hcontρ e a) h] with α hα
          exact ⟨fun _ => h.le, fun _ => hα.le⟩
      · exact Eventually.of_forall fun α => by
          rw [sortKey_lt_iff_of_eq heq.symm, sortKey_lt_iff_of_eq heq.symm]
      · rw [eventually_congr (Eventually.of_forall fun α => by rw [sortKey_lt_iff_of_lt hgt]),
          sortKey_lt_iff_of_lt hgt]
        rcases lt_trichotomy (rho m c a e) (rho m c a e') with h | h | h
        · filter_upwards [(hcontρ e a).eventually_lt (hcontρ e' a) h] with α hα
          exact ⟨fun h' => absurd h' (not_lt.2 hα.le), fun h' => absurd h' (not_lt.2 h.le)⟩
        · -- A tie at `α^(i)` with `m_e < m_{e'}`: `e'` precedes `e` immediately to the right.
          filter_upwards [self_mem_nhdsWithin] with α (hα : a < α)
          have := hshift α
          have hneg : (α - a) * (m e - m e') < 0 :=
            mul_neg_of_pos_of_neg (sub_pos.2 hα) (sub_neg.2 hgt)
          exact ⟨fun h' => by linarith, fun h' => by linarith⟩
        · filter_upwards [(hcontρ e' a).eventually_lt (hcontρ e a) h] with α hα
          exact ⟨fun _ => h, fun _ => hα⟩
    -- Immediately to the right of `α^(i)`, the set of weakly profitable elements and the
    -- ordering are those at `α^(i)`; by (2) they are constant on `(α^(i), α^(i+1))`, so (taking
    -- one share `α₁` of the interval immediately to the right of `α^(i)`) they agree with those
    -- at `α^(i)` on the whole interval.
    have h3 : ∀ᶠ α in 𝓝[>] a,
        weaklyProfitable m c α = weaklyProfitable m c a ∧ perm m c α = perm m c a := by
      filter_upwards [eventually_all.2 h3a, eventually_all.2 fun e => eventually_all.2 (h3b e)]
        with α hα hβ
      exact ⟨ext hα, sortEquiv_congr _ _ hβ⟩
    obtain ⟨α₁, hα₁', hα₁⟩ := (h3.and (Ioo_mem_nhdsGT hab)).exists
    have h3' : ∀ α ∈ Set.Ioo a b,
        weaklyProfitable m c α = weaklyProfitable m c a ∧ perm m c α = perm m c a := by
      intro α hα
      obtain ⟨hset, hperm⟩ := h2 α hα α₁ hα₁
      exact ⟨hset.trans hα₁'.1, hperm.trans hα₁'.2⟩
    -- "This argument applies to simultaneous events and to `α^(0) = 0`, whether or not it is a
    -- candidate breakpoint of either type": nothing above depends on it.
    -- (4) "By (`eq:A-greedy`), `x*(α) = x*(α^(i))` throughout `[α^(i), α^(i+1))`": the greedy
    -- response is determined by the ordering and the weakly profitable elements
    -- (`greedyResp_congr`).
    have h4 : ∀ α ∈ Set.Ico a b, xstar f m c α = xstar f m c a := by
      intro α hα
      rcases hα.1.lt_or_eq with hlt | heq
      · obtain ⟨hset, hperm⟩ := h3' α ⟨hlt, hα.2⟩
        unfold xstar
        rw [hperm]
        exact greedyResp_congr _ hset
      · rw [heq]
    -- (5) "Consequently, `U_P(α) = (1 − α) mᵀx*(α^(i))` for `α ∈ [α^(i), α^(i+1))`. This is
    -- affine in `α` with nonpositive slope `−mᵀx*(α^(i))`, since `m ≥ 0` and `x*(α^(i)) ≥ 0`.
    -- It follows that `U_P(α^(i)) ≥ U_P(α)` on this interval."
    intro α hα
    refine ⟨h4 α hα, ?_⟩
    obtain ⟨hU, hslope⟩ := utilP_affine hf hm (h4 α hα)
    obtain ⟨hUa, -⟩ := utilP_affine hf hm (h4 a ⟨le_rfl, hab⟩)
    rw [hU, hUa]
    nlinarith [hα.1]
  refine ⟨hconst, ?_⟩
  -- (6) "Finally, `U_P(1) = 0 ≤ U_P(0)`, so the share `1` need not be evaluated."
  have h6 : utilP f m c 1 ≤ utilP f m c 0 := by
    simp only [utilP, sub_self, zero_mul, sub_zero, one_mul]
    exact reward_xstar_nonneg hf hm
  -- "There is an optimal contract in `{α^(0), …, α^(K−1)}`": one of maximum utility among these
  -- finitely many shares, as every `α ∈ [0, 1)` lies in some `[α^(i), α^(i+1))`
  -- (`exists_cand_interval`) and `α = 1` is settled by (6).
  obtain ⟨i₀, hi₀, hmax⟩ := (range (numK m c)).exists_max_image (fun j => utilP f m c (cand m c j))
    ⟨0, mem_range.2 one_le_numK⟩
  refine ⟨i₀, mem_range.1 hi₀, fun α hα => ?_⟩
  rcases hα.2.lt_or_eq with hα1 | rfl
  · obtain ⟨i, hi, hαi⟩ := exists_cand_interval (m := m) (c := c) hα.1 hα1
    exact (hconst i hi α hαi).2.trans (hmax i (mem_range.2 hi))
  · refine h6.trans ?_
    have := hmax 0 (mem_range.2 one_le_numK)
    rwa [cand_zero] at this

/-! ### The evaluated shares (`lem:A-lineartime`) -/

omit [DecidableEq E] [LinearOrder E] in
/-- At most `n` Type 1 candidate breakpoints, one for each `e` with `m_e > 0` (not in the paper: the
STOC version states the count without argument, `stoc-sections/appA-proofs.tex:172`). -/
theorem card_type1_le : Multiset.card (type1 m c) ≤ Fintype.card E := by
  rw [type1, Multiset.card_map, card_val]
  exact (card_filter_le _ _).trans_eq card_univ

omit [LinearOrder E] in
/-- At most `n(n − 1)/2` Type 2 candidate breakpoints, one for each pair `{e, e'}` (not in the
paper: the STOC version states the count without argument, `stoc-sections/appA-proofs.tex:172`). -/
theorem card_type2_le :
    Multiset.card (type2 m c) ≤ Fintype.card E * (Fintype.card E - 1) / 2 := by
  set P := univ.filter fun p : E × E => m p.2 < m p.1
  have hP : #P ≤ (Fintype.card E).choose 2 := by
    rw [← card_univ, ← card_powersetCard]
    refine card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset E)) ?_ ?_
    · intro p hp
      have hp' : m p.2 < m p.1 := (mem_filter.1 hp).2
      have hne : p.1 ≠ p.2 := fun h => absurd (h ▸ hp') (lt_irrefl _)
      rw [mem_coe, mem_powersetCard]
      exact ⟨subset_univ _, card_pair hne⟩
    · intro p hp q hq hpq
      have hp' : m p.2 < m p.1 := (mem_filter.1 hp).2
      have hq' : m q.2 < m q.1 := (mem_filter.1 hq).2
      have hpq' : ({p.1, p.2} : Finset E) = {q.1, q.2} := hpq
      have h1 : p.1 ∈ ({q.1, q.2} : Finset E) := hpq' ▸ mem_insert_self p.1 {p.2}
      have h2 : p.2 ∈ ({q.1, q.2} : Finset E) :=
        hpq' ▸ mem_insert_of_mem (mem_singleton_self p.2)
      simp only [mem_insert, mem_singleton] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · rw [h1, h2] at hp'
        exact absurd hp' (lt_irrefl _)
      · exact Prod.ext h1 h2
      · rw [h1, h2] at hp'
        exact absurd (hp'.trans hq') (lt_irrefl _)
      · rw [h1, h2] at hp'
        exact absurd hp' (lt_irrefl _)
  rw [← Nat.choose_two_right, type2, Multiset.card_map, card_val]
  exact hP

omit [LinearOrder E] in
/-- `1 + n + n(n − 1)/2 = n(n + 1)/2 + 1`. -/
theorem count_eq (n : ℕ) : 1 + n + n * (n - 1) / 2 = n * (n + 1) / 2 + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h : (k + 1) * (k + 1 + 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      rw [Nat.add_sub_cancel]
      ring
    rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega

/-- The shares that the proof of `lem:A-lineartime` evaluates
(`stoc-sections/appA-proofs.tex:173-180`): `α^(0) = 0` and the candidate breakpoints, generated and
kept in `[0, 1)`. They form a multiset: they are evaluated in no particular order, and with their
duplicates. -/
def evalShares (m c : E → ℝ) : Multiset ℝ :=
  0 ::ₘ (type1 m c + type2 m c).filter fun β => 0 ≤ β ∧ β < 1

omit [DecidableEq E] [LinearOrder E] in
/-- The evaluated shares lie in `[0, 1)`. -/
theorem mem_evalShares_bounds {β : ℝ} (hβ : β ∈ evalShares m c) : 0 ≤ β ∧ β < 1 := by
  rcases Multiset.mem_cons.1 hβ with rfl | hβ
  · norm_num
  · exact (Multiset.mem_filter.1 hβ).2

omit [DecidableEq E] [LinearOrder E] in
/-- Every candidate share `α^(i)`, `i < K`, is an evaluated share, as it is `0` or a candidate
breakpoint in `[0, 1)` (not in the paper: the proof of `lem:A-lineartime` leaves this implicit in
"Including `α^(0) = 0` and omitting `α^(K) = 1`, as justified in `lem:A-candidates`",
`stoc-sections/appA-proofs.tex:173-174`). -/
theorem cand_mem_evalShares {i : ℕ} (hi : i < numK m c) : cand m c i ∈ evalShares m c := by
  have hlt1 : cand m c i < 1 := cand_numK (m := m) (c := c) ▸ cand_lt_cand hi le_rfl
  rcases mem_candidates.1 (cand_mem (m := m) (c := c) hi.le) with h | h | ⟨h, h0, -⟩
  · rw [h]
    exact Multiset.mem_cons_self _ _
  · exact absurd h hlt1.ne
  · exact Multiset.mem_cons_of_mem (Multiset.mem_filter.2 ⟨h, h0, hlt1⟩)

/-- **`lem:A-lineartime`** (Lemma A.4, statement `stoc-sections/appA-proofs.tex:167-169`, proof
:171-185): an optimal contract `α*` can be computed in time `O(n³)·FO + O(n³ log n)`. Without the
running time, which is not formalised: the shares that the proof evaluates (`evalShares`:
`α^(0) = 0` and the candidate breakpoints in `[0, 1)`, in any order and with their duplicates) are
at most `n(n + 1)/2 + 1`, and a share of maximum utility among them exists and is an optimal
contract.

The STOC version's proof: (1) there are at most `n` Type 1 and `n(n − 1)/2` Type 2 candidate
breakpoints; (2) including `α^(0) = 0` and omitting `α^(K) = 1`, as justified in
`lem:A-candidates`, at most `1 + n + n(n − 1)/2 = n(n + 1)/2 + 1` shares are evaluated;
(3) generating the candidate breakpoints and keeping those in `[0, 1)` requires `O(n²)` arithmetic
operations, their order does not matter, and duplicates do no harm; (4) for each share, the greedy
construction (`eq:A-greedy`) takes `O(n log n) + O(n)·FO` time and computing `U_P` another `O(n)`;
(5) evaluating all these shares and retaining one with maximum utility therefore gives the stated
running time. The Lean has (1); (2); of (3), that the evaluated shares form a multiset (no order,
duplicates kept) of shares in `[0, 1)` that contains every `α^(i)`, `i < K`
(`cand_mem_evalShares`); and of (5), that a share of maximum utility among them exists and is
optimal, as `lem:A-candidates` gives an optimal contract among `α^(0), …, α^(K−1)`. The running
times of (3)-(5) are not formalised.

The hypotheses are the STOC version's (`f` a rank function, `m ≥ 0`, `c ≥ 0`, `n ≥ 1`). -/
theorem lineartime [Nonempty E] (hf : IsRankFunction f) (hm : ∀ e, 0 ≤ m e)
    (hc : ∀ e, 0 ≤ c e) :
    Multiset.card (evalShares m c) ≤ Fintype.card E * (Fintype.card E + 1) / 2 + 1 ∧
      (∃ β ∈ evalShares m c, ∀ β' ∈ evalShares m c, utilP f m c β' ≤ utilP f m c β) ∧
      ∀ β ∈ evalShares m c, (∀ β' ∈ evalShares m c, utilP f m c β' ≤ utilP f m c β) →
        β ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ α ∈ Set.Icc (0 : ℝ) 1, utilP f m c α ≤ utilP f m c β := by
  -- (1) "There are at most `n` Type 1 and `n(n − 1)/2` Type 2 candidate breakpoints."
  have h1 := card_type1_le (m := m) (c := c)
  have h2 := card_type2_le (m := m) (c := c)
  -- (2) "Including `α^(0) = 0` and omitting `α^(K) = 1`, as justified in `lem:A-candidates`, we
  -- evaluate at most `1 + n + n(n − 1)/2 = n(n + 1)/2 + 1` shares": `0` and the candidate
  -- breakpoints kept in `[0, 1)` (`evalShares`).
  have hcount : Multiset.card (evalShares m c) ≤ Fintype.card E * (Fintype.card E + 1) / 2 + 1 := by
    have hfilt := Multiset.card_le_card
      (Multiset.filter_le (fun β : ℝ => 0 ≤ β ∧ β < 1) (type1 m c + type2 m c))
    rw [Multiset.card_add] at hfilt
    have heq := count_eq (Fintype.card E)
    rw [evalShares, Multiset.card_cons]
    omega
  -- (3) "Generating the candidate breakpoints and keeping those in `[0, 1)` requires `O(n²)`
  -- arithmetic operations" (not formalised). "Their order does not matter, and duplicates do no
  -- harm": the evaluated shares form a multiset, without an order and with their duplicates. They
  -- lie in `[0, 1)` (`mem_evalShares_bounds`), and every `α^(i)`, `i < K`, is among them
  -- (`cand_mem_evalShares`).
  -- (4) "For each share, the greedy construction (`eq:A-greedy`) takes `O(n log n) + O(n)·FO`
  -- time, and computing the principal's utility takes an additional `O(n)` time." Not formalised.
  -- (5) "Evaluating all these shares and retaining one with maximum utility therefore gives the
  -- stated running time": a share of maximum utility among them exists, and it is optimal, as
  -- `lem:A-candidates` gives an optimal contract among `α^(0), …, α^(K−1)`, all of which are
  -- evaluated. The running time is not formalised.
  obtain ⟨i₀, hi₀, hopt⟩ := (candidates_lemma hf hm hc).2
  refine ⟨hcount, Multiset.exists_max_image (utilP f m c) Multiset.cons_ne_zero,
    fun β hβ hmax => ⟨⟨(mem_evalShares_bounds hβ).1, (mem_evalShares_bounds hβ).2.le⟩,
      fun α hα => (hopt α hα).trans (hmax _ (cand_mem_evalShares hi₀))⟩⟩

/-- The case `E = ∅` of `thm:linear`, which Appendix A.2 settles in its standing assumption
(`stoc-sections/appA-proofs.tex:25-26`): "for `E = ∅`, the only response is `0` and every share is
optimal" (not in the paper: the STOC version states this without proof). The only response is
`0`, so it is the greedy response, agent-optimal and of maximum reward, and `U_P = 0`; there are no
candidate breakpoints, so the only evaluated share is `α^(0) = 0` (`n(n + 1)/2 + 1 = 1`), and it is
an optimal contract. -/
theorem linear_of_isEmpty [IsEmpty E] (hf : IsRankFunction f) :
    Multiset.card (evalShares m c) ≤ Fintype.card E * (Fintype.card E + 1) / 2 + 1 ∧
      (∃ β ∈ evalShares m c, ∀ β' ∈ evalShares m c, utilP f m c β' ≤ utilP f m c β) ∧
      ∀ β ∈ evalShares m c, (∀ β' ∈ evalShares m c, utilP f m c β' ≤ utilP f m c β) →
        β ∈ Set.Icc (0 : ℝ) 1 ∧ IsAgentOpt f m c β (xstar f m c β) ∧
          (∀ y, IsAgentOpt f m c β y → reward m y ≤ reward m (xstar f m c β)) ∧
          ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ y, IsAgentOpt f m c α y →
            (1 - α) * reward m y ≤ utilP f m c β := by
  -- "the only response is `0`": it is agent-optimal, and every reward is `0`.
  have h0 : ∀ x : E → ℝ, x = 0 := fun x => Subsingleton.elim x 0
  have hopt : ∀ α, IsAgentOpt f m c α (xstar f m c α) := fun α => by
    rw [h0 (xstar f m c α)]
    exact ⟨zero_mem_indepPoly hf, fun y _ => by rw [h0 y]⟩
  have hr : ∀ y : E → ℝ, reward m y = 0 := fun y => by simp [reward]
  -- "and every share is optimal": `U_P(α) = (1 − α) mᵀ0 = 0`.
  have hU : ∀ α, utilP f m c α = 0 := fun α => by
    simp [utilP, reward]
  -- There are no candidate breakpoints: the only evaluated share is `α^(0) = 0`.
  have hS : evalShares m c = {0} := by
    simp [evalShares, type1, type2]
  refine ⟨by simp [hS], ⟨0, by simp [hS], fun β' _ => by rw [hU, hU]⟩,
    fun β hβ _ => ⟨⟨(mem_evalShares_bounds hβ).1, (mem_evalShares_bounds hβ).2.le⟩, hopt β,
      fun y _ => by rw [hr, hr], fun α _ y _ => by rw [hr, hU, mul_zero]⟩⟩

/-- **`thm:linear`** (Theorem 2.1, `stoc-sections/04-linear.tex:8-12`, proof
`stoc-sections/appA-proofs.tex:190-192`): for linear costs, an optimal contract can be computed in
time `O(n³)·FO + O(n³ log n)`. Without the running time, which is not formalised: of the at most
`n(n + 1)/2 + 1` shares that `lem:A-lineartime` evaluates (`evalShares`), one has maximum utility,
and every such share `β` is an optimal contract of the model of Section 2
(`stoc-sections/02-preliminaries.tex:17`): `β ∈ [0, 1]`, its greedy response `x*(β)`
(`eq:A-greedy`) is a best response that maximizes the reward among the best responses, so that
`U_P(β) = (1 − β) mᵀx*(β)` is the principal's utility with ties broken in favor of the principal,
and `(1 − α) r(y) ≤ U_P(β)` for every share `α ∈ [0, 1]` and every best response `y` to `α`.

The hypotheses are the STOC version's: `f` a rank function, `m ≥ 0` (Section 2) and `c ≥ 0`; the
standing assumption `r̄ > 0` of Section 2 is not used. Appendix A.2 assumes `n ≥ 1` and settles
`E = ∅` in a parenthetical, "for `E = ∅`, the only response is `0` and every share is optimal"
(`stoc-sections/appA-proofs.tex:25-26`; `linear_of_isEmpty`). For `n ≥ 1`, the STOC version's proof:
(1) by `lem:A-tiebreak`, the greedy response maximizes the principal's reward among the agent's
best responses; (2) by `lem:A-candidates`, evaluating these responses at the candidate shares finds
an optimal contract; (3) the running time follows from `lem:A-lineartime`: the Lean has the shares
it evaluates and their number, and that they contain the candidate shares `α^(0), …, α^(K−1)`
(`cand_mem_evalShares`), so that a share of maximum utility among them is optimal by (1) and (2);
not the time. -/
theorem linear (hf : IsRankFunction f) (hm : ∀ e, 0 ≤ m e) (hc : ∀ e, 0 ≤ c e) :
    Multiset.card (evalShares m c) ≤ Fintype.card E * (Fintype.card E + 1) / 2 + 1 ∧
      (∃ β ∈ evalShares m c, ∀ β' ∈ evalShares m c, utilP f m c β' ≤ utilP f m c β) ∧
      ∀ β ∈ evalShares m c, (∀ β' ∈ evalShares m c, utilP f m c β' ≤ utilP f m c β) →
        β ∈ Set.Icc (0 : ℝ) 1 ∧ IsAgentOpt f m c β (xstar f m c β) ∧
          (∀ y, IsAgentOpt f m c β y → reward m y ≤ reward m (xstar f m c β)) ∧
          ∀ α ∈ Set.Icc (0 : ℝ) 1, ∀ y, IsAgentOpt f m c α y →
            (1 - α) * reward m y ≤ utilP f m c β := by
  -- The standing assumption `n ≥ 1` of Appendix A.2: "for `E = ∅`, the only response is `0` and
  -- every share is optimal" (`linear_of_isEmpty`).
  rcases isEmpty_or_nonempty E with hE | hE
  · exact linear_of_isEmpty hf
  -- (1) "By `lem:A-tiebreak`, the greedy response maximizes the principal's reward among the
  -- agent's best responses."
  have h1 : ∀ α ∈ Set.Icc (0 : ℝ) 1, IsAgentOpt f m c α (xstar f m c α) ∧
      ∀ y, IsAgentOpt f m c α y → reward m y ≤ reward m (xstar f m c α) :=
    fun α hα => tiebreak hf hm hc hα
  -- (2) "By `lem:A-candidates`, evaluating these responses at the candidate shares finds an optimal
  -- contract": an optimal contract `α^(i₀)` among `α^(0), …, α^(K−1)`.
  obtain ⟨i₀, hi₀, hopt⟩ := (candidates_lemma hf hm hc).2
  -- (3) "The running time follows from `lem:A-lineartime`": the shares it evaluates, at most
  -- `n(n + 1)/2 + 1`, of which one of maximum utility is retained; they contain `α^(i₀)`. The
  -- running time is not formalised.
  obtain ⟨hcount, hex, -⟩ := lineartime hf hm hc
  refine ⟨hcount, hex, fun β hβ hmax => ?_⟩
  have hβ01 : β ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(mem_evalShares_bounds hβ).1, (mem_evalShares_bounds hβ).2.le⟩
  refine ⟨hβ01, (h1 β hβ01).1, (h1 β hβ01).2, fun α hα y hy => ?_⟩
  calc (1 - α) * reward m y ≤ (1 - α) * reward m (xstar f m c α) :=
        mul_le_mul_of_nonneg_left ((h1 α hα).2 y hy) (sub_nonneg.2 hα.2)
    _ = utilP f m c α := rfl
    _ ≤ utilP f m c (cand m c i₀) := hopt α hα
    _ ≤ utilP f m c β := hmax _ (cand_mem_evalShares hi₀)

/-- The warm-up of Section 2 (`stoc-sections/04-linear.tex:5`): "Between two consecutive such
candidate shares, the response is constant, and the principal's utility is affine and
nonincreasing, so it suffices to evaluate the left endpoints." For every `i < K`, the response
`x*(α)` is constant on `[α^(i), α^(i+1))` (`lem:A-candidates`), and `U_P` is affine there with the
nonpositive slope `−mᵀx*(α^(i))` (the proof of `lem:A-candidates`, `utilP_affine`), so it is
nonincreasing. -/
theorem const_on_intervals [Nonempty E] (hf : IsRankFunction f) (hm : ∀ e, 0 ≤ m e)
    (hc : ∀ e, 0 ≤ c e) :
    ∀ i < numK m c,
      (∀ α ∈ Set.Ico (cand m c i) (cand m c (i + 1)), xstar f m c α = xstar f m c (cand m c i)) ∧
      (∃ p q : ℝ, q ≤ 0 ∧
        ∀ α ∈ Set.Ico (cand m c i) (cand m c (i + 1)), utilP f m c α = p + q * α) ∧
      AntitoneOn (utilP f m c) (Set.Ico (cand m c i) (cand m c (i + 1))) := by
  intro i hi
  have hconst := fun α hα => ((candidates_lemma hf hm hc).1 i hi α hα).1
  set R := reward m (xstar f m c (cand m c i))
  have hU : ∀ α ∈ Set.Ico (cand m c i) (cand m c (i + 1)), utilP f m c α = R + (-R) * α :=
    fun α hα => (utilP_affine hf hm (hconst α hα)).1
  have hR : -R ≤ 0 := neg_nonpos.2 (reward_xstar_nonneg hf hm)
  refine ⟨hconst, ⟨R, -R, hR, hU⟩, fun α hα α' hα' hle => ?_⟩
  rw [hU α hα, hU α' hα']
  nlinarith

end

end Linear

end Stoc
