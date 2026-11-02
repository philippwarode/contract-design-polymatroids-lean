-- stamp r7 2026-11-02
import Mathlib
import ContractDesignPolymatroids.OptimalShare.Exponential

/-!
# Polynomial bit length

The STOC version, Section 3 (`stoc-sections/06-optimal-share.tex:72-78`), Theorem
`thm:polybits`, with its proof in Appendix B.7 (`stoc-sections/appC-bits.tex:226-363`).

The numbers `t_k`, `λ_k`, `θ_k`, `d_i^{(k)}`, `D_k`, `K_k`, the set function `g` and the witnesses
are those of `prop:witness` (`ContractDesignPolymatroids/OptimalShare/Witness.lean`), on `E = {1, …, n}` as `Fin n` (the
element `e` being the paper's `e + 1`). Here `Λ = 1 + ∑_k D_k` (`Lam`),
`f(S) = g(S) + ∑_{e∈S} (Λ t_e − 1)` with integer values (`fZ`, real `fR`), and the rewards are
`m = t/σ = (f(E) + 1) t` (`mZ`) for `σ = 1/(f(E) + 1)`.

The paper's proof has no numbered steps. We number its paragraphs (0) to (6), as in the docstring
of `polybits`, and the lemmas `step1`, `step2` and `step3` are named after this numbering:
* (1) "We first show that `f` is a polymatroid rank function and that every `S ⊆ E` is a level
  set": `step1`, with the condition on `Λ` of `lem:embed` (`embed_cond`, through submodularity and
  `g_top`) and `lem:embed` itself (`Stoc.Exp.embed`).
* (2) "Next we show that the number `B_∞` of breakpoints of `(f, t, 1)` in `(0, ∞)` satisfies
  `2^n ≤ (B_∞ + 1)(1 + n(n + 1)/2)`": `step2`, with `Stoc.Exp.strict_near_share`,
  `Stoc.Exp.exists_point_of_near` and the line-arrangement argument `Stoc.Exp.two_pow_le_cells`
  on `(0, ∞)`.
* (3) "Next we show that all breakpoints lie in `(0, f(E)]`": `step3`, with `prop:witness` (i)
  (`Stoc.Witness.witness`), the greedy vector `vg` for the order `n, …, 1` (Edmonds' greedy
  theorem [Edm03, (19)], `Stoc.greedy_pos`) and `prop:optchar` (`Stoc.optchar`).
* (4) "Now we pass to the rewards `t/σ`": the dilation by `σ` (`lem:ops`(b),
  `Stoc.Hardness.ops_b_aux`, and the D3 lemma `Stoc.Exp.breakpoints_comp_div`), in `polybits`.
* (5) "Finally, for part (i), we show that all numbers have `O(n log n)` bits and that `f` can be
  evaluated in polynomial time": the sizes, through `τ = 2(2n + 2)^{n−1}` (`Stoc.Network.tau`,
  with the first bounds `Stoc.Network.t_le_tau`, `theta_le`, `D_le`, `K_le`): `Lam_le`,
  `summand_le`, `n_mul_summand_le`, `fE_le`, and `Stoc.Network.size_bound_le` (`O(n log n)` bits);
  the closed form of `f` (`fZ_eq`).
* (6) "It remains to prove part (ii), for networks": `Stoc.Network.polybits_ii`.

Not formalised: the running times in (5) (the recursion of `prop:witness` with `O(n²)` operations
and the evaluation of `f` in polynomial time); the statement records the closed form of `f` with
its `n` weights and `n²` pair weights, all of `O(n log n)` bits.

Taken over on 2026-10-20 from `Paper/OptimalShare/PolyBit.lean` (the paper at Overleaf f035b19) for
the STOC version (`stoc.tex`); from then on this copy follows the STOC version.
-/

namespace Stoc

namespace PolyBit

open Finset Witness Network

variable (n : ℕ)

/-- `Λ = 1 + ∑_{k∈E} D_k`. -/
noncomputable def Lam : ℤ := 1 + ∑ k ∈ Ico 1 (n + 1), D k

/-- `f(S) = g(S) + ∑_{e∈S} (Λ t_e − 1)`, with integer values. -/
noncomputable def fZ (S : Finset (Fin n)) : ℤ :=
  g (S.map (emb n)) + ∑ e ∈ S, (Lam n * t (emb n e) - 1)

/-- `f` with real values, the rank function of the instance. -/
noncomputable def fR (S : Finset (Fin n)) : ℝ := fZ n S

/-- The rewards `m_e = t_e/σ = (f(E) + 1) t_e` for `σ = 1/(f(E) + 1)`. -/
noncomputable def mZ (e : Fin n) : ℤ := (fZ n univ + 1) * t (emb n e)

variable {n}

/-! ### (1) `f` is a polymatroid rank function, and every `S ⊆ E` is a level set -/

/-- `D_k ≥ 0`, as `d_i^{(k)} ≥ 0` for all `i < k` by `prop:witness` (i)
(`Stoc.Witness.d_nonneg`). -/
lemma D_nonneg {k : ℕ} : 0 ≤ D k :=
  sum_nonneg fun _ hi => d_nonneg (mem_Ico.1 hi).1 (mem_Ico.1 hi).2

lemma one_le_Lam : 1 ≤ Lam n := by
  unfold Lam
  linarith [sum_nonneg fun k (_ : k ∈ Ico 1 (n + 1)) => (D_nonneg (k := k))]

/-- Adding an element `j` to `X`: the pairs that contain `j` are `{i, j}` with `i ∈ X`. -/
lemma g_insert_of_notMem {j : ℕ} {X : Finset ℕ} (hj : j ∉ X) :
    g (insert j X) = g X + K j - ∑ i ∈ X.filter (· < j), d i j -
      ∑ k ∈ X.filter (j < ·), d j k := by
  have h1 : (insert j X).filter (· < j) = X.filter (· < j) := by
    rw [filter_insert]
    split_ifs with h
    · exact absurd h (lt_irrefl j)
    · rfl
  have h2 : ∀ k ∈ X, ∑ i ∈ (insert j X).filter (· < k), d i k =
      ∑ i ∈ X.filter (· < k), d i k + if j < k then d j k else 0 := by
    intro k _
    rw [filter_insert]
    split_ifs with hjk
    · rw [sum_insert (fun h => hj (mem_filter.1 h).1), add_comm]
    · rw [add_zero]
  unfold g
  rw [sum_insert hj, sum_insert hj, h1, sum_congr rfl h2, sum_add_distrib, ← sum_filter]
  ring

lemma map_univ_emb : (univ : Finset (Fin n)).map (emb n) = Ico 1 (n + 1) := by
  ext j
  simp only [mem_map, mem_univ, true_and, mem_Ico, emb_apply]
  constructor
  · rintro ⟨i, rfl⟩
    omega
  · intro hj
    exact ⟨⟨j - 1, by omega⟩, by simp; omega⟩

/-- "by the definition of `g`, `g(E) − g(E ∖ {e}) = K_e − D_e − ∑_{k>e} d_e^{(k)}`". -/
lemma g_top (e : Fin n) :
    gE n univ - gE n (univ.erase e) =
      K (emb n e) - D (emb n e) - ∑ k ∈ Ioc (emb n e) n, d (emb n e) k := by
  have hX : (univ.erase e).map (emb n) = (Ico 1 (n + 1)).erase (emb n e) := by
    rw [map_erase, map_univ_emb]
  have hins : insert (emb n e) ((Ico 1 (n + 1)).erase (emb n e)) = Ico 1 (n + 1) :=
    insert_erase (by rw [← map_univ_emb]; exact mem_map_of_mem _ (mem_univ e))
  have h1 : ((Ico 1 (n + 1)).erase (emb n e)).filter (· < emb n e) = Ico 1 (emb n e) := by
    ext i
    rw [mem_filter, mem_erase, mem_Ico, mem_Ico, emb_apply]
    have := e.isLt
    omega
  have h2 : ((Ico 1 (n + 1)).erase (emb n e)).filter (emb n e < ·) = Ioc (emb n e) n := by
    ext i
    rw [mem_filter, mem_erase, mem_Ico, mem_Ioc, emb_apply]
    have := e.isLt
    omega
  have hg := g_insert_of_notMem (notMem_erase (emb n e) (Ico 1 (n + 1)))
  rw [hins, h1, h2] at hg
  simp only [gE, map_univ_emb, hX, hg, D]
  push_cast
  ring

lemma one_le_emb (e : Fin n) : 1 ≤ emb n e := by simp

lemma emb_le (e : Fin n) : emb n e ≤ n := by
  simp only [emb_apply]
  have := e.isLt
  omega

/-- `t_e ≥ 1` for `e ∈ E`, as `t_e ≥ t_1 = 2` by `prop:witness` (i) (`Stoc.Witness.two_le_t`); in
particular `t ∈ ℝ^E_{>0}`, as `lem:embed` needs for `a = t`. -/
lemma one_le_tE (e : Fin n) : (1 : ℝ) ≤ tE n e := by
  have := two_le_t (k := emb n e) (by simp)
  simp only [tE]
  exact_mod_cast (show (1 : ℤ) ≤ t (emb n e) by linarith)

/-- The condition on `Λ` of `lem:embed` in (1) of the proof of `thm:polybits`
(`appC-bits.tex:245-253`): for `e ∈ E` and `S ⊆ E ∖ {e}`, `(g(S) − g(S ∪ {e}) + 1)/t_e ≤ Λ`. -/
lemma embed_cond (hn : 1 ≤ n) :
    ∀ S e, e ∉ S → (gE n S - gE n (insert e S) + 1 * 1) / tE n e ≤ Lam n := by
  intro S e he
  -- "By submodularity and by the definition of `g`,
  -- `g(S ∪ {e}) − g(S) ≥ g(E) − g(E ∖ {e}) = K_e − D_e − ∑_{k>e} d_e^{(k)}`."
  have hdr := (witness n hn).2.1.1.diminishingReturns (X := S) (Y := univ.erase e) (e := e)
    (fun x hx => mem_erase.2 ⟨fun h => he (h ▸ hx), mem_univ x⟩) (notMem_erase e univ)
  rw [insert_erase (mem_univ e), g_top e] at hdr
  -- "Here `K_e − D_e = t_e λ̄_e + 1 ≥ 1` and `0 ≤ d_e^{(k)} ≤ D_k` for `k > e`,"
  have hKD : 1 ≤ K (emb n e) - D (emb n e) := by
    have : 0 ≤ t (emb n e) * lamBar (emb n e) :=
      mul_nonneg (t_pos (by simp)).le (lamBar_nonneg _)
    unfold K
    linarith
  have hdD : ∀ k ∈ Ioc (emb n e) n, d (emb n e) k ≤ D k := fun k hk => by
    have hk' := mem_Ioc.1 hk
    exact single_le_sum (f := fun i => d i k)
      (fun i hi => d_nonneg (mem_Ico.1 hi).1 (mem_Ico.1 hi).2)
      (mem_Ico.2 ⟨by simp, hk'.1⟩)
  -- "so `g(S) − g(S ∪ {e}) + 1 ≤ ∑_{k>e} D_k < Λ ≤ Λ t_e`."
  have h1 : ∑ k ∈ Ioc (emb n e) n, d (emb n e) k ≤ ∑ k ∈ Ioc (emb n e) n, D k := sum_le_sum hdD
  have h2 : ∑ k ∈ Ioc (emb n e) n, D k < Lam n := by
    have : ∑ k ∈ Ioc (emb n e) n, D k ≤ ∑ k ∈ Ico 1 (n + 1), D k :=
      sum_le_sum_of_subset_of_nonneg (fun k hk => by
        have := mem_Ioc.1 hk
        exact mem_Ico.2 ⟨by simp at this; omega, by omega⟩) fun k _ _ => D_nonneg
    unfold Lam
    linarith
  have hchain : gE n S - gE n (insert e S) + 1 < Lam n := by
    have h1' : ((∑ k ∈ Ioc (emb n e) n, d (emb n e) k : ℤ) : ℝ) ≤
        ((∑ k ∈ Ioc (emb n e) n, D k : ℤ) : ℝ) := by exact_mod_cast h1
    have h2' : ((∑ k ∈ Ioc (emb n e) n, D k : ℤ) : ℝ) < (Lam n : ℝ) := by exact_mod_cast h2
    have hKD' : (1 : ℝ) ≤ ((K (emb n e) - D (emb n e) : ℤ) : ℝ) := by exact_mod_cast hKD
    push_cast at h1' h2' hKD' hdr
    linarith
  have hΛt : (Lam n : ℝ) ≤ Lam n * tE n e := by
    have : (0 : ℝ) ≤ Lam n := by
      exact_mod_cast (show (0 : ℤ) ≤ Lam n by linarith [one_le_Lam (n := n)])
    nlinarith [one_le_tE e]
  rw [div_le_iff₀ (by linarith [one_le_tE e])]
  linarith

lemma wit_fst_nonneg (S : Finset (Fin n)) : 0 ≤ (wit n S).1 := by
  rw [wit_eq]
  have : (0 : ℤ) ≤ ∑ j ∈ S.map (emb n), lam j := sum_nonneg fun j _ => (lam_pos j).le
  show (0 : ℝ) ≤ ((∑ j ∈ S.map (emb n), lam j : ℤ) : ℝ)
  exact_mod_cast this

lemma wit_snd_nonneg (S : Finset (Fin n)) : 0 ≤ (wit n S).2 := by
  rw [wit_eq]
  have : (0 : ℤ) ≤ ∑ j ∈ S.map (emb n), Witness.theta j :=
    sum_nonneg fun j hj => theta_nonneg (lt_of_mem_map_emb hj).1
  show (0 : ℝ) ≤ ((∑ j ∈ S.map (emb n), Witness.theta j : ℤ) : ℝ)
  exact_mod_cast this

/-- `f = f̃ + ∑ (Λ a_e − Θ b_e)` with `f̃ = g`, `a = t`, `b = 1` and `(Λ, Θ) = (Λ, 1)`. -/
lemma fR_eq : fR n = Exp.embedF (gE n) (tE n) (fun _ => 1) (Lam n) 1 := by
  funext S
  simp only [fR, fZ, Exp.embedF, gE, tE]
  push_cast
  ring_nf

/-- `f̃ − λ a − θ b` with `b = 1` and the offsets `(λ_S, −θ_S)` is `F^g_{λ_S, θ_S}`. -/
lemma tilt_eq (w : ℝ × ℝ) (T : Finset (Fin n)) :
    Exp.tilt (gE n) (tE n) (fun _ => 1) w.1 (-w.2) T = F (gE n) (tE n) w T := by
  simp only [Exp.tilt, F, sum_const, nsmul_eq_mul, mul_one]
  ring

/-- **(1)** of the proof of `thm:polybits` (`appC-bits.tex:240-260`), "We first show that `f` is a
polymatroid rank function and that every `S ⊆ E` is a level set": `f` is a polymatroid rank
function, and in the instance `(f, t, 1)` every `S ⊆ E` is the level set `A_{1+θ_S}(Λ + λ_S)`. -/
lemma step1 (hn : 1 ≤ n) :
    IsRankFunction (fR n) ∧ ∀ S : Finset (Fin n),
      levelSet (tE n) (fun _ => 1) (Lam n + (wit n S).1)
        (bestResponse (fR n) (tE n) (fun _ => 1) (Lam n + (wit n S).1)) (1 + (wit n S).2) = S := by
  -- "We apply `lem:embed` with `f̃ := g`, `a := t`, the all-ones vector `1` as the vector `b` of
  -- the lemma, and its parameters `(Λ, Θ) := (Λ, 1)`. The instance of the lemma then has the
  -- rewards `m_e = t_e` and `β_e = 1` for all `e ∈ E`."
  have hm : (fun e => tE n e / (fun _ => (1 : ℝ)) e) = tE n := funext fun e => div_one _
  have hβ : (fun e => 1 / (fun _ => (1 : ℝ)) e) = fun _ : Fin n => (1 : ℝ) :=
    funext fun _ => div_one 1
  -- "To check the condition on `Λ`, let `e ∈ E` and `S ⊆ E∖{e}`. …" (`embed_cond`) "As also
  -- `Λ ≥ 0`, the condition on `Λ` holds, and `f` is a polymatroid rank function, with integer
  -- values as all numbers involved are integers."
  have hΛ0 : (0 : ℝ) ≤ Lam n := by
    exact_mod_cast (show (0 : ℤ) ≤ Lam n by linarith [one_le_Lam (n := n)])
  obtain ⟨hrank, hlev⟩ := Exp.embed (witness n hn).2.1.1 (witness n hn).2.1.2
    (fun e => (by linarith [one_le_tE e] : (0 : ℝ) < tE n e)) (fun _ => one_pos) one_pos hΛ0
    (embed_cond hn)
  rw [← fR_eq, hm, hβ] at hlev
  refine ⟨fR_eq ▸ hrank, fun S => ?_⟩
  -- "Now let `S ⊆ E`. By `lem:embed` with the offsets `(λ, θ) := (λ_S, −θ_S)`, where
  -- `λ_S ≥ 0 > −Λ` and `−θ_S ≤ 0 < 1 = Θ`, the level set `A_{1+θ_S}(Λ + λ_S)` is the maximal
  -- minimizer of `g − λ_S t + θ_S |·| = F^g_{λ_S, θ_S}`."
  have hlam0 : 0 ≤ (wit n S).1 := by
    exact wit_fst_nonneg S
  have hθ0 : 0 ≤ (wit n S).2 := by
    exact wit_snd_nonneg S
  have h := hlev (wit n S).1 (-(wit n S).2) (by linarith) (by linarith)
  rw [sub_neg_eq_add] at h
  have hF : Exp.tilt (gE n) (tE n) (fun _ => 1) (wit n S).1 (-(wit n S).2) =
      F (gE n) (tE n) (wit n S) :=
    funext (tilt_eq (wit n S))
  rw [hF] at h
  -- "By `prop:witness`(ii), this function has the unique minimizer `S`, so
  -- `A_{1+θ_S}(Λ + λ_S) = S`."
  exact h.eq_of_unique ((witness n hn).2.2 S)

/-! ### (2) The number `B_∞` of breakpoints in `(0, ∞)` -/

/-- **(2)** of the proof of `thm:polybits` (`appC-bits.tex:262-279`), "Next we show that the
number `B_∞` of breakpoints of `(f, t, 1)` in `(0, ∞)` satisfies
`2^n ≤ (B_∞ + 1)(1 + n(n + 1)/2)`": `B_∞` is finite and satisfies this bound. -/
lemma step2 (hn : 1 ≤ n) :
    (breakpoints (bestResponse (fR n) (tE n) (fun _ => 1))).Finite ∧
      2 ^ n ≤ ((breakpoints (bestResponse (fR n) (tE n) (fun _ => 1))).ncard + 1) *
        (1 + n * (n + 1) / 2) := by
  classical
  obtain ⟨hrank, hlevS⟩ := step1 hn
  have H : Tracing.Hyp (fR n) (tE n) (fun _ => 1) :=
    ⟨hrank, fun _ => one_pos, fun e => by linarith [one_le_tE e]⟩
  -- "By `lem:pwaffine`, `B_∞` is finite."
  have hfin : (breakpoints (bestResponse (fR n) (tE n) (fun _ => 1))).Finite := (pwaffine H).2.2.1
  refine ⟨hfin, ?_⟩
  have hpts : ∀ S : Finset (Fin n), ∃ α θ : ℝ, α ∈ Set.Ioi 0 ∧ α ∉ Tracing.BP (fR n) (tE n)
      (fun _ => 1) ∧ (∀ e, rho (fR n) (tE n) (fun _ => 1) α e ≠ θ) ∧
      levelSet (tE n) (fun _ => 1) α (bestResponse (fR n) (tE n) (fun _ => 1) α) θ = S := by
    intro S
    -- "Let `S ⊆ E` and `α_S := Λ + λ_S > 0`. As `S = A_{1+θ_S}(α_S)`, `ρ_e(α_S) ≥ 1 + θ_S` for
    -- `e ∈ S` and `ρ_e(α_S) < 1 + θ_S` for `e ∉ S`." (`S = A_{1+θ_S}(α_S)` is (1), `step1`.)
    set αS := (Lam n : ℝ) + (wit n S).1
    have hlam0 : 0 ≤ (wit n S).1 := by
      exact wit_fst_nonneg S
    have hθ0 : 0 ≤ (wit n S).2 := by
      exact wit_snd_nonneg S
    have hαS : 0 < αS := by
      have : (1 : ℝ) ≤ Lam n := by exact_mod_cast one_le_Lam (n := n)
      simp only [αS]
      linarith
    have hA := hlevS S
    have hin : ∀ e ∈ S, 1 + (wit n S).2 ≤ rho (fR n) (tE n) (fun _ => 1) αS e := fun e he => by
      rw [← hA] at he
      exact (mem_filter.1 he).2
    have hout : ∀ e ∉ S, rho (fR n) (tE n) (fun _ => 1) αS e < 1 + (wit n S).2 := fun e he => by
      rw [← hA] at he
      simp only [levelSet, mem_filter, mem_univ, true_and, not_le] at he
      exact he
    -- "Choose `θ'_S` with `max{0, ρ_e(α_S) : e ∉ S} < θ'_S < 1 + θ_S`. Then `ρ_e(α_S) > θ'_S` for
    -- `e ∈ S` and `ρ_e(α_S) < θ'_S` for `e ∉ S`,"
    set M := (insert 0 ((univ.filter (· ∉ S)).image (rho (fR n) (tE n) (fun _ => 1) αS))).max'
      (insert_nonempty _ _)
    have hM : M < 1 + (wit n S).2 := by
      rw [max'_lt_iff]
      intro y hy
      rcases mem_insert.1 hy with rfl | hy
      · linarith
      · obtain ⟨e, he, rfl⟩ := mem_image.1 hy
        exact hout e (mem_filter.1 he).2
    set θ' := (M + (1 + (wit n S).2)) / 2
    have hsin : ∀ e ∈ S, θ' < rho (fR n) (tE n) (fun _ => 1) αS e := fun e he => by
      have := hin e he
      simp only [θ']
      linarith
    have hsout : ∀ e ∉ S, rho (fR n) (tE n) (fun _ => 1) αS e < θ' := fun e he => by
      have : rho (fR n) (tE n) (fun _ => 1) αS e ≤ M :=
        le_max' _ _ (mem_insert_of_mem (mem_image.2 ⟨e, by simp [he], rfl⟩))
      simp only [θ']
      linarith
    -- "and by continuity of `ρ` (`lem:pwaffine`), these strict inequalities hold at every share
    -- near `α_S`."
    have hnear := Exp.strict_near_share H hαS hsin hsout
    -- "As `θ'_S > 0` and there are finitely many breakpoints, there is a share `α'_S > 0` that is
    -- not a breakpoint such that `A_{θ'_S}(α'_S) = S` and `ρ_e(α'_S) ≠ θ'_S` for all `e ∈ E`."
    -- (The Lean level sets need no positive level, so `θ'_S > 0` is not used.)
    obtain ⟨α', hα', hα'B, hne, hA'⟩ :=
      Exp.exists_point_of_near H isOpen_Ioi (Set.mem_Ioi.2 hαS) hnear
    exact ⟨α', θ', hα', hα'B, hne, hA'⟩
  -- "With these points `(α'_S, θ'_S)`, the line-arrangement argument of the second paragraph of
  -- the proof of `thm:expbp`, with `(0, ∞)` in place of the bounded interval of shares considered
  -- there and `B_∞` in place of the number of breakpoints in it, gives
  -- `2^n ≤ (B_∞ + 1)(1 + n(n + 1)/2)`."
  have hcount := Exp.two_pow_le_cells H Set.ordConnected_Ioi (fun _ h => h) hpts
  have hBI : Tracing.BP (fR n) (tE n) (fun _ => 1) ∩ Set.Ioi 0 =
      breakpoints (bestResponse (fR n) (tE n) (fun _ => 1)) :=
    Set.inter_eq_left.2 fun α hα => hα.1
  rw [hBI, Fintype.card_fin] at hcount
  exact hcount

/-! ### (3) All breakpoints lie in `(0, f(E)]` -/

/-- The greedy vector `v` of (3) of the proof of `thm:polybits`, for the order `n, n − 1, …, 1`:
`v_k = f({k, …, n}) − f({k + 1, …, n})`. -/
noncomputable def vg (e : Fin n) : ℝ := fR n (univ.filter (e ≤ ·)) - fR n (univ.filter (e < ·))

/-- The vector of Edmonds' greedy theorem for the order `n, n − 1, …, 1` (the enumeration
`Fin.revPerm`) is `v`. -/
lemma edmondsVec_eq_vg : edmondsVec (fR n) Fin.revPerm n = vg := by
  funext e
  have hlt : ((Fin.revPerm.symm e : Fin n) : ℕ) < n := (Fin.revPerm.symm e).isLt
  have h1 : prefixSet (Fin.revPerm (n := n)) ((Fin.revPerm.symm e : Fin n) + 1) =
      univ.filter (e ≤ ·) := by
    ext e'
    simp only [prefixSet, mem_filter, mem_univ, true_and, Fin.revPerm_symm, Fin.revPerm_apply,
      Fin.val_rev, Fin.le_def]
    have := e.isLt
    have := e'.isLt
    omega
  have h2 : prefixSet (Fin.revPerm (n := n)) (Fin.revPerm.symm e : Fin n) =
      univ.filter (e < ·) := by
    ext e'
    simp only [prefixSet, mem_filter, mem_univ, true_and, Fin.revPerm_symm, Fin.revPerm_apply,
      Fin.val_rev, Fin.lt_def]
    have := e.isLt
    have := e'.isLt
    omega
  simp only [edmondsVec, hlt, ↓reduceIte, h1, h2, vg]

/-- `v` is the vector of greedy increments for the key `Fin.rev` (the order `n, …, 1`). -/
lemma vg_eq_greedyStep : vg = greedyStep (fR n) (Fin.rev (n := n)) := by
  funext e
  have hb : before (Fin.rev (n := n)) e = univ.filter (e < ·) := by
    ext e'
    simp [before, Fin.rev_lt_rev]
  have hi : insert e (univ.filter (e < ·)) = univ.filter (e ≤ ·) := by
    ext e'
    simp only [mem_insert, mem_filter, mem_univ, true_and]
    constructor
    · rintro (rfl | h)
      · exact le_rfl
      · exact h.le
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
  simp only [vg, greedyStep, hb, hi]

lemma fin_monotone_of_succ {g : Fin n → ℝ} (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → g i ≤ g j) :
    Monotone g := by
  intro i j hij
  obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) = i + d := ⟨j - i, by rw [Fin.le_def] at hij; omega⟩
  induction d generalizing j with
  | zero =>
    have : i = j := Fin.ext (by omega)
    rw [this]
  | succ d ih =>
    have hj' : (i : ℕ) + d < n := by have := j.isLt; omega
    exact (ih (j := ⟨(i : ℕ) + d, hj'⟩) (Fin.le_def.2 (by simp)) rfl).trans
      (h _ _ (by simp; omega))

/-- **(3)** of the proof of `thm:polybits` (`appC-bits.tex:281-299`), "Next we show that all
breakpoints lie in `(0, f(E)]`": `x*(α) = v` for every `α ≥ f(E)`, so `x*` is constant on
`[f(E), ∞)`, and every breakpoint lies in `(0, f(E)]`.

The paper's steps: (1) as `t_n > ⋯ > t_1 > 0` by `prop:witness` (i) (`Stoc.Witness.witness`),
Edmonds' greedy theorem [Edm03, (19)] (`Stoc.greedy_pos`) for the order `n, …, 1` shows that `v`
maximizes `tᵀx` over `P₊(f)`, so `v ∈ P₊(f)`; (2) every set `{k, …, n}` is tight for `v`, as the
differences telescope;
(3) `0 ≤ v_k ≤ f({k}) ≤ f(E)`; (4) for `α ≥ f(E)`, `ρ_k(v) = α t_k − v_k`; (5) for `k ≥ 2`,
`t_k ≥ t_{k−1} + 1`, so `ρ_k(v) − ρ_{k−1}(v) = α (t_k − t_{k−1}) − v_k + v_{k−1} ≥ α − f(E) ≥ 0`,
and `ρ_1(v) ≥ α − f(E) ≥ 0` as `t_1 ≥ 1`; (6) so `0 ≤ ρ_1(v) ≤ ⋯ ≤ ρ_n(v)`, and every level set
`A_θ(v)`, `θ > 0`, is empty or `{k, …, n}`, hence tight; (7) by `prop:optchar` (`Stoc.optchar`),
`v = x*(α)`; (8) so `x*` is constant on `[f(E), ∞)` and every breakpoint lies in `(0, f(E)]`. -/
lemma step3 (hn : 1 ≤ n) :
    (∀ α, fR n univ ≤ α → bestResponse (fR n) (tE n) (fun _ => 1) α = vg) ∧
      breakpoints (bestResponse (fR n) (tE n) (fun _ => 1)) ⊆ Set.Ioc 0 (fR n univ) := by
  have hrank := (step1 hn).1
  -- (1) "As `t_n > ⋯ > t_1 > 0` by `prop:witness`(i), Edmonds' greedy theorem [Edm03, (19)] for
  -- the order `n, n − 1, …, 1` shows that `v` maximizes `tᵀx` over `P₊(f)`, so in particular
  -- `v ∈ P₊(f)`."
  obtain ⟨ht1, hchain, -, -⟩ := (witness n hn).1
  have hmono_t : Monotone (tE n) := fun i j hij => by
    simp only [tE, emb_apply]
    rcases (Fin.le_def.1 hij).lt_or_eq with h | h
    · exact_mod_cast (chain_lt hchain (by omega) (by omega : (i : ℕ) + 1 < j + 1)
        (by omega)).le
    · rw [h]
  have ht1R : ∀ e : Fin n, (e : ℕ) = 0 → tE n e = 2 := fun e he => by
    simp only [tE, emb_apply, he, zero_add, ht1]
    norm_num
  have htpos : ∀ e, 0 < tE n e := fun e => by
    have h0 : ⟨0, by omega⟩ ≤ e := Fin.le_def.2 (Nat.zero_le _)
    have := hmono_t h0
    rw [ht1R ⟨0, by omega⟩ rfl] at this
    linarith
  have hanti : Antitone (tE n ∘ Fin.revPerm) := fun i j hij => by
    simp only [Function.comp_apply, Fin.revPerm_apply]
    exact hmono_t (Fin.rev_le_rev.2 hij)
  have hk : (univ.filter fun e => 0 < tE n e).card = n := by
    rw [filter_true_of_mem fun e _ => htpos e, card_univ, Fintype.card_fin]
  have hgr := greedy_pos hrank Fin.revPerm (tE n) hanti
  rw [hk, edmondsVec_eq_vg] at hgr
  have hv : vg ∈ indepPoly (fR n) := hgr.1
  -- (2) "Every set `{k, …, n}` is tight with respect to `v`, as the differences telescope,"
  have htel : ∀ e : Fin n, ∑ e' ∈ univ.filter (e ≤ ·), vg e' = fR n (univ.filter (e ≤ ·)) := by
    intro e
    rw [vg_eq_greedyStep]
    refine sum_greedyStep hrank.empty Fin.rev_injective _ fun e₁ he₁ e₂ h => ?_
    simp only [mem_filter, mem_univ, true_and] at he₁ ⊢
    exact he₁.trans (Fin.rev_lt_rev.1 h).le
  -- (3) "and `0 ≤ v_k ≤ f({k}) ≤ f(E)` by monotonicity and submodularity of `f`."
  have hv0 : ∀ e, 0 ≤ vg e := fun e => sub_nonneg.2 (hrank.mono fun x hx => by
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.le)
  have hvE : ∀ e, vg e ≤ fR n univ := fun e => by
    have hdr := hrank.submod.diminishingReturns (X := ∅) (Y := univ.filter (e < ·)) (e := e)
      (empty_subset _) (by simp)
    have hins : insert e (univ.filter (e < ·)) = univ.filter (e ≤ ·) := by
      ext e'
      simp only [mem_insert, mem_filter, mem_univ, true_and]
      constructor
      · rintro (rfl | h)
        · exact le_rfl
        · exact h.le
      · intro h
        rcases h.lt_or_eq with h | h
        · exact Or.inr h
        · exact Or.inl h.symm
    rw [hins, insert_empty, hrank.empty, sub_zero] at hdr
    have := hrank.mono (subset_univ {e})
    simp only [vg]
    linarith
  -- (4) "Let `α ≥ f(E)`. The marginals at `v` are `ρ_k(v) = α t_k − v_k`."
  have hbr : ∀ α, fR n univ ≤ α → bestResponse (fR n) (tE n) (fun _ => 1) α = vg := by
    intro α hα
    have hmarg : ∀ e, marg (tE n) (fun _ => 1) α vg e = α * tE n e - vg e := fun e => by
      simp [marg]
    have hfE : 0 ≤ fR n univ := hrank.nonneg _
    have hα0 : 0 ≤ α := hfE.trans hα
    -- (5) "For `k ≥ 2`, the integers `t_k` satisfy `t_k ≥ t_{k−1} + 1`, so
    -- `ρ_k(v) − ρ_{k−1}(v) = α (t_k − t_{k−1}) − v_k + v_{k−1} ≥ α − f(E) ≥ 0`,"
    have hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 →
        marg (tE n) (fun _ => 1) α vg i ≤ marg (tE n) (fun _ => 1) α vg j := by
      intro i j hij
      have ht : tE n i + 1 ≤ tE n j := by
        have h := hchain ((i : ℕ) + 1) (by omega) (by omega)
        simp only [tE, emb_apply, hij]
        exact_mod_cast (show t ((i : ℕ) + 1) + 1 ≤ t ((i : ℕ) + 1 + 1) by omega)
      have hαt : α * 1 ≤ α * (tE n j - tE n i) := mul_le_mul_of_nonneg_left (by linarith) hα0
      have hdiff : marg (tE n) (fun _ => 1) α vg j - marg (tE n) (fun _ => 1) α vg i ≥ 0 :=
        calc marg (tE n) (fun _ => 1) α vg j - marg (tE n) (fun _ => 1) α vg i
            = α * (tE n j - tE n i) - vg j + vg i := by rw [hmarg, hmarg]; ring
          _ ≥ α - fR n univ := by linarith [hv0 i, hvE j]
          _ ≥ 0 := by linarith
      linarith
    -- "and `ρ_1(v) ≥ α − f(E) ≥ 0` as `t_1 ≥ 1`."
    have hfirst : ∀ e : Fin n, (e : ℕ) = 0 → 0 ≤ marg (tE n) (fun _ => 1) α vg e := by
      intro e he
      have hte : (1 : ℝ) ≤ tE n e := by rw [ht1R e he]; norm_num
      have hαt : α * 1 ≤ α * tE n e := mul_le_mul_of_nonneg_left hte hα0
      have h1 : marg (tE n) (fun _ => 1) α vg e ≥ 0 :=
        calc marg (tE n) (fun _ => 1) α vg e = α * tE n e - vg e := hmarg e
          _ ≥ α - fR n univ := by linarith [hvE e]
          _ ≥ 0 := by linarith
      exact h1
    -- (6) "So `0 ≤ ρ_1(v) ≤ ⋯ ≤ ρ_n(v)`,"
    have hmono : Monotone (marg (tE n) (fun _ => 1) α vg) := fin_monotone_of_succ hstep
    have hρ0 : ∀ e, 0 ≤ marg (tE n) (fun _ => 1) α vg e := fun e =>
      (hfirst ⟨0, by omega⟩ rfl).trans (hmono (Fin.le_def.2 (Nat.zero_le _)))
    -- "and every level set `A_θ(v)` with `θ > 0` is empty or of the form `{k, …, n}`, hence
    -- tight."
    have htight : ∀ θ > 0, IsTight (fR n) vg (levelSet (tE n) (fun _ => 1) α vg θ) := by
      intro θ _
      set A := levelSet (tE n) (fun _ => 1) α vg θ
      rcases A.eq_empty_or_nonempty with hA | hA
      · rw [hA]
        simp [IsTight, hrank.empty]
      · have hAe : A = univ.filter (A.min' hA ≤ ·) := by
          ext e
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · exact fun he => A.min'_le e he
          · intro he
            have h1 := (mem_filter.1 (A.min'_mem hA)).2
            exact mem_filter.2 ⟨mem_univ e, h1.trans (hmono he)⟩
        rw [hAe]
        exact htel _
    -- (7) "By `prop:optchar`, `v` is the best response at the share `α`."
    have hopt : IsBestResponse (indepPoly (fR n)) (tE n) (fun _ => 1) α vg :=
      (optchar hrank (fun _ => one_pos) (fun e => (htpos e).le) hα0 hv).1.2 ⟨hρ0, htight⟩
    exact (hopt.eq_bestResponse (fun _ => one_pos) hrank).symm
  refine ⟨hbr, ?_⟩
  -- (8) "So `x*` is constant on `[f(E), ∞)`, and every breakpoint lies in `(0, f(E)]`."
  intro α ⟨hα0, hnot⟩
  refine ⟨hα0, not_lt.1 fun hαE => hnot ⟨α - fR n univ, by linarith, vg, 0, fun α' hα' => ?_⟩⟩
  rw [hbr α' (by linarith [hα'.1])]
  funext e
  simp

/-! ### (5) The sizes -/

/-- (5) of the proof of `thm:polybits`: "Hence `Λ ≤ 1 + n² 3ⁿ τ`". -/
lemma Lam_le : Lam n ≤ 1 + n ^ 2 * 3 ^ n * tau n := by
  have h : ∑ k ∈ Ico 1 (n + 1), D k ≤ ∑ _k ∈ Ico 1 (n + 1), (n : ℤ) * 3 ^ n * tau n :=
    sum_le_sum fun k hk => D_le (mem_Ico.1 hk).1 (by have := (mem_Ico.1 hk).2; omega)
  rw [sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul] at h
  unfold Lam
  have : (n : ℤ) * ((n : ℤ) * 3 ^ n * tau n) = n ^ 2 * 3 ^ n * tau n := by ring
  linarith

/-- `g(S) ≤ ∑_{k∈S} K_k`, as the pair terms are nonnegative ((5): "as `g(E) ≤ ∑_{k∈E} K_k`"). -/
lemma g_le_sum_K (S : Finset (Fin n)) : g (S.map (emb n)) ≤ ∑ k ∈ S.map (emb n), K k := by
  unfold g
  have : 0 ≤ ∑ k ∈ S.map (emb n), ∑ i ∈ (S.map (emb n)).filter (· < k), d i k :=
    sum_nonneg fun _ _ => sum_nonneg fun _ hi =>
      d_nonneg (lt_of_mem_map_emb (mem_filter.1 hi).1).1 (mem_filter.1 hi).2
  linarith

/-- (5), the summands of the bound on `f(E)`: `K_k + Λ t_k ≤ (n + 2) 3ⁿ τ + (1 + n² 3ⁿ τ) τ` for
`k ∈ E`. -/
lemma summand_le (e : Fin n) :
    K (emb n e) + Lam n * t (emb n e) ≤
      (n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n := by
  have hK := K_le (n := n) (k := emb n e) (one_le_emb e) (emb_le e)
  have ht := t_le_tau (n := n) (k := emb n e) (one_le_emb e) (emb_le e)
  have ht0 := t_pos (k := emb n e) (by simp)
  have hτ := tau_pos n
  have := mul_le_mul (Lam_le (n := n)) ht ht0.le (by positivity)
  linarith

/-- (5): `n (n + 2) 3ⁿ τ + n (1 + n² 3ⁿ τ) τ ≤ (n + 2)³ 9ⁿ τ²`. -/
lemma n_mul_summand_le :
    (n : ℤ) * ((n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n) ≤
      (n + 2) ^ 3 * 9 ^ n * tau n ^ 2 := by
  have hτ := two_le_tau n
  have h3 : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  have h9 : (9 : ℤ) ^ n = 3 ^ n * 3 ^ n := by rw [← mul_pow]; norm_num
  rw [h9]
  have hAT : (0 : ℤ) ≤ 3 ^ n * tau n := by positivity
  have hAT2 : 3 ^ n * tau n ≤ 3 ^ n * tau n ^ 2 := by
    rw [sq, ← mul_assoc]
    exact le_mul_of_one_le_right hAT (by linarith)
  have hAT2' : (0 : ℤ) ≤ 3 ^ n * tau n ^ 2 := by positivity
  have e1 : (n : ℤ) * ((n + 2) * 3 ^ n * tau n) ≤ (n + 2) ^ 2 * (3 ^ n * tau n ^ 2) := by
    have h1 : (n : ℤ) * (n + 2) ≤ (n + 2) ^ 2 := by nlinarith
    calc (n : ℤ) * ((n + 2) * 3 ^ n * tau n) = (n * (n + 2)) * (3 ^ n * tau n) := by ring
      _ ≤ (n + 2) ^ 2 * (3 ^ n * tau n) := mul_le_mul_of_nonneg_right h1 hAT
      _ ≤ (n + 2) ^ 2 * (3 ^ n * tau n ^ 2) := mul_le_mul_of_nonneg_left hAT2 (by positivity)
  have e2 : (n : ℤ) * tau n ≤ (n + 2) * (3 ^ n * tau n ^ 2) := by
    have hT : tau n ≤ 3 ^ n * tau n := le_mul_of_one_le_left (by linarith) h3
    calc (n : ℤ) * tau n ≤ (n + 2) * tau n := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ (n + 2) * (3 ^ n * tau n ^ 2) := mul_le_mul_of_nonneg_left (hT.trans hAT2) (by linarith)
  have e3 : (n : ℤ) * (n ^ 2 * 3 ^ n * tau n * tau n) = n ^ 3 * (3 ^ n * tau n ^ 2) := by ring
  have e4 : (n + 2) ^ 2 + (n + 2) + (n : ℤ) ^ 3 ≤ (n + 2) ^ 3 := by nlinarith
  have e5 : 3 ^ n * tau n ^ 2 ≤ 3 ^ n * 3 ^ n * tau n ^ 2 := by
    rw [mul_assoc]
    exact le_mul_of_one_le_left hAT2' h3
  calc (n : ℤ) * ((n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n)
      = n * ((n + 2) * 3 ^ n * tau n) + n * tau n + n * (n ^ 2 * 3 ^ n * tau n * tau n) := by ring
    _ ≤ ((n + 2) ^ 2 + (n + 2) + n ^ 3) * (3 ^ n * tau n ^ 2) := by rw [e3]; linarith
    _ ≤ (n + 2) ^ 3 * (3 ^ n * tau n ^ 2) := mul_le_mul_of_nonneg_right e4 hAT2'
    _ ≤ (n + 2) ^ 3 * (3 ^ n * 3 ^ n * tau n ^ 2) := mul_le_mul_of_nonneg_left e5 (by positivity)
    _ = (n + 2) ^ 3 * (3 ^ n * 3 ^ n) * tau n ^ 2 := by ring

/-- (5): "as `g(E) ≤ ∑_{k∈E} K_k`,
`f(E) ≤ ∑_{k∈E} (K_k + Λ t_k) ≤ n(n + 2) 3ⁿ τ + n(1 + n² 3ⁿ τ) τ ≤ (n + 2)³ 9ⁿ τ²`". -/
lemma fE_le : fZ n univ ≤ (n + 2) ^ 3 * 9 ^ n * tau n ^ 2 := by
  have h1 : fZ n univ ≤ ∑ e : Fin n, (K (emb n e) + Lam n * t (emb n e)) := by
    have hg := g_le_sum_K (univ : Finset (Fin n))
    rw [sum_map] at hg
    have hm : ∑ e : Fin n, (Lam n * t (emb n e) - 1) ≤ ∑ e : Fin n, Lam n * t (emb n e) :=
      sum_le_sum fun e _ => by linarith
    unfold fZ
    rw [sum_add_distrib]
    linarith
  have h2 : ∑ e : Fin n, (K (emb n e) + Lam n * t (emb n e)) ≤
      n * ((n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n) := by
    calc ∑ e : Fin n, (K (emb n e) + Lam n * t (emb n e))
        ≤ ∑ _e : Fin n, ((n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n) :=
          sum_le_sum fun e _ => summand_le e
      _ = n * ((n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [n_mul_summand_le (n := n)]

/-- The closed form of `f` in (5):
`f(S) = ∑_{k∈S} (K_k + Λ t_k − 1) − ∑_{i,k∈S, i<k} d_i^{(k)}`, the pair weight of `i < k` being
the capacity `arcU n k i` of the arc `k → i` of the network of (6). -/
lemma fZ_eq (S : Finset (Fin n)) :
    fZ n S = ∑ e ∈ S, (K (emb n e) + Lam n * t (emb n e) - 1) -
      ∑ e ∈ S, ∑ e' ∈ S.filter (· < e), arcU n e e' := by
  have h : ∀ e ∈ S, ∑ e' ∈ S.filter (· < e), arcU n e e' =
      ∑ e' ∈ S.filter (· < e), d (emb n e') (emb n e) := fun e _ =>
    sum_congr rfl fun e' he' => by simp [arcU, (mem_filter.1 he').2]
  rw [sum_congr rfl h, fZ, g_map]
  simp only [sum_add_distrib, sum_sub_distrib]
  ring

lemma fZ_nonneg (hn : 1 ≤ n) (S : Finset (Fin n)) : 0 ≤ fZ n S := by
  have := (step1 hn).1.nonneg S
  simp only [fR] at this
  exact_mod_cast this

lemma fZ_le_fE (hn : 1 ≤ n) (S : Finset (Fin n)) : fZ n S ≤ fZ n univ := by
  have := (step1 hn).1.mono (subset_univ S)
  simp only [fR] at this
  exact_mod_cast this

lemma fE_le_bound : fZ n univ + 1 ≤ (n + 2) ^ 3 * 9 ^ n * tau n ^ 2 * 2 := by
  have h := fE_le (n := n)
  have : (1 : ℤ) ≤ (n + 2) ^ 3 * 9 ^ n * tau n ^ 2 := by
    have h1 : (1 : ℤ) ≤ (n + 2) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)])
    have h2 : (1 : ℤ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℤ) ≤ tau n ^ 2 := one_le_pow₀ (by linarith [two_le_tau n])
    have : (1 : ℤ) ≤ (n + 2) ^ 3 * 9 ^ n := by nlinarith
    nlinarith
  linarith

/-! ### The theorem -/

/-- **`thm:polybits`** (Theorem 3.10, statement `stoc-sections/06-optimal-share.tex:72-78`, proof
`stoc-sections/appC-bits.tex:226-363`). For every `n ≥ 1`, the following hold.
(i) There is an instance on `n` elements (`Fin n`) with `β = 1`, whose rewards and values of `f`
are integers of `O(n log n)` bits (at most `bound n = 2(n + 2)³ 9ⁿ τ³`, `τ = 2(2n + 2)^{n−1}`, which
has at most `20 n (⌊log₂ n⌋ + 1)` bits), whose rank function `f` has the closed form
`f(S) = ∑_{k∈S} w_k − ∑_{i,k∈S, i<k} d_{ik}` with integer weights of the same size (its evaluation
in polynomial time is not formalised), and whose best response has at least
`2^n/(1 + n(n + 1)/2) − 1` breakpoints in `(0, 1)`.
(ii) There is a network of type [ALM22] with a source, a sink, `n` further nodes and integral
capacities of `O(n log n)` bits (`u`, `u'`, at most `bound n`, and nonnegative, as the capacities of
a network are), except that the arc from the source to node `j` has capacity `a_j λ + b_j μ` for
two parameters `(λ, μ)` and positive integers `a_j, b_j` of `O(n log n)` bits (at most `bound n`),
in which every cut `{s} ∪ S` is the unique minimum cut at some point of `(0, 1)²` whose
coordinates have `O(n log n)` bits (quotients `p/r`, `q/r` of integers at most `bound n`).

The paper's steps, numbered by us (the proof has no step labels): (0) `Λ = 1 + ∑_k D_k`,
`f = g + ∑ (Λ t_e − 1)`, first part (i) for the instance `(f, t/σ, 1)` with `σ = 1/(f(E) + 1)`,
then part (ii), and until the rewards `t/σ` the instance `(f, t, 1)`; (1) `f` is a polymatroid
rank function and every `S ⊆ E` is a level set (`step1`); (2) the bound on the number `B_∞` of
breakpoints of `(f, t, 1)` in `(0, ∞)` (`step2`); (3) all breakpoints lie in `(0, f(E)]` (`step3`);
(4) the rewards `t/σ`: by the dilation `lem:ops`(b) (`Stoc.Hardness.ops_b_aux`, and
`Stoc.Exp.breakpoints_comp_div`), the breakpoints lie in
`(0, σ f(E)] = (0, f(E)/(f(E) + 1)] ⊆ (0, 1)`, and there are `B_∞` of them; (5) the sizes
(`Lam_le`, `fE_le`, `fZ_le_fE`, the closed form `fZ_eq`, `Stoc.Network.size_bound_le`);
(6) part (ii), for networks (`Stoc.Network.polybits_ii`). -/
theorem polybits (n : ℕ) (hn : 1 ≤ n) :
    (∃ (f : Finset (Fin n) → ℤ) (m : Fin n → ℤ) (w : Fin n → ℤ) (dw : Fin n → Fin n → ℤ),
      Tracing.Hyp (fun S => (f S : ℝ)) (fun e => (m e : ℝ)) (fun _ => 1) ∧
      (∀ S, 0 ≤ f S ∧ f S ≤ bound n) ∧ (∀ e, 0 < m e ∧ m e ≤ bound n) ∧
      (∀ S, f S = ∑ e ∈ S, w e - ∑ e ∈ S, ∑ e' ∈ S.filter (· < e), dw e e') ∧
      (∀ e, 0 ≤ w e ∧ w e ≤ bound n) ∧ (∀ e e', 0 ≤ dw e e' ∧ dw e e' ≤ bound n) ∧
      (breakpoints (bestResponse (fun S => (f S : ℝ)) (fun e => (m e : ℝ)) (fun _ => 1)) ∩
        Set.Ioo 0 1).Finite ∧
      (2 : ℝ) ^ n / (1 + n * (n + 1) / 2) - 1 ≤
        (breakpoints (bestResponse (fun S => (f S : ℝ)) (fun e => (m e : ℝ)) (fun _ => 1)) ∩
          Set.Ioo 0 1).ncard) ∧
    (∃ (a b : Fin n → ℤ) (u : Fin n → Fin n → ℤ) (u' : Fin n → ℤ),
      (∀ j, 0 < a j ∧ a j ≤ bound n) ∧ (∀ j, 0 < b j ∧ b j ≤ bound n) ∧
      (∀ i j, 0 ≤ u i j ∧ u i j ≤ bound n) ∧ (∀ i, 0 ≤ u' i ∧ u' i ≤ bound n) ∧
      ∀ S : Finset (Fin n), ∃ p q r : ℤ, 0 < p ∧ p < r ∧ 0 < q ∧ q < r ∧ r ≤ bound n ∧
        IsUniqueMinCut (fun j => (a j : ℝ)) (fun j => (b j : ℝ)) (fun i j => (u i j : ℝ))
          (fun i => (u' i : ℝ)) ((p : ℝ) / r) ((q : ℝ) / r) S) ∧
    (bound n).toNat.size ≤ 20 * n * (Nat.log 2 n + 1) := by
  -- (0) "Let `E = {1, …, n}`, let `t`, `g` and the other numbers be as in `prop:witness`, let
  -- `Λ := 1 + ∑_{k∈E} D_k`, and let `f(S) := g(S) + ∑_{e∈S} (Λ t_e − 1)`. We first prove part (i),
  -- that the instance with the rank function `f`, the rewards `m := t/σ` for the dilation factor
  -- `σ := 1/(f(E) + 1)` and `β := 1` has the claimed properties, and then part (ii), for
  -- networks, the setting in which Allman, Lo and McCormick pose their question. Until we pass to
  -- the rewards `t/σ`, we consider the instance `(f, t, 1)` with the rewards `t` instead."
  set σ : ℝ := 1 / (fR n univ + 1) with hσ_def
  have hfE0 : (0 : ℝ) ≤ fR n univ := (step1 hn).1.nonneg _
  have hσ : 0 < σ := one_div_pos.2 (by linarith)
  have hm : (fun e => (mZ n e : ℝ)) = fun e => tE n e / σ := by
    funext e
    simp only [mZ, tE, fR, hσ_def]
    push_cast
    field_simp
  -- (1) "We first show that `f` is a polymatroid rank function and that every `S ⊆ E` is a level
  -- set" (`step1`).
  have hrank := (step1 hn).1
  -- (2) "Next we show that the number `B_∞` of breakpoints of `(f, t, 1)` in `(0, ∞)` satisfies
  -- `2^n ≤ (B_∞ + 1)(1 + n(n + 1)/2)`" (`step2`).
  obtain ⟨hfin, hcount⟩ := step2 hn
  -- (3) "Next we show that all breakpoints lie in `(0, f(E)]`" (`step3`).
  have hIoc := (step3 hn).2
  -- (4) "Now we pass to the rewards `t/σ` and show that the instance `(f, t/σ, 1)` has at least
  -- `2^n/(1 + n(n + 1)/2) − 1` breakpoints in `(0, 1)`. By the dilation `lem:ops`(b) with
  -- `σ = 1/(f(E) + 1)`, the best response of this instance is `α ↦ x*(α/σ)`,"
  have hbr : ∀ α, 0 ≤ α → bestResponse (fR n) (fun e => (mZ n e : ℝ)) (fun _ => 1) α =
      bestResponse (fR n) (tE n) (fun _ => 1) (α / σ) := by
    rw [hm]
    exact (Hardness.ops_b_aux (fR n) (tE n) (fun _ => 1) hσ).1
  -- "and its breakpoints are the `B_∞` breakpoints of `(f, t, 1)` multiplied by `σ`."
  have hbp : breakpoints (bestResponse (fR n) (fun e => (mZ n e : ℝ)) (fun _ => 1)) =
      (fun b => σ * b) '' breakpoints (bestResponse (fR n) (tE n) (fun _ => 1)) :=
    Exp.breakpoints_comp_div _ _ hσ hbr
  -- "As those lie in `(0, f(E)]`, these lie in `(0, σ f(E)] = (0, f(E)/(f(E) + 1)] ⊆ (0, 1)`,"
  have hσf : σ * fR n univ = fR n univ / (fR n univ + 1) := by
    rw [hσ_def, one_div_mul_eq_div]
  have hIoc1 : Set.Ioc 0 (fR n univ / (fR n univ + 1)) ⊆ Set.Ioo 0 1 := fun x hx =>
    ⟨hx.1, hx.2.trans_lt ((div_lt_one (by linarith)).2 (by linarith))⟩
  have hsub01 : breakpoints (bestResponse (fR n) (fun e => (mZ n e : ℝ)) (fun _ => 1)) ⊆
      Set.Ioo 0 1 := by
    rw [hbp]
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨hb0, hbE⟩ := hIoc hb
    refine hIoc1 ⟨mul_pos hσ hb0, ?_⟩
    rw [← hσf]
    exact mul_le_mul_of_nonneg_left hbE hσ.le
  -- "and by the bound on `B_∞` shown above, `B_∞ ≥ 2^n/(1 + n(n + 1)/2) − 1`."
  have hcard : (breakpoints (bestResponse (fR n) (fun e => (mZ n e : ℝ)) (fun _ => 1)) ∩
      Set.Ioo 0 1).ncard = (breakpoints (bestResponse (fR n) (tE n) (fun _ => 1))).ncard := by
    rw [Set.inter_eq_left.2 hsub01, hbp,
      Set.ncard_image_of_injective _ (mul_right_injective₀ hσ.ne')]
  have hB : (2 : ℝ) ^ n / (1 + n * (n + 1) / 2) - 1 ≤
      ((breakpoints (bestResponse (fR n) (fun e => (mZ n e : ℝ)) (fun _ => 1)) ∩
        Set.Ioo 0 1).ncard : ℝ) := by
    rw [hcard]
    exact Exp.sub_one_le_of_two_pow_le hcount
  -- (5) "Finally, for part (i), we show that all numbers have `O(n log n)` bits and that `f` can
  -- be evaluated in polynomial time": `Λ ≤ 1 + n² 3ⁿ τ`, `f(E) ≤ (n + 2)³ 9ⁿ τ²`, every value of
  -- `f` is an integer in `[0, f(E)]`, every reward `m_e = (f(E) + 1) t_e` is an integer in
  -- `(0, (f(E) + 1) τ]`, so all these numbers are at most `2(n + 2)³ 9ⁿ τ³`, and the closed form
  -- of `f`.
  have hfE := fE_le (n := n)
  have hfEb := fE_le_bound (n := n)
  have hb2 : (n + 2) ^ 3 * 9 ^ n * tau n ^ 2 ≤ bound n := by
    unfold bound
    have : (0 : ℤ) ≤ (n + 2) ^ 3 * 9 ^ n * tau n ^ 2 := by
      have := two_le_tau n
      positivity
    nlinarith [two_le_tau n]
  have hm_le : ∀ e, 0 < mZ n e ∧ mZ n e ≤ bound n := fun e => by
    have ht := t_le_tau (n := n) (k := emb n e) (one_le_emb e) (emb_le e)
    have ht0 := t_pos (k := emb n e) (by simp)
    have hf0 := fZ_nonneg hn univ
    refine ⟨mul_pos (by linarith) ht0, ?_⟩
    calc mZ n e = (fZ n univ + 1) * t (emb n e) := rfl
      _ ≤ ((n + 2) ^ 3 * 9 ^ n * tau n ^ 2 * 2) * tau n :=
          mul_le_mul hfEb ht ht0.le (by linarith)
      _ = bound n := by unfold bound; ring
  have hw : ∀ e : Fin n, 0 ≤ K (emb n e) + Lam n * t (emb n e) - 1 ∧
      K (emb n e) + Lam n * t (emb n e) - 1 ≤ bound n := fun e => by
    have hK1 : 1 ≤ K (emb n e) := by
      have : 0 ≤ t (emb n e) * lamBar (emb n e) :=
        mul_nonneg (t_pos (by simp)).le (lamBar_nonneg _)
      unfold K
      linarith [D_nonneg (k := emb n e)]
    have hΛt : 0 ≤ Lam n * t (emb n e) :=
      mul_nonneg (by linarith [one_le_Lam (n := n)]) (t_pos (by simp)).le
    refine ⟨by linarith, ?_⟩
    have h1 := summand_le e
    have h2 := n_mul_summand_le (n := n)
    have hX : 0 ≤ (n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n := by
      have := tau_pos n
      positivity
    have h3 : (n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n ≤
        n * ((n + 2) * 3 ^ n * tau n + (1 + n ^ 2 * 3 ^ n * tau n) * tau n) :=
      le_mul_of_one_le_left hX (by exact_mod_cast hn)
    linarith
  have hdw : ∀ e e', 0 ≤ arcU n e e' ∧ arcU n e e' ≤ bound n := fun e e' => by
    unfold arcU
    split_ifs with h
    · have h1 := d_nonneg (i := emb n e') (k := emb n e) (by simp)
        (by simp only [emb_apply]; exact Nat.add_lt_add_right (Fin.lt_def.1 h) 1)
      have h2 := d_le_theta (i := emb n e') (k := emb n e) (by simp)
      have h3 := theta_le (n := n) (k := emb n e) (one_le_emb e) (emb_le e)
      have h4 : 3 ^ n * tau n ≤ (n + 2) ^ 3 * 9 ^ n * tau n ^ 2 := by
        have h9 : (9 : ℤ) ^ n = 3 ^ n * 3 ^ n := by rw [← mul_pow]; norm_num
        rw [h9]
        have : (1 : ℤ) ≤ (n + 2) ^ 3 * 3 ^ n * tau n := by
          have : (1 : ℤ) ≤ (n + 2) ^ 3 :=
            one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)])
          have : (1 : ℤ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
          nlinarith [two_le_tau n]
        nlinarith [two_le_tau n, (by positivity : (0 : ℤ) ≤ 3 ^ n)]
      exact ⟨h1, by linarith⟩
    · exact ⟨le_rfl, bound_nonneg n⟩
  refine ⟨⟨fZ n, mZ n, fun e => K (emb n e) + Lam n * t (emb n e) - 1, fun e e' => arcU n e e',
    ⟨hrank, fun _ => one_pos, fun e => (by exact_mod_cast (hm_le e).1.le : (0 : ℝ) ≤ mZ n e)⟩,
    fun S => ⟨fZ_nonneg hn S, (fZ_le_fE hn S).trans (hfE.trans hb2)⟩, hm_le, fZ_eq, hw, hdw,
    (Tracing.bp_finite ⟨hrank, fun _ => one_pos,
      fun e => (by exact_mod_cast (hm_le e).1.le : (0 : ℝ) ≤ mZ n e)⟩).inter_of_left _, hB⟩,
    ?_, size_bound_le hn⟩
  -- (6) "It remains to prove part (ii), for networks." (`Stoc.Network.polybits_ii`)
  exact polybits_ii hn

end PolyBit

end Stoc
