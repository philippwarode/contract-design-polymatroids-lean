-- stamp r8 2026-11-02
import Stoc.Subclasses.LaminarCount

/-!
# Laminar polymatroids

The STOC version, Appendix B.8 (`sec:A-subclasses`), Theorem `thm:laminar`
(`stoc-sections/appB-quadratic.tex:718-720`, notation `:722-768`, proof `:876-908`): if `(E, f)`
is laminar with a family `𝓛` of height `h`, then `B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}`; as `|𝓛| ≤ 2n − 1`,
this is `O(n²)` for fixed `h` and polynomial for `h = O(log n)` (`laminar`).

The proof follows the STOC version. The notation (`appB-quadratic.tex:722-768`,
`Stoc/Subclasses/Laminar.lean`):

*  (s1) every element `e` lies in some constraint set, since otherwise `x_e` would be unbounded on
  `P₊(f)` (`Stoc.exists_mem_of_indepPoly_eq`);
*  (s2) if `m_e = 0`, then `x*_e(α) = 0` for all `α`
  (`Stoc.bestResponse_eq_zero_of_reward_eq_zero`);
*  (s3) by `lem:supportmon`, the support changes at no more than `n` shares, which cut `(0, ∞)` into
  at most `n + 1` pinning intervals (`Stoc.pinning_intervals`);
*  (s4)-(s7) on a pinning interval `I` with support `W`: `𝓛_W`, the forest, `E_L`, `D_L` (eq:E-D),
  `π_L` and `Π_V`.

The proof (`appB-quadratic.tex:876-908`): let `I` be a pinning interval with support `W`;

1. `N_I = ∑_{L ∈ 𝓛_W} #(L) ≤ |𝓛| 3^{h−1}` (`lem:E-piececount`, `Stoc.piececount`);
2. by `lem:E-laminarformula`, on `I` the vector `x*` vanishes outside `W` and is determined on `W`
  by the functions `Π_V = max 𝓕_V`, `𝓕_V = {0} ∪ {π_L : L ⊇ V, π_L ≢ −∞}` (`Fv`, `PiUp_eq_sup'`);
  hence, near every breakpoint `α₀ ∈ I` of `x*`, some `Π_V` is not affine; if `α₀` is neither a
  vertex of a function in `𝓕_V` nor a boundary point of `{φ = ψ}` for `φ, ψ ∈ 𝓕_V`, then near `α₀`
  all functions in `𝓕_V` are affine and every difference `φ − ψ` either vanishes identically or has
  constant sign, so one of them is maximal on a whole neighborhood of `α₀` and `Π_V` is affine
  there (`affineAt_PiUp`); therefore, every breakpoint in `I` is (a) a vertex of some `π_L`, (b) a
  zero of some `π_L`, or (c) a boundary point of `{π_L = π_{L'}}` that is not a vertex of `π_L`,
  for constraint sets `L ⊊ L'` in `𝓛_W` (`breakpoints_inter_subset`);
3. there are at most `N_I` points of type (a) and, as the functions `π_L` are strictly increasing,
  at most `|𝓛|` points of type (b); for (c), fix `L ⊊ L'` and an open linear piece `O` of `π_L`; on
  `O`, the difference `π_L − π_{L'}` is convex, so its zero set in `O` either consists of at most
  two points or is an interval, and in both cases it has at most two boundary points in `O`; so the
  pair `L ⊊ L'` yields at most `2#(L)` points of type (c) (`frontier_diff_kinks_le`); as every `L`
  is contained in at most `h − 1` other constraint sets in `𝓛_W` (`card_ssuperset_le`), there are
  at most `2(h − 1)N_I` points of type (c);
4. altogether, `I` contains at most `(2h − 1)N_I + |𝓛| ≤ 2h|𝓛| 3^{h−1}` breakpoints
  (`breakpoints_inter_le`);
5. combining this with at most `n + 1` pinning intervals and `n` support changes
  (`lem:supportmon`) gives `B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}` (`laminar_breakpoints`).

The second sentence: `|𝓛| ≤ 2n − 1` (`IsLaminar.card_le`) and `3^{h−1} ≤ n^c` for
`h − 1 ≤ c log₃ n` (`pow_three_le_of_le_log`), which the STOC version asserts (D3). Also not in the
paper: a family of height `0` is empty (`eq_empty_of_height_eq_zero`).

As in Appendix B.8, `B` here counts the breakpoints in `(0, ∞)` (`Stoc.breakpoints`), which bound
the number in `(0, 1)` (`rem:subclasses`, `PolynomialClasses.lean`). The number `#(L)` is
`numPieces`, `N_I` is `∑_{L ∈ 𝓛_W} numPieces L`. The paper's `π_L ≡ −∞` is `∀ α, PiBot L α` and
`π_L ≢ −∞` is its negation (`Stoc/Subclasses/Laminar.lean`): `𝓕_V` contains the `π_L` of these
constraint sets (`goodMembers`), and the constraint sets `L, L'` of types (a)-(c) are among them.

Taken over on 2026-10-21 from `Paper/Subclasses/LaminarHeight.lean` (the long paper's
`thm:laminar-height`, whose proof the STOC version takes over) for the STOC version (`stoc.tex`);
from then on this copy follows the STOC version. Adapted on 2026-10-28 to the STOC version after
PR #88 (constraint sets `L`, `L'`, `V`, `#(L)`, and `π_L` defined by `D_L`).
-/

namespace Stoc

open Finset Filter Topology

noncomputable section

variable {E : Type*} [DecidableEq E]

/-! ### The second sentence: `|𝓛| ≤ 2n − 1` -/

/-- (Not in the paper: the second sentence of `thm:laminar` asserts it.) A laminar family of
nonempty subsets of a set `S` has at most `2|S| − 1` members. Induction on `S`: erasing an element
`e` from the members merges at most one pair `A`, `A ∪ {e}` and drops at most the member `{e}`. -/
theorem IsLaminar.card_le_of_subset {S : Finset E} :
    ∀ {𝓛 : Finset (Finset E)}, IsLaminar 𝓛 → (∀ L ∈ 𝓛, L ⊆ S) → 𝓛.card ≤ 2 * S.card - 1 := by
  induction S using Finset.induction_on with
  | empty =>
    intro 𝓛 h hS
    have : 𝓛 = ∅ := Finset.eq_empty_of_forall_notMem fun L hL => by
      obtain ⟨x, hx⟩ := h.nonempty L hL
      exact Finset.notMem_empty x (hS L hL hx)
    simp [this]
  | insert e S heS ih =>
    intro 𝓛 h hS
    -- the family on `S`
    set 𝓛' := (𝓛.image fun L => L.erase e).filter fun A => A.Nonempty
    have h𝓛' : IsLaminar 𝓛' := by
      refine ⟨fun A hA => (Finset.mem_filter.1 hA).2, fun A hA A' hA' => ?_⟩
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hA).1
      obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hA').1
      rcases h.disjoint_or_subset L hL L' hL' with hd | hs | hs
      · exact Or.inl (Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd))
      · exact Or.inr (Or.inl (Finset.erase_subset_erase _ hs))
      · exact Or.inr (Or.inr (Finset.erase_subset_erase _ hs))
    have hS' : ∀ A ∈ 𝓛', A ⊆ S := by
      intro A hA
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hA).1
      intro x hx
      rcases Finset.mem_insert.1 (hS L hL (Finset.mem_of_mem_erase hx)) with h' | h'
      · exact absurd h' (Finset.ne_of_mem_erase hx)
      · exact h'
    have hih := ih h𝓛' hS'
    -- `𝓛` splits into the members `{e}`, the members `L` with `L ∖ {e} ∈ 𝓛`, and the rest
    set Z := 𝓛.filter fun L => ¬ (L.erase e).Nonempty
    set R := 𝓛.filter fun L => (L.erase e).Nonempty
    set D2 := R.filter fun L => e ∈ L ∧ L.erase e ∈ 𝓛
    set D1 := R.filter fun L => ¬ (e ∈ L ∧ L.erase e ∈ 𝓛)
    have hsplit1 : R.card + Z.card = 𝓛.card := Finset.card_filter_add_card_filter_not _
    have hsplit2 : D2.card + D1.card = R.card := Finset.card_filter_add_card_filter_not _
    have hZ : Z.card ≤ 1 := by
      refine Finset.card_le_one.2 fun L hL L' hL' => ?_
      have h1 := Finset.mem_filter.1 hL
      have h2 := Finset.mem_filter.1 hL'
      rw [Finset.not_nonempty_iff_eq_empty, Finset.erase_eq_empty_iff] at h1 h2
      rcases h1.2 with h1' | h1'
      · exact absurd h1' (h.nonempty L h1.1).ne_empty
      rcases h2.2 with h2' | h2'
      · exact absurd h2' (h.nonempty L' h2.1).ne_empty
      rw [h1', h2']
    have hD1 : D1.card ≤ 𝓛'.card := by
      refine Finset.card_le_card_of_injOn (fun L => L.erase e) (fun L hL => ?_)
        (fun L hL L' hL' heq => ?_)
      · have hLR := Finset.mem_filter.1 (Finset.mem_filter.1 hL).1
        exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hLR.1, hLR.2⟩
      · have h1 := Finset.mem_filter.1 hL
        have h2 := Finset.mem_filter.1 hL'
        have heq' : L.erase e = L'.erase e := heq
        by_cases he : e ∈ L <;> by_cases he' : e ∈ L'
        · rw [← Finset.insert_erase he, ← Finset.insert_erase he', heq']
        · exfalso
          rw [Finset.erase_eq_of_notMem he'] at heq'
          exact h1.2 ⟨he, heq' ▸ (Finset.mem_filter.1 h2.1).1⟩
        · exfalso
          rw [Finset.erase_eq_of_notMem he] at heq'
          exact h2.2 ⟨he', heq' ▸ (Finset.mem_filter.1 h1.1).1⟩
        · rw [← Finset.erase_eq_of_notMem he, ← Finset.erase_eq_of_notMem he', heq']
    -- two members of `D2` are equal
    have hD2sub : ∀ L ∈ D2, ∀ L' ∈ D2, L ⊆ L' → L = L' := by
      intro L hL L' hL' hsub
      obtain ⟨hLR, heL, hLe⟩ := Finset.mem_filter.1 hL
      obtain ⟨hL'R, heL', hL'e⟩ := Finset.mem_filter.1 hL'
      have hL𝓛 := (Finset.mem_filter.1 hLR).1
      have hne := (Finset.mem_filter.1 hLR).2
      rcases h.disjoint_or_subset L hL𝓛 (L'.erase e) hL'e with hd | hs | hs
      · exfalso
        obtain ⟨x, hx⟩ := hne
        exact Finset.disjoint_left.1 hd (Finset.mem_of_mem_erase hx)
          (Finset.erase_subset_erase e hsub hx)
      · exact absurd (hs heL) (Finset.notMem_erase e L')
      · refine le_antisymm hsub fun x hx => ?_
        by_cases hxe : x = e
        · rw [hxe]; exact heL
        · exact hs (Finset.mem_erase.2 ⟨hxe, hx⟩)
    have hD2 : D2.card ≤ 1 := by
      refine Finset.card_le_one.2 fun L hL L' hL' => ?_
      have hL𝓛 := (Finset.mem_filter.1 (Finset.mem_filter.1 hL).1).1
      have hL'𝓛 := (Finset.mem_filter.1 (Finset.mem_filter.1 hL').1).1
      rcases h.subset_or_subset hL𝓛 hL'𝓛 (Finset.mem_filter.1 hL).2.1
        (Finset.mem_filter.1 hL').2.1 with hs | hs
      · exact hD2sub L hL L' hL' hs
      · exact (hD2sub L' hL' L hL hs).symm
    -- if `D2` or `𝓛'` is nonempty, so is `S`
    have hD2S : D2.card = 0 ∨ 1 ≤ S.card := by
      rcases D2.eq_empty_or_nonempty with h0 | ⟨L, hL⟩
      · left; rw [h0]; rfl
      · right
        obtain ⟨hLR, -, hLe⟩ := Finset.mem_filter.1 hL
        have hne := (Finset.mem_filter.1 hLR).2
        have hmem : L.erase e ∈ 𝓛' :=
          Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨L.erase e, hLe, Finset.erase_idem⟩, hne⟩
        obtain ⟨x, hx⟩ := hne
        exact Finset.card_pos.2 ⟨x, hS' _ hmem hx⟩
    have h𝓛'S : 𝓛'.card = 0 ∨ 1 ≤ S.card := by
      rcases 𝓛'.eq_empty_or_nonempty with h0 | ⟨A, hA⟩
      · left; rw [h0]; rfl
      · right
        obtain ⟨x, hx⟩ := (Finset.mem_filter.1 hA).2
        exact Finset.card_pos.2 ⟨x, hS' A hA hx⟩
    rw [Finset.card_insert_of_notMem heS]
    omega

/-- (Not in the paper: the second sentence of `thm:laminar` asserts it.) A laminar family of
nonempty subsets of `E` has at most `2n − 1` members (in `ℕ`, so that the bound also holds for
`n = 0`, where the family is empty; Section 2 assumes `n ≥ 1`, `02-preliminaries.tex:4`). -/
theorem IsLaminar.card_le [Fintype E] {𝓛 : Finset (Finset E)} (h : IsLaminar 𝓛) :
    𝓛.card ≤ 2 * Fintype.card E - 1 := by
  have := h.card_le_of_subset (S := Finset.univ) fun L _ => Finset.subset_univ L
  rwa [Finset.card_univ] at this

/-- (Not in the paper: the second sentence of `thm:laminar` asserts "polynomial for
`h = O(log n)`".) If `h − 1 ≤ c log₃ n`, then `3^{h−1} ≤ n^c`. -/
theorem pow_three_le_of_le_log {n c h : ℕ} (hn : n ≠ 0) (hh : h - 1 ≤ c * Nat.log 3 n) :
    3 ^ (h - 1) ≤ n ^ c :=
  calc 3 ^ (h - 1) ≤ 3 ^ (c * Nat.log 3 n) := Nat.pow_le_pow_right (by norm_num) hh
    _ = (3 ^ Nat.log 3 n) ^ c := by rw [mul_comm, pow_mul]
    _ ≤ n ^ c := Nat.pow_le_pow_left (Nat.pow_log_le_self 3 hn) c

omit [DecidableEq E] in
/-- (Not in the paper: the count of step (4) of the proof of `thm:laminar` takes `h ≥ 1` for
granted; for `h = 0` the family is empty.) A family of height `0` is empty: a constraint set alone
is a chain. -/
theorem eq_empty_of_height_eq_zero {𝓛 : Finset (Finset E)} (h : height 𝓛 = 0) : 𝓛 = ∅ := by
  by_contra hne
  obtain ⟨L, hL⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have := card_le_height (𝓛 := 𝓛) (C := {L}) (singleton_subset_iff.2 hL) (by
    rw [coe_singleton]
    exact Set.pairwise_singleton _ _)
  rw [card_singleton, h] at this
  exact absurd this (by norm_num)

/-! ### Affine functions near a point -/

omit [DecidableEq E] in
theorem affineAt_iff_eventually {g : ℝ → ℝ} {α : ℝ} :
    AffineAt g α ↔ ∃ a b : ℝ, ∀ᶠ α' in 𝓝 α, g α' = a + b * α' := by
  constructor
  · rintro ⟨ε, hε, a, b, h⟩
    exact ⟨a, b, Metric.eventually_nhds_iff_ball.2
      ⟨ε, hε, fun α' hα' => h α' (by rwa [Real.ball_eq_Ioo] at hα')⟩⟩
  · rintro ⟨a, b, h⟩
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 h
    exact ⟨ε, hε, a, b, fun α' hα' => hb α' (by rwa [Real.ball_eq_Ioo])⟩

omit [DecidableEq E] in
theorem affineAt_const (c α : ℝ) : AffineAt (fun _ => c) α :=
  ⟨1, one_pos, c, 0, fun _ _ => by ring⟩

/-! ### The functions `𝓕_V` -/

variable {𝓚 : Finset (Finset E)} {W : Finset E} {f : Finset E → ℝ} {m β : E → ℝ}

open Classical in
/-- The constraint sets `L` in `𝓚` with `π_L ≢ −∞`, that is, with `¬ ∀ α, PiBot L α`. -/
def goodMembers (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ) :
    Finset (Finset E) :=
  𝓚.filter fun L => ¬ ∀ α, PiBot 𝓚 W f m β L α

theorem mem_goodMembers {L : Finset E} :
    L ∈ goodMembers 𝓚 W f m β ↔ L ∈ 𝓚 ∧ ¬ ∀ α, PiBot 𝓚 W f m β L α := by
  classical
  unfold goodMembers
  exact mem_filter

/-- `𝓕_V := {0} ∪ {π_L : L ⊇ V, π_L ≢ −∞}` (`appB-quadratic.tex:881-882`), indexed by `none` (for
`0`) and by `some L` (for `π_L`), `L` a constraint set with `L ⊇ V` and `π_L ≢ −∞`. -/
def Fv (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ) (V : Finset E) :
    Finset (Option (Finset E)) :=
  insert none (((goodMembers 𝓚 W f m β).filter fun L => V ⊆ L).image some)

/-- The function in `𝓕_V` with index `i`: `0` for `none`, `π_L` for `some L`. -/
def fv (𝓚 : Finset (Finset E)) (W : Finset E) (f : Finset E → ℝ) (m β : E → ℝ)
    (i : Option (Finset E)) (α : ℝ) : ℝ :=
  i.elim 0 fun L => pressure 𝓚 W f m β L α

theorem mem_Fv {V : Finset E} {i : Option (Finset E)} :
    i ∈ Fv 𝓚 W f m β V ↔
      i = none ∨ ∃ L ∈ 𝓚, V ⊆ L ∧ (¬ ∀ α, PiBot 𝓚 W f m β L α) ∧ i = some L := by
  simp only [Fv, mem_insert, mem_image, mem_filter, mem_goodMembers]
  constructor
  · rintro (h | ⟨L, ⟨⟨hL, hg⟩, hVL⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨L, hL, hVL, hg, rfl⟩
  · rintro (h | ⟨L, hL, hVL, hg, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨L, ⟨⟨hL, hg⟩, hVL⟩, rfl⟩

/-- `Π_V = max 𝓕_V` (`appB-quadratic.tex:881-882`): `PiUp` is the maximum over `0` and the
`π_L(α) > −∞` with `L ⊇ V` (`maxPi`), and by the dichotomy of the proof of `lem:E-laminarformula`
(`Stoc.not_piBot_of_not_forall`), `π_L(α) > −∞` exactly when `π_L ≢ −∞`, that is, for the functions
of `𝓕_V`. -/
theorem PiUp_eq_sup' (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty)
    (V : Finset E) (α : ℝ) :
    PiUp 𝓚 W f m β V α =
      (Fv 𝓚 W f m β V).sup' (insert_nonempty _ _) fun i => fv 𝓚 W f m β i α := by
  apply le_antisymm
  · refine maxPi_le (le_sup'_of_le _ (mem_insert_self none _) le_rfl) fun L hL hg => ?_
    have hi : some L ∈ Fv 𝓚 W f m β V := mem_Fv.2 (Or.inr ⟨L, (mem_filter.1 hL).1,
      (mem_filter.1 hL).2, fun hall => hg (hall α), rfl⟩)
    exact le_sup'_of_le _ hi le_rfl
  · refine sup'_le _ _ fun i hi => ?_
    rcases mem_Fv.1 hi with rfl | ⟨L, hL, hVL, hg, rfl⟩
    · exact le_maxPi _ _ _
    · exact pressure_le_maxPi (mem_filter.2 ⟨hL, hVL⟩)
        (not_piBot_of_not_forall h𝓚 hβ hL (hmeet L hL) hg α) _

/-- **Step (2)** of the proof of `thm:laminar` (`appB-quadratic.tex:884-888`): "If `α₀` is neither a
vertex of a function in `𝓕_V` nor a boundary point of `{φ = ψ}` for `φ, ψ ∈ 𝓕_V`, then near `α₀`
all functions in `𝓕_V` are affine and every difference `φ − ψ` either vanishes identically or has
constant sign, so one of them is maximal on a whole neighborhood of `α₀` and `Π_V` is affine
there." (`Stoc.affineAt_sup'`) -/
theorem affineAt_PiUp (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) (hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty)
    {V : Finset E} {α₀ : ℝ} (hA : ∀ i ∈ Fv 𝓚 W f m β V, α₀ ∉ kinks (fv 𝓚 W f m β i))
    (hfr : ∀ i ∈ Fv 𝓚 W f m β V, ∀ j ∈ Fv 𝓚 W f m β V,
      α₀ ∉ frontier {α | fv 𝓚 W f m β i α = fv 𝓚 W f m β j α}) :
    AffineAt (PiUp 𝓚 W f m β V) α₀ := by
  have heq : PiUp 𝓚 W f m β V =
      fun α => (Fv 𝓚 W f m β V).sup' (insert_nonempty _ _) fun i => fv 𝓚 W f m β i α :=
    funext (PiUp_eq_sup' h𝓚 hβ hmeet V)
  rw [heq]
  refine affineAt_sup' _ (fun i hi => ?_) (fun i hi => not_not.1 (hA i hi)) hfr
  rcases mem_Fv.1 hi with rfl | ⟨L, hL, -, hg, rfl⟩
  · exact continuous_const
  · exact continuous_pressure h𝓚 hβ hL (hmeet L hL) hg

/-! ### The breakpoints in a pinning interval -/

section Pinning

variable [Fintype E]

/-- **Step (2)** of the proof of `thm:laminar` (`appB-quadratic.tex:880-891`): "Therefore, every
breakpoint in `I` is (a) a vertex of some `π_L`, (b) a zero of some `π_L`, or (c) a boundary point
of `{π_L = π_{L'}}` that is not a vertex of `π_L`, for constraint sets `L ⊊ L'` in `𝓛_W`." Here
`I` is a pinning interval with support `W`, and `π_L, π_{L'} ≢ −∞`. -/
theorem breakpoints_inter_subset (hf : IsRankFunction f) {𝓛 : Finset (Finset E)}
    (h𝓛 : IsLaminar 𝓛) (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {I : Set ℝ} (hI : IsPinningInterval f m β I)
    (hW : ∀ α ∈ I, brSupport f m β α = W) :
    breakpoints (bestResponse f m β) ∩ I ⊆
      (⋃ L ∈ goodMembers (meeting 𝓛 W) W f m β, kinks (pressure (meeting 𝓛 W) W f m β L)) ∪
      (⋃ L ∈ goodMembers (meeting 𝓛 W) W f m β, {α | pressure (meeting 𝓛 W) W f m β L α = 0}) ∪
      (⋃ p ∈ (goodMembers (meeting 𝓛 W) W f m β ×ˢ goodMembers (meeting 𝓛 W) W f m β).filter
          (fun p => p.1 ⊂ p.2),
        frontier {α | pressure (meeting 𝓛 W) W f m β p.1 α =
          pressure (meeting 𝓛 W) W f m β p.2 α} \
            kinks (pressure (meeting 𝓛 W) W f m β p.1)) := by
  set 𝓚 := meeting 𝓛 W with h𝓚def
  have h𝓚 : IsLaminar 𝓚 := h𝓛.subset (filter_subset _ _)
  have hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty := fun L hL => (mem_filter.1 hL).2
  have hcov : ∀ e ∈ W, ∃ L ∈ 𝓚, e ∈ L := fun e he => by
    obtain ⟨L, hL, heL⟩ := exists_mem_of_indepPoly_eq hf hP e
    exact ⟨L, mem_filter.2 ⟨hL, e, mem_inter.2 ⟨heL, he⟩⟩, heL⟩
  have hform := (laminarformula hf h𝓛 hP hβ hm hI hW).1
  have hIopen := ((pinning_intervals hf hβ hm).2.2.2.2.1 I hI).1
  -- (2) "… on `I` the vector `x*` vanishes outside `W` …"
  have hx0 : ∀ α ∈ I, ∀ e ∉ W, bestResponse f m β α e = 0 := fun α hα e he =>
    le_antisymm (not_lt.1 fun h => he (by rw [← hW α hα, mem_brSupport]; exact h))
      ((isBestResponse_bestResponse hf m β α).1.1 e)
  rintro α₀ ⟨⟨-, hnot⟩, hα₀I⟩
  -- (2) "By `lem:E-laminarformula`, on `I` the vector `x*` vanishes outside `W` and is
  -- determined on `W` by the functions `Π_V = max 𝓕_V`, where
  -- `𝓕_V := {0} ∪ {π_L : L ⊇ V, π_L ≢ −∞}`. Hence, near every breakpoint `α₀ ∈ I` of `x*`, some
  -- `Π_V` is not affine."
  -- Here `V = ℓ(e)` for an element `e ∈ W`.
  obtain ⟨e, he, hnaff⟩ : ∃ e ∈ W, ¬ AffineAt (PiUp 𝓚 W f m β (ell 𝓚 e)) α₀ := by
    by_contra hall
    push Not at hall
    apply hnot
    choose! a b hab using fun e he => affineAt_iff_eventually.1 (hall e he)
    have hev : ∀ᶠ α in 𝓝 α₀, α ∈ I ∧ ∀ e ∈ W, PiUp 𝓚 W f m β (ell 𝓚 e) α = a e + b e * α :=
      (show ∀ᶠ α in 𝓝 α₀, α ∈ I from hIopen.mem_nhds hα₀I).and ((eventually_all_finset W).2 hab)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    refine ⟨ε, hε, fun e => if e ∈ W then -a e / β e else 0,
      fun e => if e ∈ W then (m e - b e) / β e else 0, fun α hα => ?_⟩
    obtain ⟨hαI, hαe⟩ := hball α (by rw [Real.ball_eq_Ioo]; exact hα)
    funext e
    by_cases he : e ∈ W
    · rw [hform α hαI e he, hαe e he]
      simp only [he, ite_true]
      field_simp [(hβ e).ne']
      ring
    · rw [hx0 α hαI e he]
      simp [he]
  have hV : ell 𝓚 e ∈ 𝓚 := (isEll_ell h𝓚 (hcov e he)).1
  -- (2) "If `α₀` is neither a vertex of a function in `𝓕_V` nor a boundary point of `{φ = ψ}`
  -- for `φ, ψ ∈ 𝓕_V`, then … `Π_V` is affine there." (`affineAt_PiUp`) "Therefore, every
  -- breakpoint in `I` is (a) a vertex of some `π_L`, (b) a zero of some `π_L`, or (c) a boundary
  -- point of `{π_L = π_{L'}}` that is not a vertex of `π_L`, for constraint sets `L ⊊ L'` in
  -- `𝓛_W`."
  by_contra hout
  apply hnaff
  refine affineAt_PiUp h𝓚 hβ hmeet (fun i hi hk => ?_) (fun i hi j hj hfr => ?_)
  · -- a vertex of a function in `𝓕_V`: (a)
    rcases mem_Fv.1 hi with rfl | ⟨L, hL, -, hg, rfl⟩
    · exact hk (affineAt_const 0 α₀)
    · exact hout (Or.inl (Or.inl (Set.mem_biUnion (mem_goodMembers.2 ⟨hL, hg⟩) hk)))
  · -- a boundary point of `{φ = ψ}` for `φ, ψ ∈ 𝓕_V`: (b) or (c)
    rcases mem_Fv.1 hi with rfl | ⟨L, hL, hVL, hg, rfl⟩ <;>
      rcases mem_Fv.1 hj with rfl | ⟨L', hL', hVL', hg', rfl⟩
    · simp [fv] at hfr
    · have h0 := (isClosed_eq continuous_const
        (continuous_pressure h𝓚 hβ hL' (hmeet L' hL') hg')).frontier_subset hfr
      exact hout (Or.inl (Or.inr (Set.mem_biUnion (mem_goodMembers.2 ⟨hL', hg'⟩) h0.symm)))
    · have h0 := (isClosed_eq (continuous_pressure h𝓚 hβ hL (hmeet L hL) hg)
        continuous_const).frontier_subset hfr
      exact hout (Or.inl (Or.inr (Set.mem_biUnion (mem_goodMembers.2 ⟨hL, hg⟩) h0)))
    · by_cases hLL : L = L'
      · subst hLL
        simp [fv] at hfr
      -- the constraint sets `L, L' ⊇ V` are nested
      have hpair : ∀ {u u' : Finset E}, u ∈ goodMembers 𝓚 W f m β →
          u' ∈ goodMembers 𝓚 W f m β → u ⊂ u' →
          α₀ ∈ frontier {α | pressure 𝓚 W f m β u α = pressure 𝓚 W f m β u' α} → False := by
        intro u u' hu hu' huu' hfr'
        by_cases hk : α₀ ∈ kinks (pressure 𝓚 W f m β u)
        · exact hout (Or.inl (Or.inl (Set.mem_biUnion hu hk)))
        · exact hout (Or.inr (Set.mem_biUnion (x := (u, u'))
            (mem_filter.2 ⟨mem_product.2 ⟨hu, hu'⟩, huu'⟩) ⟨hfr', hk⟩))
      rcases h𝓚.subset_or_subset_of_subset hV hL hL' hVL hVL' with h | h
      · exact hpair (mem_goodMembers.2 ⟨hL, hg⟩) (mem_goodMembers.2 ⟨hL', hg'⟩)
          (ssubset_of_subset_of_ne h hLL) hfr
      · have hsymm : {α | fv 𝓚 W f m β (some L) α = fv 𝓚 W f m β (some L') α} =
            {α | pressure 𝓚 W f m β L' α = pressure 𝓚 W f m β L α} := by
          ext α
          exact eq_comm
        rw [hsymm] at hfr
        exact hpair (mem_goodMembers.2 ⟨hL', hg'⟩) (mem_goodMembers.2 ⟨hL, hg⟩)
          (ssubset_of_subset_of_ne h (Ne.symm hLL)) hfr

end Pinning

/-- **Step (3)**, type (c), of the proof of `thm:laminar` (`appB-quadratic.tex:894-898`): "For (c),
fix `L ⊊ L'` and an open linear piece `O` of `π_L`. On `O`, the difference `π_L − π_{L'}` is
convex, so its zero set in `O` either consists of at most two points or is an interval. In both
cases, it has at most two boundary points in `O`. So the pair `L ⊊ L'` yields at most `2#(L)`
points of type (c)." Here with `π_L, π_{L'} ≢ −∞`: at most `2#(L)` boundary points of
`{π_L = π_{L'}}` are not vertices of `π_L`, as such a point lies in an open linear piece of `π_L`,
and there are `#(L)` of them. -/
theorem frontier_diff_kinks_le (h𝓚 : IsLaminar 𝓚) (hβ : ∀ e, 0 < β e) {L L' : Finset E}
    (hL : L ∈ 𝓚) (hLW : (L ∩ W).Nonempty) (hgood : ¬ ∀ α, PiBot 𝓚 W f m β L α) (hL' : L' ∈ 𝓚)
    (hL'W : (L' ∩ W).Nonempty) (hgood' : ¬ ∀ α, PiBot 𝓚 W f m β L' α) :
    (frontier {α | pressure 𝓚 W f m β L α = pressure 𝓚 W f m β L' α} \
        kinks (pressure 𝓚 W f m β L)).Finite ∧
      (frontier {α | pressure 𝓚 W f m β L α = pressure 𝓚 W f m β L' α} \
        kinks (pressure 𝓚 W f m β L)).ncard ≤ 2 * numPieces 𝓚 W f m β L := by
  set πL := pressure 𝓚 W f m β L
  set πL' := pressure 𝓚 W f m β L'
  set Fr := frontier {α | πL α = πL' α}
  have hK := kinks_pressure_finite h𝓚 hβ hL hLW hgood
  have hπL : Continuous πL := continuous_pressure h𝓚 hβ hL hLW hgood
  have hπL' : Continuous πL' := continuous_pressure h𝓚 hβ hL' hL'W hgood'
  have hconc : ConcaveOn ℝ Set.univ πL' := concaveOn_pressure h𝓚 hβ hL' hL'W hgood'
  have hclosed : Fr ⊆ {α | πL α = πL' α} := (isClosed_eq hπL hπL').frontier_subset
  -- (3) "For (c), fix `L ⊊ L'` and an open linear piece `O` of `π_L`."
  have hO : ∀ O ∈ openPieces πL, (Fr ∩ O).Finite ∧ (Fr ∩ O).ncard ≤ 2 := by
    intro O hO
    obtain ⟨c, d, hcd⟩ := exists_affine_of_mem_openPieces hK hO
    replace hcd : ∀ α ∈ O, πL α = c + d * α := hcd
    have hOc : O.OrdConnected := ordConnected_of_mem_openPieces hO
    -- (3) "On `O`, the difference `π_L − π_{L'}` is convex, …"
    have hD : ConvexOn ℝ O fun α => πL α - πL' α := by
      refine ⟨hOc.convex, fun x hx y hy a b ha hb hab => ?_⟩
      have hxy : a • x + b • y ∈ O := hOc.convex hx hy ha hb hab
      have hφ := hconc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      simp only [smul_eq_mul] at hxy hφ ⊢
      rw [hcd _ hxy, hcd x hx, hcd y hy]
      have heq : c + d * (a * x + b * y) = a * (c + d * x) + b * (c + d * y) := by
        linear_combination (-c) * hab
      have e1 : a * (c + d * x - πL' x) + b * (c + d * y - πL' y) =
          (a * (c + d * x) + b * (c + d * y)) - (a * πL' x + b * πL' y) := by ring
      linarith
    -- (3) "… so its zero set in `O` either consists of at most two points or is an interval."
    set Z := {x ∈ O | πL x - πL' x = 0}
    have hFrZ : Fr ∩ O ⊆ Z := fun α hα => ⟨hα.2, sub_eq_zero.2 (hclosed hα.1)⟩
    rcases zeroSet_finite_or_ordConnected hD with ⟨hZfin, hZcard⟩ | hZc
    · exact ⟨hZfin.subset hFrZ, (Set.ncard_le_ncard hFrZ hZfin).trans hZcard⟩
    · -- (3) "In both cases, it has at most two boundary points in `O`."
      refine finite_ncard_diff_interior_le_two hZc fun α hα => ⟨hFrZ hα, fun hint => ?_⟩
      have hsub : Z ⊆ {α | πL α = πL' α} := fun x hx => sub_eq_zero.1 hx.2
      exact hα.1.2 (interior_mono hsub hint)
  -- a boundary point that is not a vertex of `π_L` lies in an open linear piece of `π_L`
  have hsub : Fr \ kinks πL ⊆ ⋃ O ∈ openPieces πL, Fr ∩ O := fun α hα =>
    Set.mem_biUnion (mem_openPieces hα.2) ⟨hα.1, mem_connectedComponentIn hα.2⟩
  obtain ⟨hfin, hcard⟩ := finite_ncard_biUnion_set_le (openPieces_finite_ncard hK).1
    (fun O => Fr ∩ O) 2 hO
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans (hcard.trans (le_of_eq ?_))⟩
  -- (3) "So the pair `L ⊊ L'` yields at most `2#(L)` points of type (c)."
  -- There are `#(L)` open linear pieces.
  rw [(openPieces_finite_ncard hK).2, numPieces_eq h𝓚 hβ hL hLW hgood]

/-- **Step (3)** (`appB-quadratic.tex:899-901`): every constraint set in `𝓛_W ⊆ 𝓛` is contained in
at most `h − 1` other constraint sets in `𝓛_W`, as it and the constraint sets containing it form a
chain (not in the paper: the proof states it without proof). -/
theorem card_ssuperset_le (h𝓚 : IsLaminar 𝓚) {𝓛 : Finset (Finset E)} (h𝓚𝓛 : 𝓚 ⊆ 𝓛)
    {L : Finset E} (hL : L ∈ 𝓚) : (𝓚.filter fun u => L ⊂ u).card ≤ height 𝓛 - 1 := by
  obtain ⟨e, he⟩ := h𝓚.nonempty L hL
  set C := insert L (𝓚.filter fun u => L ⊂ u)
  have hmem : ∀ u ∈ C, u ∈ 𝓚 ∧ L ⊆ u := by
    intro u hu
    rcases mem_insert.1 hu with rfl | hu
    · exact ⟨hL, Subset.refl _⟩
    · exact ⟨(mem_filter.1 hu).1, (mem_filter.1 hu).2.subset⟩
  have hchain : IsChain (· ⊆ ·) (C : Set (Finset E)) := by
    intro u hu u' hu' _
    obtain ⟨hu𝓚, hLu⟩ := hmem u hu
    obtain ⟨hu'𝓚, hLu'⟩ := hmem u' hu'
    exact h𝓚.subset_or_subset hu𝓚 hu'𝓚 (hLu he) (hLu' he)
  have hcard := card_le_height (fun u hu => h𝓚𝓛 (hmem u hu).1) hchain
  have hnot : L ∉ 𝓚.filter fun u => L ⊂ u := fun h => ssubset_irrefl L (mem_filter.1 h).2
  rw [card_insert_of_notMem hnot] at hcard
  omega

section Pinning

variable [Fintype E]

/-- **Steps (1), (3) and (4)** of the proof of `thm:laminar` (`appB-quadratic.tex:877-904`): a
pinning interval `I` contains at most `(2h − 1)N_I + |𝓛| ≤ 2h|𝓛| 3^{h−1}` breakpoints, where
`N_I = ∑_{L ∈ 𝓛_W} #(L) ≤ |𝓛| 3^{h−1}` (`lem:E-piececount`): at most `N_I` points of type (a), at
most `|𝓛|` of type (b), as the functions `π_L` are strictly increasing, and at most `2(h − 1)N_I` of
type (c). -/
theorem breakpoints_inter_le (hf : IsRankFunction f) {𝓛 : Finset (Finset E)} (h𝓛 : IsLaminar 𝓛)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) {I : Set ℝ} (hI : IsPinningInterval f m β I)
    (hW : ∀ α ∈ I, brSupport f m β α = W) :
    (breakpoints (bestResponse f m β) ∩ I).Finite ∧
      (breakpoints (bestResponse f m β) ∩ I).ncard ≤
        2 * height 𝓛 * 𝓛.card * 3 ^ (height 𝓛 - 1) := by
  classical
  set 𝓚 := meeting 𝓛 W with h𝓚def
  have h𝓚 : IsLaminar 𝓚 := h𝓛.subset (filter_subset _ _)
  have h𝓚𝓛 : 𝓚 ⊆ 𝓛 := filter_subset _ _
  have hmeet : ∀ L ∈ 𝓚, (L ∩ W).Nonempty := fun L hL => (mem_filter.1 hL).2
  set G := goodMembers 𝓚 W f m β
  have hG : ∀ L ∈ G, L ∈ 𝓚 ∧ ¬ ∀ α, PiBot 𝓚 W f m β L α := fun L hL => mem_goodMembers.1 hL
  set N := ∑ L ∈ 𝓚, numPieces 𝓚 W f m β L
  -- (1) "Let `I` be a pinning interval with support `W`, and let
  -- `N_I := ∑_{L∈𝓛_W} #(L) ≤ |𝓛| 3^{h−1}` (`lem:E-piececount`)."
  -- `N` is `N_I`; the sum over the `L ∈ 𝓛_W` with `π_L ≢ −∞` is at most `N`.
  have hN : N ≤ 𝓛.card * 3 ^ (height 𝓛 - 1) := (piececount hf h𝓛 hP hβ hm hI hW).2
  have hNG : ∑ L ∈ G, numPieces 𝓚 W f m β L ≤ N :=
    sum_le_sum_of_subset fun L hL => (hG L hL).1
  have hprop := (laminarformula hf h𝓛 hP hβ hm hI hW).2
  -- (2) "Therefore, every breakpoint in `I` is (a) a vertex of some `π_L`, (b) a zero of some
  -- `π_L`, or (c) a boundary point of `{π_L = π_{L'}}` that is not a vertex of `π_L`, for
  -- constraint sets `L ⊊ L'` in `𝓛_W`." (`breakpoints_inter_subset`)
  set Pr := (G ×ˢ G).filter fun p : Finset E × Finset E => p.1 ⊂ p.2
  set A := ⋃ L ∈ G, kinks (pressure 𝓚 W f m β L)
  set B := ⋃ L ∈ G, {α | pressure 𝓚 W f m β L α = 0}
  set C := ⋃ p ∈ Pr, frontier {α | pressure 𝓚 W f m β p.1 α = pressure 𝓚 W f m β p.2 α} \
    kinks (pressure 𝓚 W f m β p.1)
  have hsub : breakpoints (bestResponse f m β) ∩ I ⊆ A ∪ B ∪ C :=
    breakpoints_inter_subset hf h𝓛 hP hβ hm hI hW
  -- (3) "There are at most `N_I` points of type (a) …"
  obtain ⟨hAfin, hAcard⟩ : A.Finite ∧ A.ncard ≤ ∑ L ∈ G, numPieces 𝓚 W f m β L :=
    finite_ncard_biUnion_le G (fun L => kinks (pressure 𝓚 W f m β L))
    (fun L => numPieces 𝓚 W f m β L) fun L hL => by
      obtain ⟨hL𝓚, hg⟩ := hG L hL
      refine ⟨kinks_pressure_finite h𝓚 hβ hL𝓚 (hmeet L hL𝓚) hg, ?_⟩
      rw [numPieces_eq h𝓚 hβ hL𝓚 (hmeet L hL𝓚) hg]
      omega
  -- (3) "… and, as the functions `π_L` are strictly increasing, at most `|𝓛|` points of type
  -- (b)."
  obtain ⟨hBfin, hBcard⟩ : B.Finite ∧ B.ncard ≤ ∑ _L ∈ G, 1 :=
    finite_ncard_biUnion_le G (fun L => {α | pressure 𝓚 W f m β L α = 0}) (fun _ => 1)
    fun L hL => by
      obtain ⟨hL𝓚, hg⟩ := hG L hL
      have hmono := (hprop L hL𝓚 hg).2.2.2
      have hsub : {α | pressure 𝓚 W f m β L α = 0}.Subsingleton := fun a ha b hb =>
        hmono.injective (ha.trans hb.symm)
      exact ⟨hsub.finite, (Set.ncard_le_one hsub.finite).2 fun a ha b hb => hsub ha hb⟩
  -- (3) "For (c), fix `L ⊊ L'` and an open linear piece `O` of `π_L`." … "So the pair `L ⊊ L'`
  -- yields at most `2#(L)` points of type (c)." (`frontier_diff_kinks_le`)
  obtain ⟨hCfin, hCcard⟩ : C.Finite ∧ C.ncard ≤ ∑ p ∈ Pr, 2 * numPieces 𝓚 W f m β p.1 :=
    finite_ncard_biUnion_le Pr
    (fun p => frontier {α | pressure 𝓚 W f m β p.1 α = pressure 𝓚 W f m β p.2 α} \
      kinks (pressure 𝓚 W f m β p.1)) (fun p => 2 * numPieces 𝓚 W f m β p.1) fun p hp => by
      obtain ⟨hp1, hp2⟩ := mem_product.1 (mem_filter.1 hp).1
      exact frontier_diff_kinks_le h𝓚 hβ (hG _ hp1).1 (hmeet _ (hG _ hp1).1) (hG _ hp1).2
        (hG _ hp2).1 (hmeet _ (hG _ hp2).1) (hG _ hp2).2
  -- (3) "As every `L` is contained in at most `h − 1` other constraint sets in `𝓛_W`, there are
  -- at most `2(h − 1)N_I` points of type (c)."
  have hPr : ∑ p ∈ Pr, 2 * numPieces 𝓚 W f m β p.1 ≤ 2 * (height 𝓛 - 1) * N := by
    have hsplit : ∑ p ∈ Pr, 2 * numPieces 𝓚 W f m β p.1 =
        ∑ L ∈ G, (G.filter fun L' => L ⊂ L').card * (2 * numPieces 𝓚 W f m β L) := by
      rw [sum_filter, sum_product]
      refine sum_congr rfl fun L _ => ?_
      rw [← sum_filter]
      dsimp only
      rw [sum_const, smul_eq_mul]
    rw [hsplit]
    calc ∑ L ∈ G, (G.filter fun L' => L ⊂ L').card * (2 * numPieces 𝓚 W f m β L)
        ≤ ∑ L ∈ G, (height 𝓛 - 1) * (2 * numPieces 𝓚 W f m β L) := by
          refine sum_le_sum fun L hL => Nat.mul_le_mul_right _ ?_
          exact (card_le_card (filter_subset_filter _ fun u hu => (hG u hu).1)).trans
            (card_ssuperset_le h𝓚 h𝓚𝓛 (hG L hL).1)
      _ = 2 * (height 𝓛 - 1) * ∑ L ∈ G, numPieces 𝓚 W f m β L := by
          rw [mul_sum]
          exact sum_congr rfl fun L _ => by ring
      _ ≤ 2 * (height 𝓛 - 1) * N := Nat.mul_le_mul_left _ hNG
  -- (4) "Altogether, `I` contains at most `(2h − 1)N_I + |𝓛| ≤ 2h|𝓛| 3^{h−1}` breakpoints."
  have hUfin := (hAfin.union hBfin).union hCfin
  refine ⟨hUfin.subset hsub, (Set.ncard_le_ncard hsub hUfin).trans ?_⟩
  have hU1 := Set.ncard_union_le (A ∪ B) C
  have hU2 := Set.ncard_union_le A B
  have hGcard : G.card ≤ 𝓛.card := (card_le_card fun L hL => (hG L hL).1).trans (card_le_card h𝓚𝓛)
  simp only [sum_const, smul_eq_mul, mul_one] at hBcard
  rcases Nat.eq_zero_or_pos (height 𝓛) with h0 | hpos
  · have h𝓛e := eq_empty_of_height_eq_zero h0
    have hNe : N = 0 := by
      have : 𝓚 = ∅ := by rw [h𝓚def, meeting, h𝓛e, filter_empty]
      simp only [N, this, sum_empty]
    rw [h𝓛e, card_empty] at hGcard
    rw [h0, Nat.zero_sub, mul_zero, zero_mul] at hPr
    rw [h0, mul_zero, zero_mul, zero_mul]
    omega
  · set X := 𝓛.card * 3 ^ (height 𝓛 - 1)
    have hX : 𝓛.card ≤ X := Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
    have h3 : 2 * (height 𝓛 - 1) * N ≤ 2 * (height 𝓛 - 1) * X := Nat.mul_le_mul_left _ hN
    have h4 : 2 * height 𝓛 * 𝓛.card * 3 ^ (height 𝓛 - 1) = 2 * (height 𝓛 - 1) * X + 2 * X := by
      obtain ⟨k, hk⟩ : ∃ k, height 𝓛 = k + 1 := ⟨height 𝓛 - 1, by omega⟩
      simp only [X, hk, Nat.add_sub_cancel]
      ring
    omega

/-- **`thm:laminar`**, first sentence, with step (5) of its proof (`appB-quadratic.tex:905-907`):
"Combining this with at most `n + 1` pinning intervals and `n` support changes (`lem:supportmon`)
gives `B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}`." The pinning intervals are those of (s3). -/
theorem laminar_breakpoints (hf : IsRankFunction f) {𝓛 : Finset (Finset E)} (h𝓛 : IsLaminar 𝓛)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) :
    (breakpoints (bestResponse f m β)).Finite ∧
      (breakpoints (bestResponse f m β)).ncard ≤
        Fintype.card E + 2 * height 𝓛 * (Fintype.card E + 1) * 𝓛.card * 3 ^ (height 𝓛 - 1) := by
  obtain ⟨hTfin, hTcard, hIfin, hIcard, hI, hcover⟩ := pinning_intervals hf hβ hm
  set C := 2 * height 𝓛 * 𝓛.card * 3 ^ (height 𝓛 - 1)
  set bp := breakpoints (bestResponse f m β)
  -- (5) "Combining this with at most `n + 1` pinning intervals and `n` support changes
  -- (`lem:supportmon`) gives `B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}`."
  -- First, at most `2h|𝓛| 3^{h−1}` breakpoints in each pinning interval (step (4)),
  have hper : ∀ I ∈ {I | IsPinningInterval f m β I}, (bp ∩ I).Finite ∧ (bp ∩ I).ncard ≤ C := by
    intro I hIp
    obtain ⟨-, ⟨α₁, hα₁⟩, -, hconst⟩ := hI I hIp
    exact breakpoints_inter_le hf h𝓛 hP hβ hm hIp (W := brSupport f m β α₁)
      fun α hα => hconst α hα α₁ hα₁
  obtain ⟨hUfin, hUcard⟩ := finite_ncard_biUnion_set_le hIfin (fun I => bp ∩ I) C hper
  -- then at most `n + 1` pinning intervals and `n` support changes (`pinning_intervals`); every
  -- breakpoint is a support change or lies in a pinning interval
  have hsub : bp ⊆ supportChanges f m β ∪ ⋃ I ∈ {I | IsPinningInterval f m β I}, bp ∩ I := by
    intro α hα
    rcases hcover α hα.1 with h | ⟨I, hIp, hαI⟩
    · exact Or.inl h
    · exact Or.inr (Set.mem_biUnion hIp ⟨hα, hαI⟩)
  have hfin := hTfin.union hUfin
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans
    ((Set.ncard_union_le _ _).trans ?_)⟩
  have h1 : C * {I | IsPinningInterval f m β I}.ncard ≤ C * (Fintype.card E + 1) :=
    Nat.mul_le_mul_left _ hIcard
  have h2 : C * (Fintype.card E + 1) =
      2 * height 𝓛 * (Fintype.card E + 1) * 𝓛.card * 3 ^ (height 𝓛 - 1) := by
    simp only [C]
    ring
  omega

/-- **`thm:laminar`** (Theorem B.19, `stoc-sections/appB-quadratic.tex:718-720`, notation
`:722-768`, proof `:876-908`): if `(E, f)` is laminar with a family `𝓛` of height `h`, then
`B ≤ n + 2h(n + 1)|𝓛| 3^{h−1}` (`B` counting the breakpoints in `(0, ∞)`). As `|𝓛| ≤ 2n − 1`, this
is `O(n²)` for fixed `h`: `B ≤ n + 2h(n + 1)(2n − 1) 3^{h−1}`, and polynomial for `h = O(log n)`:
if `h − 1 ≤ c log₃ n`, then `B ≤ n + 2h(n + 1)(2n − 1) n^c`. The proof's steps: (s1)-(s7) and
(1)-(5), see the module docstring; the first sentence is `laminar_breakpoints`. -/
theorem laminar (hf : IsRankFunction f) {𝓛 : Finset (Finset E)} (h𝓛 : IsLaminar 𝓛)
    (hP : indepPoly f = {x | (∀ e, 0 ≤ x e) ∧ ∀ L ∈ 𝓛, ∑ e ∈ L, x e ≤ f L})
    (hβ : ∀ e, 0 < β e) (hm : ∀ e, 0 ≤ m e) :
    (breakpoints (bestResponse f m β)).Finite ∧
      (breakpoints (bestResponse f m β)).ncard ≤
        Fintype.card E + 2 * height 𝓛 * (Fintype.card E + 1) * 𝓛.card * 3 ^ (height 𝓛 - 1) ∧
      𝓛.card ≤ 2 * Fintype.card E - 1 ∧
      (breakpoints (bestResponse f m β)).ncard ≤ Fintype.card E +
        2 * height 𝓛 * (Fintype.card E + 1) * (2 * Fintype.card E - 1) * 3 ^ (height 𝓛 - 1) ∧
      ∀ c : ℕ, Fintype.card E ≠ 0 → height 𝓛 - 1 ≤ c * Nat.log 3 (Fintype.card E) →
        (breakpoints (bestResponse f m β)).ncard ≤ Fintype.card E +
          2 * height 𝓛 * (Fintype.card E + 1) * (2 * Fintype.card E - 1) * Fintype.card E ^ c := by
  obtain ⟨hfin, hB⟩ := laminar_breakpoints hf h𝓛 hP hβ hm
  have hL := h𝓛.card_le
  have hB' : (breakpoints (bestResponse f m β)).ncard ≤ Fintype.card E +
      2 * height 𝓛 * (Fintype.card E + 1) * (2 * Fintype.card E - 1) * 3 ^ (height 𝓛 - 1) :=
    hB.trans (by gcongr)
  refine ⟨hfin, hB, hL, hB', fun c hn hh => hB'.trans ?_⟩
  have := pow_three_le_of_le_log hn hh
  gcongr

end Pinning

end

end Stoc
