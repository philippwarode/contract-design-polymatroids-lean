-- stamp r6 2026-11-02
import ContractDesignPolymatroids.OptimalShare.Kinks

/-!
# Pieces of functions on the real line

Facts on the real line that Appendix B.8 (`sec:A-subclasses`) of the STOC version uses without
proof; all of them are "not in the paper" (D3):

*  The connected components of `S ∖ K`, for an interval `S` and a finite set `K` of reals, are told
  apart by the number of points of `K` below them (`connectedComponentIn_eq_iff`), so there are at
  most `|K| + 1` of them (`components_finite_ncard_le`), and exactly `|K| + 1` for `S = ℝ`
  (`ncard_components_compl`). This gives the "at most `n + 1` open intervals" between the support
  changes in the setup of `thm:laminar` (`stoc-sections/appB-quadratic.tex:727-730`) and the count
  of the linear pieces of the functions `π_L` in `lem:E-piececount` (`appB-quadratic.tex:835-874`).
*  The open linear pieces of a function `g` (`openPieces`: the connected components of the set of
  points near which `g` is affine) and its linear pieces (`linPieces`: their closures, as
  Section 3 defines the pieces of `x*`). If `g` is continuous and has finitely many kinks, it has
  `|kinks g| + 1` open linear pieces and as many linear pieces (`openPieces_finite_ncard`,
  `linPieces_finite_ncard`), so its graph has `#pieces − 1` vertices; every real lies in a linear
  piece (`exists_mem_linPieces`), and `g` is affine on each piece
  (`exists_affine_of_mem_openPieces`, `exists_affine_of_mem_linPieces`).
*  A minimum of finitely many affine functions is concave, piecewise linear (finitely many kinks)
  and, if all slopes are positive, strictly increasing (`concaveOn_inf'`, `kinks_inf'_finite`,
  `strictMono_inf'`; step (4) of the proof of `lem:E-laminarformula`, `appB-quadratic.tex:785-788`).
*  A point of an interval `S` that is not an interior point of `S` is its least or its greatest
  element, so there are at most two such points (`finite_ncard_diff_interior_le_two`; the boundary
  points of the zero sets in step (4) of the proof of `lem:E-piececount` and in step (3)(c) of the
  proof of `thm:laminar`).
*  The zero set of a convex function on an interval consists of at most two points or is an
  interval (`zeroSet_finite_or_ordConnected`; step (3)(c) of the proof of `thm:laminar`,
  `appB-quadratic.tex:895-898`), and so does that of a concave function
  (`zeroSet_finite_or_ordConnected_of_concaveOn`; step (4) of the proof of `lem:E-piececount`,
  `appB-quadratic.tex:860-862`).
-/

namespace Stoc

open Set Filter Topology

noncomputable section

/-! ### Components of the complement of a finite set -/

/-- The connected components of a set `F ⊆ ℝ`. -/
def components (F : Set ℝ) : Set (Set ℝ) := {C | ∃ α ∈ F, C = connectedComponentIn F α}

/-- The number of points of `K` below `α`. -/
def numBelow (K : Finset ℝ) (α : ℝ) : ℕ := (K.filter (· < α)).card

theorem numBelow_le_card (K : Finset ℝ) (α : ℝ) : numBelow K α ≤ K.card :=
  Finset.card_filter_le _ _

theorem numBelow_mono (K : Finset ℝ) : Monotone (numBelow K) := by
  intro a b hab
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans_le hab⟩

/-- A point of `K` in `[α, α')` makes the number of points of `K` below `α'` larger. -/
theorem numBelow_lt {K : Finset ℝ} {α α' k : ℝ} (hk : k ∈ K) (h1 : α ≤ k) (h2 : k < α') :
    numBelow K α < numBelow K α' := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset fun x hx => ?_).2 ⟨k, ?_, ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.trans_le (h1.trans h2.le)⟩
  · simp [hk, h2]
  · simp [not_lt.2 h1]

/-- (Not in the paper: a step of the counts of intervals that the STOC version uses without proof,
`components_finite_ncard_le` and `ncard_components_compl`.) Two points of `S ∖ K`, for an interval
`S`, lie in the same connected component of `S ∖ K` exactly when the same number of points of `K`
lie below them. -/
theorem connectedComponentIn_eq_iff {S : Set ℝ} (hS : S.OrdConnected) {K : Finset ℝ} {α α' : ℝ}
    (hα : α ∈ S \ ↑K) (hα' : α' ∈ S \ ↑K) :
    connectedComponentIn (S \ ↑K) α = connectedComponentIn (S \ ↑K) α' ↔
      numBelow K α = numBelow K α' := by
  have key : ∀ {a b : ℝ}, a ∈ S \ ↑K → b ∈ S \ ↑K → a ≤ b →
      (connectedComponentIn (S \ ↑K) a = connectedComponentIn (S \ ↑K) b ↔
        numBelow K a = numBelow K b) := by
    intro a b ha hb hab
    constructor
    · intro h
      -- the component is an interval in `S ∖ K` that contains `a` and `b`
      have hbC : b ∈ connectedComponentIn (S \ ↑K) a := h ▸ mem_connectedComponentIn hb
      have hIcc : Icc a b ⊆ S \ ↑K :=
        (isPreconnected_connectedComponentIn.Icc_subset (mem_connectedComponentIn ha) hbC).trans
          (connectedComponentIn_subset _ _)
      refine le_antisymm (numBelow_mono K hab) (le_of_not_gt fun hlt => ?_)
      obtain ⟨k, hk, hka⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_filter, not_and, not_lt] at hk hka
      exact (hIcc ⟨hka hk.1, hk.2.le⟩).2 hk.1
    · intro h
      have hIcc : Icc a b ⊆ S \ ↑K := by
        intro x hx
        refine ⟨hS.out ha.1 hb.1 hx, fun hxK => ?_⟩
        rcases hx.2.lt_or_eq with hxb | rfl
        · exact (numBelow_lt hxK hx.1 hxb).ne h
        · exact hb.2 hxK
      have := isPreconnected_Icc.subset_connectedComponentIn (left_mem_Icc.2 hab) hIcc
      exact connectedComponentIn_eq (this (right_mem_Icc.2 hab))
  rcases le_total α α' with h | h
  · exact key hα hα' h
  · rw [eq_comm, @eq_comm _ (numBelow K α)]
    exact key hα' hα h

/-- A point of each component. -/
private def pt (C : Set ℝ) : ℝ := by classical exact if h : C.Nonempty then h.some else 0

private theorem pt_spec {F : Set ℝ} {C : Set ℝ} (hC : C ∈ components F) :
    pt C ∈ F ∧ connectedComponentIn F (pt C) = C := by
  obtain ⟨α, hα, rfl⟩ := hC
  have hne : (connectedComponentIn F α).Nonempty := ⟨α, mem_connectedComponentIn hα⟩
  have hmem : pt (connectedComponentIn F α) ∈ connectedComponentIn F α := by
    simp only [pt, hne, dite_true]
    exact hne.some_mem
  exact ⟨connectedComponentIn_subset _ _ hmem, (connectedComponentIn_eq hmem).symm⟩

/-- (Not in the paper: the setup of `thm:laminar` uses without proof that the at most `n` shares at
which the support changes leave at most `n + 1` open intervals.) For an interval `S` and a finite
set `K`, `S ∖ K` has at most `|K| + 1` connected components. -/
theorem components_finite_ncard_le {S : Set ℝ} (hS : S.OrdConnected) (K : Finset ℝ) :
    (components (S \ ↑K)).Finite ∧ (components (S \ ↑K)).ncard ≤ K.card + 1 := by
  have hmaps : ∀ C ∈ components (S \ ↑K),
      numBelow K (pt C) ∈ ((Finset.range (K.card + 1) : Finset ℕ) : Set ℕ) := fun C _ => by
    simp only [Finset.coe_range, mem_Iio]
    exact Nat.lt_succ_of_le (numBelow_le_card K _)
  have hinj : InjOn (fun C => numBelow K (pt C)) (components (S \ ↑K)) := by
    intro C hC C' hC' heq
    rw [← (pt_spec hC).2, ← (pt_spec hC').2]
    exact (connectedComponentIn_eq_iff hS (pt_spec hC).1 (pt_spec hC').1).2 heq
  have hfin : (components (S \ ↑K)).Finite := by
    refine Set.Finite.of_finite_image (f := fun C => numBelow K (pt C)) ?_ hinj
    refine (Finset.finite_toSet (Finset.range (K.card + 1))).subset ?_
    rintro _ ⟨C, hC, rfl⟩
    exact hmaps C hC
  refine ⟨hfin, ?_⟩
  calc (components (S \ ↑K)).ncard
      ≤ ((Finset.range (K.card + 1) : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
    _ = K.card + 1 := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- (Not in the paper: a step of `openPieces_finite_ncard`, the count of the linear pieces that
`lem:E-piececount` uses without proof.) The complement of a finite set `K` of reals has exactly
`|K| + 1` connected components: below `K` no point of `K` lies, and right of `k ∈ K` (up to the
next point of `K`) the points of `K` up to `k`. -/
theorem ncard_components_compl (K : Finset ℝ) :
    (components (↑K : Set ℝ)ᶜ).ncard = K.card + 1 := by
  classical
  have hc : (↑K : Set ℝ)ᶜ = univ \ ↑K := compl_eq_univ_sdiff _
  obtain ⟨hfin, hle⟩ := components_finite_ncard_le ordConnected_univ K
  rw [← hc] at hfin hle
  refine le_antisymm hle ?_
  -- a point below `K`
  obtain ⟨α₀, hα₀K, hα₀⟩ : ∃ α₀, α₀ ∉ (↑K : Set ℝ) ∧ numBelow K α₀ = 0 := by
    by_cases hK : K.Nonempty
    · refine ⟨K.min' hK - 1, fun h => ?_, ?_⟩
      · have := K.min'_le _ h
        linarith
      · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun k hk hlt => ?_)
        have := K.min'_le k hk
        linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hK
      subst hK
      exact ⟨0, by simp, rfl⟩
  -- a point right of each `k ∈ K`
  have hright : ∀ k ∈ K, ∃ α, α ∉ (↑K : Set ℝ) ∧ numBelow K α = numBelow K k + 1 := by
    intro k hk
    obtain ⟨α, hkα, hαK'⟩ : ∃ α, k < α ∧ ∀ k' ∈ K, k < k' → α < k' := by
      by_cases hU : (K.filter (k < ·)).Nonempty
      · set u := (K.filter (k < ·)).min' hU
        have hku : k < u := (Finset.mem_filter.1 (Finset.min'_mem _ hU)).2
        refine ⟨(k + u) / 2, by linarith, fun k' hk' hgt => ?_⟩
        have := Finset.min'_le _ k' (Finset.mem_filter.2 ⟨hk', hgt⟩)
        linarith
      · exact ⟨k + 1, by linarith, fun k' hk' hgt => absurd ⟨k', Finset.mem_filter.2 ⟨hk', hgt⟩⟩ hU⟩
    have hαK : ∀ k' ∈ K, k' < α ↔ k' ≤ k := fun k' hk' =>
      ⟨fun h => le_of_not_gt fun hgt => absurd h (not_lt.2 (hαK' k' hk' hgt).le),
        fun h => h.trans_lt hkα⟩
    refine ⟨α, fun h => lt_irrefl α (hαK' α h hkα), ?_⟩
    · have hset : K.filter (· < α) = insert k (K.filter (· < k)) := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hk', h⟩
          rcases ((hαK k' hk').1 h).lt_or_eq with h' | h'
          · exact Or.inr ⟨hk', h'⟩
          · exact Or.inl h'
        · rintro (rfl | ⟨hk', h⟩)
          · exact ⟨hk, hkα⟩
          · exact ⟨hk', (hαK k' hk').2 h.le⟩
      simp only [numBelow]
      rw [hset, Finset.card_insert_of_notMem (by simp)]
  choose! r hr using hright
  -- the components of these points are distinct
  set ι : Option ℝ → Set ℝ := fun i => i.elim (connectedComponentIn (↑K : Set ℝ)ᶜ α₀)
    fun k => connectedComponentIn (↑K : Set ℝ)ᶜ (r k)
  set s : Finset (Option ℝ) := insert none (K.image some)
  have hs : s.card = K.card + 1 := by
    rw [Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective ℝ)]
  have hval : ∀ i ∈ s, ∃ α, α ∉ (↑K : Set ℝ) ∧ ι i = connectedComponentIn (↑K : Set ℝ)ᶜ α ∧
      numBelow K α = i.elim 0 fun k => numBelow K k + 1 := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨α₀, hα₀K, rfl, hα₀⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨r k, (hr k hk).1, rfl, (hr k hk).2⟩
  have hmaps : ∀ i ∈ (s : Set (Option ℝ)), ι i ∈ components (↑K : Set ℝ)ᶜ := by
    intro i hi
    obtain ⟨α, hα, heq, -⟩ := hval i hi
    exact ⟨α, hα, heq⟩
  have hinj : InjOn ι (s : Set (Option ℝ)) := by
    intro i hi j hj hij
    obtain ⟨α, hα, hιi, hi'⟩ := hval i hi
    obtain ⟨α', hα', hιj, hj'⟩ := hval j hj
    rw [hιi, hιj, hc, connectedComponentIn_eq_iff ordConnected_univ ⟨mem_univ _, hα⟩
      ⟨mem_univ _, hα'⟩, hi', hj'] at hij
    rcases Finset.mem_insert.1 hi with rfl | hi <;> rcases Finset.mem_insert.1 hj with rfl | hj
    · rfl
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hj
      simp at hij
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hi
      simp at hij
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hj
      simp only [Option.elim_some, add_left_inj] at hij
      rcases lt_trichotomy k k' with h | h | h
      · exact absurd hij (numBelow_lt hk le_rfl h).ne
      · rw [h]
      · exact absurd hij (numBelow_lt hk' le_rfl h).ne'
  calc K.card + 1 = (s : Set (Option ℝ)).ncard := by rw [Set.ncard_coe_finset, hs]
    _ ≤ (components (↑K : Set ℝ)ᶜ).ncard := Set.ncard_le_ncard_of_injOn ι hmaps hinj hfin

/-! ### Linear pieces -/

/-- The open linear pieces of `g`: the connected components of the set of points near which `g` is
affine. -/
def openPieces (g : ℝ → ℝ) : Set (Set ℝ) := components (kinks g)ᶜ

/-- The linear pieces of `g` on `ℝ`: the closures of the open linear pieces (as Section 3 defines
the pieces of `x*`). -/
def linPieces (g : ℝ → ℝ) : Set (Set ℝ) := closure '' openPieces g

variable {g : ℝ → ℝ}

/-- (Not in the paper: `lem:E-piececount` and step (3) of `thm:laminar` count the linear pieces of
`π_L` as its vertices plus one without proof.) A function with finitely many kinks has
`|kinks g| + 1` open linear pieces. -/
theorem openPieces_finite_ncard (hK : (kinks g).Finite) :
    (openPieces g).Finite ∧ (openPieces g).ncard = (kinks g).ncard + 1 := by
  have h1 := (components_finite_ncard_le ordConnected_univ hK.toFinset).1
  rw [← compl_eq_univ_sdiff, hK.coe_toFinset] at h1
  have h2 := ncard_components_compl hK.toFinset
  rw [hK.coe_toFinset, ← Set.ncard_eq_toFinset_card _ hK] at h2
  exact ⟨h1, h2⟩

theorem mem_openPieces {α : ℝ} (hα : α ∉ kinks g) :
    connectedComponentIn (kinks g)ᶜ α ∈ openPieces g :=
  ⟨α, hα, rfl⟩

theorem isOpen_of_mem_openPieces (hK : (kinks g).Finite) {O : Set ℝ} (hO : O ∈ openPieces g) :
    IsOpen O := by
  obtain ⟨α, -, rfl⟩ := hO
  exact hK.isClosed.isOpen_compl.connectedComponentIn

theorem isPreconnected_of_mem_openPieces {O : Set ℝ} (hO : O ∈ openPieces g) :
    IsPreconnected O := by
  obtain ⟨α, -, rfl⟩ := hO
  exact isPreconnected_connectedComponentIn

theorem subset_of_mem_openPieces {O : Set ℝ} (hO : O ∈ openPieces g) : O ⊆ (kinks g)ᶜ := by
  obtain ⟨α, -, rfl⟩ := hO
  exact connectedComponentIn_subset _ _

/-- (Not in the paper: a step of `linPieces_finite_ncard`.) Distinct open linear pieces have
distinct closures: a point of an open piece lies in the closure of another only if the two meet. -/
theorem injOn_closure_openPieces (hK : (kinks g).Finite) : InjOn closure (openPieces g) := by
  intro O hO O' hO' h
  have hOo := isOpen_of_mem_openPieces hK hO
  obtain ⟨α, hα, rfl⟩ := hO
  obtain ⟨α', -, rfl⟩ := hO'
  have hmem : α ∈ closure (connectedComponentIn (kinks g)ᶜ α') :=
    h ▸ subset_closure (mem_connectedComponentIn hα)
  obtain ⟨β, hβ, hβ'⟩ := mem_closure_iff.1 hmem _ hOo (mem_connectedComponentIn hα)
  exact (connectedComponentIn_eq hβ).trans (connectedComponentIn_eq hβ').symm

/-- (Not in the paper: `lem:E-piececount` uses without proof that the graph of `π_L` has
`#(L) − 1` vertices, that is, `|kinks π_L| + 1` linear pieces.) A function with finitely many
kinks has `|kinks g| + 1` linear pieces. -/
theorem linPieces_finite_ncard (hK : (kinks g).Finite) :
    (linPieces g).Finite ∧ (linPieces g).ncard = (kinks g).ncard + 1 := by
  obtain ⟨h1, h2⟩ := openPieces_finite_ncard hK
  exact ⟨h1.image _, (injOn_closure_openPieces hK).ncard_image.trans h2⟩

/-- (Not in the paper: step (3) of `lem:E-piececount` passes without proof from a point on the graph
of `π_J` to a linear piece of that graph.) Every real lies in a linear piece of a function with
finitely many kinks:
the points left of it, up to the previous kink, lie in one open linear piece. -/
theorem exists_mem_linPieces (hK : (kinks g).Finite) (α : ℝ) : ∃ P ∈ linPieces g, α ∈ P := by
  classical
  obtain ⟨a, haα, ha⟩ : ∃ a < α, Ioo a α ⊆ (kinks g)ᶜ := by
    set L := hK.toFinset.filter (· < α)
    by_cases hL : L.Nonempty
    · refine ⟨L.max' hL, (Finset.mem_filter.1 (L.max'_mem hL)).2, fun x hx hxk => ?_⟩
      have := L.le_max' x (Finset.mem_filter.2 ⟨hK.mem_toFinset.2 hxk, hx.2⟩)
      linarith [hx.1]
    · exact ⟨α - 1, by linarith, fun x hx hxk =>
        hL ⟨x, Finset.mem_filter.2 ⟨hK.mem_toFinset.2 hxk, hx.2⟩⟩⟩
  have hβ : (a + α) / 2 ∈ Ioo a α := ⟨by linarith, by linarith⟩
  have hsub : Ioo a α ⊆ connectedComponentIn (kinks g)ᶜ ((a + α) / 2) :=
    isPreconnected_Ioo.subset_connectedComponentIn hβ ha
  refine ⟨closure (connectedComponentIn (kinks g)ᶜ ((a + α) / 2)),
    ⟨_, mem_openPieces (ha hβ), rfl⟩, closure_mono hsub ?_⟩
  rw [closure_Ioo haα.ne]
  exact right_mem_Icc.2 haα.le

/-- (Not in the paper: a step of `exists_affine_of_mem_openPieces`.) A function that is affine near
every point of an open preconnected set `O` agrees with one affine function on `O`: its derivative
is locally constant, hence constant. -/
theorem exists_affine_of_isPreconnected {O : Set ℝ} (hO : IsOpen O) (hc : IsPreconnected O)
    (h : ∀ α ∈ O, AffineAt g α) : ∃ c d : ℝ, ∀ α ∈ O, g α = c + d * α := by
  rcases O.eq_empty_or_nonempty with rfl | ⟨α₀, hα₀⟩
  · exact ⟨0, 0, fun α hα => absurd hα (notMem_empty α)⟩
  have hloc : ∀ α ∈ O, ∃ s, HasDerivAt g s α ∧ deriv g =ᶠ[𝓝 α] fun _ => s := by
    intro α hα
    obtain ⟨ε, hε, a', b', h'⟩ := h α hα
    have hmem : α ∈ Ioo (α - ε) (α + ε) := ⟨by linarith, by linarith⟩
    refine ⟨b', hasDerivAt_of_eqOn_Ioo h' hmem, ?_⟩
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with x hx
    exact (hasDerivAt_of_eqOn_Ioo h' hx).deriv
  have hd : ∀ x ∈ O, deriv g x = deriv g α₀ := by
    have h2 : ∀ y ∈ O, HasDerivAt (deriv g) 0 y := fun y hy => by
      obtain ⟨s, -, hs⟩ := hloc y hy
      exact (hasDerivAt_const y s).congr_of_eventuallyEq hs
    intro x hx
    exact hO.is_const_of_deriv_eq_zero hc
      (fun y hy => (h2 y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (h2 y hy).deriv) hx hα₀
  set d := deriv g α₀
  have h3 : ∀ y ∈ O, HasDerivAt (fun x => g x - d * x) 0 y := by
    intro y hy
    obtain ⟨s, hs, -⟩ := hloc y hy
    have hsd : s = d := hs.deriv.symm.trans (hd y hy)
    have := hs.sub (hasDerivAt_id' y |>.const_mul d)
    rw [hsd, mul_one, sub_self] at this
    exact this
  refine ⟨g α₀ - d * α₀, d, fun x hx => ?_⟩
  have := hO.is_const_of_deriv_eq_zero (f := fun x => g x - d * x) hc
    (fun y hy => (h3 y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (h3 y hy).deriv) hx hα₀
  linarith

/-- (Not in the paper: step (3)(c) of `thm:laminar` uses without proof that `π_L` is affine on an
open linear piece.) A function is affine on each of its open linear pieces. -/
theorem exists_affine_of_mem_openPieces (hK : (kinks g).Finite) {O : Set ℝ}
    (hO : O ∈ openPieces g) : ∃ c d : ℝ, ∀ α ∈ O, g α = c + d * α :=
  exists_affine_of_isPreconnected (isOpen_of_mem_openPieces hK hO)
    (isPreconnected_of_mem_openPieces hO) fun _ hβ => not_not.1 (subset_of_mem_openPieces hO hβ)

/-- (Not in the paper: step (4) of `lem:E-piececount` uses without proof that `π_J` is affine on a
linear piece.) A continuous function is affine on each of its linear pieces. -/
theorem exists_affine_of_mem_linPieces (hK : (kinks g).Finite) (hg : Continuous g) {P : Set ℝ}
    (hP : P ∈ linPieces g) : ∃ c d : ℝ, ∀ α ∈ P, g α = c + d * α := by
  obtain ⟨O, hO, rfl⟩ := hP
  obtain ⟨c, d, hcd⟩ := exists_affine_of_mem_openPieces hK hO
  refine ⟨c, d, fun α hα => ?_⟩
  have heq : EqOn g (fun x => c + d * x) O := hcd
  exact heq.of_subset_closure hg.continuousOn
    (by fun_prop : Continuous fun x : ℝ => c + d * x).continuousOn subset_closure le_rfl hα

/-- The linear pieces are intervals. -/
theorem ordConnected_of_mem_linPieces {P : Set ℝ} (hP : P ∈ linPieces g) : P.OrdConnected := by
  obtain ⟨O, ⟨α, -, rfl⟩, rfl⟩ := hP
  exact (isPreconnected_connectedComponentIn.ordConnected.convex (𝕜 := ℝ)).closure.ordConnected

/-- The open linear pieces are intervals. -/
theorem ordConnected_of_mem_openPieces {O : Set ℝ} (hO : O ∈ openPieces g) : O.OrdConnected :=
  (isPreconnected_of_mem_openPieces hO).ordConnected

/-! ### Minima of affine functions -/

section InfAffine

variable {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (a b : ι → ℝ)

include hs in
/-- (Not in the paper: step (4) of the proof of `lem:E-laminarformula` uses without proof that a
minimum of affine functions is concave.) A minimum of affine functions is concave. -/
theorem concaveOn_inf' : ConcaveOn ℝ univ fun α => s.inf' hs fun i => a i + b i * α := by
  refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  refine Finset.le_inf' hs _ fun i hi => ?_
  have hx := Finset.inf'_le (fun i => a i + b i * x) hi
  have hy := Finset.inf'_le (fun i => a i + b i * y) hi
  have heq : a i + b i * (p * x + q * y) = p * (a i + b i * x) + q * (a i + b i * y) := by
    linear_combination (-(a i)) * hpq
  rw [heq]
  exact add_le_add (mul_le_mul_of_nonneg_left hx hp) (mul_le_mul_of_nonneg_left hy hq)

include hs in
/-- (Not in the paper: step (4) of the proof of `lem:E-laminarformula` uses without proof that a
minimum of affine functions with positive slopes is strictly increasing.) A minimum of affine
functions with positive slopes is strictly increasing. -/
theorem strictMono_inf' (hb : ∀ i ∈ s, 0 < b i) :
    StrictMono fun α => s.inf' hs fun i => a i + b i * α := by
  intro x y hxy
  obtain ⟨i, hi, hiy⟩ := Finset.exists_mem_eq_inf' hs fun i => a i + b i * y
  simp only
  rw [hiy]
  calc s.inf' hs (fun i => a i + b i * x) ≤ a i + b i * x := Finset.inf'_le _ hi
    _ < a i + b i * y := by nlinarith [hb i hi]

include hs in
/-- (Not in the paper: step (4) of the proof of `lem:E-laminarformula` derives "piecewise linear"
from "a minimum of finitely many affine functions".) A minimum of finitely many affine functions
has finitely many kinks: near a point at which no two of the functions with different slopes cross,
the function attaining the minimum there stays below the others. -/
theorem kinks_inf'_finite : (kinks fun α => s.inf' hs fun i => a i + b i * α).Finite := by
  classical
  -- the crossing points
  set C : Finset ℝ := ((s ×ˢ s).filter fun p => b p.1 ≠ b p.2).image
    fun p => (a p.2 - a p.1) / (b p.1 - b p.2)
  refine C.finite_toSet.subset fun α₀ hα₀ => ?_
  by_contra hnot
  apply hα₀
  obtain ⟨i₀, hi₀, heq⟩ := Finset.exists_mem_eq_inf' hs fun i => a i + b i * α₀
  have hev : ∀ᶠ α in 𝓝 α₀, ∀ j ∈ s, a i₀ + b i₀ * α ≤ a j + b j * α := by
    refine (Filter.eventually_all_finset s).2 fun j hj => ?_
    have hle : a i₀ + b i₀ * α₀ ≤ a j + b j * α₀ := heq ▸ Finset.inf'_le _ hj
    by_cases hbj : b i₀ = b j
    · refine Filter.Eventually.of_forall fun α => ?_
      rw [hbj] at hle ⊢
      linarith
    · have hlt : a i₀ + b i₀ * α₀ < a j + b j * α₀ := by
        refine lt_of_le_of_ne hle fun h => hnot ?_
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i₀, j), Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨hi₀, hj⟩, hbj⟩, ?_⟩)
        have hne : b i₀ - b j ≠ 0 := sub_ne_zero.2 hbj
        field_simp
        linarith
      have hc : Continuous fun α : ℝ => (a j + b j * α) - (a i₀ + b i₀ * α) := by fun_prop
      filter_upwards [(hc.tendsto α₀).eventually (lt_mem_nhds (sub_pos.2 hlt))] with α hα
      linarith
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, a i₀, b i₀, fun α hα => ?_⟩
  refine le_antisymm (Finset.inf'_le _ hi₀) (Finset.le_inf' hs _ (hball ?_))
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [hα.1, hα.2]

end InfAffine

/-! ### End points of intervals and zero sets of convex functions -/

/-- (Not in the paper: step (4) of `lem:E-piececount` and step (3)(c) of `thm:laminar` use without
proof that an interval has at most two boundary points.) A point of an interval `S` that is not an
interior point of `S` is its least or its greatest element, so at most two points of `S` are not
interior points. -/
theorem finite_ncard_diff_interior_le_two {S V : Set ℝ} (hS : S.OrdConnected)
    (hV : V ⊆ S \ interior S) : V.Finite ∧ V.ncard ≤ 2 := by
  have hend : ∀ v ∈ V, IsGreatest S v ∨ IsLeast S v := by
    intro v hv
    obtain ⟨hvS, hvi⟩ := hV hv
    by_contra h
    obtain ⟨hG', hL'⟩ := not_or.1 h
    obtain ⟨s₂, hs₂, h2⟩ : ∃ s₂ ∈ S, v < s₂ := by
      by_contra h'
      push Not at h'
      exact hG' ⟨hvS, fun s hs => h' s hs⟩
    obtain ⟨s₁, hs₁, h1⟩ : ∃ s₁ ∈ S, s₁ < v := by
      by_contra h'
      push Not at h'
      exact hL' ⟨hvS, fun s hs => h' s hs⟩
    exact hvi (mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Ioo_mem_nhds h1 h2)
      (Ioo_subset_Icc_self.trans (hS.out hs₁ hs₂))))
  have hG : {v | IsGreatest S v}.Subsingleton := fun x hx y hy => hx.unique hy
  have hL : {v | IsLeast S v}.Subsingleton := fun x hx y hy => hx.unique hy
  have hfin : ({v | IsGreatest S v} ∪ {v | IsLeast S v}).Finite := hG.finite.union hL.finite
  have hsub : V ⊆ {v | IsGreatest S v} ∪ {v | IsLeast S v} := fun v hv => hend v hv
  refine ⟨hfin.subset hsub,
    (Set.ncard_le_ncard hsub hfin).trans ((Set.ncard_union_le _ _).trans ?_)⟩
  have h1 := (Set.ncard_le_one hG.finite).2 fun x hx y hy => hG hx hy
  have h2 := (Set.ncard_le_one hL.finite).2 fun x hx y hy => hL hx hy
  omega

/-- (Not in the paper: a step of `convexOn_eq_zero_of_three`.) The three-point inequality of a
convex function on an interval, without divisions. -/
theorem convexOn_three_point {D : ℝ → ℝ} {O : Set ℝ} (hD : ConvexOn ℝ O D) {x y z : ℝ}
    (hx : x ∈ O) (hz : z ∈ O) (hxy : x < y) (hyz : y < z) :
    (z - x) * D y ≤ (z - y) * D x + (y - x) * D z := by
  have hzx : 0 < z - x := by linarith
  have hw : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hzx.ne']
    ring
  have h := hD.2 hx hz (div_nonneg (sub_nonneg.2 hyz.le) hzx.le)
    (div_nonneg (sub_nonneg.2 hxy.le) hzx.le) hw
  have hy : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    field_simp
    ring
  simp only [smul_eq_mul, hy] at h
  have h' := mul_le_mul_of_nonneg_left h hzx.le
  have he : (z - x) * ((z - y) / (z - x) * D x + (y - x) / (z - x) * D z) =
      (z - y) * D x + (y - x) * D z := by
    field_simp
  linarith

/-- (Not in the paper: a step of `zeroSet_finite_or_ordConnected`.) A convex function on an
interval that vanishes at three points `a < b < c`
vanishes on `[a, c]`: below the chord it is `≤ 0`, and as `b` lies between any point of `[a, c]`
and `a` or `c`, it is `≥ 0`. -/
theorem convexOn_eq_zero_of_three {D : ℝ → ℝ} {O : Set ℝ} (hD : ConvexOn ℝ O D) {a b c : ℝ}
    (ha : a ∈ O) (hc : c ∈ O) (hab : a < b) (hbc : b < c) (h0a : D a = 0) (h0b : D b = 0)
    (h0c : D c = 0) : ∀ x ∈ Icc a c, D x = 0 := by
  have hO : O.OrdConnected := hD.1.ordConnected
  intro x hx
  have hxO : x ∈ O := hO.out ha hc hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · exact h0a
  rcases eq_or_lt_of_le hx.2 with rfl | hxc
  · exact h0c
  have hle : D x ≤ 0 := by
    have := convexOn_three_point hD ha hc hax hxc
    rw [h0a, h0c] at this
    nlinarith
  refine le_antisymm hle ?_
  rcases lt_trichotomy x b with hxb | rfl | hxb
  · have := convexOn_three_point hD hxO hc hxb hbc
    rw [h0b, h0c] at this
    nlinarith
  · exact h0b.ge
  · have := convexOn_three_point hD ha hxO hab hxb
    rw [h0a, h0b] at this
    nlinarith

/-- (Not in the paper: step (3)(c) of `thm:laminar` uses this without proof.) The zero set of a
convex function in an interval `O` either consists of at most two points or is an interval. -/
theorem zeroSet_finite_or_ordConnected {D : ℝ → ℝ} {O : Set ℝ} (hD : ConvexOn ℝ O D) :
    ({x ∈ O | D x = 0}.Finite ∧ {x ∈ O | D x = 0}.ncard ≤ 2) ∨ {x ∈ O | D x = 0}.OrdConnected := by
  set Z := {x ∈ O | D x = 0}
  by_cases h3 : ∃ a ∈ Z, ∃ b ∈ Z, ∃ c ∈ Z, a < b ∧ b < c
  · right
    obtain ⟨a, ha, b, hb, c, hc, hab, hbc⟩ := h3
    -- any three zeros `u < v < w` give an interval `[u, w]` of zeros
    have h3' : ∀ u ∈ Z, ∀ v ∈ Z, ∀ w ∈ Z, u < v → v < w → Icc u w ⊆ Z :=
      fun u hu v hv w hw huv hvw x hx =>
        ⟨hD.1.ordConnected.out hu.1 hw.1 hx,
          convexOn_eq_zero_of_three hD hu.1 hw.1 huv hvw hu.2 hv.2 hw.2 x hx⟩
    refine Set.ordConnected_iff.2 fun x hx y hy hxy => ?_
    rcases eq_or_lt_of_le hxy with rfl | hxy
    · rw [Icc_self]
      exact singleton_subset_iff.2 hx
    -- a third zero `t`
    obtain ⟨t, ht, htx, hty⟩ : ∃ t ∈ Z, t ≠ x ∧ t ≠ y := by
      by_contra hcon
      push Not at hcon
      have hxy' : ∀ u ∈ Z, u = x ∨ u = y := fun u hu => by
        by_cases h : u = x
        · exact Or.inl h
        · exact Or.inr (hcon u hu h)
      rcases hxy' a ha with h1 | h1 <;> rcases hxy' b hb with h2 | h2 <;>
        rcases hxy' c hc with h3 | h3 <;> linarith
    rcases lt_or_gt_of_ne htx with htx | htx
    · exact (Icc_subset_Icc htx.le le_rfl).trans (h3' t ht x hx y hy htx hxy)
    · rcases lt_or_gt_of_ne hty with hty | hty
      · exact h3' x hx t ht y hy htx hty
      · exact (Icc_subset_Icc le_rfl hty.le).trans (h3' x hx y hy t ht hxy hty)
  · left
    have hno : ∀ V : Finset ℝ, (V : Set ℝ) ⊆ Z → V.card ≤ 2 := fun V hV =>
      card_le_two_of_no_triple fun x hx y hy z hz hxy hyz =>
        h3 ⟨x, hV hx, y, hV hy, z, hV hz, hxy, hyz⟩
    exact finite_ncard_le_of_forall_finset hno

/-- (Not in the paper: step (4) of `lem:E-piececount` uses this without proof.) The zero set of a
concave function in an interval `O` either consists of at most two points or is an interval: it is
the zero set of the convex function `−D` (`zeroSet_finite_or_ordConnected`). -/
theorem zeroSet_finite_or_ordConnected_of_concaveOn {D : ℝ → ℝ} {O : Set ℝ}
    (hD : ConcaveOn ℝ O D) :
    ({x ∈ O | D x = 0}.Finite ∧ {x ∈ O | D x = 0}.ncard ≤ 2) ∨ {x ∈ O | D x = 0}.OrdConnected := by
  have hset : {x ∈ O | (-D) x = 0} = {x ∈ O | D x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, neg_eq_zero]
  have h := zeroSet_finite_or_ordConnected hD.neg
  rw [hset] at h
  exact h

end

end Stoc
