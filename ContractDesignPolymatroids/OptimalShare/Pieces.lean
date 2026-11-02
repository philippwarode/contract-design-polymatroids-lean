-- stamp r7 2026-11-02
import ContractDesignPolymatroids.OptimalShare.Velocity
import ContractDesignPolymatroids.OptimalShare.Kinks

/-!
# Pieces and event points

The STOC version, Section 3 (`stoc-sections/06-optimal-share.tex:17`), the end of Appendix B.2
(`sec:A-structure`, `stoc-sections/appB-quadratic.tex:337-343`: the state and event points) and
Appendix B.4 (`sec:A-pieces`, `appB-quadratic.tex:350-399`: breakpoints, pieces and Lemma
`lem:eventcount`).

A *breakpoint* is a share `α > 0` at which `x*` is not affine on any neighborhood
(`Stoc.breakpoints`, `BP`), and `B` is the number of breakpoints in `(0, 1)` (`numBP`). A *piece*
is the closure of a connected component of the non-breakpoint shares in `(0, 1)` (`pieces`). An
*event point* is a share `α > 0` at which the state `Stoc.state` is not constant on any
neighborhood (`IsEvent`).

The STOC version asserts that there are at most `B + 1` pieces and that they cover `[0, 1]`, as
there are finitely many breakpoints (`lem:pwaffine`) (`appB-quadratic.tex:353-354`), and it uses
without proof that the connected components of the non-breakpoint shares are the open intervals
between consecutive points of `{0}`, the breakpoints in `(0, 1)` and `{1}`, that distinct pieces
have disjoint interiors, and that `x*` is affine on a piece. These are proved here (marked "not in
the paper"): `connectedComponentIn_nonBP`, `mem_pieces_iff` (a piece is an interval `[a, b]` with
`IsPiece f m β a b`, the form in terms of end points that other files use), `piece_eq_of_mem`,
`pieces_finite_ncard_le`, `exists_piece`, `affine_on_piece`.

`lem:eventcount` is `Stoc.Tracing.eventcount`; its proof follows the STOC version's, sentence by
sentence:

1. every breakpoint is an event point, by `lem:velocity` (`isEvent_of_mem_bp`);
2. inside a piece, every `x*_e` and every `ρ_e` is nonnegative and affine, so each vanishes either
   identically or nowhere in its interior (`zero_or_ne_of_nonneg`);
3. hence the free elements and the zero set are constant there;
4. and the blocks change only at an isolated zero of some `ρ_e − ρ_g`, at most `C(n, 2)` points
   per piece (one for each pair `{e, g}`: the root of `ρ_e − ρ_g` if it is nonconstant, `root`,
   `affine_zero_iff`);
5. in addition to the breakpoints: with at most `B + 1` pieces, at most `B + (B + 1) C(n, 2)`
   event points lie in `(0, 1)`.

Steps (2) to (4) are `events_in_piece`, on one piece, as in the paper. The proof of `thm:bitlength`
applies "the argument of `lem:eventcount`" to the intervals of `lem:pwaffine`; there the argument is
repeated (`Stoc.BitLength.events_in_affine`, marked "not in the paper"). That a nonnegative affine
function vanishes either identically or nowhere in the interior, the inference of step (2), and that
an affine function has at most one isolated zero, which the count of step (4) leaves implicit, are
`zero_or_ne_of_nonneg` and `affine_zero_iff` (marked "not in the paper").

Moved on 2026-10-25 from `ContractDesignPolymatroids/OptimalShare/Tracing.lean` (the paper's pieces, as closures of
connected components, and the count of `lem:eventcount` over them are new). Adapted on 2026-10-27 to
the STOC version after PR #88: `lem:eventcount` counts `B + (B + 1) C(n, 2)` event points (it was
`B + (B + 1)(2n + C(n, 2))`), with the new proof, in which the free elements and the zero set are
constant inside a piece and only the zeros of the `ρ_e − ρ_g` remain.
-/

namespace Stoc

namespace Tracing

open Finset Set

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {f : Finset E → ℝ} {m β : E → ℝ}

/-! ### Breakpoints, pieces and event points -/

section Defs

variable (f m β)

/-- The breakpoints of `x*`. -/
abbrev BP : Set ℝ := breakpoints (bestResponse f m β)

/-- `B`, the number of breakpoints in `(0, 1)` (`06-optimal-share.tex:17`). -/
noncomputable def numBP : ℕ := (BP f m β ∩ Ioo 0 1).ncard

/-- The non-breakpoint shares in `(0, 1)`. -/
def nonBP : Set ℝ := Ioo 0 1 \ BP f m β

/-- The pieces of `x*` (Section 3): the closures of the connected components of the
non-breakpoint shares in `(0, 1)`. -/
def pieces : Set (Set ℝ) :=
  {P | ∃ α ∈ nonBP f m β, P = closure (connectedComponentIn (nonBP f m β) α)}

/-- A piece `[a, b]` in terms of its end points (the form other files use; it is the piece
`Icc a b` of `pieces` by `mem_pieces_iff`): `[a, b] ⊆ [0, 1]` with `a < b`, no breakpoint in
`(a, b)`, `a = 0` or a breakpoint, and `b = 1` or a breakpoint. -/
def IsPiece (a b : ℝ) : Prop :=
  0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ (∀ α ∈ Ioo a b, α ∉ BP f m β) ∧ (a = 0 ∨ a ∈ BP f m β) ∧
    (b = 1 ∨ b ∈ BP f m β)

/-- The pieces, as pairs of end points. -/
def pieceSet : Set (ℝ × ℝ) := {p | IsPiece f m β p.1 p.2}

/-- An event point (the end of Appendix B.2, `appB-quadratic.tex:342-343`): a share `α > 0` such
that the state `(Φ, Z, 𝒫)` (`Stoc.state`) is not constant on any neighborhood of `α`, that is, on
no open interval that contains `α`. -/
def IsEvent (α : ℝ) : Prop :=
  0 < α ∧ ∀ a b, a < α → α < b →
    ¬ ∀ γ ∈ Ioo a b, ∀ γ' ∈ Ioo a b, state f m β γ = state f m β γ'

end Defs

/-- The definition of an event point, unfolded (plumbing, used by other files). -/
theorem isEvent_iff {α : ℝ} : IsEvent f m β α ↔
    0 < α ∧ ∀ a b, a < α → α < b →
      ¬ ∀ γ ∈ Ioo a b, ∀ γ' ∈ Ioo a b, state f m β γ = state f m β γ' :=
  Iff.rfl

/-- Finitely many breakpoints (`lem:pwaffine`). -/
lemma bp_finite (H : Hyp f m β) : (BP f m β).Finite := (pwaffine H).2.2.1

omit [DecidableEq E] in
/-- A piece `[a, b]` is determined by its left end (part of the proofs of `card_pieces_le` and
`piece_eq_of_mem`, not in the paper). -/
lemma piece_right_unique {a b b' : ℝ} (h : IsPiece f m β a b) (h' : IsPiece f m β a b') :
    b = b' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rcases h.2.2.2.2.2 with h1 | h1
    · linarith [h'.2.2.1]
    · exact h'.2.2.2.1 b ⟨h.2.1, hlt⟩ h1
  · rcases h'.2.2.2.2.2 with h1 | h1
    · linarith [h.2.2.1]
    · exact h.2.2.2.1 b' ⟨h'.2.1, hlt⟩ h1

omit [DecidableEq E] in
/-- Two pieces whose interiors meet are equal (not in the paper: the STOC version uses without proof
that distinct pieces have disjoint interiors). -/
lemma piece_eq_of_mem {a b c d α : ℝ} (h : IsPiece f m β a b) (h' : IsPiece f m β c d)
    (hα : α ∈ Ioo a b) (hα' : α ∈ Ioo c d) : a = c ∧ b = d := by
  have hl : a = c := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rcases h'.2.2.2.2.1 with h1 | h1
      · linarith [h.1]
      · exact h.2.2.2.1 c ⟨hlt, hα'.1.trans hα.2⟩ h1
    · rcases h.2.2.2.2.1 with h1 | h1
      · linarith [h'.1]
      · exact h'.2.2.2.1 a ⟨hlt, hα.1.trans hα'.2⟩ h1
  refine ⟨hl, piece_right_unique h (hl ▸ h')⟩

/-- Every share in `[0, 1)` lies in a piece `[a, b]` with `a ≤ α < b`: `a` is the largest point of
`{0}` and the breakpoints in `(0, α]`, and `b` the smallest point of `{1}` and the breakpoints in
`(α, 1)` (part of the proofs of `connectedComponentIn_nonBP` and `exists_piece`, not in the
paper). -/
lemma exists_piece_lt (H : Hyp f m β) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    ∃ a b, IsPiece f m β a b ∧ a ≤ α ∧ α < b := by
  classical
  set T := (bp_finite H).toFinset
  set L := insert 0 (T.filter fun x => 0 < x ∧ x ≤ α)
  set R := insert 1 (T.filter fun x => α < x ∧ x < 1)
  have hL : L.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hR : R.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  set a := L.max' hL
  set b := R.min' hR
  have ha0 : 0 ≤ a := L.le_max' 0 (Finset.mem_insert_self _ _)
  have haα : a ≤ α := L.max'_le hL _ fun x hx => by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h0
    · exact (Finset.mem_filter.1 hx).2.2
  have hb1 : b ≤ 1 := R.min'_le 1 (Finset.mem_insert_self _ _)
  have hαb : α < b := R.lt_min'_iff hR |>.2 fun x hx => by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h1
    · exact (Finset.mem_filter.1 hx).2.1
  refine ⟨a, b, ⟨ha0, haα.trans_lt hαb, hb1, fun x hx hxB => ?_, ?_, ?_⟩, haα, hαb⟩
  · have hxT : x ∈ T := (Set.Finite.mem_toFinset _).2 hxB
    rcases le_or_gt x α with hxα | hxα
    · have : x ∈ L := Finset.mem_insert_of_mem (Finset.mem_filter.2
        ⟨hxT, ha0.trans_lt hx.1, hxα⟩)
      exact absurd (L.le_max' x this) (not_le.2 hx.1)
    · have : x ∈ R := Finset.mem_insert_of_mem (Finset.mem_filter.2
        ⟨hxT, hxα, hx.2.trans_le hb1⟩)
      exact absurd (R.min'_le x this) (not_le.2 hx.2)
  · rcases Finset.mem_insert.1 (L.max'_mem hL) with h | h
    · exact Or.inl h
    · exact Or.inr ((Set.Finite.mem_toFinset _).1 (Finset.mem_filter.1 h).1)
  · rcases Finset.mem_insert.1 (R.min'_mem hR) with h | h
    · exact Or.inl h
    · exact Or.inr ((Set.Finite.mem_toFinset _).1 (Finset.mem_filter.1 h).1)

/-- Every share of `[0, 1]` lies in a piece `[a, b]` (not in the paper: asserted at
`appB-quadratic.tex:353-354`, "they cover `[0, 1]`, as there are finitely many breakpoints"; in the
end-point form, used by other files). The piece is built from the finitely many breakpoints
(`bp_finite`, `exists_piece_lt`). -/
lemma exists_piece (H : Hyp f m β) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    ∃ a b, IsPiece f m β a b ∧ α ∈ Icc a b := by
  rcases hα.2.lt_or_eq with h1 | h1
  · obtain ⟨a, b, hp, ha, hb⟩ := exists_piece_lt H hα.1 h1
    exact ⟨a, b, hp, ha, hb.le⟩
  · -- `α = 1`: the last piece.
    classical
    set T := (bp_finite H).toFinset
    set L := insert 0 (T.filter fun x => 0 < x ∧ x < 1)
    have hL : L.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
    set a' := L.max' hL
    have ha0 : 0 ≤ a' := L.le_max' 0 (Finset.mem_insert_self _ _)
    have ha1 : a' < 1 := L.max'_lt_iff hL |>.2 fun x hx => by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact one_pos
      · exact (Finset.mem_filter.1 hx).2.2
    refine ⟨a', 1, ⟨ha0, ha1, le_rfl, fun x hx hxB => ?_, ?_, Or.inl rfl⟩, ?_⟩
    · have : x ∈ L := Finset.mem_insert_of_mem (Finset.mem_filter.2
        ⟨(Set.Finite.mem_toFinset _).2 hxB, ha0.trans_lt hx.1, hx.2⟩)
      exact absurd (L.le_max' x this) (not_le.2 hx.1)
    · rcases Finset.mem_insert.1 (L.max'_mem hL) with h | h
      · exact Or.inl h
      · exact Or.inr ((Set.Finite.mem_toFinset _).1 (Finset.mem_filter.1 h).1)
    · rw [h1]
      exact ⟨ha1.le, le_rfl⟩

/-- A share in `(0, 1)` that is not a breakpoint lies in the interior of a piece `[a, b]` (part of
the proof of `connectedComponentIn_nonBP`, not in the paper). -/
lemma exists_piece_interior (H : Hyp f m β) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hbp : α ∉ BP f m β) : ∃ a b, IsPiece f m β a b ∧ α ∈ Ioo a b := by
  obtain ⟨a, b, hp, ha, hb⟩ := exists_piece_lt H hα.1.le hα.2
  refine ⟨a, b, hp, lt_of_le_of_ne ha fun h => ?_, hb⟩
  rcases hp.2.2.2.2.1 with h0 | h0
  · rw [h0] at h
    exact absurd h hα.1.ne
  · rw [h] at h0
    exact hbp h0

/-! ### The pieces of the STOC version -/

omit [DecidableEq E] in
lemma Ioo_subset_nonBP {a b : ℝ} (hp : IsPiece f m β a b) : Ioo a b ⊆ nonBP f m β :=
  fun x hx => ⟨⟨hp.1.trans_lt hx.1, hx.2.trans_le hp.2.2.1⟩, hp.2.2.2.1 x hx⟩

/-- The connected components of the non-breakpoint shares (not in the paper: the STOC version
uses without proof that they are the open intervals between consecutive points of `{0}`, the
breakpoints in `(0, 1)` and `{1}`): the component of a non-breakpoint share `α ∈ (0, 1)` is
`(a, b)` for a piece `[a, b]` around `α`. -/
theorem connectedComponentIn_nonBP (H : Hyp f m β) {α : ℝ} (hα : α ∈ nonBP f m β) :
    ∃ a b, IsPiece f m β a b ∧ α ∈ Ioo a b ∧
      connectedComponentIn (nonBP f m β) α = Ioo a b := by
  obtain ⟨a, b, hp, hαab⟩ := exists_piece_interior H hα.1 hα.2
  refine ⟨a, b, hp, hαab, Subset.antisymm ?_ ?_⟩
  · -- the component lies between `a` and `b`, which are not non-breakpoint shares
    have hpre : (connectedComponentIn (nonBP f m β) α).OrdConnected :=
      isPreconnected_connectedComponentIn.ordConnected
    have hsub := connectedComponentIn_subset (nonBP f m β) α
    have hαC := mem_connectedComponentIn hα
    have ha : a ∉ nonBP f m β := fun h => by
      rcases hp.2.2.2.2.1 with h0 | h0
      · exact (h.1.1.ne h0.symm)
      · exact h.2 h0
    have hb : b ∉ nonBP f m β := fun h => by
      rcases hp.2.2.2.2.2 with h1 | h1
      · exact (h.1.2.ne h1)
      · exact h.2 h1
    intro c hc
    constructor
    · by_contra hca
      rw [not_lt] at hca
      exact ha (hsub (hpre.out hc hαC ⟨hca, hαab.1.le⟩))
    · by_contra hcb
      rw [not_lt] at hcb
      exact hb (hsub (hpre.out hαC hc ⟨hαab.2.le, hcb⟩))
  · exact isPreconnected_Ioo.subset_connectedComponentIn hαab (Ioo_subset_nonBP hp)

/-- The pieces are the intervals `[a, b]` with `IsPiece f m β a b` (not in the paper: the
end-point form that other files use, proved equivalent). -/
theorem mem_pieces_iff (H : Hyp f m β) {P : Set ℝ} :
    P ∈ pieces f m β ↔ ∃ a b, IsPiece f m β a b ∧ P = Icc a b := by
  constructor
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨a, b, hp, -, hC⟩ := connectedComponentIn_nonBP H hα
    exact ⟨a, b, hp, by rw [hC, closure_Ioo hp.2.1.ne]⟩
  · rintro ⟨a, b, hp, rfl⟩
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith [hp.2.1], by linarith [hp.2.1]⟩
    have hα := Ioo_subset_nonBP hp hmid
    obtain ⟨a', b', hp', hα', hC⟩ := connectedComponentIn_nonBP H hα
    obtain ⟨rfl, rfl⟩ := piece_eq_of_mem hp hp' hmid hα'
    exact ⟨_, hα, by rw [hC, closure_Ioo hp.2.1.ne]⟩

/-- The pieces, as pairs of end points, are finite (part of the proof of
`pieces_finite_ncard_le`, not in the paper). -/
lemma pieceSet_finite (H : Hyp f m β) : (pieceSet f m β).Finite :=
  (((bp_finite H).insert 0).prod ((bp_finite H).insert 1)).subset fun p hp =>
    ⟨by rcases hp.2.2.2.2.1 with h | h
        · exact Or.inl h
        · exact Or.inr h,
     by rcases hp.2.2.2.2.2 with h | h
        · exact Or.inl h
        · exact Or.inr h⟩

/-- There are at most `B + 1` pieces, as pairs of end points: a piece is determined by its left
end, which is `0` or a breakpoint in `(0, 1)` (part of the proof of `pieces_finite_ncard_le`, not
in the paper). -/
theorem card_pieces_le (H : Hyp f m β) :
    (pieceSet f m β).ncard ≤ numBP f m β + 1 := by
  have hinj : Set.InjOn Prod.fst (pieceSet f m β) := by
    intro p hp q hq h
    have hp' : IsPiece f m β p.1 p.2 := hp
    have hq' : IsPiece f m β p.1 q.2 := by rw [h]; exact hq
    exact Prod.ext h (piece_right_unique hp' hq')
  have hmaps : ∀ p ∈ pieceSet f m β, p.1 ∈ insert (0 : ℝ) (BP f m β ∩ Ioo 0 1) := fun p hp => by
    have hp' : IsPiece f m β p.1 p.2 := hp
    rcases hp'.2.2.2.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h.1, lt_of_lt_of_le hp'.2.1 hp'.2.2.1⟩
  calc (pieceSet f m β).ncard ≤ (insert (0 : ℝ) (BP f m β ∩ Ioo 0 1)).ncard :=
        Set.ncard_le_ncard_of_injOn Prod.fst hmaps hinj (((bp_finite H).inter_of_left _).insert 0)
    _ ≤ numBP f m β + 1 := Set.ncard_insert_le _ _

/-- There are at most `B + 1` pieces (not in the paper: asserted at `appB-quadratic.tex:353`). By
`mem_pieces_iff`, the pieces are the images of the pairs of end points (`card_pieces_le`). -/
theorem pieces_finite_ncard_le (H : Hyp f m β) :
    (pieces f m β).Finite ∧ (pieces f m β).ncard ≤ numBP f m β + 1 := by
  have heq : pieces f m β = (fun p : ℝ × ℝ => Icc p.1 p.2) '' pieceSet f m β := by
    ext P
    rw [mem_pieces_iff H]
    constructor
    · rintro ⟨a, b, hp, rfl⟩
      exact ⟨(a, b), hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, p.2, hp, rfl⟩
  rw [heq]
  exact ⟨(pieceSet_finite H).image _,
    (Set.ncard_image_le (pieceSet_finite H)).trans (card_pieces_le H)⟩

/-- On a piece, `x*` is affine (not in the paper: the STOC version takes it for granted): `x*` is
affine near every interior share, hence on the whole piece (`exists_affine_of_affineAt`, by the
derivative and the continuity of `lem:pwaffine`). -/
lemma affine_on_piece (H : Hyp f m β) {a b : ℝ} (hp : IsPiece f m β a b) :
    ∃ p w : E → ℝ, ∀ α ∈ Icc a b, bestResponse f m β α = fun e => p e + α * w e := by
  have hcoord : ∀ e, ∃ c d : ℝ, ∀ α ∈ Icc a b, bestResponse f m β α e = c + d * α := by
    intro e
    refine exists_affine_of_affineAt hp.2.1 ((continuous_apply e).comp_continuousOn
      ((pwaffine H).1.mono fun α hα => hp.1.trans hα.1)) fun α hα => ?_
    have hpos : 0 < α := lt_of_le_of_lt hp.1 hα.1
    have hnot := hp.2.2.2.1 α hα
    simp only [BP, breakpoints, Set.mem_ofPred_eq, not_and, not_not] at hnot
    obtain ⟨ε, hε, A, W, hAW⟩ := hnot hpos
    exact ⟨ε, hε, A e, W e, fun α' hα' => by
      show bestResponse f m β α' e = _
      rw [hAW α' hα']
      ring⟩
  choose c d hcd using hcoord
  exact ⟨c, d, fun α hα => funext fun e => by rw [hcd e α hα]; ring⟩

/-! ### Event points (`lem:eventcount`) -/

/-- The inference of step (2) of the proof of `lem:eventcount` for one function: an affine function
`c + d α` that is nonnegative on `J` "vanishes either identically or nowhere in its interior" (not
in the paper: the STOC version draws this conclusion without proof). A zero `α₀` in the interior of
`J` has shares of `J` on both sides, at which `c + d α = d (α − α₀)` is nonnegative, so `d = 0`,
and then `c = 0`. -/
lemma zero_or_ne_of_nonneg {J : Set ℝ} {c d : ℝ} (hnn : ∀ α ∈ J, 0 ≤ c + d * α) :
    (∀ α ∈ interior J, c + d * α = 0) ∨ ∀ α ∈ interior J, c + d * α ≠ 0 := by
  by_cases h : ∃ α₀ ∈ interior J, c + d * α₀ = 0
  · left
    obtain ⟨α₀, hα₀, h0⟩ := h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior α₀ hα₀
    have hmem : ∀ s : ℝ, |s| < ε → α₀ + s ∈ J := fun s hs => interior_subset (hball (by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
      exact hs))
    have h1 := hnn _ (hmem (-(ε / 2)) (by rw [abs_neg, abs_of_pos (half_pos hε)]; linarith))
    have h2 := hnn _ (hmem (ε / 2) (by rw [abs_of_pos (half_pos hε)]; linarith))
    have hdε : d * ε = 0 := by linarith
    have hd : d = 0 := (mul_eq_zero.1 hdε).resolve_right hε.ne'
    intro α _
    rw [hd] at h0 ⊢
    linarith
  · right
    push Not at h
    exact h

/-- The root `−c/d` of `c + d α` (for `d ≠ 0`, its only zero). -/
noncomputable def root (c d : ℝ) : ℝ := -c / d

/-- Away from its root, an affine function is zero at all shares or at none: a nonconstant affine
function has at most one zero, its root, and a constant one is zero everywhere or nowhere. So an
affine function has at most one isolated zero (not in the paper: the STOC version leaves this
implicit in step (4) of the proof of `lem:eventcount`, "an isolated zero of some `ρ_e − ρ_g`, at
most `C(n, 2)` points per piece"). -/
lemma affine_zero_iff {c d α₁ α₂ : ℝ} (h1 : α₁ ≠ root c d) (h2 : α₂ ≠ root c d) :
    c + d * α₁ = 0 ↔ c + d * α₂ = 0 := by
  by_cases hd : d = 0
  · simp [hd]
  · have key : ∀ α, α ≠ root c d → c + d * α ≠ 0 := by
      intro α hα h
      apply hα
      unfold root
      field_simp
      linarith
    exact ⟨fun h => absurd h (key α₁ h1), fun h => absurd h (key α₂ h2)⟩

/-- Steps (2) to (4) of the proof of `lem:eventcount` for one piece `[a, b]`, whose interior is
`(a, b)`: (2) "Inside a piece, every `x*_e` and every `ρ_e` is nonnegative and affine, so each
vanishes either identically or nowhere in its interior" (`affine_on_piece`; `x*(α) ∈ P₊(f)`, and
`ρ(α) ≥ 0` by `prop:optchar`; `zero_or_ne_of_nonneg`); (3) "Hence the free elements and the zero
set are constant there," (4) "and the blocks change only at an isolated zero of some `ρ_e − ρ_g`,
at most `C(n, 2)` points per piece,": an isolated zero of the affine function `ρ_e − ρ_g` is the
root of a nonconstant one (`affine_zero_iff`), one for each pair `{e, g}`, so a set `K` of at most
`C(n, 2)` shares contains every event point in `(a, b)`. -/
theorem events_in_piece (H : Hyp f m β) {a b : ℝ} (hp : IsPiece f m β a b) :
    ∃ K : Finset ℝ, K.card ≤ (Fintype.card E).choose 2 ∧
      ∀ α ∈ Ioo a b, IsEvent f m β α → α ∈ K := by
  classical
  -- (2) "Inside a piece, every `x*_e` and every `ρ_e` is nonnegative and affine, so each vanishes
  -- either identically or nowhere in its interior": on the piece, `x*_e(α) = p_e + w_e α`
  -- (`affine_on_piece`) and `ρ_e(α) = α m_e − β_e x*_e(α) = cρ_e + dρ_e α`; `x*(α) ∈ P₊(f)`, and
  -- `ρ(α) ≥ 0` by `prop:optchar`.
  obtain ⟨p, w, hpw⟩ := affine_on_piece H hp
  set cρ : E → ℝ := fun e => -(β e * p e)
  set dρ : E → ℝ := fun e => m e - β e * w e
  have hrho : ∀ α ∈ Icc a b, ∀ e, rho f m β α e = cρ e + dρ e * α := by
    intro α hα e
    simp only [rho, marg, hpw α hα, cρ, dρ]
    ring
  have hx : ∀ α ∈ Icc a b, ∀ e, bestResponse f m β α e = p e + w e * α := by
    intro α hα e
    rw [hpw α hα]
    ring
  have h2x : ∀ e, (∀ α ∈ Ioo a b, p e + w e * α = 0) ∨ ∀ α ∈ Ioo a b, p e + w e * α ≠ 0 := by
    intro e
    have h := zero_or_ne_of_nonneg (J := Icc a b) fun α hα => by
      rw [← hx α hα e]
      exact (isBestResponse_bestResponse H.rank m β α).1.1 e
    rwa [interior_Icc] at h
  have h2ρ : ∀ e, (∀ α ∈ Ioo a b, cρ e + dρ e * α = 0) ∨
      ∀ α ∈ Ioo a b, cρ e + dρ e * α ≠ 0 := by
    intro e
    have h := zero_or_ne_of_nonneg (J := Icc a b) fun α hα => by
      rw [← hrho α hα e]
      exact (isBestResponse_bestResponse H.rank m β α).marg_nonneg H.beta
        (fun g => mul_nonneg (hp.1.trans hα.1) (H.reward g)) e
    rwa [interior_Icc] at h
  -- (3) "Hence the free elements and the zero set are constant there,"
  have h3 : ∀ {c d : ℝ}, ((∀ α ∈ Ioo a b, c + d * α = 0) ∨ ∀ α ∈ Ioo a b, c + d * α ≠ 0) →
      ∀ α ∈ Ioo a b, ∀ α' ∈ Ioo a b, (c + d * α = 0 ↔ c + d * α' = 0) := by
    rintro c d (h | h) α hα α' hα'
    · exact ⟨fun _ => h α' hα', fun _ => h α hα⟩
    · exact ⟨fun h0 => absurd h0 (h α hα), fun h0 => absurd h0 (h α' hα')⟩
  have h3free : ∀ α ∈ Ioo a b, ∀ α' ∈ Ioo a b, ∀ e,
      rho f m β α e = 0 ↔ rho f m β α' e = 0 := fun α hα α' hα' e => by
    rw [hrho α (Ioo_subset_Icc_self hα), hrho α' (Ioo_subset_Icc_self hα')]
    exact h3 (h2ρ e) α hα α' hα'
  have h3zero : ∀ α ∈ Ioo a b, ∀ α' ∈ Ioo a b, ∀ e,
      bestResponse f m β α e = 0 ↔ bestResponse f m β α' e = 0 := fun α hα α' hα' e => by
    rw [hx α (Ioo_subset_Icc_self hα), hx α' (Ioo_subset_Icc_self hα')]
    exact h3 (h2x e) α hα α' hα'
  -- (4) "and the blocks change only at an isolated zero of some `ρ_e − ρ_g`, at most `C(n, 2)`
  -- points per piece,": an isolated zero of the affine function `ρ_e − ρ_g` is the root of a
  -- nonconstant one, `dρ_e ≠ dρ_g` (`affine_zero_iff`), one for each unordered pair `{e, g}` (the
  -- set `K`).
  set rpair : E → E → ℝ := fun e g => root (cρ e - cρ g) (dρ e - dρ g)
  have hsymm : ∀ e g, rpair e g = rpair g e := by
    intro e g
    simp only [rpair, root]
    rw [show cρ g - cρ e = -(cρ e - cρ g) by ring, show dρ g - dρ e = -(dρ e - dρ g) by ring,
      neg_div_neg_eq]
  set K := (((univ : Finset E).offDiag.filter fun q => dρ q.1 ≠ dρ q.2).image
    (Function.uncurry Sym2.mk)).image (Sym2.lift ⟨rpair, hsymm⟩)
  refine ⟨K, ?_, ?_⟩
  · -- "at most `C(n, 2)` points per piece"
    refine card_image_le.trans ((Finset.card_le_card
      (Finset.image_subset_image (filter_subset _ _))).trans ?_)
    rw [Sym2.card_image_offDiag]
    simp
  · -- Away from `K`, the state is constant near `α`, so `α` is no event point.
    intro α hα hev
    by_contra hK
    -- A neighborhood of `α` in `(a, b)` that avoids `K`.
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.1 (Finset.finite_toSet K).isClosed.isOpen_compl α hK
    set δ := min ε (min (α - a) (b - α))
    have hδ : 0 < δ := lt_min hε (lt_min (by linarith [hα.1]) (by linarith [hα.2]))
    have hI : ∀ γ ∈ Ioo (α - δ) (α + δ), γ ∈ Ioo a b ∧ γ ∉ K := by
      intro γ hγ
      have k1 := min_le_left ε (min (α - a) (b - α))
      have k2 := min_le_right ε (min (α - a) (b - α))
      have k3 := min_le_left (α - a) (b - α)
      have k4 := min_le_right (α - a) (b - α)
      refine ⟨⟨by linarith [hγ.1], by linarith [hγ.2]⟩, hball ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hγ.1, hγ.2]
    have hconst : StateConstOn f m β (Ioo (α - δ) (α + δ)) := by
      -- the free set and the zero set, by (3)
      refine ⟨fun α₁ h₁ α₂ h₂ e => h3free α₁ (hI α₁ h₁).1 α₂ (hI α₂ h₂).1 e,
        fun α₁ h₁ α₂ h₂ e => h3zero α₁ (hI α₁ h₁).1 α₂ (hI α₂ h₂).1 e,
        fun α₁ h₁ α₂ h₂ e g => ?_⟩
      -- the blocks: `ρ_e − ρ_g` is zero at all shares of the neighborhood or at none, as it is
      -- constant, or nonconstant with its only zero in `K`
      by_cases heg : e = g
      · subst heg
        simp
      have hJ₁ := Ioo_subset_Icc_self (hI α₁ h₁).1
      have hJ₂ := Ioo_subset_Icc_self (hI α₂ h₂).1
      rw [hrho α₁ hJ₁, hrho α₂ hJ₂, hrho α₁ hJ₁, hrho α₂ hJ₂]
      have key : cρ e - cρ g + (dρ e - dρ g) * α₁ = 0 ↔
          cρ e - cρ g + (dρ e - dρ g) * α₂ = 0 := by
        by_cases hd : dρ e - dρ g = 0
        · simp [hd]
        · have hroot : root (cρ e - cρ g) (dρ e - dρ g) ∈ K := by
            refine Finset.mem_image.2 ⟨s(e, g), Finset.mem_image.2 ⟨(e, g), Finset.mem_filter.2
              ⟨Finset.mem_offDiag.2 ⟨Finset.mem_univ e, Finset.mem_univ g, heg⟩,
                sub_ne_zero.1 hd⟩, rfl⟩, rfl⟩
          exact affine_zero_iff (fun h => (hI α₁ h₁).2 (h ▸ hroot))
            (fun h => (hI α₂ h₂).2 (h ▸ hroot))
      constructor <;> intro h
      · have := key.1 (by linarith)
        linarith
      · have := key.2 (by linarith)
        linarith
    exact hev.2 _ _ (by linarith) (by linarith) (stateConstOn_iff.1 hconst)

/-- Step (1) of the proof of `lem:eventcount`: "The first claim follows from `lem:velocity`": on an
open interval with constant state around a share, `x*` is affine (`velocity_lemma`), so a breakpoint
is an event point. -/
theorem isEvent_of_mem_bp (H : Hyp f m β) {α : ℝ} (hα : α ∈ BP f m β) : IsEvent f m β α := by
  rw [isEvent_iff]
  refine ⟨hα.1, fun a b ha hb hS => hα.2 ?_⟩
  set a' := max a 0
  have ha' : a' < α := max_lt ha hα.1
  have hsub : Ioo a' b ⊆ Ioo a b := fun γ hγ => ⟨lt_of_le_of_lt (le_max_left _ _) hγ.1, hγ.2⟩
  have hS' : ∀ γ ∈ Ioo a' b, ∀ γ' ∈ Ioo a' b, state f m β γ = state f m β γ' :=
    fun γ hγ γ' hγ' => hS γ (hsub hγ) γ' (hsub hγ')
  have haff := (velocity_lemma H (le_max_right a 0) hS' ⟨ha', hb⟩).1
  have h1 := min_le_left (α - a') (b - α)
  have h2 := min_le_right (α - a') (b - α)
  refine ⟨min (α - a') (b - α), lt_min (by linarith) (by linarith),
    fun e => bestResponse f m β α e - α * velocity f m β α e, velocity f m β α,
    fun γ hγ => ?_⟩
  rw [haff γ ⟨by linarith [hγ.1], by linarith [hγ.2]⟩]
  funext e
  ring

/-- **`lem:eventcount`** (Lemma B.7, statement `stoc-sections/appB-quadratic.tex:387-390`, proof
:392-399): every breakpoint is an event point, and `(0, 1)` contains at most `B + (B + 1) C(n, 2)`
event points, where `B` is the number of breakpoints in `(0, 1)` (`numBP`) and `n = |E|`. Steps:
(1) "The first claim follows from `lem:velocity`" (`isEvent_of_mem_bp`); (2) "Inside a piece,
every `x*_e` and every `ρ_e` is nonnegative and affine, so each vanishes either identically or
nowhere in its interior"; (3) "Hence the free elements and the zero set are constant there,"
(4) "and the blocks change only at an isolated zero of some `ρ_e − ρ_g`, at most `C(n, 2)` points
per piece," ((2) to (4) for each piece: `events_in_piece`); (5) "in addition to the
breakpoints": an event point of `(0, 1)` is a breakpoint or lies in the interior of a piece, and
there are at most `B + 1` pieces (`appB-quadratic.tex:353`, `pieces_finite_ncard_le`), which gives
the bound. -/
theorem eventcount (H : Hyp f m β) :
    (∀ α ∈ BP f m β, IsEvent f m β α) ∧
      {α | α ∈ Ioo (0 : ℝ) 1 ∧ IsEvent f m β α}.Finite ∧
      {α | α ∈ Ioo (0 : ℝ) 1 ∧ IsEvent f m β α}.ncard ≤
        numBP f m β + (numBP f m β + 1) * (Fintype.card E).choose 2 := by
  classical
  -- (1) "The first claim follows from `lem:velocity`."
  have h1 : ∀ α ∈ BP f m β, IsEvent f m β α := fun α hα => isEvent_of_mem_bp H hα
  -- (2) "Inside a piece, every `x*_e` and every `ρ_e` is nonnegative and affine, so each vanishes
  -- either identically or nowhere in its interior." (3) "Hence the free elements and the zero set
  -- are constant there," (4) "and the blocks change only at an isolated zero of some `ρ_e − ρ_g`,
  -- at most `C(n, 2)` points per piece,": for each piece `P = [a, b]`, a set `K_P` of at most
  -- `C(n, 2)` shares that contains the event points of `(a, b)` (`events_in_piece`).
  set c := (Fintype.card E).choose 2
  have h24 : ∀ P ∈ pieces f m β, ∃ K : Finset ℝ, K.card ≤ c ∧
      ∀ α ∈ interior P, IsEvent f m β α → α ∈ K := by
    intro P hP
    obtain ⟨a, b, hp, rfl⟩ := (mem_pieces_iff H).1 hP
    obtain ⟨K, hK, hKev⟩ := events_in_piece H hp
    exact ⟨K, hK, fun α hα hev => hKev α (by rwa [interior_Icc] at hα) hev⟩
  choose! Kp hKp using h24
  -- (5) "in addition to the breakpoints": an event point of `(0, 1)` is a breakpoint or lies in
  -- the interior of a piece, the closure of its connected component of the non-breakpoint shares;
  -- and there are at most `B + 1` pieces.
  obtain ⟨hPfin, hPcard⟩ := pieces_finite_ncard_le H
  set Pf := hPfin.toFinset
  set T := ((bp_finite H).inter_of_left (Ioo 0 1)).toFinset ∪ Pf.biUnion Kp
  have hsub : {α | α ∈ Ioo (0 : ℝ) 1 ∧ IsEvent f m β α} ⊆ ↑T := by
    rintro α ⟨hα, hev⟩
    by_cases hbp : α ∈ BP f m β
    · exact Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 ⟨hbp, hα⟩)
    · have hαN : α ∈ nonBP f m β := ⟨hα, hbp⟩
      obtain ⟨a, b, -, hαab, hC⟩ := connectedComponentIn_nonBP H hαN
      have hP : closure (connectedComponentIn (nonBP f m β) α) ∈ pieces f m β := ⟨α, hαN, rfl⟩
      have hint : α ∈ interior (closure (connectedComponentIn (nonBP f m β) α)) := by
        rw [hC, closure_Ioo (ne_of_lt (hαab.1.trans hαab.2)), interior_Icc]
        exact hαab
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨_, (Set.Finite.mem_toFinset _).2 hP, (hKp _ hP).2 α hint hev⟩)
  refine ⟨h1, (T.finite_toSet).subset hsub, ?_⟩
  have hPf : Pf.card ≤ numBP f m β + 1 := by
    rw [← Set.ncard_eq_toFinset_card _ hPfin]
    exact hPcard
  calc {α | α ∈ Ioo (0 : ℝ) 1 ∧ IsEvent f m β α}.ncard ≤ (↑T : Set ℝ).ncard :=
        Set.ncard_le_ncard hsub T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ ((bp_finite H).inter_of_left (Ioo 0 1)).toFinset.card + (Pf.biUnion Kp).card :=
        card_union_le _ _
    _ ≤ numBP f m β + ∑ P ∈ Pf, (Kp P).card := by
        gcongr
        · rw [numBP, Set.ncard_eq_toFinset_card _ ((bp_finite H).inter_of_left _)]
        · exact card_biUnion_le
    _ ≤ numBP f m β + ∑ _P ∈ Pf, c := by
        gcongr with P hP
        exact (hKp P ((Set.Finite.mem_toFinset _).1 hP)).1
    _ = numBP f m β + Pf.card * c := by rw [sum_const, smul_eq_mul]
    _ ≤ numBP f m β + (numBP f m β + 1) * c := by gcongr

end Tracing

end Stoc
