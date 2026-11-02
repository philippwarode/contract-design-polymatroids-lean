-- stamp r9 2026-11-02
import Mathlib

/-!
# Arrangements of lines and strict upper sets of a pencil

The cells of an arrangement of `n` lines in the `(α, θ)`-plane, which the second paragraph of the
proof of `thm:expbp` (`stoc-sections/appB-quadratic.tex:574-583`) counts, and the bound
`1 + n + C(n, 2)` on their number, which the paper uses without proof (`cells_finite_ncard_le`,
not in the paper). The bound is proved through the strict upper sets of a pencil of `n` lines:
they number at most `1 + n + C(n, 2)` (`card_pencilUpper_le`), counted by induction on the ground
set, as adding an element `e₀` adds at most one set for each of the at most `n` open intervals into
which the crossing points of the line of `e₀` with the other lines cut the real line; and the set
of lines above a point of a cell is a strict upper set of the pencil `e ↦ c_e + d_e α` at its first
coordinate (`above_mem_pencilUpper`), which determines the cell (`connectedComponentIn_eq`). The
proof of `thm:expbp` also uses that this set is the same at all points of a cell
(`above_eq_of_mem_cell`, not in the paper). All other declarations of this file are parts of the
proofs of these two lemmas.

Taken over on 2026-10-20 from `Paper/Subclasses/LevelSetClasses.lean` (the paper at Overleaf
f035b19), only its part on pencils, for the STOC version (`stoc.tex`); from then on this copy
follows the STOC version.
-/

namespace Stoc

open Finset

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### Strict upper sets of a pencil of lines -/

/-- `A ⊆ D` is a strict upper set of `h` in `D`: every element of `A` has a larger value than every
element of `D ∖ A`. -/
def StrictUpper (D : Finset E) (h : E → ℝ) (A : Finset E) : Prop :=
  A ⊆ D ∧ ∀ e ∈ A, ∀ e' ∈ D, e' ∉ A → h e' < h e

open Classical in
/-- The strict upper sets in `D` of the functions `e ↦ t_e − λ b_e`, `λ ∈ ℝ`. -/
def pencilUpper (t b : E → ℝ) (D : Finset E) : Finset (Finset E) :=
  D.powerset.filter fun A => ∃ l : ℝ, StrictUpper D (fun e => t e - l * b e) A

omit [Fintype E] [DecidableEq E] in
/-- An affine function that is positive at two points is positive between them. -/
theorem affine_pos_of_mem_uIcc {c d l₁ l₂ l : ℝ} (h₁ : 0 < c - l₁ * d) (h₂ : 0 < c - l₂ * d)
    (hl : l ∈ Set.uIcc l₁ l₂) : 0 < c - l * d := by
  rcases Set.mem_uIcc.1 hl with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases le_total 0 d with hd | hd <;>
    nlinarith

omit [Fintype E] in
/-- If `B` and `B ∪ {e₀}` are strict upper sets of the pencil in `D ∪ {e₀}`, possibly for different
`λ`, then they are so for a common `λ`. -/
theorem exists_common_strictUpper {t b : E → ℝ} {D B : Finset E} {e₀ : E} (he₀ : e₀ ∉ D)
    (heB : e₀ ∉ B) {l₁ l₂ : ℝ} (h₁ : StrictUpper (insert e₀ D) (fun e => t e - l₁ * b e) B)
    (h₂ : StrictUpper (insert e₀ D) (fun e => t e - l₂ * b e) (insert e₀ B)) :
    ∃ l, StrictUpper (insert e₀ D) (fun e => t e - l * b e) B ∧
      StrictUpper (insert e₀ D) (fun e => t e - l * b e) (insert e₀ B) := by
  have hBD : B ⊆ D := fun x hx => by
    rcases mem_insert.1 (h₁.1 hx) with rfl | h
    · exact absurd hx heB
    · exact h
  have hne : ∀ y ∈ D, y ≠ e₀ := fun y hy h => he₀ (h ▸ hy)
  -- `B` is a strict upper set in `D` at `l₁` and `l₂`, hence between them.
  have hQ : ∀ l ∈ Set.uIcc l₁ l₂, ∀ x ∈ B, ∀ y ∈ D, y ∉ B → t y - l * b y < t x - l * b x := by
    intro l hl x hx y hy hyB
    have e1 := h₁.2 x hx y (mem_insert_of_mem hy) hyB
    have e2 := h₂.2 x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
      (by rw [mem_insert, not_or]; exact ⟨hne y hy, hyB⟩)
    have := affine_pos_of_mem_uIcc (c := t x - t y) (d := b x - b y) (by linarith)
      (by linarith) hl
    linarith
  -- `e₀` lies above `D ∖ B` on `U` and below `B` on `V`.
  set U : Set ℝ := ⋂ y ∈ D \ B, {l | t y - l * b y < t e₀ - l * b e₀}
  set V : Set ℝ := ⋂ x ∈ B, {l | t e₀ - l * b e₀ < t x - l * b x}
  have hcont : ∀ y, Continuous fun l : ℝ => t y - l * b y := fun y => by fun_prop
  have hU : IsOpen U := isOpen_biInter_finset fun y _ => isOpen_lt (hcont y) (hcont e₀)
  have hV : IsOpen V := isOpen_biInter_finset fun x _ => isOpen_lt (hcont e₀) (hcont x)
  have hl₂U : l₂ ∈ U := by
    simp only [U, Set.mem_iInter₂, Set.mem_ofPred_eq]
    intro y hy
    rw [Finset.mem_sdiff] at hy
    exact h₂.2 e₀ (mem_insert_self _ _) y (mem_insert_of_mem hy.1)
      (by rw [mem_insert, not_or]; exact ⟨hne y hy.1, hy.2⟩)
  have hl₁V : l₁ ∈ V := by
    simp only [V, Set.mem_iInter₂, Set.mem_ofPred_eq]
    intro x hx
    exact h₁.2 x hx e₀ (mem_insert_self _ _) heB
  have hcover : Set.uIcc l₁ l₂ ⊆ U ∪ V := by
    intro l hl
    by_contra hUV
    rw [Set.mem_union, not_or] at hUV
    simp only [U, V, Set.mem_iInter₂, Set.mem_ofPred_eq, not_forall, not_lt] at hUV
    obtain ⟨⟨y, hy, hy'⟩, ⟨x, hx, hx'⟩⟩ := hUV
    rw [Finset.mem_sdiff] at hy
    have := hQ l hl x hx y hy.1 hy.2
    linarith
  obtain ⟨l, hl, hlU, hlV⟩ := isPreconnected_uIcc U V hU hV hcover
    ⟨l₂, Set.right_mem_uIcc, hl₂U⟩ ⟨l₁, Set.left_mem_uIcc, hl₁V⟩
  simp only [U, V, Set.mem_iInter₂, Set.mem_ofPred_eq] at hlU hlV
  refine ⟨l, ⟨h₁.1, fun x hx y hy hyB => ?_⟩,
    ⟨insert_subset_insert e₀ hBD, fun x hx y hy hyB => ?_⟩⟩
  · rcases mem_insert.1 hy with rfl | hy
    · exact hlV x hx
    · exact hQ l hl x hx y hy hyB
  · rw [mem_insert, not_or] at hyB
    have hyD : y ∈ D := by
      rcases mem_insert.1 hy with h | h
      · exact absurd h hyB.1
      · exact h
    rcases mem_insert.1 hx with rfl | hx
    · exact hlU y (Finset.mem_sdiff.2 ⟨hyD, hyB.2⟩)
    · exact hQ l hl x hx y hyD hyB.2

omit [Fintype E] in
/-- The strict upper sets of a pencil of `n` lines number at most `1 + n + C(n, 2)`. -/
theorem card_pencilUpper_le (t b : E → ℝ) (D : Finset E) :
    (pencilUpper t b D).card ≤ 1 + D.card + D.card.choose 2 := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    have : pencilUpper t b ∅ ⊆ {∅} := by
      intro A hA
      simp only [pencilUpper, mem_filter, mem_powerset, subset_empty] at hA
      simp [hA.1]
    simpa using card_le_card this
  | insert e₀ D he₀ ih =>
    set X := pencilUpper t b (insert e₀ D)
    set Y := pencilUpper t b D
    have hmemX : ∀ A, A ∈ X ↔ A ⊆ insert e₀ D ∧
        ∃ l : ℝ, StrictUpper (insert e₀ D) (fun e => t e - l * b e) A := by
      intro A
      simp only [X, pencilUpper, mem_filter, mem_powerset]
    have hmemY : ∀ A, A ∈ Y ↔ A ⊆ D ∧ ∃ l : ℝ, StrictUpper D (fun e => t e - l * b e) A := by
      intro A
      simp only [Y, pencilUpper, mem_filter, mem_powerset]
    have hne : ∀ y ∈ D, y ≠ e₀ := fun y hy h => he₀ (h ▸ hy)
    -- Removing `e₀` from the ground set keeps strict upper sets.
    have hrestr : ∀ A ∈ X, A.erase e₀ ∈ Y := by
      intro A hA
      obtain ⟨hAD, l, hl⟩ := (hmemX A).1 hA
      have hsub : A.erase e₀ ⊆ D := fun x hx => by
        rcases mem_insert.1 (hAD (mem_of_mem_erase hx)) with h | h
        · exact absurd h (ne_of_mem_erase hx)
        · exact h
      refine (hmemY _).2 ⟨hsub, l, hsub, fun x hx y hy hyA => ?_⟩
      exact hl.2 x (mem_of_mem_erase hx) y (mem_insert_of_mem hy)
        (fun h => hyA (mem_erase.2 ⟨hne y hy, h⟩))
    set X₁ := X.filter fun A => e₀ ∉ A
    set X₂ := X.filter fun A => e₀ ∈ A
    set I₁ := X₁.image fun A => A.erase e₀
    set I₂ := X₂.image fun A => A.erase e₀
    have hI₁ : I₁.card = X₁.card := by
      refine card_image_of_injOn fun A hA A' hA' h => ?_
      simp only [X₁, coe_filter, Set.mem_ofPred_eq] at hA hA'
      simpa [erase_eq_of_notMem hA.2, erase_eq_of_notMem hA'.2] using h
    have hI₂ : I₂.card = X₂.card := by
      refine card_image_of_injOn fun A hA A' hA' h => ?_
      simp only [X₂, coe_filter, Set.mem_ofPred_eq] at hA hA'
      exact erase_injOn' e₀ hA.2 hA'.2 h
    have hIY : I₁ ∪ I₂ ⊆ Y := by
      intro B hB
      rcases mem_union.1 hB with hB | hB <;>
      · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
        exact hrestr A (mem_filter.1 hA).1
    -- The overlap: `B` and `B ∪ {e₀}` are both strict upper sets, hence for a common `λ`.
    have hcommon : ∀ B ∈ I₁ ∩ I₂, ∃ l, StrictUpper (insert e₀ D) (fun e => t e - l * b e) B ∧
        StrictUpper (insert e₀ D) (fun e => t e - l * b e) (insert e₀ B) := by
      intro B hB
      obtain ⟨hB₁, hB₂⟩ := mem_inter.1 hB
      obtain ⟨A₁, hA₁, rfl⟩ := mem_image.1 hB₁
      obtain ⟨A₂, hA₂, hA₂B⟩ := mem_image.1 hB₂
      obtain ⟨hA₁X, hA₁e⟩ := mem_filter.1 hA₁
      obtain ⟨hA₂X, hA₂e⟩ := mem_filter.1 hA₂
      rw [erase_eq_of_notMem hA₁e] at hA₂B ⊢
      obtain ⟨-, l₁, hl₁⟩ := (hmemX A₁).1 hA₁X
      obtain ⟨-, l₂, hl₂⟩ := (hmemX A₂).1 hA₂X
      have hA₂' : A₂ = insert e₀ A₁ := by
        rw [← hA₂B, insert_erase hA₂e]
      rw [hA₂'] at hl₂
      exact exists_common_strictUpper he₀ hA₁e hl₁ hl₂
    choose! L hL using hcommon
    -- The crossing points of the line of `e₀` with the other lines.
    set R : Finset ℝ := (D.filter fun x => b x ≠ b e₀).image
      fun x => (t x - t e₀) / (b x - b e₀)
    have hR : R.card ≤ D.card := card_image_le.trans (card_filter_le _ _)
    -- On the overlap, `B` is determined by the number of crossing points below its `λ`.
    have hside : ∀ B ∈ I₁ ∩ I₂, ∀ x ∈ D,
        (x ∈ B → t e₀ - L B * b e₀ < t x - L B * b x) ∧
          (x ∉ B → t x - L B * b x < t e₀ - L B * b e₀) := by
      intro B hB x hx
      obtain ⟨h1, h2⟩ := hL B hB
      have heB : e₀ ∉ B := fun h => by
        obtain ⟨A, hA, rfl⟩ := mem_image.1 (mem_inter.1 hB).1
        exact (mem_filter.1 hA).2 (mem_of_mem_erase h)
      refine ⟨fun hxB => h1.2 x hxB e₀ (mem_insert_self _ _) heB, fun hxB => ?_⟩
      exact h2.2 e₀ (mem_insert_self _ _) x (mem_insert_of_mem hx)
        (by rw [mem_insert, not_or]; exact ⟨hne x hx, hxB⟩)
    have hsubD : ∀ B ∈ I₁ ∩ I₂, B ⊆ D := fun B hB => (hmemY B).1 (hIY (mem_union_left _
      (mem_inter.1 hB).1)) |>.1
    have hkey : ∀ B ∈ I₁ ∩ I₂, ∀ B' ∈ I₁ ∩ I₂, L B ≤ L B' →
        (R.filter (· < L B)).card = (R.filter (· < L B')).card → B = B' := by
      intro B hB B' hB' hle hcard
      have hfeq : R.filter (· < L B) = R.filter (· < L B') :=
        eq_of_subset_of_card_le (fun r hr => by
          rw [mem_filter] at hr ⊢
          exact ⟨hr.1, lt_of_lt_of_le hr.2 hle⟩) hcard.ge
      -- No crossing point lies strictly between the two shares.
      have hnone : ∀ x ∈ D, b x ≠ b e₀ → ¬ (L B < (t x - t e₀) / (b x - b e₀) ∧
          (t x - t e₀) / (b x - b e₀) < L B') := by
        rintro x hx hb ⟨h1, h2⟩
        have hr : (t x - t e₀) / (b x - b e₀) ∈ R :=
          mem_image.2 ⟨x, mem_filter.2 ⟨hx, hb⟩, rfl⟩
        have : (t x - t e₀) / (b x - b e₀) ∈ R.filter (· < L B') := mem_filter.2 ⟨hr, h2⟩
        rw [← hfeq, mem_filter] at this
        exact lt_irrefl _ (lt_trans h1 this.2)
      ext x
      by_cases hx : x ∈ D
      · obtain ⟨hin, hout⟩ := hside B hB x hx
        obtain ⟨hin', hout'⟩ := hside B' hB' x hx
        constructor
        · intro hxB
          by_contra hxB'
          have i1 := hin hxB
          have i2 := hout' hxB'
          -- `x` crosses `e₀` between `L B` and `L B'`.
          have hd : 0 < b x - b e₀ := by nlinarith
          refine hnone x hx (by linarith) ⟨?_, ?_⟩
          · rw [lt_div_iff₀ hd]; linarith
          · rw [div_lt_iff₀ hd]; linarith
        · intro hxB'
          by_contra hxB
          have i1 := hout hxB
          have i2 := hin' hxB'
          have hd : b x - b e₀ < 0 := by nlinarith
          refine hnone x hx (by linarith) ⟨?_, ?_⟩
          · rw [lt_div_iff_of_neg hd]; linarith
          · rw [div_lt_iff_of_neg hd]; linarith
      · exact ⟨fun h => absurd (hsubD B hB h) hx, fun h => absurd (hsubD B' hB' h) hx⟩
    have hover : (I₁ ∩ I₂).card ≤ D.card + 1 := by
      calc (I₁ ∩ I₂).card ≤ (range (R.card + 1)).card := by
            refine card_le_card_of_injOn (fun B => (R.filter (· < L B)).card) ?_ ?_
            · intro B _
              simp only [coe_range, Set.mem_Iio]
              exact Nat.lt_succ_of_le (card_filter_le _ _)
            · intro B hB B' hB' h
              rcases le_total (L B) (L B') with hle | hle
              · exact hkey B hB B' hB' hle h
              · exact (hkey B' hB' B hB hle h.symm).symm
        _ ≤ D.card + 1 := by rw [card_range]; omega
    have hsplit : X₂.card + X₁.card = X.card := card_filter_add_card_filter_not _
    have hunion := card_union_add_card_inter I₁ I₂
    have hY : (I₁ ∪ I₂).card ≤ Y.card := card_le_card hIY
    have hch : (D.card + 1).choose 2 = D.card + D.card.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [card_insert_of_notMem he₀, hch]
    omega


/-! ### Arrangements of lines and their cells

The cells of the arrangement of the lines `ℓ_e = {(α, θ) | θ = c_e + d_e α}` in the `(α, θ)`-plane,
which the proof of `thm:expbp` (`stoc-sections/appB-quadratic.tex:574-583`) counts, are the
connected components of the complement of the lines (`cells`). A point off the lines lies above or
below each line, and the set of lines above it (`above`) is the same on a cell
(`above_eq_of_mem_cell`). The bound `1 + n + C(n, 2)` on the number of cells, which the paper uses
without proof, is `cells_finite_ncard_le`: a cell is the set of points with a given set of lines
above them (`connectedComponentIn_eq`), and these sets are strict upper sets of the pencil
`e ↦ c_e + d_e α` (`above_mem_pencilUpper`). -/

section Arrangement

/-- The complement of the union of the lines `ℓ_e = {(α, θ) | θ = c_e + d_e α}`. -/
def offLines (c d : E → ℝ) : Set (ℝ × ℝ) := {p | ∀ e, p.2 ≠ c e + d e * p.1}

/-- The cells of the arrangement of the lines `ℓ_e`: the connected components of the complement of
their union. -/
def cells (c d : E → ℝ) : Set (Set (ℝ × ℝ)) :=
  {C | ∃ p ∈ offLines c d, C = connectedComponentIn (offLines c d) p}

/-- The lines `ℓ_e` that pass through or above the point `p`. -/
def above (c d : E → ℝ) (p : ℝ × ℝ) : Finset E := univ.filter fun e => p.2 ≤ c e + d e * p.1

/-- The points off the lines below exactly the lines of `A`. -/
def signRegion (c d : E → ℝ) (A : Finset E) : Set (ℝ × ℝ) :=
  {q | q ∈ offLines c d ∧ above c d q = A}

variable {c d : E → ℝ}

omit [DecidableEq E] in
/-- A point off the lines lies strictly below the lines above it and strictly above the others. -/
lemma lt_of_mem_above {p : ℝ × ℝ} (hp : p ∈ offLines c d) (e : E) :
    (e ∈ above c d p → p.2 < c e + d e * p.1) ∧ (e ∉ above c d p → c e + d e * p.1 < p.2) := by
  simp only [above, mem_filter, mem_univ, true_and, not_le]
  exact ⟨fun h => lt_of_le_of_ne h (hp e), id⟩

omit [DecidableEq E] in
/-- On a cell, the set of lines above a point is constant: a line that is above one point of a
connected set off the lines and below another one would meet the set (not in the paper: the proof of
`thm:expbp` leaves implicit that all points of a cell have the same set of lines through or above
them). -/
lemma above_eq_of_mem_cell {p q : ℝ × ℝ} (hp : p ∈ offLines c d)
    (hq : q ∈ connectedComponentIn (offLines c d) p) : above c d q = above c d p := by
  set C := connectedComponentIn (offLines c d) p
  have hC : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCU : C ⊆ offLines c d := connectedComponentIn_subset _ _
  have hpC : p ∈ C := mem_connectedComponentIn hp
  ext e
  have hφ : ContinuousOn (fun r : ℝ × ℝ => c e + d e * r.1 - r.2) C := by fun_prop
  have hne : ∀ r ∈ C, c e + d e * r.1 - r.2 ≠ 0 := fun r hr h => (hCU hr) e (by linarith)
  simp only [above, mem_filter, mem_univ, true_and]
  constructor
  · intro hqe
    by_contra hpe
    rw [not_le] at hpe
    obtain ⟨r, hr, hr0⟩ := hC.intermediate_value hpC hq hφ
      (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by linarith, by linarith⟩)
    exact hne r hr hr0
  · intro hpe
    by_contra hqe
    rw [not_le] at hqe
    have hp' := lt_of_le_of_ne hpe (hp e)
    obtain ⟨r, hr, hr0⟩ := hC.intermediate_value hq hpC hφ
      (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by linarith, by linarith⟩)
    exact hne r hr hr0

lemma signRegion_eq (A : Finset E) : signRegion c d A =
    {q | ∀ e, (e ∈ A → q.2 < c e + d e * q.1) ∧ (e ∉ A → c e + d e * q.1 < q.2)} := by
  ext q
  simp only [signRegion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hq, rfl⟩ e
    exact lt_of_mem_above hq e
  · intro h
    refine ⟨fun e he => ?_, ?_⟩
    · by_cases heA : e ∈ A
      · exact (ne_of_lt ((h e).1 heA)) (by rw [he])
      · exact (ne_of_lt ((h e).2 heA)) (by rw [he])
    · ext e
      simp only [above, mem_filter, mem_univ, true_and]
      by_cases heA : e ∈ A
      · exact ⟨fun _ => heA, fun _ => ((h e).1 heA).le⟩
      · exact ⟨fun h' => absurd h' (not_le.2 ((h e).2 heA)), fun h' => absurd h' heA⟩

/-- The points below exactly the lines of `A` form a convex set, an intersection of open
half-planes. -/
lemma convex_signRegion (A : Finset E) : Convex ℝ (signRegion c d A) := by
  rw [signRegion_eq]
  intro q₁ h₁ q₂ h₂ a b ha hb hab e
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have key : c e + d e * (a * q₁.1 + (1 - a) * q₂.1) =
      a * (c e + d e * q₁.1) + (1 - a) * (c e + d e * q₂.1) := by ring
  rw [key]
  refine ⟨fun he => ?_, fun he => ?_⟩
  · have e1 := (h₁ e).1 he
    have e2 := (h₂ e).1 he
    rcases ha.lt_or_eq with ha' | rfl
    · have := mul_lt_mul_of_pos_left e1 ha'
      have := mul_le_mul_of_nonneg_left e2.le hb
      linarith
    · simpa using e2
  · have e1 := (h₁ e).2 he
    have e2 := (h₂ e).2 he
    rcases ha.lt_or_eq with ha' | rfl
    · have := mul_lt_mul_of_pos_left e1 ha'
      have := mul_le_mul_of_nonneg_left e2.le hb
      linarith
    · simpa using e2

/-- A cell is the set of points off the lines with the same lines above them. -/
lemma connectedComponentIn_eq {p : ℝ × ℝ} (hp : p ∈ offLines c d) :
    connectedComponentIn (offLines c d) p = signRegion c d (above c d p) := by
  apply Set.Subset.antisymm
  · intro q hq
    exact ⟨connectedComponentIn_subset _ _ hq, above_eq_of_mem_cell hp hq⟩
  · exact (convex_signRegion _).isPreconnected.subset_connectedComponentIn ⟨hp, rfl⟩
      fun q hq => hq.1

omit [DecidableEq E] in
/-- The set of lines above a point off the lines is a strict upper set of the pencil
`e ↦ c_e + d_e α` at its first coordinate. -/
lemma above_mem_pencilUpper {p : ℝ × ℝ} (hp : p ∈ offLines c d) :
    above c d p ∈ pencilUpper c (fun e => -d e) univ := by
  classical
  simp only [pencilUpper, mem_filter, mem_powerset]
  refine ⟨subset_univ _, p.1, subset_univ _, fun e he e' _ he' => ?_⟩
  have h1 := (lt_of_mem_above hp e).1 he
  have h2 := (lt_of_mem_above hp e').2 he'
  linarith

/-- The number of cells of an arrangement of `n` lines (not in the paper: the proof of `thm:expbp`
uses without proof that `n` lines cut the plane into at most `1 + n + C(n, 2) = 1 + n(n + 1)/2`
cells). -/
theorem cells_finite_ncard_le (c d : E → ℝ) :
    (cells c d).Finite ∧ (cells c d).ncard ≤ 1 + Fintype.card E + (Fintype.card E).choose 2 := by
  classical
  set P := pencilUpper c (fun e => -d e) univ
  have hsub : cells c d ⊆ ↑(P.image (signRegion c d)) := by
    rintro C ⟨p, hp, rfl⟩
    rw [connectedComponentIn_eq hp]
    exact mem_coe.2 (mem_image_of_mem _ (above_mem_pencilUpper hp))
  refine ⟨(finite_toSet _).subset hsub, ?_⟩
  calc (cells c d).ncard ≤ (↑(P.image (signRegion c d)) : Set (Set (ℝ × ℝ))).ncard :=
        Set.ncard_le_ncard hsub (finite_toSet _)
    _ = (P.image (signRegion c d)).card := Set.ncard_coe_finset _
    _ ≤ P.card := card_image_le
    _ ≤ 1 + Fintype.card E + (Fintype.card E).choose 2 := by
        have := card_pencilUpper_le c (fun e => -d e) univ
        rwa [card_univ] at this

end Arrangement


end

end Stoc
