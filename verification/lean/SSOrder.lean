/-
  SSOrder.lean — order-theoretic lemmas underlying the manuscript
  "A Lifting Criterion for Subalgebra Bases beyond Term Orders and Integral
  Domains", formalized in core Lean 4 (v4.15.0) WITHOUT Mathlib.

  Scope: only the monoid/order layer of the paper is formalized here
  (standing hypotheses of §1.3, the degree bookkeeping in Lemma 2.6(i),
  cancellativity in the proof of Theorem 3.3, the least-element and
  antichain steps of Lemma 3.8, the descent arguments behind Lemma 2.9,
  the choice of a minimal Ω in Theorem 3.3, and the descent step of the
  referee's termination argument for Algorithm 1).  Graded rings,
  polynomial rings, kernels and liftings are NOT formalized.

  Check with:  lean SSOrder.lean     (no output = success)
-/

namespace SS

/-- A commutative monoid with a strict total order such that
    `a < b → a + c < b + c` (the standing hypothesis of §1.3). -/
class OrdMonoid (Γ : Type) extends Add Γ, Zero Γ, LT Γ where
  add_assoc : ∀ a b c : Γ, a + b + c = a + (b + c)
  add_comm  : ∀ a b : Γ, a + b = b + a
  zero_add  : ∀ a : Γ, 0 + a = a
  lt_irrefl : ∀ a : Γ, ¬ a < a
  lt_trans  : ∀ a b c : Γ, a < b → b < c → a < c
  lt_trichotomy : ∀ a b : Γ, a < b ∨ a = b ∨ b < a
  add_lt_add_right : ∀ a b c : Γ, a < b → a + c < b + c

variable {Γ : Type} [OrdMonoid Γ]
open OrdMonoid

/-- `a ≼ b` means `a < b ∨ a = b`. -/
def le (a b : Γ) : Prop := a < b ∨ a = b

theorem add_zero' (a : Γ) : a + 0 = a := by
  rw [add_comm]; exact zero_add a

theorem add_lt_add_left {a b : Γ} (c : Γ) (h : a < b) : c + a < c + b := by
  rw [add_comm c a, add_comm c b]; exact add_lt_add_right a b c h

/-- Cancellativity (used in the proof of Theorem 3.3, (⇐)). -/
theorem add_right_cancel {a b c : Γ} (h : a + c = b + c) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := add_lt_add_right a b c hab
    rw [h] at this; exact absurd this (lt_irrefl _)
  · exact hab
  · have := add_lt_add_right b a c hab
    rw [h] at this; exact absurd this (lt_irrefl _)

theorem le_lt_trans {a b c : Γ} (h₁ : le a b) (h₂ : b < c) : a < c := by
  rcases h₁ with h | h
  · exact lt_trans _ _ _ h h₂
  · rw [h]; exact h₂

theorem lt_le_trans {a b c : Γ} (h₁ : a < b) (h₂ : le b c) : a < c := by
  rcases h₂ with h | h
  · exact lt_trans _ _ _ h₁ h
  · rw [← h]; exact h₁

theorem add_le_add_left {a b : Γ} (c : Γ) (h : le a b) : le (c + a) (c + b) := by
  rcases h with h | h
  · exact Or.inl (add_lt_add_left c h)
  · exact Or.inr (by rw [h])

/-- Strict + weak gives strict. -/
theorem add_lt_add_of_lt_of_le {a b c d : Γ} (h₁ : a < b) (h₂ : le c d) :
    a + c < b + d :=
  lt_le_trans (add_lt_add_right a b c h₁) (add_le_add_left b h₂)

/-! ### Lemma 2.6(i): degree bookkeeping in a product of homogeneous parts -/

/-- Pointwise relation between two lists of equal length (core Lean 4 has no
    `Forall2` without Mathlib/Batteries). -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a b xs ys} : R a b → Forall2 R xs ys → Forall2 R (a :: xs) (b :: ys)

/-- Sum of a list of degrees. -/
def lsum : List Γ → Γ
  | [] => 0
  | x :: xs => x + lsum xs

/-- If `δ_k ≼ υ_k` for every factor, then `∑ δ_k ≺ ∑ υ_k` unless the two lists
    coincide.  This is the step "replacing δ_k by υ(g_k) never decreases the
    sum and strictly increases it whenever δ_k < υ(g_k)" in Lemma 2.6(i). -/
theorem lsum_lt_or_eq :
    ∀ (l₁ l₂ : List Γ), Forall2 le l₁ l₂ → lsum l₁ < lsum l₂ ∨ l₁ = l₂
  | [], [], _ => Or.inr rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: xs, b :: ys, h => by
    cases h with
    | cons hab hrest =>
      have ih := lsum_lt_or_eq xs ys hrest
      have hle : le (lsum xs) (lsum ys) := by
        rcases ih with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [h'])
      rcases hab with hab | hab
      · exact Or.inl (add_lt_add_of_lt_of_le hab hle)
      · rcases ih with h' | h'
        · left; show a + lsum xs < b + lsum ys
          rw [hab]; exact add_lt_add_left b h'
        · right; rw [hab, h']

/-- Consequence: the product has no component above the formal degree. -/
theorem lsum_le_of_forall2 (l₁ l₂ : List Γ) (h : Forall2 le l₁ l₂) :
    le (lsum l₁) (lsum l₂) := by
  rcases lsum_lt_or_eq l₁ l₂ h with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by rw [h'])

/-! ### Well-ordered monoids: 0 is the least element (proof of Lemma 3.8) -/


/-- In a well-ordered compatible monoid nothing lies below `0`. -/
theorem not_lt_zero (wf : WellFounded (fun a b : Γ => a < b)) : ∀ a : Γ, ¬ a < 0 := by
  intro a
  refine WellFounded.induction (C := fun a => ¬ a < 0) wf a ?_
  intro a ih ha
  -- a + a < 0 + a = a, and a + a < a < 0
  have h1 : a + a < a := by
    have := add_lt_add_right a 0 a ha
    rwa [zero_add] at this
  exact ih (a + a) h1 (lt_trans _ _ _ h1 ha)

/-- `0 ≼ a` for every `a`. -/
theorem zero_le (wf : WellFounded (fun a b : Γ => a < b)) (a : Γ) : le 0 a := by
  rcases lt_trichotomy 0 a with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (not_lt_zero wf a)

/-! ### Lemma 3.8: formal degrees are strictly monotone (antichain step) -/

/-- `n • d`. -/
def nsmul : Nat → Γ → Γ
  | 0, _ => 0
  | n + 1, d => d + nsmul n d

theorem lt_add_of_pos {a d : Γ} (hd : 0 < d) : a < d + a := by
  have := add_lt_add_right 0 d a hd
  rwa [zero_add] at this

theorem nsmul_lt_succ {d : Γ} (hd : 0 < d) (n : Nat) : nsmul n d < nsmul (n + 1) d :=
  lt_add_of_pos hd

theorem nsmul_strictMono {d : Γ} (hd : 0 < d) :
    ∀ {n m : Nat}, n < m → nsmul n d < nsmul m d
  | n, m + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · exact lt_trans _ _ _ (nsmul_strictMono hd h') (nsmul_lt_succ hd m)
    · rw [h']; exact nsmul_lt_succ hd m

theorem nsmul_le {d : Γ} (hd : 0 < d) {n m : Nat} (h : n ≤ m) : le (nsmul n d) (nsmul m d) := by
  rcases Nat.lt_or_eq_of_le h with h' | h'
  · exact Or.inl (nsmul_strictMono hd h')
  · exact Or.inr (by rw [h'])

/-- Formal degree `∑ α_i υ(f_i)` for exponent list `α` and degree list `d`. -/
def fdeg : List Nat → List Γ → Γ
  | a :: as, d :: ds => nsmul a d + fdeg as ds
  | _, _ => 0

/-- If every generator has positive degree and `α ≤ β` componentwise with
    `α ≠ β`, then `deg_F(α) < deg_F(β)`.  Hence each fibre
    `{α : deg_F(α) = γ}` is an antichain of `ℕ^m` (Lemma 3.8; finiteness
    then follows from Dickson's lemma, which is not formalized here). -/
theorem fdeg_lt :
    ∀ (α β : List Nat) (d : List Γ), (∀ x ∈ d, 0 < x) →
      α.length = d.length → β.length = d.length →
      Forall2 (· ≤ ·) α β → α ≠ β → fdeg α d < fdeg β d
  | [], [], [], _, _, _, _, hne => absurd rfl hne
  | a :: as, b :: bs, x :: xs, hpos, hla, hlb, hab, hne => by
    cases hab with
    | cons h₁ hrest =>
      have hx : 0 < x := hpos x (List.mem_cons_self x xs)
      have hpos' : ∀ y ∈ xs, 0 < y := fun y hy => hpos y (List.mem_cons_of_mem x hy)
      have hla' : as.length = xs.length := by simpa using hla
      have hlb' : bs.length = xs.length := by simpa using hlb
      show nsmul a x + fdeg as xs < nsmul b x + fdeg bs xs
      by_cases hrestEq : as = bs
      · subst hrestEq
        have hab' : a ≠ b := fun h => hne (by rw [h])
        have hlt : a < b := Nat.lt_of_le_of_ne h₁ hab'
        exact add_lt_add_right _ _ _ (nsmul_strictMono hx hlt)
      · have ih := fdeg_lt as bs xs hpos' hla' hlb' hrest hrestEq
        exact lt_le_trans (add_lt_add_left (nsmul a x) ih)
          (by rw [add_comm (nsmul a x), add_comm (nsmul b x)]
              exact add_le_add_left (fdeg bs xs) (nsmul_le hx h₁))
  | [], _ :: _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _ => by cases h
  | [], [], _ :: _, _, hla, _, _, _ => by simp at hla
  | _ :: _, _ :: _, [], _, hla, _, _, _ => by simp at hla

/-! ### Lemma 2.9, Theorem 3.3 and the termination argument: descent -/

/-- Lemma 2.9: there is no infinite strictly descending sequence of degrees. -/
theorem no_infinite_descent (wf : WellFounded (fun a b : Γ => a < b)) (γ : Nat → Γ) : ¬ ∀ k, γ (k + 1) < γ k := by
  intro hdesc
  have key : ∀ a : Γ, ∀ k, γ k = a → False := by
    intro a
    refine WellFounded.induction (C := fun a => ∀ k, γ k = a → False) wf a ?_
    intro a ih k hk
    exact ih (γ (k + 1)) (by rw [← hk]; exact hdesc k) (k + 1) rfl
  exact key (γ 0) 0 rfl

/-- Theorem 3.3 (⇐): a nonempty set of degrees has a least element, so a
    representation `H` with minimal `Ω(H)` exists. -/
theorem exists_minimal (wf : WellFounded (fun a b : Γ => a < b)) (P : Γ → Prop) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, b < a → ¬ P b := by
  rcases h with ⟨a, ha⟩
  revert ha
  refine WellFounded.induction (C := fun a => P a → ∃ a, P a ∧ ∀ b, b < a → ¬ P b) wf a ?_
  intro a ih ha
  by_cases hmin : ∀ b, b < a → ¬ P b
  · exact ⟨a, ha, hmin⟩
  · have : ∃ b, b < a ∧ P b := by
      apply Classical.byContradiction
      intro hne
      exact hmin (fun b hb hPb => hne ⟨b, hb, hPb⟩)
    rcases this with ⟨b, hb, hPb⟩
    exact ih b hb hPb

/-- Descent step of the referee's termination argument for Algorithm 1:
    if `γ_k ≽ b` always, and `γ_{k+1} ≺ γ_k` whenever `γ_k ≻ b`, then some
    `γ_k = b`.  (Here `γ_k` is the least Ω of a representation of a fixed
    `h ∈ A` after `k` passes and `b = υ(h)`.) -/
theorem descent_reaches (wf : WellFounded (fun a b : Γ => a < b)) (b : Γ) (γ : Nat → Γ) (hge : ∀ k, le b (γ k))
    (hdec : ∀ k, b < γ k → γ (k + 1) < γ k) : ∃ k, γ k = b := by
  apply Classical.byContradiction
  intro hno
  have hgt : ∀ k, b < γ k := by
    intro k
    rcases hge k with h | h
    · exact h
    · exact absurd ⟨k, h.symm⟩ hno
  exact no_infinite_descent wf γ (fun k => hdec k (hgt k))

end SS

/-! ### The gradings of the examples satisfy the standing hypotheses -/

namespace Examples
open SS

/-- `ℕ²` with the lexicographic order comparing the first coordinate first
    (Examples 1.5, 2.4, 4.1, 4.6, 4.10). -/
def LexLt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

instance : SS.OrdMonoid (Nat × Nat) where
  add a b := (a.1 + b.1, a.2 + b.2)
  zero := (0, 0)
  lt := LexLt
  add_assoc a b c := by
    show (a.1 + b.1 + c.1, a.2 + b.2 + c.2) = (a.1 + (b.1 + c.1), a.2 + (b.2 + c.2))
    rw [Nat.add_assoc, Nat.add_assoc]
  add_comm a b := by
    show (a.1 + b.1, a.2 + b.2) = (b.1 + a.1, b.2 + a.2)
    rw [Nat.add_comm a.1, Nat.add_comm a.2]
  zero_add a := by
    show (0 + a.1, 0 + a.2) = a
    rw [Nat.zero_add, Nat.zero_add]
  lt_irrefl a := by
    intro h; rcases h with h | ⟨_, h⟩ <;> exact Nat.lt_irrefl _ h
  lt_trans a b c := by
    intro h₁ h₂
    rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
    · exact Or.inl (Nat.lt_trans h₁ h₂)
    · exact Or.inl (by rw [← e₂]; exact h₁)
    · exact Or.inl (by rw [e₁]; exact h₂)
    · exact Or.inr ⟨e₁.trans e₂, Nat.lt_trans h₁ h₂⟩
  lt_trichotomy a b := by
    rcases Nat.lt_trichotomy a.1 b.1 with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_trichotomy a.2 b.2 with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inl (Prod.ext h h'))
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
    · exact Or.inr (Or.inr (Or.inl h))
  add_lt_add_right a b c := by
    intro h
    rcases h with h | ⟨e, h⟩
    · exact Or.inl (Nat.add_lt_add_right h c.1)
    · exact Or.inr ⟨by show a.1 + c.1 = b.1 + c.1; rw [e], Nat.add_lt_add_right h c.2⟩

/-- The lexicographic order on `ℕ²` is well founded. -/
theorem lex_wf : WellFounded (fun a b : Nat × Nat => LexLt a b) := by
  have h := (Prod.lex (α := Nat) (β := Nat) ⟨_, Nat.lt_wfRel.wf⟩ ⟨_, Nat.lt_wfRel.wf⟩).wf
  apply Subrelation.wf _ h
  intro a b hab
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
  rcases hab with h1 | ⟨e, h2⟩
  · exact Prod.Lex.left _ _ h1
  · simp only at e; subst e; exact Prod.Lex.right _ h2

/-- Example 2.4: Ω(Y_{j+1}) = (2j+3, 2j+1) < (2j+4, 2j) = Ω(Y_1 Y_j). -/
theorem ex24_degree_drop (j : Nat) : LexLt (2 * j + 3, 2 * j + 1) (2 * j + 4, 2 * j) :=
  Or.inl (by show 2 * j + 3 < 2 * j + 4; omega)

/-- Example 2.4: υ(g_n) = (2n+1, 2n-1) is additive along the identity
    deg(f_1) + deg(g_n) = deg(g_1 g_n) = deg(g_2 g_{n-1}). -/
theorem ex24_degrees (n : Nat) (hn : 2 ≤ n) :
    ((3 : Nat) + (2 * n + 1), (1 : Nat) + (2 * n - 1)) =
      ((2 * 2 + 1) + (2 * (n - 1) + 1), (2 * 2 - 1) + (2 * (n - 1) - 1)) := by
  apply Prod.ext <;> simp <;> omega

/-- Example 4.6: the formal degree (2,0) of Y_3^2 is lex-larger than the
    actual degree (0,6) of f_3^2 = y^6 (Remark 2.7 phenomenon). -/
theorem ex46_formal_vs_actual : LexLt (0, 6) (2, 0) := Or.inl (by decide)

/-- Using the general results for this instance: 0 is least, cancellativity. -/
example (a : Nat × Nat) : SS.le (0 : Nat × Nat) a := SS.zero_le lex_wf a
example (a b c : Nat × Nat) (h : a + c = b + c) : a = b := SS.add_right_cancel h

end Examples
