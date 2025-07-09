import Mathlib.Data.Real.Basic

/-# Overview
- Reference: mathematics in lean C02, theorem proving in lean Chapter 3
-/

/-# Conjunction-/

section Conjuction

variable {P Q R : Prop}

-- P ∧ R → Q ∨ R ∧ P means (P ∧ R) → (Q ∨ (R ∧ P))
#check P ∧ R → Q ∨ R ∧ P

-- `constructor` tactic for constructing conjunctions
example (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  exact q

#check And.intro

example (p : P) (q : Q) : P ∧ Q := And.intro p q

-- `⟨⟩` for constructing conjunctions
example (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

-- (doge
example : ∃ x : ℕ, 1 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

-- #eval 1 / 0
#check Nat.instDiv

-- `rcases` and `rintro` for using conjunctions
example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  intro h
  rcases h with ⟨z, xltz, zlty⟩
  -- rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_, ⟨xltz, zlty⟩⟩ ↦ lt_trans xltz zlty
  -- fun ⟨_, h⟩ ↦ lt_trans h.1 h.2


-- In Lean, `A ↔ B` is not defined to be `(A → B) ∧ (B → A)`, but it behaves roughly the same way.
example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
  sorry

-- since iff is an equivalence relation, we can use `rw`
#check abs_lt
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

end Conjuction

/-# Disjunction-/

section Disjunction

variable {P Q : Prop}

-- `left` and `right` for constructing disjunctions
example {p : P} : P ∨ Q := by
  left
  exact p

example {q : Q} : P ∨ Q := by
  right
  exact q

example {y : ℝ} (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example {y : ℝ} (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

-- `rcases` for using disjunctions
example {x y : ℝ} : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

-- Exercise
namespace MyAbs

theorem lt_abs {x y : ℝ} : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt {x y : ℝ} : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

-- Exercise
example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end Disjunction

section Negation

/-# Negation
- Negation, `¬p`, is actually defined to be `p → False`, so we obtain `¬p` by deriving a contradiction from `p`
-/
variable {P Q : Prop}
#check Not

/- Similarly, the expression `hnp hp` produces a proof of `False` from `hp : p` and `hnp : ¬p`-/
example (hpq : P → Q) (hnq : ¬Q) : ¬P := by
  intro hp
  apply hnq
  apply hpq
  exact hp

example (hpq : P → Q) (hnq : ¬Q) : ¬P :=
  fun hp : P => hnq (hpq hp)

variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

-- Exericise, notice that `x ≠ y` is just `¬ x = y`
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  sorry

variable {P : ℝ → Prop}

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

-- `by contra` tactic
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

-- `contrapose` tactic
example {P Q : Prop} (h : ¬ Q → ¬ P) : P → Q := by
  contrapose!
  exact h

-- `exfalso` tactic
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

end Negation

/-# cheetsheet
- `→` `∀` : `apply`, `intro`
- `∃` : `use`, `rcases`
- `∧` (`↔`): `constructor`, `⟨⟩`, `rcases`
- `∨` : `left`, `right`, `rcases`
- `¬` : `by_contra`, `contrapose!`, `push_neg`
-/
