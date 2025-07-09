import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
variable {ℒ : Type} [LE ℒ] [BoundedOrder ℒ]
variable {S : Type} [CompleteLattice S]

variable (Pless : Type := {p : ℒ × ℒ // p.1 ≤ p.2 ∧ p.1 ≠ p.2})

variable (μ : Pless → S)


def Vₐ (x : ℒ) (hₓ : x ≠ ⊤) : Type := {z : S // ∃ y : ℒ, x ≤  y ∧ x ≠ y ∧ z = μ ⟨(x, y),???⟩}
