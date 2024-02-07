import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Valuation
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Group.TypeTags
/-!
# Missing Pieces of Mathlib

In this file, we collect missing theorems, instances as prequisite of this project. Theorems in this file should be added to mathlib file scatterly into each file.
-/
set_option autoImplicit false

section ValuationTopology
variable (R: Type*)
-- variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

namespace ValuationRingTopology
variable [CommRing R] [IsDomain R] [ValuationRing R]

/-- The preorder of divisibility associated to a valuation ring, i.e. `a ≤ b` if there exist `c`, such that `a * c = b`. -/
scoped instance : Preorder R where
 le a b := ∃ c, a * c = b
 le_refl _ := ⟨1, mul_one _⟩
 le_trans _ _ _ := fun ⟨u, h⟩ ⟨v, g⟩ => ⟨u * v, by rw [← g, ← h]; ring⟩

-- /-- The topology on a valuation ring `R` is defined to be the topology associated to the preorder of divisibility.-/
-- scoped instance : TopologicalSpace R := Preorder.topology R

-- scoped instance : OrderTopology R := ⟨rfl⟩

-- scoped instance : UniformSpace R where
--   uniformity := sorry
--   refl := sorry
--   symm := sorry
--   comp := sorry
--   isOpen_uniformity := sorry


/-!
-- the following is missed in `Mathlib.RingTheory.Valuation.ValuationRing`

def ValuationRing.setoid : Setoid R where
  r a b := a ≤ b ∧ b ≤ a
  -- 2 elements is equiv if both a ≤ b and b ≤ a
  iseqv := sorry


def ValuationRing.ValueMonoid := Quotient (ValuationRing.setoid R) -- this is really a monoid with zero

instance : LinearOrderedCommMonoidWithZero (ValuationRing.ValueMonoid R) := sorry

scoped instance : Valued R (ValuationRing.ValueMonoid R) := _

-- `Valued` uses Group instead of Monoid... `Maybe the correct way is to generalize mathlib's valued to monoid instead of group???`
-/

scoped instance : Valued R (ValuationRing.ValueGroup R (FractionRing R)) := sorry

scoped instance : OrderTopology R where
  topology_eq_generate_intervals := sorry

-- the topology not rfl to
scoped instance : TopologicalRing R := sorry



end ValuationRingTopology


-- open ValuationTopology
-- variable [CommRing R] [IsDomain R] [ValuationRing R]
-- #synth TopologicalRing R

end ValuationTopology

section ValuationIdeal

#check Valuation.integer

notation:max " 𝒪[" v:max "] " => Valuation.integer v

-- Mathlib.RingTheory.Valuation.Integers
def Valuation.LEIdeal {R : Type*}  {Γ₀ : Type*}  [Ring R] [LinearOrderedCommGroupWithZero Γ₀]  (v : Valuation R Γ₀) (γ : Γ₀) : Ideal (Valuation.integer v) := sorry
-- when gamma < 1, the ideal is whole ring

def Valuation.LTIdeal {R : Type*}  {Γ₀ : Type*}  [Ring R] [LinearOrderedCommGroupWithZero Γ₀]  (v : Valuation R Γ₀) (γ : Γ₀) : Ideal (Valuation.integer v) := sorry
-- when gamma < 1, the ideal is whole ring

def Valuation.maximalIdeal {R : Type*}  {Γ₀ : Type*}  [Ring R] [LinearOrderedCommGroupWithZero Γ₀]  (v : Valuation R Γ₀) : Ideal (Valuation.integer v) := Valuation.LTIdeal v 1 -- def use either localring.maximalideal or v < 1, then show the remaining one as theorem when K is a field

notation:max " 𝓂[" v:max "] " => Valuation.maximalIdeal v

-- `In Discrete Valuation Ring, relation between LT LE Ideal`

variable {R : Type*}  {Γ₀ : Type*}  [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]  (v : Valuation R Γ₀)

-- may need field
instance : (Valuation.maximalIdeal v).IsMaximal := sorry

end ValuationIdeal

section ValuationInteger
variable {K L : Type*} [Field K] [Field L] {ΓK ΓL : Type*} [LinearOrderedCommGroupWithZero ΓK][LinearOrderedCommGroupWithZero ΓL] [Algebra K L] {vK : Valuation K ΓK} {vL : Valuation L ΓL}

instance : ValuationRing vK.integer where
  cond' := sorry

-- `the maximal ideal = the lt ideal`

notation:max " 𝓀[" v:max "] " => LocalRing.ResidueField ↥𝒪[v]

#check 𝓀[vK]
-- `instance, when 𝓀[vK] is a field`


-- `Key theorem, OL/OK is generated by 1 element`

end ValuationInteger

-- `Instance of trivial group Unit being LinearOrderedCommGroupWithZero`

section QuotientAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S} [Algebra R S]

def Ideal.quotientAlgebra' (h : I ≤ RingHom.ker (algebraMap R S)) : Algebra (R⧸I) S := (Ideal.Quotient.lift _ _ h).toAlgebra

-- Maybe we should just keep this ignored
instance [h : Fact (I ≤ RingHom.ker (algebraMap R S))] : Algebra (R⧸I) S := Ideal.quotientAlgebra' h.out

-- variable {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂] {I : Ideal R} {J₁ : Ideal S₁} {J₂ : Ideal S₂}

-- def AlgHom.Quotient₂ (s : S₁ →ₐ[R] S₂) (h : J₁ ≤ J₂.comap s) : S₁⧸J₁ →ₐ[R] S₂⧸J₂ := Ideal.quotientMapₐ _ s h

#check Ideal.quotientMapₐ




end QuotientAlgebra
