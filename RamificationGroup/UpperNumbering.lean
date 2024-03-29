import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import RamificationGroup.HerbrandFunction
import RamificationGroup.Valued.Hom.Discrete'

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation
open HerbrandFunction

section

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

/-
--lemma 4
theorem Varphi_With_i (σ : (L ≃ₐ[K] L) ⧸ H) : (varphi K L (Sup (i_[L/K] ((mk' H)⁻¹' {σ})))) = (i_[L/K'] σ) - (1 : WithTop ℤ):= by sorry

--lemma 5
theorem Herbrand_Thm {u : ℚ} {v : ℚ} (h : v = varphi K L u) {H : Subgroup (L ≃ₐv[K] L)} [Subgroup.Normal H]: G(L/K')_[(Int.ceil v)] = (G(L/K)_[(Int.ceil u)] ⊔ H) ⧸ H:= by sorry

--prop 15
theorem varphi_comp_field_ext : (varphi K K') ∘ (varphi K' L) = varphi K L:= by sorry

theorem psi_comp_field_ext : (psi K K') ∘ (psi K' L) = psi K L:= by sorry

-/

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S] (x : ℚ)
#check Int.ceil
#check φ_[L/K] x
#check ψ_[L/K] x

theorem phi_comp_field_ext : (phi K' L) ∘ (phi K K') = phi K L := by sorry

theorem psi_comp_field_ext : (psi K K') ∘ (psi K' L) = psi K L := by sorry

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.
def upperRamificationGroup_aux (u : ℚ): (Subgroup (S ≃ₐv[R] S)) := lowerRamificationGroup R S ⌈ψ_[S/R] u⌉

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" u:max "] " => upperRamificationGroup_aux K L u

end

section

open DiscreteValuation

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vL.v] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

#synth Valued K' ℤₘ₀

#check valuedIntermediateField

variable (v : ℚ)
#check (G(L/K)^[v]).subgroupOf (H.comap ValAlgEquiv.toAlgEquivₘ)

#check AlgEquiv.restrictNormalHom

variable (K') in
def ValAlgEquiv.restrictNormalHom : (L ≃ₐv[K] L) →* K' ≃ₐv[K] K' := sorry

theorem herbrand' [Normal K K'] (v : ℚ) : G(K'/K)^[v] = G(L/K)^[v].map (ValAlgEquiv.restrictNormalHom K'):= by sorry

end
