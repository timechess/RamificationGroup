import RamificationGroup.LowerNumbering
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.KrullTopology
import RamificationGroup.HerbrandFunction
import RamificationGroup.Valued.Hom.Discrete'

open QuotientGroup IntermediateField DiscreteValuation Valued Valuation
open HerbrandFunction


namespace ValAlgEquiv
#check AlgEquiv.restrictNormalHom
variable {K L} (K') {ΓK ΓK' ΓL : outParam Type*} [Field K] [Field K'] [Field L]
[LinearOrderedCommGroupWithZero ΓK]
[LinearOrderedCommGroupWithZero ΓK']
[LinearOrderedCommGroupWithZero ΓL]
[Valued K ΓK] [Valued K' ΓK'] [Valued L ΓL]
[ValAlgebra K K'] [ValAlgebra K L] [ValAlgebra K' L] [IsScalarTower K K' L] [Normal K K']
-- change this using IsScalatower
open algebraMap

noncomputable def restrictNormalHom : (L ≃ₐv[K] L) →* K' ≃ₐv[K] K' where
  toFun f :=
    {
      AlgEquiv.restrictNormalHom K' (f : L ≃ₐ[K] L) with
      map_le_map_iff' := sorry
      val_isEquiv_comap' := by
        intro x y
        convert f.val_isEquiv_comap' (x : L) (y : L)
        simp only [ValAlgebra.val_map_le_iff]
        dsimp
        -- rw [← ValAlgebra.val_map_le_iff (A := L)]
        sorry
      continuous_toFun := sorry
      continuous_invFun := sorry
    }
  map_one' := by
    ext
    sorry
  map_mul' := sorry

theorem restrictNormalHom_surjective : Function.Surjective (restrictNormalHom K' (K := K) (L := L)) := sorry

end ValAlgEquiv



section

-- principle : first try to state a theorem in IsScalarTower, then try IntermediateField
variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero ΓK] [vK : Valued K ΓK] [vL : Valued L ℤₘ₀] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L}

/-
--lemma 4
theorem Varphi_With_i (σ : (L ≃ₐ[K] L) ⧸ H) : (varphi K L (Sup (i_[L/K] ((mk' H)⁻¹' {σ})))) = (i_[L/K'] σ) - (1 : WithTop ℤ):= by sorry

-/

variable (R S : Type*) {ΓR : outParam Type*} [CommRing R] [Ring S] [LinearOrderedCommGroupWithZero ΓR] [vR : Valued R ΓR] [vS : Valued S ℤₘ₀] [ValAlgebra R S] (x : ℚ)
#check Int.ceil

namespace HerbrandFunction

-- Prop 15
-- probably need to rename
variable (K') in
@[simp]
theorem phi_comp_of_intermediateField : (phi K K') ∘ (phi K' L) = phi K L := by
  ext u
  sorry

--Prop 15
variable (K') in
@[simp]
theorem psi_comp_of_intermediateField : (psi K' L) ∘ (psi K K') = psi K L := by
  ext v
  sorry

end HerbrandFunction

-- aux construction of upper numbering ramification group, correct for finite extension of local fields only. later we define a more general version on all algebraic extensions of local fields.
def upperRamificationGroup_aux (v : ℚ): (Subgroup (S ≃ₐv[R] S)) := lowerRamificationGroup R S ⌈psi R S v⌉

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" u:max "] " => upperRamificationGroup_aux K L u

end

section

open DiscreteValuation

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vL.v] [Algebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L} [Normal K K']
#synth IsScalarTower K K' L

variable {K L : Type*} {ΓK : outParam Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [IsDiscrete vL.v] [ValAlgebra K L] {H : Subgroup (L ≃ₐ[K] L)} [Subgroup.Normal H] {K' : IntermediateField K L} [Normal K K']

#check valuedIntermediateField -- this should be renamed

variable (v : ℚ)
#check (G(L/K)^[v]).subgroupOf (H.comap ValAlgEquiv.toAlgEquivₘ)


variable [FiniteDimensional K L]

#synth Fintype (L ≃ₐ[K] L)
instance : Fintype (L ≃ₐv[K] L) := sorry

variable (σ : K' ≃ₐv[K] K')
open Classical
#synth Fintype (((ValAlgEquiv.restrictNormalHom K' (L := L)) ⁻¹' {σ}))



-- Lemma 4
theorem preimage_singleton_nonempty {σ : K' ≃ₐv[K] K'} : ((ValAlgEquiv.restrictNormalHom K' (L := L))⁻¹' {σ}).toFinset.Nonempty := by
  apply Finset.coe_nonempty.mp
  simp [ValAlgEquiv.restrictNormalHom_surjective]

noncomputable def HerbrandFunction.truncatedJ (u : ℚ) (σ : K' ≃ₐv[K] K') : ℚ := (Finset.sup'  ((ValAlgEquiv.restrictNormalHom K')⁻¹' {σ}).toFinset preimage_singleton_nonempty (fun x => x.truncatedLowerIndex K L u - 1))

variable {σ : K' ≃ₐv[K] K'}

#synth Fintype ((ValAlgEquiv.restrictNormalHom K' ( L := L ))⁻¹' {σ})

theorem phi_truncatedJ_sub_one (u : ℚ) (σ : K' ≃ₐv[K] K') : phi K' L ((truncatedJ u σ) - 1) = σ.truncatedLowerIndex K K' ((phi K L (u-1)) + 1) - 1:= by sorry

theorem mem_lowerRamificationGroup_of_le_truncatedJ_sub_one {u r : ℚ} (h : u ≤ truncatedJ r σ - 1) : σ ∈ (G(L/K)_[⌈u⌉].map (ValAlgEquiv.restrictNormalHom K')) := sorry

theorem le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup (u : ℚ) (r : ℚ) (h : u + 1 ≤ r) : u ≤ truncatedJ r σ - 1 ↔ σ ∈ (G(L/K)_[⌈u⌉].map (ValAlgEquiv.restrictNormalHom K')) := sorry

-- Lemma 5
@[simp]
theorem herbrand (u : ℚ) : G(L/K)_[⌈u⌉].map (ValAlgEquiv.restrictNormalHom K') = G(K'/K)_[⌈phi K' L u⌉] := by
  ext σ
  calc
  _ ↔ truncatedJ (u + 1) σ - 1 ≥ u := (le_truncatedJ_sub_one_iff_mem_lowerRamificationGroup u (u + 1) (by linarith)).symm
  _ ↔ phi K' L (truncatedJ (u + 1) σ - 1) ≥ phi K' L u := (phi_strictMono K L).le_iff_le.symm
  _ ↔ σ.truncatedLowerIndex K K' ((phi K L u) + 1) - 1 ≥ phi K' L u := by
    simp [phi_truncatedJ_sub_one]
  _ ↔ σ ∈ G(K'/K)_[⌈phi K' L u⌉] := le_truncatedLowerIndex_sub_one_iff_mem_lowerRamificationGroup σ (phi K L u) _ (by linarith)

@[simp]
theorem herbrand' [Normal K K'] (v : ℚ) : G(L/K)^[v].map (ValAlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  convert herbrand (psi K L v)
  rw [← psi_comp_of_intermediateField K']
  simp only [Function.comp_apply, phi_psi_eq_self]
  rfl

end

/-
variable (K L) [Field K] [Field L] {ΓL : outParam Type*} [LinearOrderedCommGroupWithZero ΓL] [vK : Valued K ℤₘ₀] [vL : Valued L ΓL] [ValAlgebra K L] {E : IntermediateField K L}

variable {K L} in
def discreteValuedOfFinite : Valued E ℤₘ₀ := sorry

variable {K L} in
def valAlgebraOfFinite : ValAlgebra K (A := E) (vA := discreteValuedOfFinite) := sorry
variable {K L} in
def valAlgebraOfFinite' : ValAlgebra (R := E) L (vR := discreteValuedOfFinite) := sorry

def upperRamificationGroup (v : ℚ): (Subgroup (L ≃ₐv[K] L)) where
  carrier := { s | ∀ E ∈ finiteExts K L,
    letI : Valued E ℤₘ₀ := discreteValuedOfFinite;
    letI : ValAlgebra K E := valAlgebraOfFinite
    letI : ValAlgebra E L := valAlgebraOfFinite'
    Normal K E → (ValAlgEquiv.restrictNormalHom (K' := E) s ∈ G(E/K)^[v]) }
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

/-
theorem upperRamificationGroup compatible with quotient

theorem upperRamificationGroup = upperRamificationGroup_aux in finite case

-/

#check finiteExts
#check fixedByFinite
-/
