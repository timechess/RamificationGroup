import RamificationGroup.UpperNumbering.phiComp
section
open DiscreteValuation Valued Valuation HerbrandFunction

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [vL : Valued L ℤₘ₀] [IsDiscrete vL.v][Algebra K L] [FiniteDimensional K L] [IsValExtension vK.v vL.v] [CompleteSpace K]
[Algebra.IsSeparable K L] [Algebra.IsSeparable (IsLocalRing.ResidueField 𝒪[K]) (IsLocalRing.ResidueField 𝒪[L])]

local notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup_aux K L v
-- this uses local fields and bichang's work, check if the condition is too strong...
theorem UpperRamificationGroup_aux.exist_eq_bot [LocalField K] [LocalField L] [IsValExtension vK.v vL.v] : ∃ v : ℚ, G(L/K)^[v] = ⊥ := by
  obtain ⟨u, hu⟩ := exist_lowerRamificationGroup_eq_bot (K := K) (L := L)
  use (phi K L u)
  simp only [upperRamificationGroup_aux]
  rw [psi_phi_eq_self K L _, Int.ceil_intCast u]
  exact hu

end

section upperRamificationGroup
-- need a set up that every intermidiate field has a valued instance. in the cdvf case, this is possible.

-- Is this instance ok? it is possible to avoid instance and always use def, but I do think a scoped instance make statements much easier.

open DiscreteValuation Valuation Valued

#check Valued.toUniformSpace
theorem Valued.toUniformSpace_eq_of_v_eq {K Γ : Type*} [Ring K] [LinearOrderedCommGroupWithZero Γ] {v₁ v₂ : Valued K Γ} (h : v₁.v = v₂.v) : v₁.toUniformSpace = v₂.toUniformSpace := by
  apply UniformAddGroup.ext v₁.toUniformAddGroup v₂.toUniformAddGroup
  ext s
  rw [v₁.is_topological_valuation, v₂.is_topological_valuation, h]

def completeSpaceIsValExtension (K F : Type*) [Field K] [vK : Valued K ℤₘ₀] [IsDiscrete vK.v] [CompleteSpace K] [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] (h : vK.v.IsEquiv <| vF.v.comap (algebraMap K F)) [FiniteDimensional K F]: CompleteSpace F := by
  have veq : vF.v = extendedValuation K F := by
    rw [← isEquiv_iff_eq]
    exact extension_valuation_equiv_extendedValuation_of_discrete h
  have ueq: vF.toUniformSpace = (DiscreteValuation.Extension.valued K F).toUniformSpace := Valued.toUniformSpace_eq_of_v_eq veq
  erw [ueq]
  exact DiscreteValuation.Extension.completeSpace K F

open AlgEquiv

#check extension_valuation_equiv_extendedValuation_of_discrete
#check isEquiv_iff_eq
#check IntermediateField
#check DiscreteValuation.Extension.completeSpace
-- this is easier to use

universe u v

-- universe problem, what should be F's universe? max u v requires ULift
def upperRamificationGroup (K : Type u) (L : Type v) [Field K] [vK : Valued K ℤₘ₀] [Field L] [vL : Valued L ℤₘ₀] [Algebra K L] [IsDiscrete vK.v] [CompleteSpace K] (v : ℚ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {s | ∀ (F : Type v) [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] [IsValExtension vK.v vF.v] [Algebra F L] [IsScalarTower K F L] [Normal K F] [FiniteDimensional K F] [IsValExtension vF.v vL.v],
    restrictNormalHom F s ∈ upperRamificationGroup_aux K F v}
  mul_mem' {s} {s'} hs hs' F:= by
    intros
    rw [(restrictNormalHom F).map_mul s s']
    exact Subgroup.mul_mem (upperRamificationGroup_aux K F v) (hs F) (hs' F)
  one_mem' F := by
    intros
    rw [(restrictNormalHom F).map_one]
    exact Subgroup.one_mem (upperRamificationGroup_aux K F v)
  inv_mem' {s} hs F:= by
    intros
    rw [(restrictNormalHom F).map_inv s]
    exact Subgroup.inv_mem (upperRamificationGroup_aux K F v) (hs F)

#check upperRamificationGroup

scoped [Valued] notation:max " G(" L:max "/" K:max ")^[" v:max "] " => upperRamificationGroup K L v

namespace UpperRamificationGroup

variable {K L : Type*} [Field K] [vK : Valued K ℤₘ₀] [Field L] [vL : Valued L ℤₘ₀] [Algebra K L] [IsDiscrete vK.v] [IsDiscrete vL.v] [CompleteSpace K] [IsValExtension vK.v vL.v] [FiniteDimensional K L]

@[simp]
theorem restrictNormal_eq_self {F E : Type*}  [Field F] [Field E] [Algebra F E] [Algebra F E] (s : E ≃ₐ[F] E) [Normal F E] : s.restrictNormal E = s := by
  ext x
  calc
  _ = (algebraMap E E) ((s.restrictNormal E) x) := by simp
  _ = _ := by
    rw [AlgEquiv.restrictNormal_commutes]
    simp


theorem restrictNormal_restrictNormal {F K₁ K₂ : Type*} [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]  (s : K₁ ≃ₐ[F] K₂) (E M: Type*) [Field E] [Field M] [Algebra F M] [Algebra F E] [Algebra M E] [Algebra M K₁] [Algebra M K₂] [Algebra E K₁] [Algebra E K₂] [IsScalarTower F M K₁] [IsScalarTower F M K₂] [IsScalarTower F E K₁] [IsScalarTower F E K₂]  [Normal F E] [Normal F M] [IsScalarTower F M E] [IsScalarTower M E K₁] [IsScalarTower M E K₂] : (s.restrictNormal E).restrictNormal M = s.restrictNormal M := by
  ext x
  apply (algebraMap M K₂).injective
  simp only [AlgEquiv.restrictNormal_commutes]
  have h : algebraMap M K₂ = RingHom.comp (algebraMap E K₂) (algebraMap M E) := by
    refine IsScalarTower.algebraMap_eq M E K₂
  have h' : algebraMap M K₁ = RingHom.comp (algebraMap E K₁) (algebraMap M E) := by
    refine IsScalarTower.algebraMap_eq M E K₁
  rw [h, RingHom.comp_apply, AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormal_commutes, ← RingHom.comp_apply, ← h']

-- theorem relation with aux
theorem eq_UpperRamificationGroup_aux [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension vK.v vL.v] [FiniteDimensional K L] [Normal K L] {v : ℚ} : upperRamificationGroup K L v = upperRamificationGroup_aux K L v := by
  ext s
  simp only [upperRamificationGroup, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h
    have hL := h L
    suffices restrictNormalHom (F := K) L = MonoidHom.id _ by
      simp [this] at hL
      assumption
    ext s a
    simp [restrictNormalHom]
  · intro h F
    intros
    have : FiniteDimensional F L := by exact Module.Finite.of_restrictScalars_finite K F L
    sorry
    -- rw [← herbrand']
    -- apply Subgroup.mem_map_of_mem
    -- exact h


-- universe problem here. `∀ (F : Type u_2)`
theorem mem_iff_mem_UpperRamificationGroup_aux {s : L ≃ₐ[K] L} {v : ℚ} : s ∈ G(L/K)^[v] ↔ ∀ (F : Type u_2) [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] [IsValExtension vK.v vF.v] [Algebra F L] [IsScalarTower K F L] [Normal K F] [FiniteDimensional K F] [IsValExtension vF.v vL.v],
    restrictNormalHom F s ∈ upperRamificationGroup_aux K F v := by
      rfl

set_option maxHeartbeats 0
-- theorem compatible with quotient, finite quotient
@[simp]
theorem map_restrictNormalHom {K'} [Field K'] [vK' : Valued K' ℤₘ₀] [IsDiscrete vK'.v] [Algebra K K'] [Algebra K' L] [Algebra.IsSeparable K' L] [FiniteDimensional K K'] [IsScalarTower K K' L] [Normal K K'] [Normal K L] [IsValExtension vK.v vK'.v] [IsValExtension vK'.v vL.v] [CompleteSpace K'] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K']) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable ↥𝒪[K'] ↥𝒪[L]] [Algebra.IsSeparable K L] [Algebra.IsSeparable K K'] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[K'])] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Normal K' L] (v : ℚ) : G(L/K)^[v].map (AlgEquiv.restrictNormalHom K') = G(K'/K)^[v] := by
  have : FiniteDimensional K' L:= by exact Module.Finite.of_restrictScalars_finite K K' L
  rw [eq_UpperRamificationGroup_aux, eq_UpperRamificationGroup_aux, upperRamificationGroup_aux, upperRamificationGroup_aux]
  apply herbrand'

theorem mem_iff {s : L ≃ₐ[K] L} {v : ℚ} : s ∈ G(L/K)^[v] ↔ ∀ (F : Type u_2) [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] [IsValExtension vK.v vF.v] [Algebra F L] [IsScalarTower K F L] [Normal K F] [FiniteDimensional K F] [IsValExtension vF.v vL.v],restrictNormalHom F s ∈ upperRamificationGroup_aux K F v := by
  calc
  _ ↔ s ∈ G(L/K)^[v].carrier := by apply Subgroup.mem_carrier
  _ ↔ ∀ F [Field F] [vF : Valued F ℤₘ₀] [IsDiscrete vF.v] [Algebra K F] [IsValExtension vK.v vF.v] [Algebra F L] [IsScalarTower K F L] [Normal K F] [FiniteDimensional K F] [IsValExtension vF.v vL.v],restrictNormalHom F s ∈ upperRamificationGroup_aux K F v := by
    unfold upperRamificationGroup
    simp only [Set.mem_setOf_eq]


section autCongr

variable {L': Type*} [Field L'] [vL : Valued L' ℤₘ₀] [Algebra K L'] [Normal K L] [IsDiscrete vL.v] [IsValExtension vK.v vL.v] [FiniteDimensional K L'] [Normal K L']
open HerbrandFunction

theorem autCongr_mem_upperRamificationGroup_iff {f : L ≃ₐ[K] L'} (s : L ≃ₐ[K] L) (v : ℚ) (h : ∀ (a : L), Valued.v a = Valued.v (f a)) : s ∈ G(L/K)^[v] ↔ (AlgEquiv.autCongr f s : L' ≃ₐ[K] L') ∈ G(L'/K)^[v] := by
  have h1 : ⌈psi K L v⌉ = ⌈psi K L' v⌉ := by
    rw [psi_eq_ofEquiv K L L' h]
  rw [eq_UpperRamificationGroup_aux, eq_UpperRamificationGroup_aux, upperRamificationGroup_aux, upperRamificationGroup_aux, ←h1]
  apply autCongr_mem_lowerRamificationGroup_iff (s := s) (u := ⌈psi K L v⌉) (f := f) h

end autCongr

-- theorems about exhausive and separated
-- under what condition this is correct? this is too strong?
theorem eq_decompositionGroup [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension vK.v vL.v] [FiniteDimensional K L] [Normal K L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] {v : ℚ} (h : v ≤ -1) :
G(L/K)^[v] = decompositionGroup K L := by
  rw [eq_UpperRamificationGroup_aux (vL := vL), upperRamificationGroup_aux, HerbrandFunction.psi_eq_self_of_le_neg_one K L (by linarith)]
  apply lowerRamificationGroup_eq_decompositionGroup (Int.ceil_le.mpr h)

theorem eq_top [vL : Valued L ℤₘ₀] [IsDiscrete vL.v] [IsValExtension vK.v vL.v] [FiniteDimensional K L] [Normal K L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])] [Algebra.IsSeparable K L] {v : ℚ} (h : v ≤ -1) : G(L/K)^[v] = ⊤ := by
  rw [eq_decompositionGroup (vL := vL) h]
  exact decompositionGroup_eq_top

end UpperRamificationGroup

namespace UpperRamificationGroup

variable {K L : Type*} [Field K] [Field L] [vK : Valued K ℤₘ₀]  [vL : Valued L ℤₘ₀] [IsDiscrete vK.v] [CompleteSpace K] [Algebra K L] [FiniteDimensional K L] [LocalField K] [LocalField L] [IsValExtension vK.v vL.v] [IsDiscrete vL.v] [Normal K L] [Algebra.IsSeparable K L] [Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[K]) (IsLocalRing.ResidueField ↥𝒪[L])]

set_option synthInstance.maxHeartbeats 0
#synth Algebra K L

theorem inf_eq_bot (s : L ≃ₐ[K] L) : (∀ v, s ∈ G(L/K)^[v]) ↔ s = 1 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := UpperRamificationGroup_aux.exist_eq_bot (K := K) (L := L)
    rw [← eq_UpperRamificationGroup_aux] at hv
    have h1 : s ∈ G(L/K)^[v] := h v
    rw [hv] at h1
    apply Subgroup.mem_bot.1 h1
  · intro hs v
    simp only [hs]
    apply Subgroup.one_mem
