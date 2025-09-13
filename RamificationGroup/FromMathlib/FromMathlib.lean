import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Valuation.ValExtension


open Valuation
theorem Valuation.HasExtension.val_algebraMap{R : Type*} {A : Type*} [CommRing R] [Ring A] [Algebra R A] {ΓR : Type*} {ΓA : Type*} [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓA] {vR : Valuation R ΓR} {vA : Valuation A ΓA} [IsValExtension vR vA] (r : ↥vR.integer) :
↑((algebraMap ↥vR.integer ↥vA.integer) r) = (algebraMap R A) ↑r := sorry

theorem algebraMap_isIntegral_iff{R : Type*} {A : Type*} [CommRing R] [Ring A] [Algebra R A] :
(algebraMap R A).IsIntegral ↔ Algebra.IsIntegral R A := sorry
