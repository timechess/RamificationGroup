import RamificationGroup.HerbrandFunction.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical


open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction MeasureTheory.MeasureSpace intervalIntegral Pointwise AlgEquiv ExtDVR Asymptotics Filter intervalIntegral MeasureTheory Topology

variable (R S : Type*) [CommRing R] [Field S] [Algebra R S] [Fintype (S ≃ₐ[R] S)] [vS : Valued S ℤₘ₀] [DecidableEq (S ≃ₐ[R] S)]
#check Valuation.IsEquiv

noncomputable def phiReal (u : Real) : Real := (1 /(Nat.card ↥ G(S/R)_[0])) * (∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card G(S/R)_[(max 0 x)] : ℝ) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(S/R)_[(max 0 ⌈u⌉)] : ℝ))

noncomputable def AlgEquiv.truncatedLowerIndexReal (u : ℝ) (s : (S ≃ₐ[R] S)) : ℝ :=
    if h : i_[S/R] s = ⊤ then u
    else min u ((i_[S/R] s).untop h)

theorem lowerRamificationGroup_le_decompositionGroup {n : ℤ} : G(S/R)_[n] ≤ decompositionGroup R S := by
  unfold lowerRamificationGroup
  intro s hs
  simp only [neg_zero, zero_sub, Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, Subtype.forall, Subgroup.mem_mk, Set.mem_setOf_eq] at hs
  exact hs.left

open Multiplicative in
theorem le_toAdd_iff {a : ℤ} {b : ℤ} : b ≤ ofAdd a ↔ toAdd b ≤ a := ⟨fun a ↦ a, fun a ↦ a⟩

--already exist in Mathlib
theorem WithZero.unbot_le_iff{α : Type u_1} [LE α] [LE (WithZero α)] {x : WithZero α} {b : α} (hx : x ≠ 0) :
unzero hx ≤ b ↔ x ≤ (b : WithZero α) := by sorry

theorem Int.add_neg_eq_sub {a b : ℤ} : a + -b = a - b := rfl

theorem BddAbove_value_autCongr {s : S ≃ₐ[R] S} (hs : s ∈ decompositionGroup R S) : BddAbove (Set.range fun x : vS.v.integer ↦ v (s ↑x - ↑x)) := by
  use 1
  apply mem_upperBounds.2
  rintro x ⟨hx1, hx2⟩
  simp only [← hx2]
  obtain h := (vS.v.map_add_le_max' (s hx1) (- hx1))
  simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe, toMonoidWithZeroHom_coe_eq_coe, Valuation.map_neg, show (s hx1 + - hx1) = (s hx1 - hx1) by ring] at h
  apply le_trans h
  apply sup_le_iff.2
  constructor
  · have h : s hx1 ∈ vS.v.integer := by
      apply (vS.v.mem_integer_iff _).2
      suffices hx : hx1.1 ∈ (vS.v.comap s.toRingHom).integer by exact hx
      simp only [(Valuation.isEquiv_iff_integer (v.comap s.toRingHom) v).1 hs.symm]
      exact hx1.2
    exact h
  · exact hx1.2

open Multiplicative in
theorem mem_lowerRamificationGroup_iff {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S) (n : ℕ) : s ∈ G(S/R)_[n] ↔ n + 1 ≤ i_[S/R] s := by
  simp only [lowerRamificationGroup, Subtype.forall, Subgroup.mem_mk, Set.mem_setOf_eq, AlgEquiv.lowerIndex]
  by_cases hrefl : s = .refl
  · simp only [hrefl, AlgEquiv.coe_refl, id_eq, sub_self, _root_.map_zero, ofAdd_sub, ofAdd_neg,
    zero_le', implies_true, and_true, ciSup_const, ↓reduceDIte, le_top, iff_true]
    exact refl_mem_decompositionGroup R S
  · have hne0 : ¬ ⨆ x : vS.v.integer, vS.v (s x - x) = 0 := by rw [iSup_val_map_sub_eq_zero_iff_eq_refl hs']; exact hrefl
    constructor
    · intro ⟨_, hs⟩
      simp only [hne0, ↓reduceDIte]
      simp only [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.cast_le]
      rw [← Nat.cast_le (α := ℤ), Int.toNat_of_nonneg]
      suffices (WithZero.unzero hne0) ≤ ofAdd (- (n : ℤ) - 1) by
        rw [Nat.cast_add, Nat.cast_one, le_neg, ← le_toAdd_iff, neg_add_rev, add_comm, Int.add_neg_eq_sub]
        exact this
      exact (WithZero.unbot_le_iff hne0).2 (ciSup_le (fun x => hs x (SetLike.coe_mem x)))
      simp only [Left.nonneg_neg_iff, ← le_toAdd_iff, ofAdd_zero, WithZero.unbot_le_iff hne0]
      exact ciSup_le (fun x => val_map_sub_le_one hs' x)
    · intro hs
      refine ⟨hs', ?_⟩
      intro a ha
      by_cases ha1 : v (s a - a) = 0
      · simp only [ha1, ofAdd_sub, ofAdd_neg, zero_le']
      · apply (WithZero.unbot_le_iff ha1).1
        apply le_toAdd_iff.2
        simp only [hne0, ↓reduceDIte, ← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.cast_le] at hs
        rw [← Nat.cast_le (α := ℤ), Int.toNat_of_nonneg, Nat.cast_add, le_neg, neg_add, Int.add_neg_eq_sub, Nat.cast_one] at hs
        exact le_trans (toAdd_le.2 ((WithZero.unzero_le_unzero ha1 hne0).2 (le_ciSup (f := fun (x : vS.v.integer) ↦ v (s x - x)) (BddAbove_value_autCongr R S hs') ⟨a, ha⟩))) hs
        simp only [Left.nonneg_neg_iff, ← le_toAdd_iff, ofAdd_zero, WithZero.unbot_le_iff hne0]
        exact ciSup_le (fun x => val_map_sub_le_one hs' x)

theorem lowerIndex_pos {s : S ≃ₐ[R] S} : i_[S/R] s ≥ 0 := by
  unfold lowerIndex
  simp only [zero_le]

noncomputable instance : Fintype (decompositionGroup R S : Set (S ≃ₐ[R] S)) :=  Fintype.ofFinite (decompositionGroup R S)

noncomputable instance {n : ℤ} : Fintype (G(S/R)_[n] : Set (S ≃ₐ[R] S)) := Fintype.ofFinite G(S/R)_[n]

noncomputable instance {n : ℤ} : Fintype G(S/R)_[n] := Fintype.ofFinite G(S/R)_[n]

theorem decompositionGroup_eq_diff (n : ℤ) : (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset = (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ ((G(S/R)_[n] : Set (S ≃ₐ[R] S)).toFinset) ∪ ((G(S/R)_[n] : Set (S ≃ₐ[R] S)).toFinset) := by
    simp only [Finset.sdiff_union_self_eq_union, Finset.left_eq_union, Set.subset_toFinset, Set.coe_toFinset, SetLike.coe_subset_coe]
    exact lowerRamificationGroup_le_decompositionGroup R S

theorem auxx {u : ℝ} (hu2 : 0 ≤ u) :  ∑ x ∈ ((decompositionGroup R S : Set (S ≃ₐ[R] S))).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x = ∑ _ ∈ ((decompositionGroup R S : Set (S ≃ₐ[R] S))).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, 0 := by
  have h : ∀ i ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u i = 0 := by
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    intro i hi1 hi2
    unfold truncatedLowerIndexReal
    have h : i_[S/R] i ≠ ⊤ := WithTop.lt_top_iff_ne_top.1 (lt_of_lt_of_le (lt_of_not_ge (mt (mem_lowerRamificationGroup_iff R S hi1 0).2 hi2)) (OrderTop.le_top _))
    simp only [h, ↓reduceDIte]
    have : i_[S/R] i = 0 := by
      apply eq_of_ge_of_not_gt (lowerIndex_pos R S)
      by_contra hc
      have hle : 1 ≤ i_[S/R] i := Order.one_le_iff_pos.mpr hc
      apply hi2
      exact (mem_lowerRamificationGroup_iff R S hi1 0).2 hle
    rw[min_eq_right]
    · simp only [Nat.cast_eq_zero, this, WithTop.untop_zero]
    · simp only [this, WithTop.untop_zero]
      simp only [CharP.cast_eq_zero]
      exact hu2
  apply (Finset.sum_eq_sum_iff_of_le ?_).2
  exact h
  exact fun i hi ↦ le_of_eq (h i hi)

theorem auxx_1 {n : ℕ} {u : ℝ} (hu1 : u ≤ n + 1) :
    ∑ x ∈ (G(S/R)_[n] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x = ∑ _ ∈ (G(S/R)_[n] : Set (S ≃ₐ[R] S)).toFinset, u := by
  have h : ∀ i ∈ (G(S/R)_[n] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u i = u := by
      simp only [Set.mem_toFinset, SetLike.mem_coe]
      intro i hi
      unfold truncatedLowerIndexReal
      by_cases hc : i_[S/R] i = ⊤
      · simp only [hc, ↓reduceDIte]
      · simp only [hc, ↓reduceDIte, inf_eq_left]
        apply le_trans hu1
        rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
        apply (WithTop.le_untop_iff hc).2
        simp only [WithTop.coe_add, ENat.some_eq_coe, WithTop.coe_one]
        apply (mem_lowerRamificationGroup_iff R S ((lowerRamificationGroup_le_decompositionGroup R S) hi) n).1 hi
  apply (Finset.sum_eq_sum_iff_of_le ?_).2
  exact h
  exact fun i hi => le_of_eq (h i hi)

theorem sum_truncatedLowerIndexReal_eq_of_le_one {u : ℝ} (hu1 : u ≤ 1) (hu2 : 0 ≤ u) : ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x = (Nat.card G(S/R)_[0]) * u := by
  rw [decompositionGroup_eq_diff R S 0, Finset.sum_union]
  calc
    _ = ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, 0 +
    ∑ x ∈ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x := by rw [auxx R S hu2]
    _ = ∑ x ∈ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, u := by
      have hu1' : u ≤ (0 : ℕ) + 1 := by rw [Nat.cast_zero, zero_add]; exact hu1
      obtain h := auxx_1 R S (n := 0) (u := u) hu1'
      simp only [CharP.cast_eq_zero] at h
      rw [Finset.sum_const, smul_zero, zero_add, h]
    _ = _ := by
      simp only [Finset.sum_const, Set.toFinset_card, SetLike.coe_sort_coe, nsmul_eq_mul, Nat.card_eq_fintype_card, mul_eq_mul_right_iff, Nat.cast_inj]
  exact Finset.sdiff_disjoint

theorem phiReal_zero_eq_zero : phiReal R S 0 = 0 := by
  unfold phiReal
  simp only [Int.ceil_zero, zero_sub, Int.reduceNeg, neg_lt_self_iff, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, Left.neg_nonpos_iff, zero_le_one, sup_of_le_left, Int.cast_zero, sub_self, max_self, zero_mul, add_zero, mul_zero]

#check insert_Icc_right
theorem phiReal_linear_section {n : ℕ} {x : ℝ} (h : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ)) : phiReal R S x = phiReal R S n + (1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)]) * (x - n) := by
  by_cases hc : x = n
  · simp only [hc, sub_self, one_div, mul_zero, add_zero]
  · have hc' : ⌈x⌉ = n + 1 := by
      apply Int.ceil_eq_iff.2
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, add_sub_cancel_right]
      refine ⟨lt_of_le_of_ne (Set.mem_Icc.1 h).1 ?_, (Set.mem_Icc.1 h).2⟩
      exact fun a ↦ hc (id (Eq.symm a))
    have hx : 0 < x := by
      apply lt_of_le_of_lt (b := (n : ℝ))
      exact Nat.cast_nonneg' n
      apply lt_of_le_of_ne (Set.mem_Icc.1 h).1
      exact fun a ↦ hc (id (Eq.symm a))
    by_cases hc'' : n = 0
    · unfold phiReal
      simp only [hc', hc'', one_div, CharP.cast_eq_zero, zero_add, sub_self, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, max_self, Int.cast_zero, sub_zero, phiReal_zero_eq_zero, zero_add]
      simp only [zero_le_one, sup_of_le_right, Int.ceil_zero, zero_sub, Int.reduceNeg,neg_lt_self_iff, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, Left.neg_nonpos_iff, sup_of_le_left, Int.cast_zero, sub_self, max_self, zero_mul, add_zero, mul_zero, zero_add]
      ring
    · rw [phiReal, hc', phiReal]
      simp only [add_sub_cancel_right, Nat.cast_sum, Nat.cast_nonneg, max_eq_right, Int.cast_natCast, sub_self, zero_mul, add_zero]
      rw [mul_assoc, ← mul_add, mul_eq_mul_left_iff, max_eq_right, max_eq_right, max_eq_right]
      simp only [Int.ceil_natCast, Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_sub_cancel, one_mul, one_div, inv_eq_zero, Nat.cast_eq_zero]
      left
      rw [mul_comm, add_right_cancel_iff]
      calc
        _ = ∑ x ∈ insert (n : ℤ) (Finset.Icc (1 : ℤ) (n - 1)), ↑(Nat.card ↥ G(S/R)_[(0 ⊔ x)] ) := by
          rw [insert_Icc_right (1 : ℤ) n]
          simp only [Nat.one_le_cast]
          exact Nat.one_le_iff_ne_zero.mpr hc''
        _ = _ := by
          simp only [Finset.mem_Icc, Nat.one_le_cast, le_sub_self_iff, Int.reduceLE, and_false, not_false_eq_true, Finset.sum_insert, Nat.cast_nonneg, sup_of_le_right, add_comm]
      apply Int.le_ceil_iff.2
      simp only [Int.cast_zero, zero_sub]
      apply lt_of_lt_of_le (by linarith) (Nat.cast_nonneg n)
      rw [le_sub_iff_add_le]
      apply Int.le_ceil_iff.2
      simp only [zero_add, Int.cast_one, sub_self, Nat.cast_pos]
      omega
      omega

theorem a {n : ℕ} : ∀ x ∈ Set.Ico (n : ℝ) (n + 1 : ℝ), HasDerivWithinAt (phiReal R S) (1 / (Nat.card ↥ G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(↑n + 1)])) (Set.Ici x) x := by
  intro x hx
  have hx' : x ∈ Set.Icc (n : ℝ) (n + 1 : ℝ) := ⟨hx.left, by linarith [hx.right]⟩
  let linear_fn := (fun y : ℝ =>
    phiReal R S n + (1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)]) * (y - n))
  have h_eq : phiReal R S =ᶠ[𝓝[≥] x] linear_fn := by
    filter_upwards [Ico_mem_nhdsGE_of_mem ⟨le_refl x, hx.right⟩] with y hy
    exact phiReal_linear_section R S ⟨by apply le_trans hx.left hy.left, by linarith [hy.right]⟩
  have h_deriv_linear : HasDerivWithinAt linear_fn
      ((1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)])) (Set.Ici x) x := by
    have : linear_fn = fun y =>
        ((1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)])) * y +
        (phiReal R S n - ((1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)])) * n) := by
      ext y; ring
    rw [this]
    simpa [id_eq, mul_one, add_zero] using HasDerivWithinAt.add ((hasDerivWithinAt_id x (Set.Ici x)).const_mul ((1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)]))) (hasDerivWithinAt_const x (Set.Ici x) (phiReal R S n - ((1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)])) * n))
  apply HasDerivWithinAt.congr_of_eventuallyEq h_deriv_linear h_eq
  unfold linear_fn
  exact phiReal_linear_section R S hx'

theorem sum_diff_eq_floor {n : ℕ} {y : ℝ} (hy : n ≤ y) : ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ ((G(S/R)_[(n + 1)] : Set (S ≃ₐ[R] S)).toFinset), truncatedLowerIndexReal R S (y + 1) x = ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ ((G(S/R)_[(n + 1)] : Set (S ≃ₐ[R] S)).toFinset), truncatedLowerIndexReal R S (n + 1) x := by
  have h : ∀ i ∈ ((decompositionGroup R S) : Set (S ≃ₐ[R] S)).toFinset \ (G(S/R)_[(n + 1)] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S (n + 1) i = truncatedLowerIndexReal R S (y + 1) i := by
    intro i hi
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hi
    rcases hi with ⟨hi1, hi2⟩
    unfold truncatedLowerIndexReal
    have hnetop : i_[S/R] i ≠ ⊤ := by
      by_contra hc
      apply hi2
      rw [(lowerIndex_eq_top_iff_eq_refl hi1).1 hc]
      exact Subgroup.one_mem _
    simp only [hnetop, ↓reduceDIte]
    have h : (WithTop.untop ( i_[S/R] i) hnetop) ≤ (n : ℝ) + 1 := by
      by_contra hc
      push_neg at hc
      apply hi2
      apply (mem_lowerRamificationGroup_iff R S hi1 (n + 1)).2
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, Nat.cast_lt] at hc
      rw [show ↑((n + 1 : ℕ) : ℕ∞) + (1 : ℕ∞) = ((n + 1 + 1 : ℕ) : ℕ∞) by rfl]
      exact (WithTop.le_untop_iff hnetop).1 (Nat.succ_le_of_lt hc)
    rw [min_eq_right, min_eq_right]
    exact le_trans h (by linarith [hy])
    exact h
  apply Eq.symm ((Finset.sum_eq_sum_iff_of_le _).mpr _)
  exact fun i hi => le_of_eq (h i hi)
  exact h


theorem aux_linear_section {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ico (n : ℝ) (n + 1 : ℝ)) : (fun y => ∑ t ∈ ((decompositionGroup R S) : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S (y + 1) t) =ᶠ[𝓝[≥] x] (fun y => ∑ t ∈ ((decompositionGroup R S) : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S (n + 1) t + (y - n) * (Nat.card G(S/R)_[(n + 1)])) := by
  filter_upwards [Ico_mem_nhdsGE_of_mem ⟨le_refl x, hx.right⟩] with y hy
  have hy1 : y + 1 ≤ (n + 1 : ℕ) + 1 := by rw [Nat.cast_add, Nat.cast_one]; linarith [hy.2]
  have hn1 : (n : ℝ) + 1 ≤ (n + 1 : ℕ) + 1 := by rw [Nat.cast_add, Nat.cast_one]; linarith
  obtain hy2 := auxx_1 R S hy1
  obtain hn2 := auxx_1 R S (n := n + 1) (u := n + 1) hn1
  simp only [Nat.cast_add, Nat.cast_one] at hy2 hn2
  rw [decompositionGroup_eq_diff R S (n + 1), Finset.sum_union (Finset.sdiff_disjoint), Finset.sum_union (Finset.sdiff_disjoint), sum_diff_eq_floor R S (le_trans hx.1 hy.1), add_assoc, add_left_cancel_iff, hy2, hn2, Finset.sum_const, Finset.sum_const]
  simp only [Set.toFinset_card, SetLike.coe_sort_coe, smul_add, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]
  ring

theorem b {n : ℕ} : ∀ x ∈ Set.Ico (n : ℝ) (n + 1 : ℝ), HasDerivWithinAt (fun u ↦ 1 / ↑(Nat.card ↥ G(S/R)_[0] ) * ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S (u + 1) x - 1) ((1 / (Nat.card ↥ G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(↑n + 1)]))) (Set.Ici x) x := by
  intro x hx
  apply ((HasDerivWithinAt.congr_of_eventuallyEq _ (aux_linear_section R S hx) _).const_mul _).sub_const _
  · obtain h := ((hasDerivWithinAt_id x (Set.Ici x)).const_mul (Nat.card G(S/R)_[((n : ℤ) + 1)] : ℝ)).sub_const ((Nat.card G(S/R)_[((n : ℤ) + 1)] : ℝ) * n)
    simp only [id_eq, mul_one] at h
    simp only [mul_comm _ (Nat.card G(S/R)_[(n + 1)] : ℝ), mul_sub]
    exact h.const_add _
  · simpa using (aux_linear_section R S hx).eq_of_nhdsWithin

theorem c {n : ℕ} : ContinuousOn (phiReal R S) (Set.Icc (↑n) (↑n + 1)) := by
  let g : ℝ → ℝ := fun x => phiReal R S n + (1 / Nat.card G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(n + 1)]) * (x - n)
  apply ContinuousOn.congr (f := g)
  apply ContinuousOn.add (continuousOn_const)
  apply ContinuousOn.mul (continuousOn_const)
  apply ContinuousOn.add (continuousOn_id' (Set.Icc (n : ℝ) (n + 1 : ℝ))) (continuousOn_const)
  intro x hx
  apply phiReal_linear_section R S hx

theorem d {n : ℕ} : ContinuousOn (fun u ↦ 1 / ↑(Nat.card ↥ G(S/R)_[0] ) * ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S (u + 1) x - 1) (Set.Icc (↑n) (↑n + 1)) := by
  apply ContinuousOn.sub _ (continuousOn_const)
  apply ContinuousOn.mul (continuousOn_const)
  apply continuousOn_finset_sum
  intro i hi
  unfold AlgEquiv.truncatedLowerIndexReal
  by_cases h_top : i_[S/R] i = ⊤
  · have : (fun a ↦ if h : i_[S/R] i = ⊤ then a + 1 else (a + 1) ⊓ ↑(WithTop.untop (i_[S/R] i) h)) = (fun a : ℝ => a + 1) := by
      ext a
      simp [h_top]
    rw [this]
    apply ContinuousOn.add (continuousOn_id) (continuousOn_const)
  · have h_not_top : ¬(i_[S/R] i = ⊤) := h_top
    let c : ℝ := ↑(WithTop.untop (i_[S/R] i) h_not_top)
    have : (fun a : ℝ =>
        if h : i_[S/R] i = ⊤ then a + 1 else (a + 1) ⊓ ↑(WithTop.untop (i_[S/R] i) h))
        = (fun a : ℝ => (a + 1) ⊓ c) := by
      ext a
      simp [h_not_top]
      rfl
    rw [this]
    refine Continuous.continuousOn ?_
    have h1 : Continuous fun a : ℝ => a + 1 := by
      apply Continuous.add (continuous_id) (continuous_const)
    have h2 : Continuous fun _ : ℝ => c := continuous_const
    exact Continuous.min h1 h2

theorem phiReal_eq_sum_inf_pos_aux {n : ℕ} : ∀ u ∈ Set.Icc (n : ℝ) (n + 1 : ℝ), (phiReal R S u) = (1 / Nat.card G(S/R)_[0]) * ((Finset.sum (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset) (AlgEquiv.truncatedLowerIndexReal R S (u + 1) ·)) - 1 := by
  induction' n with n ih
  <;> intro u hu
  · apply eq_of_has_deriv_right_eq (a := (0 : ℕ)) (b := (0 : ℕ) + 1) (f' := fun u => (1 / (Nat.card ↥ G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[1])))
    · exact a R S
    · exact b R S
    · exact c R S
    · exact d R S
    · simp only [CharP.cast_eq_zero, zero_add, phiReal_zero_eq_zero]
      symm
      rw [sub_eq_zero, one_div, inv_mul_eq_one₀]
      · rw [sum_truncatedLowerIndexReal_eq_of_le_one R S (by linarith [hu.left]) (by linarith [hu.left]), mul_one]
      · apply ne_of_gt
        simp only [Nat.cast_pos, Nat.card_pos]
    · exact hu
  · apply eq_of_has_deriv_right_eq (a := ↑(n + (1 : ℕ))) (b := ↑(n + (1 : ℕ)) + 1) (f' := (fun u => (1 / (Nat.card ↥ G(S/R)_[0] : ℝ)) * (Nat.card G(S/R)_[(n + 2)])))
    · exact a R S
    · exact b R S
    · exact c R S
    · exact d R S
    · apply ih
      apply Set.mem_Icc.2
      refine ⟨by rw [Nat.cast_add]; linarith, by rw [Nat.cast_add, Nat.cast_one]⟩
    · exact hu


theorem phiReal_eq_sum_inf_neg_aux {u : ℝ} (hu1 : -1 ≤ u) (hu2 : u ≤ 0) : (phiReal R S u) = (1 / Nat.card G(S/R)_[0]) * ((Finset.sum (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset (AlgEquiv.truncatedLowerIndexReal R S (u + 1) ·))) - 1 := by
  unfold phiReal
  rw [Finset.Icc_eq_empty_of_lt, Finset.sum_empty, max_eq_left, zero_add, Int.cast_zero, sub_zero, one_div, mul_comm, mul_assoc, max_eq_left, mul_inv_cancel₀, mul_one]
  · rw [sum_truncatedLowerIndexReal_eq_of_le_one R S (by linarith) (by linarith)]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul, eq_sub_iff_add_eq]
    apply ne_of_gt
    simp only [Nat.cast_pos, Nat.card_pos]
  · apply ne_of_gt
    simp only [Nat.cast_pos, Nat.card_pos]
  · apply Int.ceil_le.2
    simpa [Int.cast_zero]
  · rw [sub_le_iff_le_add, Int.ceil_le]
    apply le_trans hu2
    simp only [zero_add, Int.cast_one, zero_le_one]
  · rw [sub_lt_iff_lt_add, Int.ceil_lt_iff]
    simp only [Int.reduceAdd, Int.cast_ofNat]
    apply le_trans hu2 (by linarith)

theorem phiReal_eq_sum_inf_aux {u : ℝ} (hu : -1 ≤ u) : (phiReal R S u) = (1 / Nat.card G(S/R)_[0]) * ((Finset.sum (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset (AlgEquiv.truncatedLowerIndexReal R S (u + 1) ·))) - 1 := by
  by_cases hu' : 0 < u
  · apply phiReal_eq_sum_inf_pos_aux R S (n := (⌈u⌉ - 1).toNat)
    rw [Int.pred_toNat, ← Int.cast_natCast, Nat.cast_sub ((Int.le_toNat ((Int.ceil_nonneg (le_of_lt hu')))).mpr (Int.one_le_ceil_iff.2 hu')), Int.toNat_of_nonneg ((Int.ceil_nonneg (le_of_lt hu'))), Nat.cast_one, Int.cast_sub, Int.cast_one, sub_add_cancel, Set.mem_Icc]
    refine ⟨(le_trans ?_ (Int.floor_le u)), Int.le_ceil u⟩
    · rw [tsub_le_iff_right, ← Int.cast_one, ← Int.cast_add, Int.cast_le]
      apply Int.ceil_le_floor_add_one
  · exact phiReal_eq_sum_inf_neg_aux R S hu (le_of_not_gt hu')

theorem phiReal_eq_phi {u : ℚ} : phiReal R S u = phi R S u := by
  unfold phiReal phi phiDeriv
  simp only [← Finset.sum_div, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, ← mul_div_assoc, ← add_div, one_div_mul_eq_div]
  simp only [Rat.ceil_cast, Int.cast_max, Int.cast_zero, Int.cast_sub, Int.cast_one, Int.ceil_intCast, Rat.cast_sum, Rat.cast_natCast, Rat.cast_sub, Rat.cast_max, Rat.cast_zero, Rat.cast_intCast, Rat.cast_one]

theorem phi_eq_sum_inf_aux {u : ℚ} (hu : -1 ≤ u) : (phi R S u) = (1 / Nat.card G(S/R)_[0]) * ((Finset.sum (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset (AlgEquiv.truncatedLowerIndexReal R S (u + 1) ·))) - 1 := by
  rw [← phiReal_eq_phi R S]
  apply phiReal_eq_sum_inf_aux R S
  rw [← Rat.cast_one, ← Rat.cast_neg, Rat.cast_le]
  exact hu
