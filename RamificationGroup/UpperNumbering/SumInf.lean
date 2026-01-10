import RamificationGroup.HerbrandFunction.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Basic


open QuotientGroup IntermediateField DiscreteValuation Valued Valuation HerbrandFunction MeasureTheory.MeasureSpace intervalIntegral Pointwise AlgEquiv ExtDVR Asymptotics Filter intervalIntegral MeasureTheory Topology

variable (R S : Type*) [CommRing R] [Ring S] [Algebra R S] [Fintype (S ≃ₐ[R] S)] [Finite (S ≃ₐ[R] S)] [vS : Valued S ℤₘ₀] [DecidableEq (S ≃ₐ[R] S)]

noncomputable def μ : MeasureTheory.Measure ℝ := MeasureTheory.volume

noncomputable def phiReal (u : Real) : Real := (1 /(Nat.card ↥ G(S/R)_[0])) * (∑ x ∈ Finset.Icc 1 (⌈u⌉ - 1), (Nat.card G(S/R)_[(max 0 x)] : ℝ) + (u - (max 0 (⌈u⌉ - 1))) * (Nat.card G(S/R)_[(max 0 ⌈u⌉)] : ℝ))

noncomputable def AlgEquiv.truncatedLowerIndexReal (u : ℝ) (s : (S ≃ₐ[R] S)) : ℝ :=
    if h : i_[S/R] s = ⊤ then u
    else min u ((i_[S/R] s).untop h)

open Multiplicative in
theorem mem_lowerRamificationGroup_iff {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S) (n : ℕ) : s ∈ G(S/R)_[n] ↔ n + 1 ≤ i_[S/R] s := by sorry

theorem lowerIndex_ne_one' {s : S ≃ₐ[R] S} (hs' : s ∈ decompositionGroup R S) (hs : s ≠ .refl) : i_[S/R] s ≠ ⊤ := by sorry

theorem lowerIndex_pos {s : S ≃ₐ[R] S} (hs : s ∈ decompositionGroup R S ) : i_[S/R] s ≥ 0 := by sorry

noncomputable instance : Fintype (decompositionGroup R S : Set (S ≃ₐ[R] S)) :=  Fintype.ofFinite (decompositionGroup R S)

noncomputable instance : Fintype (G(S/R)_[0] : Set (S ≃ₐ[R] S)) := Fintype.ofFinite G(S/R)_[0]

noncomputable instance : Fintype G(S/R)_[0] := Fintype.ofFinite G(S/R)_[0]

theorem auxx {u : ℝ} (hu1 : u ≤ 1) (hu2 : 0 ≤ u) :  ∑ x ∈ ((decompositionGroup R S : Set (S ≃ₐ[R] S))).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x + ∑ x ∈ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x = ∑ x ∈ ((decompositionGroup R S : Set (S ≃ₐ[R] S))).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, 0 + ∑ x ∈ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x := by
  rw [add_right_cancel_iff]
  have h : ∀ i ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u i = 0 := by
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    intro i hi1 hi2
    unfold truncatedLowerIndexReal
    have h : i_[S/R] i ≠ ⊤ := by
      apply lowerIndex_ne_one' R S hi1
      by_contra hc
      apply hi2
      rw [hc]
      apply Subgroup.one_mem G(S/R)_[0]
    simp only [h, ↓reduceDIte]
    have : i_[S/R] i = 0 := by
      apply eq_of_ge_of_not_gt (lowerIndex_pos R S hi1)
      
      sorry
    rw[min_eq_right]
    · simp only [Nat.cast_eq_zero, this, WithTop.untop_zero]
    · simp only [this, WithTop.untop_zero]
      simp only [CharP.cast_eq_zero]
      exact hu2
  apply (Finset.sum_eq_sum_iff_of_le ?_).2
  exact h
  exact fun i hi ↦ le_of_eq (h i hi)

theorem sum_truncatedLowerIndexReal_eq_of_le_one {u : ℝ} (hu1 : u ≤ 1) (hu2 : 0 ≤ u) : ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x = (Nat.card G(S/R)_[0]) * u := by
  have hunion : (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset = (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ ((G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset) ∪ ((G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset) := by
    simp only [Finset.sdiff_union_self_eq_union, Finset.left_eq_union, Set.subset_toFinset, Set.coe_toFinset, SetLike.coe_subset_coe]
    unfold lowerRamificationGroup
    intro s hs
    simp only [neg_zero, zero_sub, Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, Subtype.forall, Subgroup.mem_mk, Set.mem_setOf_eq] at hs
    exact hs.left
  rw [hunion, Finset.sum_union]
  calc
    _ = ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset \ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, 0 +
    ∑ x ∈ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u x :=  auxx R S hu1 hu2
    _ = ∑ x ∈ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, u := by
      rw [Finset.sum_const, smul_zero, zero_add]
      have h : ∀ i ∈ (G(S/R)_[0] : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S u i = u := by
        simp only [Set.mem_toFinset, SetLike.mem_coe]
        intro i hi
        sorry
      apply (Finset.sum_eq_sum_iff_of_le ?_).2
      exact h
      exact fun i hi => le_of_eq (h i hi)
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


theorem b {n : ℕ} : ∀ x ∈ Set.Ico (n : ℝ) (n + 1 : ℝ), HasDerivWithinAt (fun u ↦ 1 / ↑(Nat.card ↥ G(S/R)_[0] ) * ∑ x ∈ (decompositionGroup R S : Set (S ≃ₐ[R] S)).toFinset, truncatedLowerIndexReal R S (u + 1) x - 1) ((1 / (Nat.card ↥ G(S/R)_[0] : ℝ) * (Nat.card G(S/R)_[(↑n + 1)]))) (Set.Ici x) x := by
  intro x hx
  apply HasDerivWithinAt.sub_const
  apply HasDerivWithinAt.const_mul
  unfold AlgEquiv.truncatedLowerIndexReal
  sorry

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
