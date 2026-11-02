import Erdos1135.ND.PositiveDensity.ExplicitRetainedMarginPositiveDensityPair

namespace Erdos1135.ND.PositiveDensity

noncomputable section

def explicitTernaryGrowthExponent (b : ℕ) : ℕ := 2 * b - 19 * b / 12

theorem explicitTernaryGrowthExponent_add (b : ℕ) :
    19 * b / 12 + explicitTernaryGrowthExponent b = 2 * b := by
  unfold explicitTernaryGrowthExponent
  omega

theorem explicitTernaryGrowthExponent_radius {b : ℕ} (hb : 200 ≤ b) :
    ndGeom2ShiftedWideSymmetricShiftRadius b + explicitTernaryGrowthExponent b ≤ 2 * b / 3 := by
  have hr := ndGeom2ShiftedWideSymmetricShiftRadius_add_two_margin hb
  have hc := ndBalancedTotal_le_two_mul (ndGeom2ShiftedWideSymmetricWidth b)
  have hl := nineteen_mul_div_twelve_le_ndBalancedTotal (ndGeom2ShiftedWideSymmetricWidth b)
  unfold ndGeom2ShiftedWideSymmetricGap ndGeom2ShiftedWideSymmetricMarginNat
    ndGeom2ShiftedWideSymmetricWidth at hr
  unfold ndGeom2ShiftedWideSymmetricWidth at hc hl
  unfold explicitTernaryGrowthExponent
  omega

theorem physicalIntervalMax_le_ternary_height {b root : ℕ} (hb : 200 ≤ b) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMax b root ≤ ((2 ^ (2 * b / 3) * root : ℕ) : ℝ) := by
  have hr := explicitTernaryGrowthExponent_radius hb
  have he := explicitTernaryGrowthExponent_add b
  have hl := two_pow_nineteen_mul_div_twelve_le_three_pow b
  let R := ndGeom2ShiftedWideSymmetricShiftRadius b
  have hpow : 2 ^ (2 * R + 2 * b) ≤ 2 ^ (2 * b / 3 + 2 + R + 19 * b / 12) :=
    Nat.pow_le_pow_right (by decide) (by dsimp [R]; omega)
  have hn : 2 ^ (2 * R) * 4 ^ b * root ≤ (2 ^ (2 * b / 3) * root) * (4 * 2 ^ R * 3 ^ b) := by
    calc
      _ = 2 ^ (2 * R + 2 * b) * root := by
        rw [show (4:ℕ) = 2^2 by decide, ← pow_mul, ← pow_add]
      _ ≤ 2 ^ (2 * b / 3 + 2 + R + 19 * b / 12) * root := Nat.mul_le_mul_right root hpow
      _ = (2 ^ (2 * b / 3) * root) * (4 * 2 ^ R * 2 ^ (19 * b / 12)) := by
        simp only [pow_add]
        norm_num
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hl)
  unfold ndGeom2ShiftedWideSymmetricPhysicalIntervalMax ndGeom2ShiftedWideSymmetricPhysicalLowerScale
  apply (div_le_iff₀ (by positivity)).2
  exact_mod_cast hn

def explicitTernaryAccumulatedExponent (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => explicitTernaryAccumulatedExponent b n + 17 + n / 100 +
      explicitTernaryGrowthExponent (explicitSeedFloor b n)

@[irreducible] def explicitTernaryIntervalHeight (b M N : ℕ) : ℕ :=
  2 ^ (explicitTernaryAccumulatedExponent b N + 2 * explicitSeedFloor b N / 3) * M

@[irreducible] def explicitTernaryPublicCutoff (b M N : ℕ) : ℕ :=
  32 * (explicitTernaryIntervalHeight b M N + 1)

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem next_root_le_ternary_twoPow
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (K : ℕ) (z : (U.next K).state.Label) :
    (U.next K).state.root z ≤ 2 ^ (K + 1 + explicitTernaryGrowthExponent U.floor) *
      U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) := by
  have hlower : ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)
  have h := ndGeom2PredictableRootSideUnitChildIncidence_threePow_mul_source_le_twoPow_capSucc_mul_fourPow_mul_parent
    U.state.root_odd (by have h := U.floor_twoHundred; omega) hlower z
  have hl := two_pow_nineteen_mul_div_twelve_le_three_pow U.floor
  have he := explicitTernaryGrowthExponent_add U.floor
  apply Nat.le_of_mul_le_mul_left (c := 2 ^ (19 * U.floor / 12)) _ (by positivity)
  calc
    _ ≤ 3 ^ U.floor * (U.next K).state.root z := Nat.mul_le_mul_right _ hl
    _ ≤ 2 ^ (K + 1) * 4 ^ U.floor *
        U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) := h
    _ = _ := by
      rw [show (4:ℕ) = 2^2 by decide, ← pow_mul]
      simp only [← mul_assoc, ← pow_add]
      congr 2
      omega

theorem iterate_root_le_ternary_accumulated
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (M : ℕ)
    (hroot : ∀ i, U.state.root i ≤ M) (n : ℕ) :
    ∀ i : (U.iterate (fun j => 16 + j / 100) n).state.Label,
      (U.iterate (fun j => 16 + j / 100) n).state.root i ≤
        2 ^ explicitTernaryAccumulatedExponent U.floor n * M := by
  induction n with
  | zero => simpa [iterate, explicitTernaryAccumulatedExponent] using hroot
  | succ n ih =>
    intro z
    let V := U.iterate (fun j => 16 + j / 100) n
    calc
      _ ≤ 2 ^ (16 + n / 100 + 1 + explicitTernaryGrowthExponent V.floor) *
          V.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) :=
        V.next_root_le_ternary_twoPow (16 + n / 100) z
      _ ≤ 2 ^ (16 + n / 100 + 1 + explicitTernaryGrowthExponent V.floor) *
          (2 ^ explicitTernaryAccumulatedExponent U.floor n * M) := Nat.mul_le_mul_left _ (ih _)
      _ = _ := by
        dsimp [V]
        rw [U.explicit_iterate_floor, explicitTernaryAccumulatedExponent, ← mul_assoc, ← pow_add]
        congr 2
        omega

theorem iterate_physicalIntervalMax_le_ternary
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (M : ℕ)
    (hroot : ∀ i, U.state.root i ≤ M) (n : ℕ)
    (i : (U.iterate (fun j => 16 + j / 100) n).state.Label) :
    ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
      (U.iterate (fun j => 16 + j / 100) n).floor
      ((U.iterate (fun j => 16 + j / 100) n).state.root i) ≤
      (explicitTernaryIntervalHeight U.floor M n : ℝ) := by
  have hr := U.iterate_root_le_ternary_accumulated M hroot n i
  apply le_trans (physicalIntervalMax_le_ternary_height
    (U.iterate (fun j => 16 + j / 100) n).floor_twoHundred)
  exact_mod_cast (show 2 ^ (2 * (U.iterate (fun j => 16 + j / 100) n).floor / 3) *
      (U.iterate (fun j => 16 + j / 100) n).state.root i ≤
      explicitTernaryIntervalHeight U.floor M n by
    calc
      _ ≤ 2 ^ (2 * (U.iterate (fun j => 16 + j / 100) n).floor / 3) *
          (2 ^ explicitTernaryAccumulatedExponent U.floor n * M) := Nat.mul_le_mul_left _ hr
      _ = _ := by
        rw [U.explicit_iterate_floor]
        unfold explicitTernaryIntervalHeight
        rw [← mul_assoc, ← pow_add, Nat.add_comm])

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135.ND.PositiveDensity
