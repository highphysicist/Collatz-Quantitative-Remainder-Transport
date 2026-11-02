import Erdos1135.ND.PositiveDensity.ExplicitUnitSeedConductor

namespace Erdos1135.ND.PositiveDensity

noncomputable section

theorem explicit_count_ten46_from_onePeriod_full_unit_seed
    {b : ℕ} (hb : 2 ^ 80 ≤ b) (C : ℕ)
    (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    {N : ℕ} (hN : explicitLogarithmicSeedGeneration b C ≤ N)
    {m : ℕ} (hm : 1 ≤ m)
    (hsixth : 88 * explicitOnePeriodSeedRootBound b N * C ≤ m ^ 6) :
    ∀ Y : ℕ,
      explicitTernaryPublicCutoff b (explicitOnePeriodSeedRootBound b N)
        (explicitMaximumPublicGeneration b C N m) ≤ Y →
      (3 / (256 * (explicitOnePeriodSeedRootBound b N : ℝ) * ((2 ^ m : ℕ) : ℝ))) * Y ≤
        (Terras.natCount (rawCollatzLogTimeOneSet (523 / 50 : ℝ)) Y : ℝ) := by
  have hscaled := explicitUnitSeedSixthBudget_scaled hm
    (show (88 : ℝ) * (explicitOnePeriodSeedRootBound b N : ℝ) * C ≤ (m : ℝ) ^ 6 by
      exact_mod_cast hsixth)
  unfold explicitTernaryPublicCutoff
  have hc := explicit_count_ten46_from_supplied_margin_and_reference_height hb
    (explicitOnePeriodSeedRootBound b N) (explicitLogarithmicGoodMarkedStart b C N)
    (2/3:ℝ) (by norm_num)
    (exists_bounded_logarithmic_uniform_twoThirds_seed_of_mark hb C hmix hN
      (explicitOnePeriodSeedRootBound b N) (exists_onePeriod_bounded_successful_full_core_mark hb N)) hm
    ((2/3:ℝ) * C / (m : ℝ) ^ 4) (by positivity)
    (explicitMixing_quadratic_normalized hmix hm) hscaled (2 ^ m) (by positivity)
    (unitReferenceDensity_binary_upper m)
    (explicitMaximumPublicGeneration b C N m)
    (by unfold explicitMaximumPublicGeneration; omega)
    (by unfold explicitMaximumPublicGeneration; omega)
    (by
      intro U hfloor n hn
      exact (U.explicitConductor_logarithmic_quarter_room_eighty
        (fun j => 16 + j / 100) m n (by rwa [hfloor]) (by
          unfold explicitMaximumPublicGeneration at hn; omega)).1)
    (explicitTernaryIntervalHeight b (explicitOnePeriodSeedRootBound b N)
      (explicitMaximumPublicGeneration b C N m))
    (by
      intro U hfloor hroot i
      simpa only [hfloor] using U.iterate_physicalIntervalMax_le_ternary
        (explicitOnePeriodSeedRootBound b N) hroot (explicitMaximumPublicGeneration b C N m) i)
  intro Y hY
  convert hc Y hY using 1 <;> ring

@[irreducible] def explicitUnitSeedDensityConstantAt (b C : ℕ) : ℚ :=
  let N := explicitLogarithmicSeedGeneration b C
  let M := explicitOnePeriodSeedRootBound b N
  let m := explicitUnitSeedConductorFor M C
  3 / (256 * (M : ℚ) * ((2 ^ m : ℕ) : ℚ))

@[irreducible] def explicitUnitSeedDensityCutoffAt (b C : ℕ) : ℕ :=
  let N := explicitLogarithmicSeedGeneration b C
  let M := explicitOnePeriodSeedRootBound b N
  let m := explicitUnitSeedConductorFor M C
  explicitTernaryPublicCutoff b M (explicitMaximumPublicGeneration b C N m)

@[irreducible] def explicitPositiveDensityUnitSeedConstant : ℚ :=
  explicitUnitSeedDensityConstantAt explicitDensityFloor explicitSyracuseMixingCoefficient

@[irreducible] def explicitPositiveDensityUnitSeedCutoff : ℕ :=
  explicitUnitSeedDensityCutoffAt explicitDensityFloor explicitSyracuseMixingCoefficient

private theorem unit_seed_pair_recipe (b C : ℕ) (hb : 2 ^ 80 ≤ b)
    (hmix : Tao.syracFineScaleMixingAt 6 (C:ℝ)) :
    0 < explicitUnitSeedDensityConstantAt b C ∧
      0 < explicitUnitSeedDensityCutoffAt b C ∧
      2 * explicitRetainedDensityConstantAt b C ≤ explicitUnitSeedDensityConstantAt b C ∧
      explicitRetainedDensityConstantAt b C < explicitUnitSeedDensityConstantAt b C ∧
      explicitUnitSeedDensityCutoffAt b C ≤ explicitTernaryDensityCutoffAt b C ∧
      ∀ X : ℕ, explicitUnitSeedDensityCutoffAt b C ≤ X →
        (explicitUnitSeedDensityConstantAt b C : ℝ) * X ≤
          (Terras.natCount (rawCollatzLogTimeOneSet (523/50:ℝ)) X : ℝ) := by
  unfold explicitUnitSeedDensityConstantAt explicitUnitSeedDensityCutoffAt
    explicitRetainedDensityConstantAt explicitTernaryDensityCutoffAt
  let N := explicitLogarithmicSeedGeneration b C
  let M := explicitOnePeriodSeedRootBound b N
  let m := explicitUnitSeedConductorFor M C
  let mold := explicitNormalizedSixthConductorFor M C
  have hM : 0 < M := explicitOnePeriodSeedRootBound_pos b N
  have hm := explicitUnitSeedConductorFor_budget M C
  have hmle : m ≤ mold := explicitUnitSeedConductorFor_le M C
  have hp : ((2^m:ℕ):ℚ) ≤ ((2^mold:ℕ):ℚ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : (1:ℕ) ≤ 2) hmle
  have hgain :
      2 * (3/(512*(M:ℚ)*((2^mold:ℕ):ℚ))) ≤
        3/(256*(M:ℚ)*((2^m:ℕ):ℚ)) := by
    calc
      _ = 3/(256*(M:ℚ)*((2^mold:ℕ):ℚ)) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hp (by positivity))
  refine ⟨by positivity, ?_, hgain, ?_, ?_, ?_⟩
  · unfold explicitTernaryPublicCutoff; positivity
  · have hpos : (0:ℚ) < 3/(512*(M:ℚ)*((2^mold:ℕ):ℚ)) := by positivity
    linarith only [hgain, hpos]
  · exact explicitTernaryPublicCutoff_monotone b M
      (explicitMaximumPublicGeneration_monotone b C N hmle)
  · have h := explicit_count_ten46_from_onePeriod_full_unit_seed hb C hmix
      (N := N) le_rfl hm.1 hm.2
    intro X hX
    push_cast
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h X hX

private theorem numerical_unit_seed_pair :
    0 < explicitPositiveDensityUnitSeedConstant ∧
      0 < explicitPositiveDensityUnitSeedCutoff ∧
      2 * explicitPositiveDensityRetainedConstant ≤ explicitPositiveDensityUnitSeedConstant ∧
      explicitPositiveDensityRetainedConstant < explicitPositiveDensityUnitSeedConstant ∧
      explicitPositiveDensityUnitSeedCutoff ≤ explicitPositiveDensityTernaryCutoff ∧
      ∀ X : ℕ, explicitPositiveDensityUnitSeedCutoff ≤ X →
        (explicitPositiveDensityUnitSeedConstant : ℝ) * X ≤
          (Terras.natCount (rawCollatzLogTimeOneSet (523/50:ℝ)) X : ℝ) := by
  have hb : 2 ^ 80 ≤ explicitDensityFloor := by unfold explicitDensityFloor; rfl
  have h := unit_seed_pair_recipe explicitDensityFloor explicitSyracuseMixingCoefficient hb
    explicitSyracuseMixing_six
  unfold explicitPositiveDensityUnitSeedConstant explicitPositiveDensityUnitSeedCutoff
    explicitPositiveDensityRetainedConstant explicitPositiveDensityTernaryCutoff
  exact h

theorem explicitPositiveDensityUnitSeedConstant_pos :
    0 < explicitPositiveDensityUnitSeedConstant := numerical_unit_seed_pair.1

theorem explicitPositiveDensityUnitSeedCutoff_pos :
    0 < explicitPositiveDensityUnitSeedCutoff := numerical_unit_seed_pair.2.1

theorem explicitPositiveDensityUnitSeedCount_ten46 :
    ∀ X : ℕ, explicitPositiveDensityUnitSeedCutoff ≤ X →
      (explicitPositiveDensityUnitSeedConstant : ℝ) * X ≤
        (Terras.natCount (rawCollatzLogTimeOneSet (523/50:ℝ)) X : ℝ) :=
  numerical_unit_seed_pair.2.2.2.2.2

theorem explicitPositiveDensityUnitSeedCount_ten48 :
    ∀ X : ℕ, explicitPositiveDensityUnitSeedCutoff ≤ X →
      (explicitPositiveDensityUnitSeedConstant : ℝ) * X ≤
        (Terras.natCount (rawCollatzLogTimeOneSet (262/25:ℝ)) X : ℝ) := by
  intro X hX
  apply (explicitPositiveDensityUnitSeedCount_ten46 X hX).trans
  exact_mod_cast Terras.natCount_mono
    (rawCollatzLogTimeOneSet_mono (by norm_num : (523/50:ℝ) ≤ 262/25)) X

end

end Erdos1135.ND.PositiveDensity
