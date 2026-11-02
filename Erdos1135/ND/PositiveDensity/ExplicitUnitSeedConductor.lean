import Erdos1135.ND.PositiveDensity.ExplicitTernaryHeightPositiveDensityPair
import Erdos1135.ND.PositiveDensity.ExplicitUnitSupportedFrozenSeed

namespace Erdos1135.ND.PositiveDensity

noncomputable section

theorem explicitUnitSeedSixthBudget_scaled {M C : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hbudget : 88 * M * C ≤ (m:ℝ)^6) :
    88 * M * ((2/3:ℝ) * C / (m:ℝ)^4) ≤ (2/3:ℝ) * (m:ℝ)^2 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (m:ℝ)^4)).2
  nlinarith only [hbudget]

@[irreducible] def explicitUnitSeedConductorFor (M C : ℕ) : ℕ :=
  Nat.nthRoot 6 (88 * M * C) + 1

theorem explicitUnitSeedConductorFor_budget (M C : ℕ) :
    1 ≤ explicitUnitSeedConductorFor M C ∧
      88 * M * C ≤ explicitUnitSeedConductorFor M C ^ 6 := by
  unfold explicitUnitSeedConductorFor
  exact ⟨by omega, (Nat.lt_pow_nthRoot_add_one (by decide : 6 ≠ 0) _).le⟩

theorem explicitUnitSeedConductorFor_le (M C : ℕ) :
    explicitUnitSeedConductorFor M C ≤ explicitNormalizedSixthConductorFor M C := by
  unfold explicitUnitSeedConductorFor explicitNormalizedSixthConductorFor
  apply Nat.add_le_add_right
  apply (Nat.le_nthRoot_iff (by decide : 6 ≠ 0)).2
  exact (Nat.pow_nthRoot_le (Or.inl (by decide : 6 ≠ 0))).trans
    (Nat.mul_le_mul_right C (Nat.mul_le_mul_right M (by decide : 88 ≤ 176)))

theorem explicitTernaryAccumulatedExponent_monotone (b : ℕ) :
    Monotone (explicitTernaryAccumulatedExponent b) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [explicitTernaryAccumulatedExponent]
  omega

theorem explicitTernaryPublicCutoff_monotone (b M : ℕ) :
    Monotone (explicitTernaryPublicCutoff b M) := by
  intro N K hNK
  have he := explicitTernaryAccumulatedExponent_monotone b hNK
  have hf := explicitSeedFloor_monotone b hNK
  unfold explicitTernaryPublicCutoff explicitTernaryIntervalHeight
  gcongr
  norm_num

end

end Erdos1135.ND.PositiveDensity
