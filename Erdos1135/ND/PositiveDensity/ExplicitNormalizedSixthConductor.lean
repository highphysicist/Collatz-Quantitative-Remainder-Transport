import Erdos1135.ND.PositiveDensity.ExplicitMaximumGuardPositiveDensityPair

namespace Erdos1135.ND.PositiveDensity

noncomputable section

theorem explicitMixing_quadratic_normalized {C : ℝ}
    (hmix : Tao.syracFineScaleMixingAt 6 C) {m : ℕ} (hm : 1 ≤ m) :
    ndExplicitQuadraticMixingAt ((2/3:ℝ) * C / (m:ℝ)^4) m := by
  intro k hmk
  rw [unitReferenceDensity_fullL1_eq_twoThirds_oscillation hmk]
  calc
    _ ≤ (2/3:ℝ) * (C / (m:ℝ)^6) :=
      mul_le_mul_of_nonneg_left (hmix k m hm hmk) (by norm_num)
    _ = _ := by rw [div_div, ← pow_add]; ring

@[irreducible] def explicitNormalizedSixthConductorFor (M C : ℕ) : ℕ :=
  Nat.nthRoot 6 (176 * M * C) + 1

end

end Erdos1135.ND.PositiveDensity
