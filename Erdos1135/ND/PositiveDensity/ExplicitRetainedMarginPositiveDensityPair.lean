import Erdos1135.ND.PositiveDensity.ExplicitNormalizedSixthConductor

namespace Erdos1135.ND.PositiveDensity

noncomputable section

@[irreducible] def explicitRetainedDensityConstantAt (b C : ℕ) : ℚ :=
  let N := explicitLogarithmicSeedGeneration b C
  let M := explicitOnePeriodSeedRootBound b N
  let m := explicitNormalizedSixthConductorFor M C
  3 / (512 * (M : ℚ) * ((2 ^ m : ℕ) : ℚ))

@[irreducible] def explicitPositiveDensityRetainedConstant : ℚ :=
  explicitRetainedDensityConstantAt explicitDensityFloor explicitSyracuseMixingCoefficient

end

end Erdos1135.ND.PositiveDensity
