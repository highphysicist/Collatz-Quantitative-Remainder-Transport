import Erdos1135.ND.PositiveDensity.ExplicitTernaryDivisorHeight

namespace Erdos1135.ND.PositiveDensity

noncomputable section

@[irreducible] def explicitTernaryDensityCutoffAt (b C : ℕ) : ℕ :=
  let N := explicitLogarithmicSeedGeneration b C
  let M := explicitOnePeriodSeedRootBound b N
  let m := explicitNormalizedSixthConductorFor M C
  explicitTernaryPublicCutoff b M (explicitMaximumPublicGeneration b C N m)

@[irreducible] def explicitPositiveDensityTernaryCutoff : ℕ :=
  explicitTernaryDensityCutoffAt explicitDensityFloor explicitSyracuseMixingCoefficient

end

end Erdos1135.ND.PositiveDensity
