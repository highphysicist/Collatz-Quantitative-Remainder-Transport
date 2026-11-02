import Erdos1135.ND.PositiveDensity.ExplicitOnePeriodSeedToCount
import Erdos1135.ND.PositiveDensity.SyracuseBinaryAtomHeight

namespace Erdos1135.ND.PositiveDensity

noncomputable section

@[irreducible] def explicitMaximumPublicGeneration (b C N m : ℕ) : ℕ :=
  max (explicitLogarithmicGoodMarkedStart b C N)
    (max (explicitLogarithmicRoomStart m) (20 * 10 ^ 9))

theorem explicitMaximumPublicGeneration_monotone (b C N : ℕ) :
    Monotone (explicitMaximumPublicGeneration b C N) := by
  intro m k hmk
  have h := explicitLogarithmicRoomStart_mono hmk
  unfold explicitMaximumPublicGeneration
  omega

end

end Erdos1135.ND.PositiveDensity
