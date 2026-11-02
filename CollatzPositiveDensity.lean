import Erdos1135.ND.PositiveDensity.ExplicitUnitSeedPositiveDensityPair

namespace CollatzPositiveDensity

def step (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

def fastConvergent (C : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∃ k : ℕ, (k : ℝ) ≤ C * Real.log (n : ℝ) ∧ step^[k] n = 1

noncomputable def densityConstant : ℚ :=
  Erdos1135.ND.PositiveDensity.explicitPositiveDensityUnitSeedConstant

noncomputable def cutoff : ℕ :=
  Erdos1135.ND.PositiveDensity.explicitPositiveDensityUnitSeedCutoff

noncomputable def countBelow (C : ℝ) (X : ℕ) : ℕ := by
  classical
  exact Nat.count (fastConvergent C) X

theorem densityConstant_pos : 0 < densityConstant :=
  Erdos1135.ND.PositiveDensity.explicitPositiveDensityUnitSeedConstant_pos

theorem cutoff_pos : 0 < cutoff :=
  Erdos1135.ND.PositiveDensity.explicitPositiveDensityUnitSeedCutoff_pos

theorem positive_density (X : ℕ) (hX : cutoff ≤ X) :
    (densityConstant : ℝ) * X ≤ (countBelow (523 / 50) X : ℝ) := by
  exact Erdos1135.ND.PositiveDensity.explicitPositiveDensityUnitSeedCount_ten46 X hX

theorem positive_density_ten48 (X : ℕ) (hX : cutoff ≤ X) :
    (densityConstant : ℝ) * X ≤ (countBelow (262 / 25) X : ℝ) := by
  exact Erdos1135.ND.PositiveDensity.explicitPositiveDensityUnitSeedCount_ten48 X hX

end CollatzPositiveDensity
