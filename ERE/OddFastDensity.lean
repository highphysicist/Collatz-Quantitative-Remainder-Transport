import ERE.OddFastSourceCount
import Erdos1135.ND.PositiveDensity.ExplicitUnitSeedPositiveDensityPair

namespace Erdos1135.ND.PositiveDensity

open scoped BigOperators

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem oddPublicCount_ten46_from_potential_and_height
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (hb : 512 ^ 5 ≤ U.floor)
    (hseed : ∀ i, Tao.syracuse (U.state.root i) = 1)
    (cap : ℕ → ℕ) {e L : ℕ} (he : U.rootSpan e)
    (hcap : ∀ n, cap n ≤ L * (n + 1))
    {Cclock eta Pbar : ℝ} (hCclock : 250 ≤ Cclock)
    (htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet Cclock)
    (hP : 0 < U.parentSourcePotential) (heta : 0 ≤ eta)
    (hPbar : U.parentSourcePotential ≤ Pbar)
    (N H : ℕ) (hN : 1000000000 * (e + L + 3) ≤ N)
    (hH : ∀ i : (U.iterate cap N).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.iterate cap N).floor
        ((U.iterate cap N).state.root i) ≤ H)
    (hmass : ∀ n, N ≤ n →
      let V := U.forwardIterate cap n;
      ∀ (X : ℝ) (hX : 0 < X)
        (hi : ∀ i : V.state.Label,
          ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
          X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
        eta ≤ U.fullGoodCoreTerminalMass cap ndRootCoreWidth n (V.fullTerminalShift X hX hi) 1) :
    ∀ Y : ℕ, 32 * (H + 1) ≤ Y →
      eta / (32 * Pbar) * Y ≤
        (Terras.natCount (oddRawCollatzLogTimeOneSet (523 / 50 : ℝ)) Y : ℝ) := by
  intro Y hY
  have hcount := U.oddPublicCount_from_explicit_start_and_clock hseed cap he hcap
    hCclock htarget hP (fun n shift z hc hg =>
      U.fullGoodCoreTerminal_source_mem_rawCollatzLogTimeOneSet_ten46 hb hseed cap n shift 1 z hc hg)
    N H hN hH hmass Y hY
  apply le_trans _ hcount
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg Y)
  exact div_le_div_of_nonneg_left heta (by positivity : (0 : ℝ) < 32 * U.parentSourcePotential)
    (mul_le_mul_of_nonneg_left hPbar (by norm_num))

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem odd_explicit_count_ten46_from_supplied_margin_and_reference_height
    {b : ℕ} (hb : 2 ^ 80 ≤ b) (M Nmark : ℕ) (a : ℝ) (ha : 0 < a)
    (hsupplied : ∃ (r : ℕ) (hr : Odd r) (hl : 16 ^ b ≤ r),
      r < M ∧ r ∈ oddSyracuseLogTimeOneSet 250 ∧ Tao.syracuse r = 1 ∧
      IsUnit (r : ZMod (3 ^ 1)) ∧
      ∀ n ≥ Nmark,
        let U := ndRootCoreSingletonState b r
          ((by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb) hr hl;
        let V := U.forwardIterate (fun j => 16 + j / 100) n;
        ∀ (X : ℝ) (hX : 0 < X)
          (hi : ∀ i : V.state.Label,
            ndGeom2ShiftedWideSymmetricPhysicalIntervalMin V.floor (V.state.root i) < X ∧
            X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax V.floor (V.state.root i)),
          a ≤ U.forwardCoreTerminalGoodDepthShiftUnitMass
            (fun j => 16 + j / 100) ndRootCoreWidth n (16 + n / 100) (V.floor / 4) X hX hi)
    {m : ℕ} (hm : 1 ≤ m)
    (Cbudget : ℝ) (hCbudget : 0 ≤ Cbudget)
    (hquadratic : ndExplicitQuadraticMixingAt Cbudget m)
    (hbudget : 88 * (M : ℝ) * Cbudget ≤ a * (m : ℝ) ^ 2)
    (p : ℕ) (hp : 0 < p)
    (href : ∀ y, ndSyracuseUnitReferenceDensity m y ≤ (2/3:ℝ)*(p:ℝ))
    (J : ℕ) (hJ : 20 * 10 ^ 9 ≤ J)
    (hstart : Nmark ≤ J)
    (hroom : ∀ U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState,
      U.floor = b → ∀ n, J ≤ n →
        m ≤ (U.forwardIterate (fun j => 16 + j / 100) n).floor / 4)
    (H : ℕ)
    (hheight : ∀ U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState,
      U.floor = b → (∀ i, U.state.root i ≤ M) →
      ∀ i : (U.iterate (fun j => 16 + j / 100) J).state.Label,
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
          (U.iterate (fun j => 16 + j / 100) J).floor
          ((U.iterate (fun j => 16 + j / 100) J).state.root i) ≤ H) :
    ∀ Y : ℕ,
      32 * (H + 1) ≤ Y →
      (9 * a / (512 * (M : ℝ) * (p : ℝ))) * Y ≤
        (Terras.natCount (oddRawCollatzLogTimeOneSet (523 / 50 : ℝ)) Y : ℝ) := by
  obtain ⟨r, hr, hl, hbound, ht, hhit, _hunit, hgood⟩ := hsupplied
  have hb200 : 200 ≤ b := (by norm_num : (200 : ℕ) ≤ 2 ^ 80).trans hb
  let U := ndRootCoreSingletonState b r hb200 hr hl
  let cap := fun j : ℕ => 16 + j / 100
  have he : U.rootSpan 0 := by intro i j; change r ≤ 2 ^ 0 * r; simp
  have hcap : ∀ j, cap j ≤ 17 * (j + 1) := by
    intro j
    have hj := Nat.div_le_self j 100
    dsimp [cap]
    omega
  have htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet 250 := fun _ => ht
  have hseed : ∀ i, Tao.syracuse (U.state.root i) = 1 := fun _ => hhit
  have hP : U.parentSourcePotential = (r : ℝ) := by
    change ndGeom2PredictableRootSideParentSourcePotential (Finset.univ : Finset Unit)
      (fun _ => (1 : ℝ)) (fun _ => r) = _
    simp [ndGeom2PredictableRootSideParentSourcePotential]
  have hPpos : 0 < U.parentSourcePotential := by rw [hP]; exact_mod_cast hr.pos
  have hPbar : U.parentSourcePotential ≤ (M : ℝ) := by
    rw [hP]
    exact_mod_cast hbound.le
  have hsq : 88 * U.parentSourcePotential * Cbudget ≤ a * (m : ℝ) ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hPbar hCbudget
    linarith only [hbudget, hp]
  have hcount := U.oddPublicCount_ten46_from_potential_and_height
    ((by norm_num : (512 : ℕ) ^ 5 ≤ 2 ^ 80).trans hb) hseed cap he hcap
    (by norm_num : (250 : ℝ) ≤ 250) htarget hPpos
    (show 0 ≤ 9 * a / (16 * (p : ℝ)) by positivity)
    hPbar J H (by norm_num at hJ ⊢; exact hJ) (hheight U rfl (fun _ => hbound.le))
    (fun n hn X hX hi =>
      U.fullGoodCoreTerminalMass_ge_of_square_budget_and_height cap ndRootCoreWidth n (cap n) m
        ((U.forwardIterate cap n).floor / 4) hm (hroom U rfl n hn)
        (Nat.div_le_self _ _) (by norm_num : (250 : ℝ) ≤ 250) htarget hCbudget
        hquadratic ha
        hsq p hp href X hX hi (hgood n (hstart.trans hn) X hX hi))
  intro Y hY
  have h := hcount Y hY
  convert h using 1 <;> ring


theorem odd_explicit_count_ten46_from_onePeriod_full_unit_seed
    {b : ℕ} (hb : 2 ^ 80 ≤ b) (C : ℕ)
    (hmix : Tao.syracFineScaleMixingAt 6 (C : ℝ))
    {N : ℕ} (hN : explicitLogarithmicSeedGeneration b C ≤ N)
    {m : ℕ} (hm : 1 ≤ m)
    (hsixth : 88 * explicitOnePeriodSeedRootBound b N * C ≤ m ^ 6) :
    ∀ Y : ℕ,
      explicitTernaryPublicCutoff b (explicitOnePeriodSeedRootBound b N)
        (explicitMaximumPublicGeneration b C N m) ≤ Y →
      (3 / (256 * (explicitOnePeriodSeedRootBound b N : ℝ) * ((2 ^ m : ℕ) : ℝ))) * Y ≤
        (Terras.natCount (oddRawCollatzLogTimeOneSet (523 / 50 : ℝ)) Y : ℝ) := by
  have hscaled := explicitUnitSeedSixthBudget_scaled hm
    (show (88 : ℝ) * (explicitOnePeriodSeedRootBound b N : ℝ) * C ≤ (m : ℝ) ^ 6 by
      exact_mod_cast hsixth)
  unfold explicitTernaryPublicCutoff
  have hc := odd_explicit_count_ten46_from_supplied_margin_and_reference_height hb
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


private theorem odd_unit_seed_pair_recipe (b C : ℕ) (hb : 2 ^ 80 ≤ b)
    (hmix : Tao.syracFineScaleMixingAt 6 (C:ℝ)) :
    0 < explicitUnitSeedDensityConstantAt b C ∧
      0 < explicitUnitSeedDensityCutoffAt b C ∧
      2 * explicitRetainedDensityConstantAt b C ≤ explicitUnitSeedDensityConstantAt b C ∧
      explicitRetainedDensityConstantAt b C < explicitUnitSeedDensityConstantAt b C ∧
      explicitUnitSeedDensityCutoffAt b C ≤ explicitTernaryDensityCutoffAt b C ∧
      ∀ X : ℕ, explicitUnitSeedDensityCutoffAt b C ≤ X →
        (explicitUnitSeedDensityConstantAt b C : ℝ) * X ≤
          (Terras.natCount (oddRawCollatzLogTimeOneSet (523/50:ℝ)) X : ℝ) := by
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
  · have h := odd_explicit_count_ten46_from_onePeriod_full_unit_seed hb C hmix
      (N := N) le_rfl hm.1 hm.2
    intro X hX
    push_cast
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h X hX


private theorem odd_numerical_unit_seed_pair :
    0 < explicitPositiveDensityUnitSeedConstant ∧
      0 < explicitPositiveDensityUnitSeedCutoff ∧
      2 * explicitPositiveDensityRetainedConstant ≤ explicitPositiveDensityUnitSeedConstant ∧
      explicitPositiveDensityRetainedConstant < explicitPositiveDensityUnitSeedConstant ∧
      explicitPositiveDensityUnitSeedCutoff ≤ explicitPositiveDensityTernaryCutoff ∧
      ∀ X : ℕ, explicitPositiveDensityUnitSeedCutoff ≤ X →
        (explicitPositiveDensityUnitSeedConstant : ℝ) * X ≤
          (Terras.natCount (oddRawCollatzLogTimeOneSet (523/50:ℝ)) X : ℝ) := by
  have hb : 2 ^ 80 ≤ explicitDensityFloor := by unfold explicitDensityFloor; rfl
  have h := odd_unit_seed_pair_recipe explicitDensityFloor explicitSyracuseMixingCoefficient hb
    explicitSyracuseMixing_six
  unfold explicitPositiveDensityUnitSeedConstant explicitPositiveDensityUnitSeedCutoff
    explicitPositiveDensityRetainedConstant explicitPositiveDensityTernaryCutoff
  exact h


/--
Explicit positive density of odd positive starts reaching one within
`(523/50) * log n` ordinary Collatz steps.

This retains the same explicit constant and cutoff as Mazur's public theorem,
because the finite sources counted in its proof are already odd.
-/
theorem explicitPositiveDensityOddUnitSeedCount_ten46 :
    ∀ X : ℕ, explicitPositiveDensityUnitSeedCutoff ≤ X →
      (explicitPositiveDensityUnitSeedConstant : ℝ) * X ≤
        (Terras.natCount
          (oddRawCollatzLogTimeOneSet (523 / 50 : ℝ)) X : ℝ) :=
  odd_numerical_unit_seed_pair.2.2.2.2.2

end

end Erdos1135.ND.PositiveDensity

#print axioms Erdos1135.ND.PositiveDensity.explicitPositiveDensityOddUnitSeedCount_ten46
