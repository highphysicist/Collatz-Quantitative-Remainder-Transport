import ERE.DirectToOneLogarithmicCount
import ERE.FactorizedRemainderTransport

namespace EREQuantitativeTransport

open Erdos1135.ND.PositiveDensity

private noncomputable abbrev Cfast : Real := 523 / 50

/--
Common Mazur-counting engine. Any selector on the live targets that reaches
its target, lies in the requested residue, and has a uniform size bound
produces an explicit direct-to-one family of size Ω(X / log X).
-/
theorem direct_to_one_count_of_selector
    (N X r bound : Nat)
    (hX : explicitPositiveDensityUnitSeedCutoff ≤ X)
    (witness : Nat → Nat)
    (hreach :
      ∀ w ∈ liveTargetsBelow Cfast X,
        ERE.Reaches w (witness w))
    (hmod :
      ∀ w ∈ liveTargetsBelow Cfast X,
        witness w % N = r % N)
    (hbound :
      ∀ w ∈ liveTargetsBelow Cfast X,
        witness w ≤ bound) :
    ∃ W : Finset Nat,
      ((explicitPositiveDensityUnitSeedConstant : Real) * X) /
          (2 * (uniformLogTimeBound Cfast X + 4) : Nat) ≤
        (W.card : Real) ∧
      (∀ n ∈ W, n % N = r % N) ∧
      (∀ n ∈ W, ERE.Reaches 1 n) ∧
      (∀ n ∈ W, n ≤ bound) := by
  classical

  let targets := liveTargetsBelow Cfast X
  let W := targets.image witness
  let B := uniformLogTimeBound Cfast X

  have htargets :
      targets.card ≤ W.card * (B + 4) := by
    apply ERE.selected_witness_image_count targets witness B
    · intro w hw
      exact hreach w (by simpa [targets] using hw)
    · intro w hw
      exact liveTargetsBelow_uniform_time
        (C := Cfast) (by norm_num) X w
        (by simpa [targets] using hw)

  have hfinite :
      (oddFastBelow Cfast X).card ≤
        2 * W.card * (B + 4) := by
    calc
      (oddFastBelow Cfast X).card
          ≤ 2 * targets.card :=
        oddFast_card_le_two_mul_liveTargets_card Cfast X
      _ ≤ 2 * (W.card * (B + 4)) :=
        Nat.mul_le_mul_left 2 htargets
      _ = 2 * W.card * (B + 4) := by
        simp only [Nat.mul_assoc]

  have hMazur :
      (explicitPositiveDensityUnitSeedConstant : Real) * X ≤
        ((oddFastBelow Cfast X).card : Real) := by
    have h :=
      explicitPositiveDensityOddUnitSeedCount_ten46 X hX
    rw [← oddFastBelow_card_eq_natCount Cfast X] at h
    exact h

  have htransport :
      (explicitPositiveDensityUnitSeedConstant : Real) * X ≤
        (W.card : Real) * (2 * (B + 4) : Nat) := by
    have hfinite' :
        (oddFastBelow Cfast X).card ≤
          W.card * (2 * (B + 4)) := by
      calc
        (oddFastBelow Cfast X).card
            ≤ 2 * W.card * (B + 4) := hfinite
        _ = W.card * (2 * (B + 4)) := by
          ac_rfl
    calc
      (explicitPositiveDensityUnitSeedConstant : Real) * X
          ≤ ((oddFastBelow Cfast X).card : Real) := hMazur
      _ ≤ (W.card : Real) * (2 * (B + 4) : Nat) := by
        exact_mod_cast hfinite'

  have hdenNat : 0 < 2 * (B + 4) := by omega
  have hdenReal : (0 : Real) < (2 * (B + 4) : Nat) := by
    exact_mod_cast hdenNat

  refine ⟨W, ?_, ?_, ?_, ?_⟩

  · change
      ((explicitPositiveDensityUnitSeedConstant : Real) * X) /
          (2 * (B + 4) : Nat) ≤
        (W.card : Real)
    apply (div_le_iff₀ hdenReal).2
    simpa [mul_comm] using htransport

  · intro n hn
    have hn' : n ∈ targets.image witness := by simpa [W] using hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn'
    exact hmod w (by simpa [targets] using hw)

  · intro n hn
    have hn' : n ∈ targets.image witness := by simpa [W] using hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn'
    have hw' : w ∈ liveTargetsBelow Cfast X := by
      simpa [targets] using hw
    obtain ⟨steps, hsteps, hhit⟩ :=
      liveTargetsBelow_uniform_time
        (C := Cfast) (by norm_num) X w hw'
    exact ERE.reaches_trans (hreach w hw') ⟨steps, hhit⟩

  · intro n hn
    have hn' : n ∈ targets.image witness := by simpa [W] using hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn'
    exact hbound w (by simpa [targets] using hw)

/-- QRT-8: coprime-to-six modulus, with exponent `15 * (3*N*N)`. -/
theorem direct_to_one_logarithmic_count_coprime_six
    (N : Nat) (_hN : 1 ≤ N) (hN6 : N.Coprime 6)
    (X r : Nat)
    (hX : explicitPositiveDensityUnitSeedCutoff ≤ X) :
    ∃ W : Finset Nat,
      ((explicitPositiveDensityUnitSeedConstant : Real) * X) /
          (2 * (uniformLogTimeBound Cfast X + 4) : Nat) ≤
        (W.card : Real) ∧
      (∀ n ∈ W, n % N = r % N) ∧
      (∀ n ∈ W, ERE.Reaches 1 n) ∧
      (∀ n ∈ W,
        n ≤ (3 * X + 1) *
          2 ^ (2 ^ (15 * (3 * N * N)))) := by
  classical
  let targets := liveTargetsBelow Cfast X

  have hex :
      ∀ w, w ∈ targets →
        ∃ n, ERE.Reaches w n ∧
          n % N = r % N ∧
          n ≤ w * 2 ^ (2 ^ (15 * (3 * N * N))) := by
    intro w hw
    exact ERE.effective_remainder_transport_coprime_six
      N hN6 w
      (liveTarget_mem_not_divisible_by_three
        (by simpa [targets] using hw))
      r

  let witness := fun w =>
    if hw : w ∈ targets then Classical.choose (hex w hw) else 0

  have hspec :
      ∀ w (hw : w ∈ targets),
        ERE.Reaches w (witness w) ∧
        witness w % N = r % N ∧
        witness w ≤ w * 2 ^ (2 ^ (15 * (3 * N * N))) := by
    intro w hw
    simpa only [witness, dif_pos hw] using
      (Classical.choose_spec (hex w hw))

  apply direct_to_one_count_of_selector
    N X r
    ((3 * X + 1) * 2 ^ (2 ^ (15 * (3 * N * N))))
    hX witness

  · intro w hw
    exact (hspec w (by simpa [targets] using hw)).1

  · intro w hw
    exact (hspec w (by simpa [targets] using hw)).2.1

  · intro w hw
    have hwTargets : w ∈ targets := by simpa [targets] using hw
    have hwle : w ≤ 3 * X + 1 :=
      Nat.le_of_lt (liveTarget_mem_lt hw)
    exact Nat.le_trans (hspec w hwTargets).2.2
      (Nat.mul_le_mul_right
        (2 ^ (2 ^ (15 * (3 * N * N)))) hwle)

/-- QRT-9: power-of-three modulus, with exponent `15 * (3*3^b)`. -/
theorem direct_to_one_logarithmic_count_pow_three
    (b X r : Nat)
    (hX : explicitPositiveDensityUnitSeedCutoff ≤ X) :
    ∃ W : Finset Nat,
      ((explicitPositiveDensityUnitSeedConstant : Real) * X) /
          (2 * (uniformLogTimeBound Cfast X + 4) : Nat) ≤
        (W.card : Real) ∧
      (∀ n ∈ W, n % (3 ^ b) = r % (3 ^ b)) ∧
      (∀ n ∈ W, ERE.Reaches 1 n) ∧
      (∀ n ∈ W,
        n ≤ (3 * X + 1) *
          2 ^ (2 ^ (15 * (3 * 3 ^ b)))) := by
  classical
  let targets := liveTargetsBelow Cfast X

  have hex :
      ∀ w, w ∈ targets →
        ∃ n, ERE.Reaches w n ∧
          n % (3 ^ b) = r % (3 ^ b) ∧
          n ≤ w * 2 ^ (2 ^ (15 * (3 * 3 ^ b))) := by
    intro w hw
    exact ERE.effective_remainder_transport_pow_three
      b w
      (liveTarget_mem_not_divisible_by_three
        (by simpa [targets] using hw))
      r

  let witness := fun w =>
    if hw : w ∈ targets then Classical.choose (hex w hw) else 0

  have hspec :
      ∀ w (hw : w ∈ targets),
        ERE.Reaches w (witness w) ∧
        witness w % (3 ^ b) = r % (3 ^ b) ∧
        witness w ≤ w * 2 ^ (2 ^ (15 * (3 * 3 ^ b))) := by
    intro w hw
    simpa only [witness, dif_pos hw] using
      (Classical.choose_spec (hex w hw))

  apply direct_to_one_count_of_selector
    (3 ^ b) X r
    ((3 * X + 1) * 2 ^ (2 ^ (15 * (3 * 3 ^ b))))
    hX witness

  · intro w hw
    exact (hspec w (by simpa [targets] using hw)).1

  · intro w hw
    exact (hspec w (by simpa [targets] using hw)).2.1

  · intro w hw
    have hwTargets : w ∈ targets := by simpa [targets] using hw
    have hwle : w ≤ 3 * X + 1 :=
      Nat.le_of_lt (liveTarget_mem_lt hw)
    exact Nat.le_trans (hspec w hwTargets).2.2
      (Nat.mul_le_mul_right
        (2 ^ (2 ^ (15 * (3 * 3 ^ b)))) hwle)

/-- QRT-10: factor-sensitive modulus and Effective RE scale. -/
theorem direct_to_one_logarithmic_count_factorized
    (N alpha b M r Xscale e Y : Nat)
    (hN : 1 ≤ N)
    (hfactor : N = 2 ^ alpha * (3 ^ b * M))
    (hM : M.Coprime 6)
    (p : List Nat)
    (hplength : p.length = alpha)
    (hpbits : ∀ d ∈ p, d ≤ 1)
    (he : 3 ^ ERE.oneCount p * (r % N) + ERE.offset p =
      2 ^ alpha * e)
    (hXscale :
      3 * (3 ^ (ERE.oneCount p + b) * M * M) ≤ Xscale)
    (heX : e ≤ Xscale)
    (hY : explicitPositiveDensityUnitSeedCutoff ≤ Y) :
    ∃ W : Finset Nat,
      ((explicitPositiveDensityUnitSeedConstant : Real) * Y) /
          (2 * (uniformLogTimeBound Cfast Y + 4) : Nat) ≤
        (W.card : Real) ∧
      (∀ n ∈ W, n % N = r % N) ∧
      (∀ n ∈ W, ERE.Reaches 1 n) ∧
      (∀ n ∈ W,
        n ≤
          2 * (N *
            ((3 * Y + 1) *
              2 ^ (2 ^ (15 * Xscale))))) := by
  classical
  let targets := liveTargetsBelow Cfast Y

  have hex :
      ∀ w, w ∈ targets →
        ∃ n, ERE.Reaches w n ∧
          n % N = r % N ∧
          n ≤ 2 * (N *
            (w * 2 ^ (2 ^ (15 * Xscale)))) := by
    intro w hw
    exact ERE.effective_remainder_transport_factorized
      N alpha b M r w Xscale e
      hN hfactor hM
      (liveTarget_mem_not_divisible_by_three
        (by simpa [targets] using hw))
      p hplength hpbits he hXscale heX

  let witness := fun w =>
    if hw : w ∈ targets then Classical.choose (hex w hw) else 0

  have hspec :
      ∀ w (hw : w ∈ targets),
        ERE.Reaches w (witness w) ∧
        witness w % N = r % N ∧
        witness w ≤
          2 * (N * (w * 2 ^ (2 ^ (15 * Xscale)))) := by
    intro w hw
    simpa only [witness, dif_pos hw] using
      (Classical.choose_spec (hex w hw))

  apply direct_to_one_count_of_selector
    N Y r
    (2 * (N *
      ((3 * Y + 1) * 2 ^ (2 ^ (15 * Xscale)))))
    hY witness

  · intro w hw
    exact (hspec w (by simpa [targets] using hw)).1

  · intro w hw
    exact (hspec w (by simpa [targets] using hw)).2.1

  · intro w hw
    have hwTargets : w ∈ targets := by simpa [targets] using hw
    have hwle : w ≤ 3 * Y + 1 :=
      Nat.le_of_lt (liveTarget_mem_lt hw)
    refine Nat.le_trans (hspec w hwTargets).2.2 ?_
    exact Nat.mul_le_mul_left 2
      (Nat.mul_le_mul_left N
        (Nat.mul_le_mul_right
          (2 ^ (2 ^ (15 * Xscale))) hwle))

end EREQuantitativeTransport

#print axioms EREQuantitativeTransport.direct_to_one_count_of_selector
#print axioms EREQuantitativeTransport.direct_to_one_logarithmic_count_coprime_six
#print axioms EREQuantitativeTransport.direct_to_one_logarithmic_count_pow_three
#print axioms EREQuantitativeTransport.direct_to_one_logarithmic_count_factorized
