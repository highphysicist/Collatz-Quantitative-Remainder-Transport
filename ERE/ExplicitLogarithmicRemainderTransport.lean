import ERE.LogarithmicRemainderTransport
import ERE.OddFastDensity

namespace EREQuantitativeTransport

open Erdos1135.ND.PositiveDensity

/--
QRT-7: explicit logarithmic remainder transport.

For every sufficiently large `X`, every modulus `N ≥ 1`, and every residue
`r`, there is a selected family of Collatz predecessors in residue `r mod N`
whose cardinality is at least

  δ X / (2 * (ceil ((523/50) * log X) + 4)),

where `δ` is Mazur's explicit positive-density constant.

Every selected witness reaches a distinct live target below `3X+1` and obeys
Hallqvist's effective numerical bound.
-/
theorem explicit_logarithmic_remainder_transport_ten46
    (N : Nat) (hN : 1 ≤ N)
    (X r : Nat)
    (hX : explicitPositiveDensityUnitSeedCutoff ≤ X) :
    ∃ witness : Nat → Nat,
      (∀ w ∈ liveTargetsBelow (523 / 50 : Real) X,
        ERE.Reaches w (witness w)) ∧
      (∀ w ∈ liveTargetsBelow (523 / 50 : Real) X,
        witness w % N = r % N) ∧
      (∀ w ∈ liveTargetsBelow (523 / 50 : Real) X,
        witness w ≤
          (3 * X + 1) *
            2 ^ (2 ^ (48 * N ^ 4))) ∧
      ((explicitPositiveDensityUnitSeedConstant : Real) * X) /
          (2 *
            (uniformLogTimeBound (523 / 50 : Real) X + 4) : Nat) ≤
        (((liveTargetsBelow (523 / 50 : Real) X).image witness).card :
          Real) := by
  obtain ⟨witness, hreach, hmod, hbound, hfinite⟩ :=
    logarithmic_remainder_transport
      N hN (523 / 50 : Real) (by norm_num) X r

  refine ⟨witness, hreach, hmod, hbound, ?_⟩

  let S := oddFastBelow (523 / 50 : Real) X
  let I := ((liveTargetsBelow (523 / 50 : Real) X).image witness).card
  let K := uniformLogTimeBound (523 / 50 : Real) X + 4

  have hfinite' : S.card ≤ I * (2 * K) := by
    change
      (oddFastBelow (523 / 50 : Real) X).card ≤
        ((liveTargetsBelow (523 / 50 : Real) X).image witness).card *
          (2 * (uniformLogTimeBound (523 / 50 : Real) X + 4))
    calc
      (oddFastBelow (523 / 50 : Real) X).card
          ≤ 2 *
              ((liveTargetsBelow (523 / 50 : Real) X).image witness).card *
              (uniformLogTimeBound (523 / 50 : Real) X + 4) := hfinite
      _ =
          ((liveTargetsBelow (523 / 50 : Real) X).image witness).card *
            (2 * (uniformLogTimeBound (523 / 50 : Real) X + 4)) := by
              ac_rfl

  have hMazur :
      (explicitPositiveDensityUnitSeedConstant : Real) * X ≤
        (S.card : Real) := by
    have h :=
      explicitPositiveDensityOddUnitSeedCount_ten46 X hX
    rw [← oddFastBelow_card_eq_natCount (523 / 50 : Real) X] at h
    exact h

  have htransport :
      (explicitPositiveDensityUnitSeedConstant : Real) * X ≤
        (I : Real) * (2 * K : Nat) := by
    calc
      (explicitPositiveDensityUnitSeedConstant : Real) * X
          ≤ (S.card : Real) := hMazur
      _ ≤ (I : Real) * (2 * K : Nat) := by
        exact_mod_cast hfinite'

  have hK : 0 < K := by
    dsimp [K]
    omega

  have hden : (0 : Real) < (2 * K : Nat) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hK)

  change
    ((explicitPositiveDensityUnitSeedConstant : Real) * X) /
        (2 * K : Nat) ≤
      (I : Real)

  apply (div_le_iff₀ hden).2
  simpa [mul_comm] using htransport

end EREQuantitativeTransport

#print axioms
  EREQuantitativeTransport.explicit_logarithmic_remainder_transport_ten46
