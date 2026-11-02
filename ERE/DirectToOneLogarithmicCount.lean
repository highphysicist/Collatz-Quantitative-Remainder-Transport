import ERE.ExplicitLogarithmicRemainderTransport
import ERE.FastTargetTimeBridge

namespace EREQuantitativeTransport

open Erdos1135.ND.PositiveDensity

/--
Direct-to-one quantitative remainder theorem.

For every sufficiently large scale `X`, every modulus `N ≥ 1`, and every
residue `r`, there is a finite set `W` containing at least

  δ X / (2 * (ceil ((523/50) * log X) + 4))

distinct integers. Every member of `W` is congruent to `r` modulo `N`,
reaches `1` under Collatz iteration, and satisfies Hallqvist's explicit
numerical bound.
-/
theorem direct_to_one_logarithmic_count_ten46
    (N : Nat) (hN : 1 ≤ N)
    (X r : Nat)
    (hX : explicitPositiveDensityUnitSeedCutoff ≤ X) :
    ∃ W : Finset Nat,
      ((explicitPositiveDensityUnitSeedConstant : Real) * X) /
          (2 *
            (uniformLogTimeBound (523 / 50 : Real) X + 4) : Nat) ≤
        (W.card : Real) ∧
      (∀ n ∈ W, n % N = r % N) ∧
      (∀ n ∈ W, ERE.Reaches 1 n) ∧
      (∀ n ∈ W,
        n ≤
          (3 * X + 1) *
            2 ^ (2 ^ (48 * N ^ 4))) := by
  classical

  obtain ⟨witness, hreach, hmod, hbound, hcard⟩ :=
    explicit_logarithmic_remainder_transport_ten46
      N hN X r hX

  let targets := liveTargetsBelow (523 / 50 : Real) X
  let W := targets.image witness

  refine ⟨W, ?_, ?_, ?_, ?_⟩

  · simpa [W, targets] using hcard

  · intro n hn
    have hn' : n ∈ targets.image witness := by
      simpa [W] using hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn'
    exact hmod w (by simpa [targets] using hw)

  · intro n hn
    have hn' : n ∈ targets.image witness := by
      simpa [W] using hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn'

    have hwTargets :
        w ∈ liveTargetsBelow (523 / 50 : Real) X := by
      simpa [targets] using hw

    obtain ⟨source, hsourceX, steps, hsteps, hhit⟩ :=
      liveTarget_mem_fast_certificate hwTargets

    have hwOne : ERE.Reaches 1 w := by
      exact ⟨steps, hhit⟩

    exact ERE.reaches_trans (hreach w hwTargets) hwOne

  · intro n hn
    have hn' : n ∈ targets.image witness := by
      simpa [W] using hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn'
    exact hbound w (by simpa [targets] using hw)

end EREQuantitativeTransport

#print axioms
  EREQuantitativeTransport.direct_to_one_logarithmic_count_ten46
