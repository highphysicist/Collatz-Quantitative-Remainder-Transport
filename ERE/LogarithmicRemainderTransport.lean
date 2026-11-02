import ERE.SelectedWitnessCounting

open Erdos1135
open Erdos1135.ND.PositiveDensity

namespace EREQuantitativeTransport

/--
QRT-7: generic-modulus logarithmic quantitative remainder transport.

For every live target arising from an odd logarithmic-time source below
`X`, select one Effective-RE predecessor in the prescribed residue
class modulo `N`.

The number of odd fast sources is at most

`2 * (number of distinct selected predecessors) *
     (ceil(C log X) + 4)`.

Every selected predecessor also satisfies the generic Effective-RE
size bound, uniformly using `w < 3X+1`.
-/
theorem logarithmic_remainder_transport
    (N : Nat) (hN : 1 ≤ N)
    (C : Real) (hC : 0 ≤ C)
    (X r : Nat) :
    ∃ witness : Nat → Nat,
      (∀ w ∈ liveTargetsBelow C X,
        ERE.Reaches w (witness w)) ∧
      (∀ w ∈ liveTargetsBelow C X,
        witness w % N = r % N) ∧
      (∀ w ∈ liveTargetsBelow C X,
        witness w ≤
          (3 * X + 1) *
            2 ^ (2 ^ (48 * N ^ 4))) ∧
      (oddFastBelow C X).card ≤
        2 *
          ((liveTargetsBelow C X).image witness).card *
          (uniformLogTimeBound C X + 4) := by
  classical

  let S : Finset Nat :=
    liveTargetsBelow C X

  have hex :
      ∀ w, w ∈ S →
        ∃ n : Nat,
          ERE.Reaches w n ∧
          n % N = r % N ∧
          n ≤ w * 2 ^ (2 ^ (48 * N ^ 4)) := by
    intro w hw
    exact ERE.effective_remainder_everywhere
      N hN w
      (liveTarget_mem_not_divisible_by_three hw)
      r

  let witness : Nat → Nat :=
    fun w =>
      if hw : w ∈ S then
        Classical.choose (hex w hw)
      else
        0

  have hspec :
      ∀ w (hw : w ∈ S),
        ERE.Reaches w (witness w) ∧
        witness w % N = r % N ∧
        witness w ≤ w * 2 ^ (2 ^ (48 * N ^ 4)) := by
    intro w hw
    simp only [witness, dif_pos hw]
    exact Classical.choose_spec (hex w hw)

  have hreach :
      ∀ w ∈ S, ERE.Reaches w (witness w) := by
    intro w hw
    exact (hspec w hw).1

  have hmod :
      ∀ w ∈ S, witness w % N = r % N := by
    intro w hw
    exact (hspec w hw).2.1

  have hbound :
      ∀ w ∈ S,
        witness w ≤
          (3 * X + 1) *
            2 ^ (2 ^ (48 * N ^ 4)) := by
    intro w hw

    have hwBound : w ≤ 3 * X + 1 :=
      Nat.le_of_lt (liveTarget_mem_lt hw)

    exact (hspec w hw).2.2.trans
      (Nat.mul_le_mul_right
        (2 ^ (2 ^ (48 * N ^ 4)))
        hwBound)

  have hstop :
      ∀ w ∈ S,
        ∃ b : Nat,
          b ≤ uniformLogTimeBound C X ∧
          ERE.iter ERE.collatz b w = 1 := by
    intro w hw
    exact liveTarget_mem_uniform_time hC hw

  have himage :
      S.card ≤
        (S.image witness).card *
          (uniformLogTimeBound C X + 4) :=
    ERE.selected_witness_image_count
      S witness (uniformLogTimeBound C X)
      hreach hstop

  have hnormalize :
      (oddFastBelow C X).card ≤ 2 * S.card := by
    simpa [S] using
      oddFast_card_le_two_mul_liveTargets_card C X

  have hcount :
      (oddFastBelow C X).card ≤
        2 *
          (S.image witness).card *
          (uniformLogTimeBound C X + 4) := by
    calc
      (oddFastBelow C X).card
          ≤ 2 * S.card :=
        hnormalize
      _ ≤ 2 *
          ((S.image witness).card *
            (uniformLogTimeBound C X + 4)) :=
        Nat.mul_le_mul_left 2 himage
      _ = 2 *
          (S.image witness).card *
            (uniformLogTimeBound C X + 4) := by
        simp only [Nat.mul_assoc]

  refine ⟨witness, ?_, ?_, ?_, ?_⟩
  · simpa [S] using hreach
  · simpa [S] using hmod
  · simpa [S] using hbound
  · simpa [S] using hcount


theorem oddFastBelow_card_eq_natCount
    (C : Real) (X : Nat) :
    (oddFastBelow C X).card =
      Erdos1135.Terras.natCount
        (Erdos1135.ND.PositiveDensity.oddRawCollatzLogTimeOneSet C) X := by
  classical
  unfold oddFastBelow Erdos1135.Terras.natCount
  exact
    (Nat.count_eq_card_filter_range
      (fun n =>
        n ∈ Erdos1135.ND.PositiveDensity.oddRawCollatzLogTimeOneSet C)
      X).symm
end EREQuantitativeTransport

#print axioms EREQuantitativeTransport.logarithmic_remainder_transport
