import ERE.FactorizedRemainderTransport
import Erdos1135.StoppingTime
import Erdos1135.CollatzStep

/-!
# Live-target transport

This module separates three facts:

* QRT-6A: the elementary two-branch live-target map is globally at most
  two-to-one and produces a target not divisible by three;
* QRT-6B: this map is orbit-preserving on odd inputs;
* QRT-6C: every positive Collatz orbit reaches some target not divisible
  by three.

The unrestricted map is not orbit-preserving on even multiples of three.
-/

namespace EREQuantitativeTransport

open Function

/--
The elementary live-target map. It removes divisibility by three, but is
orbit-preserving only when its input is odd.
-/
def liveTarget (x : Nat) : Nat :=
  if x % 3 = 0 then 3 * x + 1 else x

/-- QRT-6A. Every elementary live target is nonzero modulo three. -/
theorem liveTarget_not_divisible_by_three (x : Nat) :
    liveTarget x % 3 ≠ 0 := by
  unfold liveTarget
  split <;> omega

/-- QRT-6A. The elementary live target has controlled size. -/
theorem liveTarget_le (x : Nat) :
    liveTarget x ≤ 3 * x + 1 := by
  unfold liveTarget
  split <;> omega

/--
QRT-6A collision classification. If two inputs have the same live target,
then they are equal or one is the `3x+1` image of the other.
-/
theorem liveTarget_collision
    {x y : Nat}
    (h : liveTarget x = liveTarget y) :
    x = y ∨ x = 3 * y + 1 ∨ y = 3 * x + 1 := by
  unfold liveTarget at h
  split at h <;> split at h <;> omega

/--
QRT-6A in an explicitly finite-fibre form: among three inputs with the same
live target, two inputs coincide. Hence every fibre has cardinality at most
two.
-/
theorem liveTarget_three_preimages
    {x y z : Nat}
    (hxy : liveTarget x = liveTarget y)
    (hxz : liveTarget x = liveTarget z) :
    x = y ∨ x = z ∨ y = z := by
  by_cases hx : x % 3 = 0
  · by_cases hy : y % 3 = 0
    · by_cases hz : z % 3 = 0
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega
    · by_cases hz : z % 3 = 0
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega
  · by_cases hy : y % 3 = 0
    · by_cases hz : z % 3 = 0
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega
    · by_cases hz : z % 3 = 0
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega
      · simp [liveTarget, hx, hy, hz] at hxy hxz
        omega

/--
QRT-6B. On odd inputs, the live-target map stays on the ordinary Collatz
orbit.
-/
theorem odd_reaches_liveTarget
    {x : Nat}
    (hxodd : Odd x) :
    Erdos1135.Reaches x (liveTarget x) := by
  by_cases hthree : x % 3 = 0
  · have hnotEven : ¬ Even x := by
      exact Nat.not_even_iff_odd.mpr hxodd
    have hstep :
        Erdos1135.collatzStep x = 3 * x + 1 :=
      Erdos1135.collatzStep_eq_three_mul_add_one_of_not_even hnotEven
    have hreach :
        Erdos1135.Reaches x (3 * x + 1) :=
      Erdos1135.reaches_of_step_eq hstep
    simpa [liveTarget, hthree] using hreach
  · simpa [liveTarget, hthree] using
      Erdos1135.reaches_refl x

/--
QRT-6C. Every positive ordinary Collatz orbit reaches a number not divisible
by three.
-/
theorem exists_live_orbit_target
    (x : Nat)
    (hx : 0 < x) :
    ∃ y : Nat,
      Erdos1135.Reaches x y ∧ y % 3 ≠ 0 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hthree : x % 3 = 0
      · by_cases heven : Even x
        · have hlt : x / 2 < x :=
            Nat.div_lt_self hx (by omega)

          have hhalfpos : 0 < x / 2 := by
            rcases heven with ⟨k, hk⟩
            omega

          obtain ⟨y, hreach, hlive⟩ :=
            ih (x / 2) hlt hhalfpos

          have hstep :
              Erdos1135.collatzStep x = x / 2 :=
            Erdos1135.collatzStep_eq_div_two_of_even heven

          have hhead :
              Erdos1135.Reaches x (x / 2) :=
            Erdos1135.reaches_of_step_eq hstep

          exact ⟨y, hhead.trans hreach, hlive⟩

        · let y := 3 * x + 1

          have hstep :
              Erdos1135.collatzStep x = y := by
            dsimp [y]
            exact
              Erdos1135.collatzStep_eq_three_mul_add_one_of_not_even
                heven

          have hreach : Erdos1135.Reaches x y :=
            Erdos1135.reaches_of_step_eq hstep

          have hlive : y % 3 ≠ 0 := by
            dsimp [y]
            omega

          exact ⟨y, hreach, hlive⟩

      · exact
          ⟨x, Erdos1135.reaches_refl x, hthree⟩

end EREQuantitativeTransport

#print axioms EREQuantitativeTransport.liveTarget_not_divisible_by_three
#print axioms EREQuantitativeTransport.liveTarget_le
#print axioms EREQuantitativeTransport.liveTarget_collision
#print axioms EREQuantitativeTransport.liveTarget_three_preimages
#print axioms EREQuantitativeTransport.odd_reaches_liveTarget
#print axioms EREQuantitativeTransport.exists_live_orbit_target
