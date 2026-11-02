import ERE.FastTargetTimeBridge

open Erdos1135
open Erdos1135.ND.PositiveDensity

namespace EREQuantitativeTransport

/--
A natural-number upper bound for a real logarithmic stopping-time
certificate.
-/
noncomputable def uniformLogTimeBound (C : Real) (X : Nat) : Nat :=
  Nat.ceil (C * Real.log (X : Real))

/--
Every live target constructed from an odd fast source below `X` reaches
`1` within `ceil(C log X)` ordinary Collatz steps.
-/
theorem liveTarget_mem_uniform_time
    {C : Real} (hC : 0 ≤ C)
    {X w : Nat}
    (hw : w ∈ liveTargetsBelow C X) :
    ∃ b : Nat,
      b ≤ uniformLogTimeBound C X ∧
        ERE.iter ERE.collatz b w = 1 := by
  obtain ⟨n, hnX, hodd, hfast, htarget⟩ :=
    liveTarget_data_of_mem hw

  have hnpos : 0 < n :=
    hfast.1

  obtain ⟨b, hb, hhit⟩ :=
    liveTarget_fast_certificate hodd hfast

  have hnXnat : n ≤ X :=
    Nat.le_of_lt hnX

  have hnposR : (0 : Real) < (n : Real) := by
    exact_mod_cast hnpos

  have hXpos : 0 < X :=
    lt_of_lt_of_le hnpos hnXnat

  have hXposR : (0 : Real) < (X : Real) := by
    exact_mod_cast hXpos

  have hnXreal : (n : Real) ≤ (X : Real) := by
    exact_mod_cast hnXnat

  have hlog :
      Real.log (n : Real) ≤ Real.log (X : Real) :=
    Real.strictMonoOn_log.monotoneOn
      hnposR hXposR hnXreal

  have hmul :
      C * Real.log (n : Real) ≤
        C * Real.log (X : Real) :=
    mul_le_mul_of_nonneg_left hlog hC

  have hbReal :
      (b : Real) ≤
        (uniformLogTimeBound C X : Nat) := by
    exact hb.trans <|
      hmul.trans <|
        Nat.le_ceil (C * Real.log (X : Real))

  have hbNat :
      b ≤ uniformLogTimeBound C X := by
    exact_mod_cast hbReal

  exact ⟨b, hbNat, by simpa [htarget] using hhit⟩

/--
The complete finite set of live targets has the same uniform
logarithmic stopping-time bound.
-/
theorem liveTargetsBelow_uniform_time
    {C : Real} (hC : 0 ≤ C)
    (X : Nat) :
    ∀ w ∈ liveTargetsBelow C X,
      ∃ b : Nat,
        b ≤ uniformLogTimeBound C X ∧
          ERE.iter ERE.collatz b w = 1 := by
  intro w hw
  exact liveTarget_mem_uniform_time hC hw

end EREQuantitativeTransport

#print axioms EREQuantitativeTransport.liveTarget_mem_uniform_time
#print axioms EREQuantitativeTransport.liveTargetsBelow_uniform_time
