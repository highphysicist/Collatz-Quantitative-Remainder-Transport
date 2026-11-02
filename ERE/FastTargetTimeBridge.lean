import ERE.OrbitFiberCount

open Erdos1135
open Erdos1135.ND.PositiveDensity

namespace ERE

/--
Mazur's ordinary Collatz step and Effective RE's Collatz step are
extensionally equal.
-/
theorem collatzStep_eq_collatz :
    Erdos1135.collatzStep = collatz := by
  funext n
  simp only [
    Erdos1135.collatzStep,
    CollatzConjecture.collatzStep,
    collatz
  ]
  by_cases h : n % 2 = 0
  · have heven : Even n := by
      exact Nat.even_iff.mpr h
    simp [heven, h]
  · have hnotEven : ¬ Even n := by
      exact fun heven => h (Nat.even_iff.mp heven)
    simp [hnotEven, h]

/-- Effective RE's iterator agrees with ordinary function iteration. -/
theorem iter_eq_function_iterate
    (f : Nat → Nat) (k n : Nat) :
    iter f k n = (f^[k]) n := by
  induction k generalizing n with
  | zero =>
      rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      change iter f k (f n) = _
      exact ih (f n)

/--
A Mazur raw logarithmic-time certificate can be read directly as an
Effective-RE `iter` certificate.
-/
theorem rawFast_iter_certificate
    {C : Real} {n : Nat}
    (hn : n ∈ rawCollatzLogTimeOneSet C) :
    0 < n ∧
      ∃ m : Nat,
        (m : Real) ≤ C * Real.log (n : Real) ∧
          iter collatz m n = 1 := by
  rcases hn with ⟨hnpos, m, hm, hhit⟩
  refine ⟨hnpos, m, hm, ?_⟩
  rw [iter_eq_function_iterate]
  rw [← collatzStep_eq_collatz]
  exact hhit

end ERE

namespace EREQuantitativeTransport

/--
For an odd source, `liveTarget` is either the source itself or its
first ordinary Collatz successor.
-/
theorem liveTarget_eq_self_or_collatz
    {n : Nat}
    (hodd : Odd n) :
    liveTarget n = n ∨
      liveTarget n = ERE.collatz n := by
  by_cases hthree : n % 3 = 0
  · right
    have hnotEven : ¬ Even n :=
      Nat.not_even_iff_odd.mpr hodd
    have hmodTwo : n % 2 ≠ 0 := by
      intro hmod
      exact hnotEven (Nat.even_iff.mpr hmod)
    have hstep :
        ERE.collatz n = 3 * n + 1 := by
      simp [ERE.collatz, hmodTwo]
    simp [liveTarget, hthree, hstep]
  · left
    simp [liveTarget, hthree]

/--
Passing from an odd fast source to its live target never increases
the certified stopping time.
-/
theorem liveTarget_fast_certificate
    {C : Real} {n : Nat}
    (hodd : Odd n)
    (hfast : n ∈ rawCollatzLogTimeOneSet C) :
    ∃ b : Nat,
      (b : Real) ≤ C * Real.log (n : Real) ∧
        ERE.iter ERE.collatz b (liveTarget n) = 1 := by
  obtain ⟨hnpos, m, hm, hhit⟩ :=
    ERE.rawFast_iter_certificate hfast
  rcases liveTarget_eq_self_or_collatz hodd with hself | hstep
  · exact ⟨m, hm, by simpa [hself] using hhit⟩
  · cases m with
    | zero =>
        have hn1 : n = 1 := by
          simpa using hhit
        subst n
        exact ⟨0, by simpa using hm, by
          simp [liveTarget, ERE.collatz]⟩
    | succ k =>
        refine ⟨k, ?_, ?_⟩
        · have hk :
              (k : Real) ≤ (Nat.succ k : Nat) := by
            exact_mod_cast Nat.le_succ k
          exact hk.trans hm
        · simpa [Nat.succ_eq_add_one, ERE.iter_succ, hstep] using hhit

/--
Every member of `liveTargetsBelow C X` inherits a stopping-time
certificate from one odd source below `X`.
-/
theorem liveTarget_mem_fast_certificate
    {C : Real} {X w : Nat}
    (hw : w ∈ liveTargetsBelow C X) :
    ∃ n : Nat,
      n < X ∧
      ∃ b : Nat,
        (b : Real) ≤ C * Real.log (n : Real) ∧
          ERE.iter ERE.collatz b w = 1 := by
  obtain ⟨n, hnX, hodd, hfast, htarget⟩ :=
    liveTarget_data_of_mem hw
  obtain ⟨b, hb, hhit⟩ :=
    liveTarget_fast_certificate hodd hfast
  exact ⟨n, hnX, b, hb, by simpa [htarget] using hhit⟩

end EREQuantitativeTransport

#print axioms ERE.collatzStep_eq_collatz
#print axioms ERE.iter_eq_function_iterate
#print axioms ERE.rawFast_iter_certificate
#print axioms EREQuantitativeTransport.liveTarget_eq_self_or_collatz
#print axioms EREQuantitativeTransport.liveTarget_fast_certificate
#print axioms EREQuantitativeTransport.liveTarget_mem_fast_certificate
