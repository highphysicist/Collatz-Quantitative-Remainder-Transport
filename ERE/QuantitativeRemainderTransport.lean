import ERE.EffectiveRemainderEverywhere

/-!
Quantitative remainder transport for Collatz predecessors.

This module begins the formal development of quantitative theorems obtained
by transporting Collatz predecessor mass into prescribed residue classes.
The first theorem proves a finite quantitative transport statement from
Effective Remainder Everywhere: for every Q, one obtains Q pairwise distinct
bounded predecessors in one prescribed residue class modulo N.

Later modules will combine this construction with Mazur's positive-density
theorems to obtain quantitative and positive-density transport results.
-/

namespace ERE

theorem quantitative_remainder_transport_finite
    (N : Nat) (hN : 1 ≤ N) (w : Nat) (hw3 : w % 3 ≠ 0)
    (r Q : Nat) (hQ : 1 ≤ Q) :
    ∃ witness : {j : Nat // j < Q} → Nat,
      (∀ j, Reaches w (witness j)) ∧
      (∀ j, witness j % N = r % N) ∧
      (∀ j, witness j ≤ w * 2 ^ (2 ^ (48 * (N * Q) ^ 4))) ∧
      (∀ i j, witness i = witness j → i = j) := by
  have hNQ : 1 ≤ N * Q := Nat.mul_pos hN hQ
  let residue : {j : Nat // j < Q} → Nat :=
    fun j => r % N + N * j.val
  have hres_lt (j : {j : Nat // j < Q}) : residue j < N * Q := by
    dsimp [residue]
    have hr := Nat.mod_lt r (by omega : 0 < N)
    calc
      r % N + N * j.val < N + N * j.val := Nat.add_lt_add_right hr _
      _ = N * (j.val + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ N * Q := Nat.mul_le_mul_left N (Nat.succ_le_of_lt j.property)
  have hex (j : {j : Nat // j < Q}) :
      ∃ n : Nat, Reaches w n ∧
        n % (N * Q) = residue j % (N * Q) ∧
        n ≤ w * 2 ^ (2 ^ (48 * (N * Q) ^ 4)) :=
    effective_remainder_everywhere (N * Q) hNQ w hw3 (residue j)
  let witness : {j : Nat // j < Q} → Nat := fun j => Classical.choose (hex j)
  have hspec (j : {j : Nat // j < Q}) :
      Reaches w (witness j) ∧
        witness j % (N * Q) = residue j % (N * Q) ∧
        witness j ≤ w * 2 ^ (2 ^ (48 * (N * Q) ^ 4)) := by
    dsimp [witness]
    exact Classical.choose_spec (hex j)
  refine ⟨witness, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hspec j).1
  · intro j
    have hmodNQ := (hspec j).2.1
    have hmodN := mod_of_dvd_mod (Nat.dvd_mul_right N Q) hmodNQ
    dsimp [residue] at hmodN
    simpa [Nat.add_mul_mod_self_left, Nat.mod_mod] using hmodN
  · intro j
    exact (hspec j).2.2
  · intro i j hij
    have hi : witness i % (N * Q) = residue i :=
      (hspec i).2.1.trans (Nat.mod_eq_of_lt (hres_lt i))
    have hj : witness j % (N * Q) = residue j :=
      (hspec j).2.1.trans (Nat.mod_eq_of_lt (hres_lt j))
    have hres : residue i = residue j := by rw [← hi, ← hj, hij]
    dsimp [residue] at hres
    have hmul : N * i.val = N * j.val := Nat.add_left_cancel hres
    have hval : i.val = j.val :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < N) hmul
    exact Subtype.ext hval

/--
Scale-counting form of finite quantitative remainder transport.

If the ERE witness bound for `Q` refined residue classes is at most `X`, then
the prescribed class modulo `N` contains an injectively indexed family of `Q`
predecessors of `w`, all at most `X`.
-/
theorem quantitative_remainder_transport_count_at_scale
    (N : Nat) (hN : 1 ≤ N) (w : Nat) (hw3 : w % 3 ≠ 0)
    (r Q X : Nat) (hQ : 1 ≤ Q)
    (hscale : w * 2 ^ (2 ^ (48 * (N * Q) ^ 4)) ≤ X) :
    ∃ witness : {j : Nat // j < Q} → Nat,
      (∀ j, Reaches w (witness j)) ∧
      (∀ j, witness j % N = r % N) ∧
      (∀ j, witness j ≤ X) ∧
      (∀ i j, witness i = witness j → i = j) := by
  obtain ⟨witness, hreach, hmod, hbound, hinjective⟩ :=
    quantitative_remainder_transport_finite N hN w hw3 r Q hQ
  refine ⟨witness, hreach, hmod, ?_, hinjective⟩
  intro j
  exact Nat.le_trans (hbound j) hscale

/--
Sharper effective remainder transport when the modulus is coprime to six.

In this case the 2-adic and 3-adic lifting layers disappear, so Hallqvist's
internal `hit_residue` theorem can be applied directly with `X = 3*N*N`.
-/
theorem effective_remainder_transport_coprime_six
    (N : Nat) (hN6 : Nat.Coprime N 6)
    (w : Nat) (hw3 : w % 3 ≠ 0) (r : Nat) :
    ∃ n : Nat, Reaches w n ∧ n % N = r % N ∧
      n ≤ w * 2 ^ (2 ^ (15 * (3 * N * N))) := by
  obtain ⟨n, -, hmod, hreach, hbound⟩ :=
    hit_residue N 0 (r % N) 0 w (3 * N * N) hN6 hw3
      (by
        simp only [Nat.pow_zero, Nat.one_mul]
        rw [Nat.mul_assoc])
      (by omega)
  refine ⟨n, hreach, ?_, hbound⟩
  simpa using hmod

/--
Sharper effective remainder transport for a power-of-three modulus.

Here the coprime part of the modulus is `M = 1`, and Hallqvist's internal
`hit_residue` theorem applies with `X = 3 * 3^b`. Thus the inner exponent is
`15 * (3 * 3^b)`, algebraically `45 * 3^b = 45N`.
-/
theorem effective_remainder_transport_pow_three
    (b : Nat) (w : Nat) (hw3 : w % 3 ≠ 0) (r : Nat) :
    ∃ n : Nat, Reaches w n ∧ n % (3 ^ b) = r % (3 ^ b) ∧
      n ≤ w * 2 ^ (2 ^ (15 * (3 * 3 ^ b))) := by
  obtain ⟨n, -, hmod, hreach, hbound⟩ :=
    hit_residue 1 b (r % (3 ^ b)) 0 w (3 * 3 ^ b) (by decide) hw3
      (by
        simp only [Nat.mul_one]
        exact Nat.le_refl _)
      (by omega)
  refine ⟨n, hreach, ?_, hbound⟩
  simpa [Nat.mul_one, Nat.mod_mod] using hmod

end ERE

#print axioms ERE.quantitative_remainder_transport_finite
#print axioms ERE.quantitative_remainder_transport_count_at_scale
#print axioms ERE.effective_remainder_transport_coprime_six
#print axioms ERE.effective_remainder_transport_pow_three
