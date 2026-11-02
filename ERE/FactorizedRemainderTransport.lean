import ERE.QuantitativeRemainderTransport

namespace ERE

/--
Factorization- and residue-sensitive effective remainder transport.

Unlike the uniform `48 * N^4` theorem, this retains the factorization
`N = 2^alpha * 3^b * M`, a parity word for the prescribed residue, and the
actual size parameter supplied to Hallqvist's `hit_residue`.
-/
theorem effective_remainder_transport_factorized
    (N alpha b M r w X e : Nat)
    (hN : 1 ≤ N)
    (hfactor : N = 2 ^ alpha * (3 ^ b * M))
    (hM : Nat.Coprime M 6)
    (hw3 : w % 3 ≠ 0)
    (p : List Nat)
    (hplength : p.length = alpha)
    (hpbits : ∀ d ∈ p, d ≤ 1)
    (he : 3 ^ oneCount p * (r % N) + offset p = 2 ^ alpha * e)
    (hX : 3 * (3 ^ (oneCount p + b) * M * M) ≤ X)
    (heX : e ≤ X) :
    ∃ n : Nat, Reaches w n ∧ n % N = r % N ∧
      n ≤ 2 * (N * (w * 2 ^ (2 ^ (15 * X)))) := by
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with hzero | hpos
    · subst hzero
      exact absurd hM (by decide)
    · exact hpos

  have h2pos : 0 < 2 ^ alpha :=
    Nat.pow_pos (by omega)

  have h3bM : 0 < 3 ^ b * M :=
    Nat.mul_pos (Nat.pow_pos (by omega)) hM0

  have h2aN : 2 ^ alpha ≤ N := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_right _ h3bM

  obtain ⟨m, hme, hmc, hmw, hmbound⟩ :=
    hit_residue M (oneCount p + b) e e w X hM hw3 hX heX

  have hj0 : 0 < 3 ^ oneCount p :=
    Nat.pow_pos (by omega)

  have hzero := Nat.sub_mod_eq_zero_of_mod_eq hmc
  obtain ⟨s, hs⟩ := Nat.dvd_of_mod_eq_zero hzero

  have hm' :
      m = e + 3 ^ oneCount p * (3 ^ b * M * s) := by
    have hsub :
        m - e = 3 ^ oneCount p * (3 ^ b * M * s) := by
      rw [hs, Nat.pow_add]
      grind
    omega

  have htm : 3 ^ b * M * s ≤ m := by
    have hmul :=
      Nat.le_mul_of_pos_left (3 ^ b * M * s) hj0
    omega

  have hn :
      3 ^ oneCount p *
            (r % N + 2 ^ alpha * (3 ^ b * M * s)) +
          offset p =
        2 ^ alpha *
            (e + 3 ^ oneCount p * (3 ^ b * M * s)) := by
    have hrearrange :
        3 ^ oneCount p *
              (r % N + 2 ^ alpha * (3 ^ b * M * s)) +
            offset p =
          (3 ^ oneCount p * (r % N) + offset p) +
            2 ^ alpha *
              (3 ^ oneCount p * (3 ^ b * M * s)) := by
      grind
    rw [hrearrange, he]
    grind

  have hm1 : 1 ≤ m := by
    omega

  let n := r % N + 2 ^ alpha * (3 ^ b * M * s)

  refine ⟨n, ?_, ?_, ?_⟩

  · have hdiv :
        2 ^ p.length ∣
          3 ^ oneCount p * n + offset p := by
      dsimp [n]
      rw [hplength, hn]
      exact Nat.dvd_mul_right _ _

    have hr := integrality_reaches p hpbits n hdiv

    have hquot :
        (3 ^ oneCount p * n + offset p) /
            2 ^ p.length = m := by
      dsimp [n]
      rw [hplength, hn,
        Nat.mul_div_cancel_left _ h2pos, ← hm']

    rw [hquot] at hr
    exact reaches_trans hr hmw

  · dsimp [n]
    rw [show
      2 ^ alpha * (3 ^ b * M * s) = N * s by
        rw [hfactor]
        grind,
      Nat.add_mul_mod_self_left,
      Nat.mod_mod]

  · dsimp [n]

    have hn1 :
        r % N + 2 ^ alpha * (3 ^ b * M * s) ≤
          2 * (N * m) := by
      have h1 :
          2 ^ alpha * (3 ^ b * M * s) ≤ N * m :=
        Nat.mul_le_mul h2aN htm

      have h2 : N ≤ N * m :=
        Nat.le_mul_of_pos_right N hm1

      have hrN := Nat.mod_lt r (by omega : 0 < N)
      omega

    exact Nat.le_trans hn1
      (Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_left N hmbound))

end ERE

#print axioms ERE.effective_remainder_transport_factorized
