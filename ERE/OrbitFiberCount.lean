import ERE.OrbitTailBound

namespace ERE

/--
Every nonempty finite set has an element minimizing any
natural-number-valued function.
-/
theorem Finset.exists_nat_argmin
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (hs : s.Nonempty)
    (time : α → Nat) :
    ∃ u : α, u ∈ s ∧
      ∀ v ∈ s, time u ≤ time v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact False.elim (by simpa using hs)
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · obtain ⟨u, hu, hmin⟩ := ih hs'
        by_cases hau : time a ≤ time u
        · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
          intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact Nat.le_refl _
          · exact hau.trans (hmin v hv)
        · refine ⟨u, Finset.mem_insert_of_mem hu, ?_⟩
          intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · exact Nat.le_of_lt (Nat.lt_of_not_ge hau)
          · exact hmin v hv
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Nat.le_refl _
        · exact False.elim (hs' ⟨v, hv⟩)

/--
If `u` is the earliest-occurring member of a finite collection of
values on one Collatz orbit, and `u` reaches `1` in at most `B` steps,
then the collection has cardinality at most `B+4`.
-/
theorem orbit_fiber_card_le_of_minimal_time
    (s : Finset Nat)
    (n : Nat)
    (time : Nat → Nat)
    (u : Nat)
    (hu : u ∈ s)
    (hoccurs :
      ∀ v ∈ s, iter collatz (time v) n = v)
    (hminimal :
      ∀ v ∈ s, time u ≤ time v)
    {b B : Nat}
    (hit : iter collatz b u = 1)
    (hbB : b ≤ B) :
    s.card ≤ B + 4 := by
  have hsubset :
      s ⊆ orbitPrefix u B ∪ terminalCycle := by
    intro v hv
    exact later_value_mem_bounded_orbit_set
      (hoccurs u hu)
      (hoccurs v hv)
      (hminimal v hv)
      hit hbB
  exact (Finset.card_le_card hsubset).trans
    (orbitPrefix_union_terminalCycle_card_le u B)

/--
Abstract bounded-fibre theorem for a deterministic Collatz orbit.

If every value in a finite set occurs on one orbit, and every such
value reaches `1` within at most `B` steps, then the set contains at
most `B+4` distinct values.
-/
theorem finite_collatz_orbit_fiber_card_le
    (s : Finset Nat)
    (n B : Nat)
    (time : Nat → Nat)
    (hoccurs :
      ∀ v ∈ s, iter collatz (time v) n = v)
    (hstops :
      ∀ v ∈ s, ∃ b : Nat,
        b ≤ B ∧ iter collatz b v = 1) :
    s.card ≤ B + 4 := by
  by_cases hs : s.Nonempty
  · obtain ⟨u, hu, hminimal⟩ :=
      Finset.exists_nat_argmin s hs time
    obtain ⟨b, hbB, hit⟩ := hstops u hu
    exact orbit_fiber_card_le_of_minimal_time
      s n time u hu hoccurs hminimal hit hbB
  · have hsempty : s = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hsempty]

/--
A convenient form where occurrence times and stopping times are supplied
as explicit functions.
-/
theorem finite_collatz_orbit_fiber_card_le_explicit
    (s : Finset Nat)
    (n B : Nat)
    (occurTime stopTime : Nat → Nat)
    (hoccurs :
      ∀ v ∈ s,
        iter collatz (occurTime v) n = v)
    (hstopBound :
      ∀ v ∈ s, stopTime v ≤ B)
    (hhits :
      ∀ v ∈ s,
        iter collatz (stopTime v) v = 1) :
    s.card ≤ B + 4 := by
  apply finite_collatz_orbit_fiber_card_le
    s n B occurTime hoccurs
  intro v hv
  exact ⟨stopTime v, hstopBound v hv, hhits v hv⟩

end ERE

#print axioms ERE.Finset.exists_nat_argmin
#print axioms ERE.orbit_fiber_card_le_of_minimal_time
#print axioms ERE.finite_collatz_orbit_fiber_card_le
#print axioms ERE.finite_collatz_orbit_fiber_card_le_explicit
