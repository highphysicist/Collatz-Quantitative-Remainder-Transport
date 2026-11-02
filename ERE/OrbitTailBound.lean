import ERE.OrbitAlgebra

namespace ERE

/-- The three values in the terminal positive Collatz cycle. -/
def terminalCycle : Finset Nat := {1, 2, 4}

@[simp]
theorem one_mem_terminalCycle :
    1 ∈ terminalCycle := by
  simp [terminalCycle]

@[simp]
theorem two_mem_terminalCycle :
    2 ∈ terminalCycle := by
  simp [terminalCycle]

@[simp]
theorem four_mem_terminalCycle :
    4 ∈ terminalCycle := by
  simp [terminalCycle]

/-- The three explicit Collatz transitions in the terminal cycle. -/
theorem collatz_terminal_cycle :
    collatz 1 = 4 ∧ collatz 4 = 2 ∧ collatz 2 = 1 := by
  norm_num [collatz]

/--
Starting from any of `1`, `2`, or `4`, every later Collatz iterate
remains in the terminal cycle.
-/
theorem iter_terminal_cycle
    (k : Nat) :
    iter collatz k 1 ∈ terminalCycle ∧
      iter collatz k 2 ∈ terminalCycle ∧
      iter collatz k 4 ∈ terminalCycle := by
  induction k with
  | zero =>
      simp [terminalCycle]
  | succ k ih =>
      simpa [iter_succ, collatz, Nat.succ_eq_add_one] using
        And.intro ih.2.2 (And.intro ih.1 ih.2.1)

/-- Every iterate starting at `1` lies in the terminal cycle. -/
theorem iter_one_mem_terminalCycle
    (k : Nat) :
    iter collatz k 1 ∈ terminalCycle :=
  (iter_terminal_cycle k).1

/--
Once an orbit has reached `1`, every later iterate lies in
`{1,2,4}`.
-/
theorem iter_mem_terminalCycle_of_hit_one
    {w b d : Nat}
    (hit : iter collatz b w = 1)
    (hbd : b ≤ d) :
    iter collatz d w ∈ terminalCycle := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hbd
  have hd :
      iter collatz d w = iter collatz q 1 := by
    calc
      iter collatz d w =
          iter collatz (q + b) w := by
            rw [hq, Nat.add_comm]
      _ = iter collatz q (iter collatz b w) :=
            iter_add collatz q b w
      _ = iter collatz q 1 := by rw [hit]
  rw [hd]
  exact iter_one_mem_terminalCycle q

/--
Suppose `u` and `v` occur on the same orbit, with `u` occurring first,
and suppose `u` reaches `1` after `b` steps. Then `v` is either among
the first `b+1` iterates starting at `u`, or lies in the terminal cycle.
-/
theorem later_value_mem_prefix_or_terminalCycle
    {n u v i j b : Nat}
    (hi : iter collatz i n = u)
    (hj : iter collatz j n = v)
    (hij : i ≤ j)
    (hit : iter collatz b u = 1) :
    (∃ d : Nat, d < b + 1 ∧ iter collatz d u = v) ∨
      v ∈ terminalCycle := by
  obtain ⟨d, hd⟩ :=
    reaches_of_iter_indices hi hj hij
  rcases Nat.le_total d b with hdb | hbd
  · exact Or.inl ⟨d, Nat.lt_succ_of_le hdb, hd⟩
  · exact Or.inr <| by
      rw [← hd]
      exact iter_mem_terminalCycle_of_hit_one hit hbd

/--
A version with a uniform time bound `B`: if `u` reaches `1` in
`b ≤ B` steps, every later orbit value is in the first `B+1`
positions from `u`, or in the terminal cycle.
-/
theorem later_value_mem_bounded_prefix_or_terminalCycle
    {n u v i j b B : Nat}
    (hi : iter collatz i n = u)
    (hj : iter collatz j n = v)
    (hij : i ≤ j)
    (hit : iter collatz b u = 1)
    (hbB : b ≤ B) :
    (∃ d : Nat, d < B + 1 ∧ iter collatz d u = v) ∨
      v ∈ terminalCycle := by
  rcases later_value_mem_prefix_or_terminalCycle
      hi hj hij hit with hprefix | hcycle
  · obtain ⟨d, hdb, hd⟩ := hprefix
    exact Or.inl ⟨d, lt_of_lt_of_le hdb (Nat.succ_le_succ hbB), hd⟩
  · exact Or.inr hcycle

/--
The set of values among the first `B+1` iterates of `u`.
-/
def orbitPrefix (u B : Nat) : Finset Nat :=
  (Finset.range (B + 1)).image
    (fun d => iter collatz d u)

/-- The orbit prefix has at most `B+1` distinct values. -/
theorem orbitPrefix_card_le
    (u B : Nat) :
    (orbitPrefix u B).card ≤ B + 1 := by
  classical
  unfold orbitPrefix
  exact (Finset.card_image_le.trans_eq (Finset.card_range (B + 1)))

/-- Membership in the explicitly bounded orbit prefix. -/
theorem mem_orbitPrefix_of_iter
    {u v B d : Nat}
    (hdB : d < B + 1)
    (hd : iter collatz d u = v) :
    v ∈ orbitPrefix u B := by
  classical
  unfold orbitPrefix
  exact Finset.mem_image.mpr
    ⟨d, Finset.mem_range.mpr hdB, hd⟩

/--
Every later orbit value after `u`, when `u` has stopping time at most
`B`, belongs to `orbitPrefix u B ∪ terminalCycle`.
-/
theorem later_value_mem_bounded_orbit_set
    {n u v i j b B : Nat}
    (hi : iter collatz i n = u)
    (hj : iter collatz j n = v)
    (hij : i ≤ j)
    (hit : iter collatz b u = 1)
    (hbB : b ≤ B) :
    v ∈ orbitPrefix u B ∪ terminalCycle := by
  rcases later_value_mem_bounded_prefix_or_terminalCycle
      hi hj hij hit hbB with hprefix | hcycle
  · obtain ⟨d, hdB, hd⟩ := hprefix
    exact Finset.mem_union_left terminalCycle
      (mem_orbitPrefix_of_iter hdB hd)
  · exact Finset.mem_union_right (orbitPrefix u B) hcycle

/--
The containing set for a fibre has at most `B+4` values:
`B+1` prefix positions and the three terminal-cycle values.
-/
theorem orbitPrefix_union_terminalCycle_card_le
    (u B : Nat) :
    (orbitPrefix u B ∪ terminalCycle).card ≤ B + 4 := by
  calc
    (orbitPrefix u B ∪ terminalCycle).card
        ≤ (orbitPrefix u B).card + terminalCycle.card :=
      Finset.card_union_le _ _
    _ ≤ (B + 1) + 3 := by
      exact Nat.add_le_add
        (orbitPrefix_card_le u B)
        (by simp [terminalCycle])
    _ = B + 4 := by omega

end ERE

#print axioms ERE.collatz_terminal_cycle
#print axioms ERE.iter_terminal_cycle
#print axioms ERE.iter_mem_terminalCycle_of_hit_one
#print axioms ERE.later_value_mem_prefix_or_terminalCycle
#print axioms ERE.later_value_mem_bounded_prefix_or_terminalCycle
#print axioms ERE.orbitPrefix_card_le
#print axioms ERE.later_value_mem_bounded_orbit_set
#print axioms ERE.orbitPrefix_union_terminalCycle_card_le
