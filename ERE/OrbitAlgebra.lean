import ERE.LiveTargetFiniteCount

namespace ERE

/-- Zero iterations leave the input unchanged. -/
@[simp]
theorem iter_zero (f : Nat → Nat) (x : Nat) :
    iter f 0 x = x := by
  rfl

/-- One additional iteration applies `f` before the remaining iterations. -/
@[simp]
theorem iter_succ (f : Nat → Nat) (k x : Nat) :
    iter f (k + 1) x = iter f k (f x) := by
  rfl

/-- An explicitly exhibited iterate gives reachability. -/
theorem reaches_of_iter_eq
    {v n : Nat} {k : Nat}
    (h : iter collatz k n = v) :
    Reaches v n :=
  ⟨k, h⟩

/-- Every number reaches itself in zero steps. -/
theorem reaches_refl (n : Nat) :
    Reaches n n :=
  ⟨0, rfl⟩

/--
If `u` occurs at time `i` and `v` occurs at a later time `j` on the
same deterministic orbit, then `u` reaches `v`.
-/
theorem reaches_of_iter_indices
    {f : Nat → Nat} {n u v i j : Nat}
    (hi : iter f i n = u)
    (hj : iter f j n = v)
    (hij : i ≤ j) :
    ∃ d : Nat, iter f d u = v := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
  refine ⟨d, ?_⟩
  calc
    iter f d u = iter f d (iter f i n) := by rw [hi]
    _ = iter f (d + i) n := by
      symm
      exact iter_add f d i n
    _ = iter f j n := by
      rw [hd, Nat.add_comm]
    _ = v := hj

/--
Two indexed points on one orbit are comparable: one is reachable
from the other.
-/
theorem iter_indices_comparable
    {f : Nat → Nat} {n u v i j : Nat}
    (hi : iter f i n = u)
    (hj : iter f j n = v) :
    (∃ d : Nat, iter f d u = v) ∨
      (∃ d : Nat, iter f d v = u) := by
  rcases Nat.le_total i j with hij | hji
  · exact Or.inl (reaches_of_iter_indices hi hj hij)
  · exact Or.inr (reaches_of_iter_indices hj hi hji)

/--
Any two values reached from one Collatz starting value are comparable
under Collatz reachability.
-/
theorem reached_values_comparable
    {n u v : Nat}
    (hu : Reaches u n)
    (hv : Reaches v n) :
    Reaches v u ∨ Reaches u v := by
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := hv
  rcases iter_indices_comparable hi hj with huv | hvu
  · exact Or.inl huv
  · exact Or.inr hvu

end ERE

#print axioms ERE.iter_zero
#print axioms ERE.iter_succ
#print axioms ERE.reaches_of_iter_eq
#print axioms ERE.reaches_refl
#print axioms ERE.reaches_trans
#print axioms ERE.reaches_of_iter_indices
#print axioms ERE.iter_indices_comparable
#print axioms ERE.reached_values_comparable
