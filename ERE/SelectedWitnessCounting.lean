import ERE.UniformLiveTargetTime

namespace ERE

/--
A finite map whose fibres have cardinality at most `K` has domain
cardinality at most `K` times its image cardinality.
-/
theorem card_le_image_card_mul_of_fiber_le
    {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (s : Finset α)
    (f : α → β)
    (K : Nat)
    (hfiber :
      ∀ y ∈ s.image f,
        (s.filter fun x => f x = y).card ≤ K) :
    s.card ≤ (s.image f).card * K := by
  classical

  have hmaps :
      ∀ x ∈ s, f x ∈ s.image f := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

  have hpartition :=
    Finset.sum_fiberwise_of_maps_to
      hmaps (fun _ : α => (1 : Nat))

  calc
    s.card = ∑ x ∈ s, (1 : Nat) := by simp
    _ = ∑ y ∈ s.image f,
          ∑ x ∈ s with f x = y, (1 : Nat) :=
      hpartition.symm
    _ ≤ ∑ y ∈ s.image f, K := by
      apply Finset.sum_le_sum
      intro y hy
      simpa using hfiber y hy
    _ = (s.image f).card * K := by simp

/--
If every target in `s` is reached by its selected witness `witness w`,
and every target reaches `1` in at most `B` steps, then each fibre of
the selected-witness map has at most `B+4` elements.
-/
theorem selected_witness_fiber_card_le
    (s : Finset Nat)
    (witness : Nat → Nat)
    (B y : Nat)
    (hy : y ∈ s.image witness)
    (hreach :
      ∀ w ∈ s, Reaches w (witness w))
    (hstop :
      ∀ w ∈ s, ∃ b : Nat,
        b ≤ B ∧ iter collatz b w = 1) :
    (s.filter fun w => witness w = y).card ≤ B + 4 := by
  classical

  let fiber : Finset Nat :=
    s.filter fun w => witness w = y

  have hex :
      ∀ w, w ∈ fiber →
        ∃ k : Nat, iter collatz k y = w := by
    intro w hw
    have hws : w ∈ s :=
      (Finset.mem_filter.mp hw).1
    have hwy : witness w = y :=
      (Finset.mem_filter.mp hw).2
    have hr : Reaches w y := by
      simpa [hwy] using hreach w hws
    exact hr

  let occurTime : Nat → Nat :=
    fun w =>
      if hw : w ∈ fiber then
        Classical.choose (hex w hw)
      else
        0

  have hoccurs :
      ∀ w ∈ fiber,
        iter collatz (occurTime w) y = w := by
    intro w hw
    simp only [occurTime, dif_pos hw]
    exact Classical.choose_spec (hex w hw)

  have hstops :
      ∀ w ∈ fiber, ∃ b : Nat,
        b ≤ B ∧ iter collatz b w = 1 := by
    intro w hw
    exact hstop w (Finset.mem_filter.mp hw).1

  change fiber.card ≤ B + 4
  exact finite_collatz_orbit_fiber_card_le
    fiber y B occurTime hoccurs hstops

/--
Finite selected-witness counting theorem.

The target set is at most `(B+4)` times the number of distinct
selected witnesses.
-/
theorem selected_witness_image_count
    (s : Finset Nat)
    (witness : Nat → Nat)
    (B : Nat)
    (hreach :
      ∀ w ∈ s, Reaches w (witness w))
    (hstop :
      ∀ w ∈ s, ∃ b : Nat,
        b ≤ B ∧ iter collatz b w = 1) :
    s.card ≤ (s.image witness).card * (B + 4) := by
  apply card_le_image_card_mul_of_fiber_le
  intro y hy
  exact selected_witness_fiber_card_le
    s witness B y hy hreach hstop

end ERE

#print axioms ERE.card_le_image_card_mul_of_fiber_le
#print axioms ERE.selected_witness_fiber_card_le
#print axioms ERE.selected_witness_image_count
