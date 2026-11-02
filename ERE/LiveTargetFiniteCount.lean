import ERE.OddFastDensity

namespace EREQuantitativeTransport

open Erdos1135
open Erdos1135.ND.PositiveDensity

noncomputable section

/-- Odd logarithmic-time convergent inputs strictly below `X`. -/
def oddFastBelow (C : ℝ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter
    (fun n => n ∈ oddRawCollatzLogTimeOneSet C)

/-- Distinct live targets obtained from odd fast inputs below `X`. -/
def liveTargetsBelow (C : ℝ) (X : ℕ) : Finset ℕ :=
  (oddFastBelow C X).image liveTarget

@[simp]
theorem mem_oddFastBelow_iff
    {C : ℝ} {X n : ℕ} :
    n ∈ oddFastBelow C X ↔
      n < X ∧ n ∈ oddRawCollatzLogTimeOneSet C := by
  classical
  simp [oddFastBelow]

theorem odd_of_mem_oddFastBelow
    {C : ℝ} {X n : ℕ}
    (hn : n ∈ oddFastBelow C X) :
    Odd n := by
  exact (mem_oddFastBelow_iff.mp hn).2.1

theorem rawFast_of_mem_oddFastBelow
    {C : ℝ} {X n : ℕ}
    (hn : n ∈ oddFastBelow C X) :
    n ∈ rawCollatzLogTimeOneSet C := by
  exact (mem_oddFastBelow_iff.mp hn).2.2

theorem lt_of_mem_oddFastBelow
    {C : ℝ} {X n : ℕ}
    (hn : n ∈ oddFastBelow C X) :
    n < X :=
  (mem_oddFastBelow_iff.mp hn).1

@[simp]
theorem mem_liveTargetsBelow_iff
    {C : ℝ} {X w : ℕ} :
    w ∈ liveTargetsBelow C X ↔
      ∃ n ∈ oddFastBelow C X, liveTarget n = w := by
  simp [liveTargetsBelow]

theorem liveTarget_data_of_mem
    {C : ℝ} {X w : ℕ}
    (hw : w ∈ liveTargetsBelow C X) :
    ∃ n : ℕ,
      n < X ∧
      Odd n ∧
      n ∈ rawCollatzLogTimeOneSet C ∧
      liveTarget n = w := by
  obtain ⟨n, hn, rfl⟩ :=
    mem_liveTargetsBelow_iff.mp hw

  exact ⟨n,
    lt_of_mem_oddFastBelow hn,
    odd_of_mem_oddFastBelow hn,
    rawFast_of_mem_oddFastBelow hn,
    rfl⟩

/-- Every finite live target is nonzero modulo three. -/
theorem liveTarget_mem_not_divisible_by_three
    {C : ℝ} {X w : ℕ}
    (hw : w ∈ liveTargetsBelow C X) :
    w % 3 ≠ 0 := by
  obtain ⟨n, _, rfl⟩ :=
    mem_liveTargetsBelow_iff.mp hw
  exact liveTarget_not_divisible_by_three n

/-- Every finite live target is strictly below `3*X+1`. -/
theorem liveTarget_mem_lt
    {C : ℝ} {X w : ℕ}
    (hw : w ∈ liveTargetsBelow C X) :
    w < 3 * X + 1 := by
  obtain ⟨n, hn, rfl⟩ :=
    mem_liveTargetsBelow_iff.mp hw

  have hnX : n < X :=
    lt_of_mem_oddFastBelow hn

  have hbound := liveTarget_le n
  omega

/-- The original odd input reaches its corresponding live target. -/
theorem source_reaches_liveTarget_of_mem
    {C : ℝ} {X n : ℕ}
    (hn : n ∈ oddFastBelow C X) :
    Erdos1135.Reaches n (liveTarget n) :=
  odd_reaches_liveTarget
    (odd_of_mem_oddFastBelow hn)

/--
The live-target map is injective on inputs divisible by three.
-/
theorem liveTarget_injective_on_three
    {s : Finset ℕ} :
    Set.InjOn liveTarget
      (↑(s.filter (fun n => n % 3 = 0)) : Set ℕ) := by
  intro x hx y hy hxy

  have hx3 : x % 3 = 0 :=
    (Finset.mem_filter.mp hx).2

  have hy3 : y % 3 = 0 :=
    (Finset.mem_filter.mp hy).2

  simp [liveTarget, hx3, hy3] at hxy
  omega

/--
The live-target map is injective on inputs not divisible by three.
-/
theorem liveTarget_injective_on_live
    {s : Finset ℕ} :
    Set.InjOn liveTarget
      (↑(s.filter (fun n => n % 3 ≠ 0)) : Set ℕ) := by
  intro x hx y hy hxy

  have hx3 : x % 3 ≠ 0 :=
    (Finset.mem_filter.mp hx).2

  have hy3 : y % 3 ≠ 0 :=
    (Finset.mem_filter.mp hy).2

  simpa [liveTarget, hx3, hy3] using hxy

/--
Step 4: mapping a finite set through `liveTarget` loses at most a factor of
two in cardinality.
-/
theorem card_le_two_mul_card_liveTarget_image
    (s : Finset ℕ) :
    s.card ≤ 2 * (s.image liveTarget).card := by
  let a := s.filter (fun n => n % 3 = 0)
  let b := s.filter (fun n => n % 3 ≠ 0)

  have hsub : s ⊆ a ∪ b := by
    intro n hn
    by_cases h3 : n % 3 = 0
    · exact Finset.mem_union_left b
        (Finset.mem_filter.mpr ⟨hn, h3⟩)
    · exact Finset.mem_union_right a
        (Finset.mem_filter.mpr ⟨hn, h3⟩)

  have ha_sub : a ⊆ s := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1

  have hb_sub : b ⊆ s := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1

  have ha_image :
      (a.image liveTarget).card = a.card := by
    apply Finset.card_image_iff.mpr
    exact liveTarget_injective_on_three

  have hb_image :
      (b.image liveTarget).card = b.card := by
    apply Finset.card_image_iff.mpr
    exact liveTarget_injective_on_live

  have ha_image_sub :
      a.image liveTarget ⊆ s.image liveTarget :=
    Finset.image_subset_image ha_sub

  have hb_image_sub :
      b.image liveTarget ⊆ s.image liveTarget :=
    Finset.image_subset_image hb_sub

  have ha_card :
      a.card ≤ (s.image liveTarget).card := by
    rw [← ha_image]
    exact Finset.card_le_card ha_image_sub

  have hb_card :
      b.card ≤ (s.image liveTarget).card := by
    rw [← hb_image]
    exact Finset.card_le_card hb_image_sub

  calc
    s.card ≤ (a ∪ b).card :=
      Finset.card_le_card hsub
    _ ≤ a.card + b.card :=
      Finset.card_union_le a b
    _ ≤
        (s.image liveTarget).card +
          (s.image liveTarget).card :=
      Nat.add_le_add ha_card hb_card
    _ = 2 * (s.image liveTarget).card := by
      omega

/--
The finite odd-fast set loses at most a factor two when converted to live
targets.
-/
theorem oddFast_card_le_two_mul_liveTargets_card
    (C : ℝ) (X : ℕ) :
    (oddFastBelow C X).card ≤
      2 * (liveTargetsBelow C X).card := by
  exact card_le_two_mul_card_liveTarget_image
    (oddFastBelow C X)

end

end EREQuantitativeTransport

#print axioms EREQuantitativeTransport.oddFast_card_le_two_mul_liveTargets_card
#print axioms EREQuantitativeTransport.liveTarget_mem_not_divisible_by_three
#print axioms EREQuantitativeTransport.liveTarget_mem_lt
#print axioms EREQuantitativeTransport.source_reaches_liveTarget_of_mem
