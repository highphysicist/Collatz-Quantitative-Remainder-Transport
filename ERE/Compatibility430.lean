import Mathlib.Tactic.Abel
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card

namespace ERECompat

open Classical

theorem nodup_length_le_of_subset {α : Type*} [DecidableEq α]
    {l₁ l₂ : List α} (hnd : l₁.Nodup) (hsub : l₁ ⊆ l₂) :
    l₁.length ≤ l₂.length := by
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card (by
    intro x hx
    simpa using hsub (by simpa using hx))).trans (List.toFinset_card_le l₂)

theorem nodup_finRange : ∀ n, (List.finRange n).Nodup
  | 0 => by simp
  | n + 1 => by
      rw [List.finRange_succ_last]
      apply List.nodup_append.mpr
      refine ⟨?_, by simp, ?_⟩
      · exact List.Nodup.map
          (f := fun i : Fin n => i.castSucc)
          (fun _ _ heq => Fin.castSucc_inj.mp heq)
          (nodup_finRange n)
      · intro a ha b hb
        simp only [List.mem_map] at ha
        simp only [List.mem_singleton] at hb
        obtain ⟨i, _, rfl⟩ := ha
        subst b
        exact Fin.ne_of_lt i.castSucc_lt_last

end ERECompat
