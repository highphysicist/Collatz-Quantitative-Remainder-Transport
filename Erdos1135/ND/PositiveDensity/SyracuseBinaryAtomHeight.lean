import Erdos1135.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135.ND.PositiveDensity.Geom2ShiftedWideSymmetricReferenceDensityTransport

namespace Erdos1135.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem syracStep_fixedExponent_injective (q : ℕ) (a : ℕ+) :
    Function.Injective (fun y => Tao.syracStep q y a) := by
  intro y z h
  let x := Tao.syracStep q y a
  have hy : Tao.syracStep q y a = (x.val : ZMod (3 ^ (q+1))) := by simp [x]
  have hz : Tao.syracStep q z a = (x.val : ZMod (3 ^ (q+1))) := by
    simpa [x] using h.symm
  exact (ndSyracuseFullReversePredecessor_residue q x.val y a hy).symm.trans
    (ndSyracuseFullReversePredecessor_residue q x.val z a hz)

theorem syracStep_levelOne_of_eq (q : ℕ) (x : ZMod (3 ^ (q+1)))
    (y : ZMod (3 ^ q)) (a : ℕ+) (h : Tao.syracStep q y a = x) :
    Tao.syracStep 0 0 a = (x.val : ZMod (3 ^ 1)) := by
  have hp := ndSyracuseFullReverseLabel_product_modEq_one q x.val y a
    (by simpa using h)
  have hc : (2 : ZMod (3^1)) ^ (a:ℕ) * (x.val : ZMod (3^1)) = 1 := by
    have hh := (ZMod.natCast_eq_natCast_iff (2^(a:ℕ)*x.val) 1 3).mpr hp
    simpa using hh
  have hi := Tao.taoZModThreePow_inv_two_pow_mul 1 (a:ℕ)
  have hh := congrArg (fun z : ZMod (3^1) => ((2 : ZMod (3^1))^(a:ℕ))⁻¹*z) hc
  simpa [Tao.syracStep, ← mul_assoc, hi] using hh.symm

theorem syracPMF_one_toReal_le_twoThirds (x : ZMod (3^1)) :
    (Tao.syracPMF 1 x).toReal ≤ (2/3:ℝ) := by
  rw [Tao.syracPMF_one_apply]
  split_ifs <;> norm_num

theorem syracPMF_succ_height_bound (q : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ y, (Tao.syracPMF q y).toReal ≤ B)
    (x : ZMod (3^(q+1))) :
    (Tao.syracPMF (q+1) x).toReal ≤ B * (2/3:ℝ) := by
  classical
  let z : ZMod (3^1) := x.val
  let f := fun y a => ndSyracuseFullReverseLabelMass q x y a
  let g := fun a => ndSyracuseFullReverseLabelMass 0 z 0 a
  have hs (y : ZMod (3^q)) : Summable (f y) := by
    simpa [f] using summable_ndSyracuseFullReverseLabelMass q x.val y
  have hg : Summable g := by
    simpa [g, z] using summable_ndSyracuseFullReverseLabelMass 0 x.val 0
  have hcolumn (a : ℕ+) : (∑ y, f y a) ≤ B * g a := by
    by_cases hex : ∃ y, Tao.syracStep q y a = x
    · obtain ⟨y, hy⟩ := hex
      have hz := syracStep_levelOne_of_eq q x y a hy
      have heq : (∑ t, f t a) = f y a := by
        apply Finset.sum_eq_single y
        · intro t _ ht
          have hn : Tao.syracStep q t a ≠ x := by
            intro hh
            exact ht (syracStep_fixedExponent_injective q a (hh.trans hy.symm))
          simp [f, ndSyracuseFullReverseLabelMass, hn]
        · simp
      rw [heq]
      simpa [f, g, z, ndSyracuseFullReverseLabelMass, hy, hz, Tao.syracPMF]
        using mul_le_mul_of_nonneg_right (hb y) (ENNReal.toReal_nonneg (a := Tao.geom2PNat a))
    · have hn : ∀ y, Tao.syracStep q y a ≠ x := by simpa using hex
      have hzero : (∑ y, f y a) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        simp [f, ndSyracuseFullReverseLabelMass, hn y]
      rw [hzero]
      exact mul_nonneg hB (ndSyracuseFullReverseLabelMass_nonneg 0 z 0 a)
  have hsumg : (∑' a, g a) = (Tao.syracPMF 1 z).toReal := by
    simpa [g] using sum_ndSyracuseFullReverseLabelMass_eq_syracPMF 0 z
  calc
    _ = ∑ y, ∑' a, f y a := (sum_ndSyracuseFullReverseLabelMass_eq_syracPMF q x).symm
    _ = ∑' a, ∑ y, f y a := (Summable.tsum_finsetSum (s := Finset.univ)
      (fun y _ => hs y)).symm
    _ ≤ ∑' a, B * g a := Summable.tsum_le_tsum hcolumn
      (summable_sum (fun y _ => hs y)) (hg.mul_left B)
    _ = B * (Tao.syracPMF 1 z).toReal := by rw [tsum_mul_left, hsumg]
    _ ≤ B * (2/3:ℝ) := mul_le_mul_of_nonneg_left (syracPMF_one_toReal_le_twoThirds z) hB

theorem syracPMF_toReal_le_twoThirds_pow (q : ℕ) (x : ZMod (3^q)) :
    (Tao.syracPMF q x).toReal ≤ (2/3:ℝ)^q := by
  induction q with
  | zero =>
    simp only [Tao.syracPMF, PMF.pure_apply, pow_zero]
    split_ifs <;> norm_num
  | succ q ih =>
    simpa only [pow_succ] using syracPMF_succ_height_bound q _ (by positivity) ih x

theorem unitReferenceDensity_binary_upper (m : ℕ) (y : ZMod (3^m)) :
    ndSyracuseUnitReferenceDensity m y ≤ (2/3:ℝ) * ((2^m:ℕ):ℝ) := by
  have h := mul_le_mul_of_nonneg_left (syracPMF_toReal_le_twoThirds_pow m y)
    (show 0 ≤ (2/3:ℝ)*3^m by positivity)
  have he : (2/3:ℝ)*3^m*(2/3:ℝ)^m = (2/3:ℝ)*2^m := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [he] at h
  simpa [ndSyracuseUnitReferenceDensity, ndSyracuseUniformDensity,
    Tao.syracPMFMassVector, ← mul_assoc] using h

end

end Erdos1135.ND.PositiveDensity
