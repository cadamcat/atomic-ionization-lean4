import OAI.Analysis.CoulombRadii.SpectralTheory.StrictBinding

namespace AtomicIonization.AtomicBinding

open OAI.NeutralAtom MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section

def chargeCenter (Z : ℕ) : Position := (8 * (Z : ℝ)) • EuclideanSpace.single 0 1

theorem chargeCenter_norm (Z : ℕ) : ‖chargeCenter Z‖ = 8 * (Z : ℝ) := by
  simp [chargeCenter, norm_smul, EuclideanSpace.single, PiLp.norm_single]

def chargePacket (Z : ℕ) (t : ℝ) (y : Position) : ℝ :=
  (Real.sqrt (t^3 * distantMass))⁻¹ * bindingBump (t⁻¹ • y - chargeCenter Z)

theorem chargePacket_smooth (Z : ℕ) (t : ℝ) : ContDiff ℝ ∞ (chargePacket Z t) :=
  contDiff_const.mul (bindingBump.contDiff.comp
    (((contDiff_const (c := t⁻¹)).smul (contDiff_id (E := Position))).sub contDiff_const))

theorem chargePacket_compact (Z : ℕ) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (chargePacket Z t) := by
  let u : ℝˣ := Units.mk0 t⁻¹ (inv_ne_zero ht.ne')
  have hc : HasCompactSupport (fun y : Position => bindingBump (t⁻¹ • y - chargeCenter Z)) :=
    (bindingBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (chargeCenter Z))).comp_homeomorph
      (Homeomorph.smul u)
  exact hc.mul_left

theorem chargePacket_memLp (Z : ℕ) {t : ℝ} (ht : 0 < t) :
    MemLp (chargePacket Z t) 2 volume :=
  (chargePacket_smooth Z t).continuous.memLp_of_hasCompactSupport (chargePacket_compact Z ht)

theorem chargePacket_derivative_memLp (Z : ℕ) {t : ℝ} (ht : 0 < t) (v : Position) :
    MemLp (fun y => fderiv ℝ (chargePacket Z t) y v) 2 volume :=
  (((chargePacket_smooth Z t).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    ((chargePacket_compact Z ht).fderiv_apply ℝ v)

theorem integral_charge_comp (Z : ℕ) {t : ℝ} (ht : 0 < t) (F : Position → ℝ) :
    (∫ y : Position, F (t⁻¹ • y - chargeCenter Z)) = t^3 * ∫ y : Position, F y := by
  rw [show (fun y : Position => F (t⁻¹ • y - chargeCenter Z)) =
      (fun y : Position => (fun z : Position => F (z - chargeCenter Z)) (t⁻¹ • y)) from rfl]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun z : Position => F (z - chargeCenter Z)) t⁻¹ (hR := by positivity)]
  simp [integral_sub_right_eq_self, Position, inv_pow]

theorem chargePacket_normalized (Z : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ y : Position, (chargePacket Z t y)^2) = 1 := by
  simp only [chargePacket, mul_pow, integral_const_mul]
  rw [integral_charge_comp Z ht (fun y => (bindingBump y)^2)]
  rw [inv_pow, Real.sq_sqrt (mul_nonneg (pow_nonneg ht.le 3) distantMass_pos.le)]
  change (t^3 * distantMass)⁻¹ * (t^3 * distantMass) = 1
  exact inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ ht.ne') distantMass_pos.ne')

theorem chargePacket_inner_zero (Z : ℕ) {t : ℝ} (ht : 0 < t) {y : Position}
    (hy : ‖y‖ ≤ (8 * (Z : ℝ) - 2) * t) : chargePacket Z t y = 0 := by
  have hnorm : ‖t⁻¹ • y‖ ≤ 8 * (Z : ℝ) - 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_iff₀ ht).mpr (by nlinarith [hy])
  have hdist : 2 ≤ ‖t⁻¹ • y - chargeCenter Z‖ := by
    have H := norm_sub_norm_le (chargeCenter Z) (t⁻¹ • y)
    rw [chargeCenter_norm, norm_sub_rev] at H
    linarith
  have H := bindingBump.zero_of_le_dist (by simpa [bindingBump] using hdist)
  simp [chargePacket, H]

theorem chargePacket_outer_zero (Z : ℕ) {t : ℝ} (ht : 0 < t) {y : Position}
    (hy : (8 * (Z : ℝ) + 2) * t ≤ ‖y‖) : chargePacket Z t y = 0 := by
  have hnorm : 8 * (Z : ℝ) + 2 ≤ ‖t⁻¹ • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact (le_inv_mul_iff₀ ht).mpr (by nlinarith [hy])
  have hdist : 2 ≤ ‖t⁻¹ • y - chargeCenter Z‖ := by
    have H := norm_sub_norm_le (t⁻¹ • y) (chargeCenter Z)
    rw [chargeCenter_norm] at H
    linarith
  have H := bindingBump.zero_of_le_dist (by simpa [bindingBump] using hdist)
  simp [chargePacket, H]

theorem chargePacket_derivative_zero (Z : ℕ) (hZ : 1 ≤ Z) {t : ℝ} (ht : 0 < t)
    {y : Position} (hy : ‖y‖ ≤ 2 * t) (v : Position) :
    fderiv ℝ (chargePacket Z t) y v = 0 := by
  have hZ' : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hn : ‖y‖ < (8 * (Z : ℝ) - 2) * t := by nlinarith
  have he : chargePacket Z t =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hn] with z hz
    exact chargePacket_inner_zero Z ht hz.le
  rw [he.fderiv_eq]
  simp

theorem chargePacket_fderiv (Z : ℕ) {t : ℝ} (y v : Position) :
    fderiv ℝ (chargePacket Z t) y v =
      (Real.sqrt (t^3 * distantMass))⁻¹ * t⁻¹ *
        fderiv ℝ (fun z : Position => bindingBump z) (t⁻¹ • y - chargeCenter Z) v := by
  have hb := ((bindingBump_smooth).differentiable (by simp) (t⁻¹ • y - chargeCenter Z)).hasFDerivAt
  have hc := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul t⁻¹).sub_const (chargeCenter Z)
  have hh := ((hb.comp y hc).const_mul (Real.sqrt (t^3 * distantMass))⁻¹).fderiv
  change fderiv ℝ (fun y : Position => (Real.sqrt (t^3 * distantMass))⁻¹ *
    (bindingBump ∘ fun x : Position => (t⁻¹ • id) x - chargeCenter Z) y) y v = _
  rw [hh]
  simp [mul_assoc]

theorem chargePacket_gradientNorm (Z : ℕ) {t : ℝ} (ht : 0 < t) :
    oneParticleGradientNorm (chargePacket Z t) =
      t⁻¹^2 * (distantMass⁻¹ * oneParticleGradientNorm bindingBump) := by
  unfold oneParticleGradientNorm
  simp_rw [chargePacket_fderiv, mul_pow, integral_const_mul]
  have hi (a : Fin 3) := integral_charge_comp Z ht
    (fun y => (fderiv ℝ (fun z : Position => bindingBump z) y (EuclideanSpace.single a 1))^2)
  simp_rw [hi]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt (mul_nonneg (pow_nonneg ht.le 3) distantMass_pos.le)]
  field_simp

end
end AtomicIonization.AtomicBinding
